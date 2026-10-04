/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Devissage
import SGA.Foundations.Cohomology.RelativeSerre
import SGA.Foundations.Cohomology.TwistProjection
import SGA.Foundations.Cohomology.PushforwardProjective

/-!
# Finiteness of cohomology for proper morphisms

We prove `ProperFinitenessStatement` (EGA III 3.2.1; Stacks Tag 02O5; Hartshorne III.8.8 (b)):
for `A` noetherian, `f : X ⟶ Spec A` proper and `M` coherent, each `Hᵖ(X, M)` is a finitely
generated `A`-module.

* `CohomologyAux.finiteCohomology_of_bijective_on_open`: a morphism of coherent modules which is
  an isomorphism over a dense open transfers finiteness, given it for modules supported in proper
  closed subsets.
* `CohomologyAux.exists_twist_acyclic`: relative Serre vanishing for closed subschemes of
  `ℙ(σ; Z)`, via the projection formula and Leray for the closed immersion.
* `CohomologyAux.finiteCohomology_of_isIntegral`: the integral case, via Chow's lemma
  (`exists_isHProjective_of_isProper`), the coherence of `π_*` for H-projective `π`, relative Serre
  vanishing, Leray for `π` and multiplication by a power of a coordinate.
* `properFinitenessStatement`: the theorem, by the dévissage of `Devissage`.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TopCat.Presheaf

namespace AlgebraicGeometry.CohomologyAux

section Preliminaries

variable {X Y : Scheme.{u}}

/-- A scheme separated over an affine scheme has affine diagonal. -/
lemma isAffineHom_diagonal_of_isSeparated {S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    [IsAffine S] : IsAffineHom (pullback.diagonal (terminal.from X)) := by
  have : IsSeparated (terminal.from S) := inferInstance
  have e : terminal.from X = f ≫ terminal.from S := terminal.hom_ext _ _
  have : IsSeparated (terminal.from X) := by rw [e]; infer_instance
  infer_instance

/-- A section of a sheaf vanishing on all affine opens contained in `V` vanishes. -/
lemma eq_zero_of_forall_affine_le (M : X.Modules) (V : X.Opens)
    (h : ∀ V' : X.Opens, V' ≤ V → IsAffineOpen V' → ∀ t : Γ(M, V'), t = 0) (s : Γ(M, V)) :
    s = 0 := by
  have hx : ∀ x : V, ∃ W : X.Opens, IsAffineOpen W ∧ x.1 ∈ W ∧ W ≤ V := fun x ↦ by
    obtain ⟨W, hW, hxW, hWV⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
      x.2
    exact ⟨W, hW, hxW, hWV⟩
  choose W hW hxW hWV using hx
  refine TopCat.Sheaf.eq_of_locally_eq' M.toAbSheaf W V (fun x ↦ homOfLE (hWV x))
    (fun x hxV ↦ Opens.mem_iSup.mpr ⟨⟨x, hxV⟩, hxW ⟨x, hxV⟩⟩) s 0 fun x ↦ ?_
  rw [map_zero]
  exact h _ (hWV x) (hW x) _

/-- Along a morphism which is an isomorphism over `U`, the inverse image of sections over opens
contained in `U` is bijective. -/
lemma pullbackApp_bijective_of_isIso_morphismRestrict (π : X ⟶ Y) (U : Y.Opens)
    [IsIso (π ∣_ U)] (G : Y.Modules) {V : Y.Opens} (hV : V ≤ U) :
    Function.Bijective (Scheme.Modules.pullbackApp π G V) := by
  have hι : IsOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) := by
    rw [← morphismRestrict_ι]; infer_instance
  have hr : ((π ⁻¹ᵁ U).ι ≫ π).opensRange = U := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.coe_opensRange]
    have e : ((π ⁻¹ᵁ U).ι ≫ π) = (π ∣_ U) ≫ U.ι := (morphismRestrict_ι π U).symm
    rw [e, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Set.range_eq_univ.mpr (inferInstance : Surjective (π ∣_ U)).surj, Set.image_univ,
      Scheme.Opens.range_ι]
  have h1 := Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion ((π ⁻¹ᵁ U).ι ≫ π) G V
    (hr.symm ▸ hV)
  have h2 := Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion (π ⁻¹ᵁ U).ι
    ((Scheme.Modules.pullback π).obj G) (π ⁻¹ᵁ V)
    (by rw [Scheme.Opens.opensRange_ι]; exact π.preimage_mono hV)
  have h3 := ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp (π ⁻¹ᵁ U).ι π).hom.app G).app ((π ⁻¹ᵁ U).ι ⁻¹ᵁ π ⁻¹ᵁ V))
  have e : ⇑(Scheme.Modules.pullbackApp ((π ⁻¹ᵁ U).ι ≫ π) G V) =
      ⇑(((Scheme.Modules.pullbackComp (π ⁻¹ᵁ U).ι π).hom.app G).app _) ∘
        ⇑(Scheme.Modules.pullbackApp (π ⁻¹ᵁ U).ι ((Scheme.Modules.pullback π).obj G) (π ⁻¹ᵁ V)) ∘
          ⇑(Scheme.Modules.pullbackApp π G V) := by
    ext s
    exact Scheme.Modules.pullbackApp_comp _ _ G V s
  rw [e] at h1
  exact (Function.Bijective.of_comp_iff' (h3.comp h2) _).mp h1

/-- If `π` is closed, surjective and an isomorphism over a non-empty open `U`, and `X'` is
irreducible, then for every non-empty open `D ⊆ X'` there is a non-empty open `W ⊆ U` with
`π⁻¹ W ⊆ D`. -/
lemma exists_open_preimage_le {X' : Scheme.{u}} [IrreducibleSpace X'] (π : X' ⟶ Y)
    [UniversallyClosed π] [Surjective π] (U : Y.Opens) (hU : (U : Set Y).Nonempty)
    [IsIso (π ∣_ U)] (D : X'.Opens) (hD : (D : Set X').Nonempty) :
    ∃ W : Y.Opens, (W : Set Y).Nonempty ∧ W ≤ U ∧ π ⁻¹ᵁ W ≤ D := by
  have hcl : IsClosed (π '' (D : Set X')ᶜ) := π.isClosedMap _ D.2.isClosed_compl
  let W : Y.Opens := U ⊓ ⟨(π '' (D : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  refine ⟨W, ?_, inf_le_left, fun x hx ↦ ?_⟩
  · obtain ⟨z, hz⟩ := hU
    obtain ⟨x₁, rfl⟩ := π.surjective z
    obtain ⟨x, hxU, hxD⟩ := (IrreducibleSpace.isIrreducible_univ X').isPreirreducible
      (π ⁻¹ᵁ U) D (π ⁻¹ᵁ U).2 D.2 ⟨x₁, trivial, hz⟩ (by simpa using hD)
    refine ⟨π x, hxD.1, ?_⟩
    rintro ⟨y, hyD, hxy⟩
    have hyU : y ∈ π ⁻¹ᵁ U := by
      change π y ∈ U; rw [hxy]; exact hxD.1
    have hinj := (ConcreteCategory.bijective_of_isIso (π ∣_ U).base).1
    have : (⟨y, hyU⟩ : π ⁻¹ᵁ U) = ⟨x, hxD.1⟩ := by
      apply hinj
      apply Subtype.ext
      exact (morphismRestrict_base_coe π U ⟨y, hyU⟩).trans
        (hxy.trans (morphismRestrict_base_coe π U ⟨x, hxD.1⟩).symm)
    have hyx : y = x := congrArg Subtype.val this
    exact hyD (hyx ▸ hxD.2)
  · by_contra hxD
    exact hx.2 ⟨x, hxD, rfl⟩

end Preliminaries

section Comparison

variable {Z : Scheme.{u}}

/-- **Comparison over a dense open** (EGA III 3.2.1, proof): let `φ : G ⟶ Q` be a morphism of
coherent modules which is bijective on sections over the opens contained in a non-empty open `W`.
If `Q` has finitely generated cohomology, and so do all coherent modules supported in a proper
closed subset, then so does `G` (the kernel and cokernel of `φ` are supported in `Z ∖ U` for an
affine `U ⊆ W`: `vanishesOff_kernel_factorThruImage`, `vanishesOff_cokernel`). -/
theorem finiteCohomology_of_bijective_on_open [IsLocallyNoetherian Z] {R : Type*} [CommRing R]
    [IsNoetherianRing R] (ρ : R →+* Γ(Z, ⊤))
    (IH : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
      VanishesOff N T' → FiniteCohomology ρ N)
    (G Q : Z.Modules) [G.IsCoherent] [Q.IsCoherent] (φ : G ⟶ Q) (W : Z.Opens)
    (hW : (W : Set Z).Nonempty) (hφ : ∀ V : Z.Opens, V ≤ W → Function.Bijective (φ.app V))
    (hQ : FiniteCohomology ρ Q) : FiniteCohomology ρ G := by
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : Q.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  -- a nonempty affine open `U ⊆ W`
  obtain ⟨z, hz⟩ := hW
  obtain ⟨U, hU, hzU, hUW⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) hz
  have hT : IsClosed (U : Set Z)ᶜ := U.2.isClosed_compl
  have hTne : (U : Set Z)ᶜ ≠ Set.univ := fun h ↦ (h ▸ Set.mem_univ z : z ∈ (U : Set Z)ᶜ) hzU
  -- the two short exact sequences
  have hS₁ := shortExact_kernelSequence (Abelian.factorThruImage φ)
  have hS₂ := shortExact_kernelSequence (cokernel.π φ)
  have : (Abelian.image φ).IsQuasicoherent := isQuasicoherent_image φ
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₂.IsQuasicoherent :=
    ‹G.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₃.IsQuasicoherent :=
    ‹(Abelian.image φ).IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁.IsQuasicoherent :=
    isQuasicoherent_X₁_of_shortExact hS₁
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₂.IsCoherent :=
    ‹G.IsCoherent›
  have hK : (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁.IsCoherent :=
    isCoherent_X₁_of_shortExact hS₁
  have : (ShortComplex.kernelSequence (cokernel.π φ)).X₁.IsQuasicoherent :=
    ‹(Abelian.image φ).IsQuasicoherent›
  have : (ShortComplex.kernelSequence (cokernel.π φ)).X₂.IsCoherent := ‹Q.IsCoherent›
  have hC : (ShortComplex.kernelSequence (cokernel.π φ)).X₃.IsCoherent :=
    isCoherent_X₃_of_shortExact hS₂
  have hFK : FiniteCohomology ρ (ShortComplex.kernelSequence (Abelian.factorThruImage φ)).X₁ :=
    IH _ hK _ hT hTne (vanishesOff_kernel_factorThruImage φ hU (hφ U hUW).1)
  have hFC : FiniteCohomology ρ (ShortComplex.kernelSequence (cokernel.π φ)).X₃ :=
    IH _ hC _ hT hTne (vanishesOff_cokernel φ hU (hφ U hUW).2)
  have hFI : FiniteCohomology ρ (ShortComplex.kernelSequence (cokernel.π φ)).X₁ :=
    FiniteCohomology.of_shortExact₁ hS₂ hQ hFC
  exact FiniteCohomology.of_shortExact₂ hS₁ hFK hFI

end Comparison

section Integral

open ProjectiveSpace

/-- On `ℙ(σ; S)`, the intersection of a standard open with the inverse image of an affine open of
`S` is affine. -/
lemma isAffineOpen_basicOpen_inf_preimage {S : Scheme.{u}} {σ : Type u} (i : σ) {c : S.Opens}
    (hc : IsAffineOpen c) : IsAffineOpen (basicOpen S i ⊓ (ℙ(σ; S) ↘ S) ⁻¹ᵁ c) := by
  have h := (hc.preimage ((basicOpen S i).ι ≫ ℙ(σ; S) ↘ S)).image_of_isOpenImmersion
    (basicOpen S i).ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι] at h

/-- **Vanishing of higher direct images for a closed subscheme of `ℙ(σ; Z)`** (EGA III 2.2.1 (ii)
with the projection formula): let `κ : X' ⟶ ℙ(σ; Z)` be a closed immersion over a separated
locally noetherian `Z`, `G'` coherent on `X'`, and `V` a finite affine family of opens of `Z` with
affine finite intersections. Then for `n ≫ 0`, `G'(n)` has no higher cohomology over the inverse
images in `X'` of all finite intersections of the `V`. -/
theorem exists_twist_acyclic {Z X' : Scheme.{u}} [IsLocallyNoetherian Z] {σ : Type u} [Finite σ]
    [Nonempty σ] [IsAffineHom (pullback.diagonal (terminal.from ℙ(σ; Z)))] (κ : X' ⟶ ℙ(σ; Z))
    [IsClosedImmersion κ] (G' : X'.Modules) [G'.IsCoherent] {N : ℕ} (V : Fin N → Z.Opens)
    (hV : ∀ {m : ℕ} (x : Fin (m + 1) → Fin N), IsAffineOpen (cechOpen V x)) :
    ∃ n₀ : ℤ, ∀ n ≥ n₀, ∀ {m : ℕ} (x : Fin (m + 1) → Fin N) (q : ℕ), Subsingleton
      (((twistingSheaf σ Z).pullback κ |>.twist G' n).H' (q + 1)
        ((κ ≫ ℙ(σ; Z) ↘ Z) ⁻¹ᵁ cechOpen V x)) := by
  have : G'.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  let L := twistingSheaf σ Z
  let 𝓕 := (Scheme.Modules.pushforward κ).obj G'
  have : 𝓕.IsCoherent := isCoherent_pushforward_of_isClosedImmersion κ G'
  obtain ⟨n₀, hn₀⟩ := exists_twist_H'_preimage_cechOpen_subsingleton 𝓕 V hV
  refine ⟨n₀, fun n hn m x q ↦ ?_⟩
  let Fn := (L.pullback κ).twist G' n
  have : Fn.IsQuasicoherent := inferInstance
  have : ((Scheme.Modules.pushforward κ).obj Fn).IsQuasicoherent :=
    isQuasicoherent_pushforward κ Fn
  have h1 := hn₀ n hn x q
  have h2 : Subsingleton (((Scheme.Modules.pushforward κ).obj Fn).H' (q + 1)
      ((ℙ(σ; Z) ↘ Z) ⁻¹ᵁ cechOpen V x)) :=
    @Scheme.Modules.subsingleton_H'_of_iso _ _ _ _ _ (L.twistPushforwardIso κ G' n).symm h1
  obtain ⟨r, ⟨e⟩⟩ := exists_equiv_fin_succ σ
  let W : Fin (r + 1) → ℙ(σ; Z).Opens := fun k ↦
    basicOpen Z (e k) ⊓ (ℙ(σ; Z) ↘ Z) ⁻¹ᵁ cechOpen V x
  have hWa : ∀ {m' : ℕ} (y : Fin (m' + 1) → Fin (r + 1)), IsAffineOpen (cechOpen W y) :=
    isAffineOpen_cechOpen W fun k ↦ isAffineOpen_basicOpen_inf_preimage (e k) (hV x)
  have hWsup : ⨆ k, W k = (ℙ(σ; Z) ↘ Z) ⁻¹ᵁ cechOpen V x := by
    simp only [W, ← iSup_inf_eq]
    rw [show (⨆ k, basicOpen Z (e k)) = ⊤ from
      (e.iSup_comp (g := fun i ↦ basicOpen Z i)).trans (iSup_basicOpen Z), top_inf_eq]
  have hacycκ : ∀ {m' : ℕ} (y : Fin (m' + 1) → Fin (r + 1)) (q' : ℕ),
      Subsingleton (Fn.H' (q' + 1) (κ ⁻¹ᵁ cechOpen W y)) := fun y q' ↦
    Fn.H'_subsingleton_of_isAffineOpen ((hWa y).preimage κ) q'
  let E := pushforwardH'AddEquiv Fn W (q + 1) κ hWa hacycκ
  have h3 : Subsingleton (((Scheme.Modules.pushforward κ).obj Fn).H' (q + 1) (⨆ k, W k)) := by
    rw [hWsup]; exact h2
  have h4 : Subsingleton (Fn.H' (q + 1) (⨆ k, κ ⁻¹ᵁ W k)) := E.injective.subsingleton
  have he : (⨆ k, κ ⁻¹ᵁ W k) = (κ ≫ ℙ(σ; Z) ↘ Z) ⁻¹ᵁ cechOpen V x := by
    rw [← Scheme.Hom.preimage_iSup, hWsup, Scheme.Hom.comp_preimage]
  rw [he] at h4
  exact h4

/-- **The integral case of the finiteness theorem** (EGA III 3.2.1, via Chow's lemma): let `Z`
be an integral scheme proper over a noetherian ring `A`, and suppose that every coherent module on
`Z` supported in a proper closed subset has finitely generated cohomology over `A`. Then so does
every coherent module `G`.

Proof: Chow's lemma gives `π : X' ⟶ Z` H-projective, an isomorphism over a dense open `U`, with
`X'` H-projective over `A`; write `π = p ∘ κ` with `κ : X' ⟶ ℙ(σ; Z)` a closed immersion. For
`n ≫ 0`, `Q = π_*(π^* G(n))` is coherent (`isCoherent_pushforward_of_isHProjective`) with
`Hᵖ(Z, Q) = Hᵖ(X', π^* G(n))` (relative Serre vanishing and Leray), finitely generated over `A`
(`properFiniteness_of_isHProjective`). Multiplication by a coordinate `xᵢⁿ` gives
`G ⟶ Q`, bijective over a dense open, and one concludes with
`finiteCohomology_of_bijective_on_open`. -/
theorem finiteCohomology_of_isIntegral {A : CommRingCat.{u}} [IsNoetherianRing A]
    (Z : Scheme.{u}) [IsIntegral Z] (g : Z ⟶ Spec A) [IsProper g]
    (IH : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
      VanishesOff N T' → FiniteCohomology g.specStructureRingHom N)
    (G : Z.Modules) [G.IsCoherent] : FiniteCohomology g.specStructureRingHom G := by
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  have : IsAffineHom (pullback.diagonal (terminal.from Z)) := isAffineHom_diagonal_of_isSeparated g
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : G.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  obtain ⟨X', π, U, hπ, hsurj, hπg, hUne, hiso, hX'⟩ := exists_isHProjective_of_isProper g
  obtain ⟨σ, hσ, κ, hκ, hκπ⟩ := hπ.exists_isClosedImmersion
  subst hκπ
  obtain ⟨x₀⟩ : Nonempty X' := inferInstance
  obtain ⟨i₀, hi₀⟩ : ∃ i, κ x₀ ∈ basicOpen Z i := by
    have : κ x₀ ∈ (⨆ i, basicOpen Z i : ℙ(σ; Z).Opens) := by
      rw [iSup_basicOpen]; exact True.intro
    exact TopologicalSpace.Opens.mem_iSup.mp this
  have : Nonempty σ := ⟨i₀⟩
  have : IsAffineHom (pullback.diagonal (terminal.from ℙ(σ; Z))) :=
    isAffineHom_diagonal_of_isSeparated (ℙ(σ; Z) ↘ Z ≫ g)
  have : IsAffineHom (pullback.diagonal (terminal.from X')) :=
    isAffineHom_diagonal_of_isSeparated ((κ ≫ ℙ(σ; Z) ↘ Z) ≫ g)
  obtain ⟨N, V, hcov, hV⟩ := exists_cechCover Z
  let L := twistingSheaf σ Z
  let G' := (Scheme.Modules.pullback (κ ≫ ℙ(σ; Z) ↘ Z)).obj G
  have : G'.IsCoherent := ⟨inferInstance, inferInstance⟩
  obtain ⟨n₀, hn₀⟩ := exists_twist_acyclic κ G' V hV
  let n : ℕ := n₀.toNat
  have hn : (n : ℤ) ≥ n₀ := Int.self_le_toNat n₀
  let Fn := (L.pullback κ).twist G' (n : ℤ)
  have : Fn.IsCoherent := inferInstance
  let Q := (Scheme.Modules.pushforward (κ ≫ ℙ(σ; Z) ↘ Z)).obj Fn
  have hQc : Q.IsCoherent := isCoherent_pushforward_of_isHProjective _ Fn
  have : Q.IsQuasicoherent := hQc.isQuasicoherent
  -- the cohomology of `Q` is that of `Fn`
  have hQ : FiniteCohomology g.specStructureRingHom Q :=
    (finiteCohomology_iff_pushforward (κ ≫ ℙ(σ; Z) ↘ Z) Fn V g hcov hV (hn₀ n hn)).mp
      fun q ↦ properFiniteness_of_isHProjective A X' ((κ ≫ ℙ(σ; Z) ↘ Z) ≫ g) Fn q
  -- multiplication by `xᵢⁿ`
  let s : L.sections n := homogeneousSection Z (MvPolynomial.isHomogeneous_X_pow i₀ n)
  let μ := (L.pullback κ).mulSection G' (s.pullback L κ)
  let φ : G ⟶ Q := unitPushPull (κ ≫ ℙ(σ; Z) ↘ Z) G ≫
    (Scheme.Modules.pushforward (κ ≫ ℙ(σ; Z) ↘ Z)).map μ
  obtain ⟨W, hWne, hWU, hWD⟩ := exists_open_preimage_le (κ ≫ ℙ(σ; Z) ↘ Z) U hUne
    (κ ⁻¹ᵁ basicOpen Z i₀) ⟨x₀, hi₀⟩
  have hφ : ∀ V' : Z.Opens, V' ≤ W → Function.Bijective (φ.app V') := by
    intro V' hV'
    have h1 := pullbackApp_bijective_of_isIso_morphismRestrict (κ ≫ ℙ(σ; Z) ↘ Z) U G
      (hV'.trans hWU)
    have hle : (κ ≫ ℙ(σ; Z) ↘ Z) ⁻¹ᵁ V' ≤ (L.pullback κ).U i₀ :=
      ((κ ≫ ℙ(σ; Z) ↘ Z).preimage_mono hV').trans hWD
    have hnv : (κ ≫ ℙ(σ; Z) ↘ Z) ⁻¹ᵁ V' ≤ (L.pullback κ).nonvanishingLocus (s.pullback L κ) := by
      rw [Scheme.LineBundle.nonvanishingLocus_pullback, nonvanishingLocus_homogeneousSection]
      refine hle.trans (κ.preimage_mono ?_)
      exact (toProj σ Z).preimage_mono (Proj.basicOpen_le_basicOpen_pow _ _ _)
    have h2 := (L.pullback κ).mulSection_app_bijective G' (s.pullback L κ) i₀ hle
      ((L.pullback κ).isUnit_of_le_nonvanishingLocus (s.pullback L κ) i₀ hle hnv)
    exact h2.comp h1
  exact finiteCohomology_of_bijective_on_open g.specStructureRingHom IH G Q φ W hWne hφ hQ

end Integral

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

open CohomologyAux

/-- **Finiteness of cohomology for proper morphisms** (EGA III 3.2.1; Stacks Tag 02O5;
Hartshorne III.8.8 (b)): for `A` noetherian, `f : X ⟶ Spec A` proper and `M` coherent, every
`Hᵖ(X, M)` is a finitely generated `A`-module. The proof is the dévissage of EGA III 3.1.2
(`finiteCohomology_of_integral_step`), reducing to integral closed subschemes, where Chow's lemma
reduces to the projective case (`finiteCohomology_of_isIntegral`). -/
theorem properFinitenessStatement : ProperFinitenessStatement.{u} := by
  intro A _ X f _ M _ p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : IsNoetherian X := {}
  have : IsAffineHom (pullback.diagonal (terminal.from X)) := isAffineHom_diagonal_of_isSeparated f
  exact finiteCohomology_of_integral_step f
    (fun Z ι _ _ IH G _ ↦ finiteCohomology_of_isIntegral Z (ι ≫ f) IH G) M p

end AlgebraicGeometry
