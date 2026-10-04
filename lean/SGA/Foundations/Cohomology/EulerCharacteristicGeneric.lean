/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristicDevissage
import SGA.Foundations.Cohomology.ExistenceLocallyFree
import Mathlib.RingTheory.Localization.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Additive functions of coherent modules on an integral scheme

Let `Z` be an integral noetherian scheme and `λ` a function on coherent `𝒪_Z`-modules which is
additive on short exact sequences and vanishes on modules supported in proper closed subsets.
Then `λ G = r · λ 𝒪_Z`, where `r` is the generic rank of `G`
(`CohomologyAux.exists_additive_eq_mul_unitModule`; EGA III 3.2.1, proof; Stacks Tag 01YF).

The usual proof compares `G` with `𝓘^{⊕r}` for a suitable ideal `𝓘`, using the extension of
coherent subsheaves and of morphisms from an open subscheme (Stacks Tag 01PD). We avoid it: on a
nonempty affine open `U` where `Γ(U, G)` is free with basis `b₁, …, b_r` (generic freeness), both
`G` and `𝒪_Z^{⊕r}` map to the quasi-coherent module `Q = j_* j^* G`, `j : U ⟶ Z`, bijectively on
sections over `U`; the
image `S` of `G ⊕ 𝒪_Z^{⊕r} ⟶ Q` is coherent, and `G ⟶ S`, `𝒪_Z^{⊕r} ⟶ S` are bijective on
sections over `U`, so `λ G = λ S = λ 𝒪_Z^{⊕r}`.

* `Module.exists_ne_zero_free_of_isLocalizedModule`: generic freeness of a finite module over a
  noetherian domain (Stacks Tag 051R, the case of a finite module), from mathlib's
  `Module.FinitePresentation.exists_free_localizedModule_powers`, in a form that applies to any
  localization away from the element;
* `CohomologyAux.additive_eq_of_bijective_app_comp`: two coherent modules mapping to a
  quasi-coherent one through a common coherent module, bijectively over a nonempty affine open,
  have the same `λ`;
* `CohomologyAux.additive_biproduct`: `λ` is additive on finite biproducts;
* `CohomologyAux.exists_additive_eq_mul_unitModule`: `λ G = r · λ 𝒪_Z`.
-/

universe u w

open CategoryTheory Limits TopologicalSpace Opposite

section Algebra

open Module

/-- **Generic freeness** of a finite module over a noetherian domain (Stacks Tag 051R, the case of
a finite module): there is `r ≠ 0` such that every localization `N` of `M` away from `r` is free
over the corresponding localization `B` of `A`. The core is mathlib's
`Module.FinitePresentation.exists_free_localizedModule_powers`; the point of this form is the
transfer to an arbitrary `IsLocalizedModule` (e.g. restriction of sections to a basic open).
For the canonical localizations, and for modules finite over a finite type `A`-algebra (SGA 1
IV.6.7), see `SGA.SGA1.ExposeIV.exists_isFreeAway_of_finite` and
`exists_free_localizedModule_of_finiteType` (`SGA/SGA1/ExposeIV/GenericFreeness.lean`). -/
theorem Module.exists_ne_zero_free_of_isLocalizedModule {A M : Type*} [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ r : A, r ≠ 0 ∧ ∀ (B N : Type w) [CommRing B] [Algebra A B] [IsLocalization.Away r B]
      [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] (f : M →ₗ[A] N)
      [IsLocalizedModule (.powers r) f], Module.Free B N := by
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Module.Free (FractionRing A) (LocalizedModule (nonZeroDivisors A) M) :=
    Module.Free.of_divisionRing _ _
  obtain ⟨r, hr, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (nonZeroDivisors A) (LocalizedModule.mkLinearMap (nonZeroDivisors A) M) (FractionRing A)
  refine ⟨r, nonZeroDivisors.ne_zero hr, fun B N _ _ _ _ _ _ _ f _ ↦ ?_⟩
  let e : Localization.Away r ≃ₐ[A] B := IsLocalization.algEquiv (.powers r) _ B
  let φ : LocalizedModule.Away r M ≃ₗ[A] N := IsLocalizedModule.iso (.powers r) f
  let σ : Localization.Away r ≃+* B := e.toRingEquiv
  have := RingHomInvPair.of_ringEquiv σ
  have := RingHomInvPair.of_ringEquiv_symm σ
  -- `φ` is semilinear over `e : A_r ≅ B`
  let ψ : LocalizedModule.Away r M ≃ₛₗ[(σ : Localization.Away r →+* B)] N :=
    { φ with
      map_smul' := fun c x ↦ by
        obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (.powers r) c
        apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
        change (s : A) • φ (IsLocalization.mk' _ a s • x) =
          (s : A) • (e (IsLocalization.mk' _ a s) • φ x)
        have h1 : (s : A) • IsLocalization.mk' (Localization.Away r) a s =
            algebraMap A (Localization.Away r) a := by
          rw [Algebra.smul_def, IsLocalization.mk'_spec']
        have h2 : (s : A) • e (IsLocalization.mk' (Localization.Away r) a s) =
            algebraMap A B a := by
          rw [← map_smul, h1, AlgEquiv.commutes]
        rw [← smul_assoc, h2, algebraMap_smul, ← map_smul, ← smul_assoc, h1, algebraMap_smul,
          map_smul] }
  exact Module.Free.of_equiv ψ

end Algebra

namespace AlgebraicGeometry.CohomologyAux

variable {Z : Scheme.{u}}

section Additive

variable [IsLocallyNoetherian Z] (lam : Z.Modules → ℤ)
  (hadd : ∀ S : ShortComplex Z.Modules, S.ShortExact → S.X₁.IsCoherent → S.X₂.IsCoherent →
    S.X₃.IsCoherent → lam S.X₂ = lam S.X₁ + lam S.X₃)

include hadd in
/-- **Comparison through a common target**: let `λ` be additive and vanish on coherent modules
supported in proper closed subsets. If `Φ : P ⟶ Q` is a morphism from a coherent module to a
quasi-coherent one and `aᵢ : Gᵢ ⟶ P` (`i = 1, 2`) are morphisms from coherent modules with
`aᵢ ≫ Φ` bijective on sections over a nonempty affine open `U`, then `λ G₁ = λ G₂`: both map
bijectively over `U` to the (coherent) image of `Φ`. -/
theorem additive_eq_of_bijective_app_comp
    (IH : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
      VanishesOff N T' → lam N = 0)
    {P Q G₁ G₂ : Z.Modules} [P.IsCoherent] [Q.IsQuasicoherent] [G₁.IsCoherent] [G₂.IsCoherent]
    (Φ : P ⟶ Q) (a₁ : G₁ ⟶ P) (a₂ : G₂ ⟶ P) {U : Z.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set Z).Nonempty) (h₁ : Function.Bijective ((a₁ ≫ Φ).app U))
    (h₂ : Function.Bijective ((a₂ ≫ Φ).app U)) : lam G₁ = lam G₂ := by
  have : P.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have hS := shortExact_kernelSequence (Abelian.factorThruImage Φ)
  have : (Abelian.image Φ).IsQuasicoherent := isQuasicoherent_image Φ
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage Φ)).X₂.IsCoherent :=
    ‹P.IsCoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage Φ)).X₂.IsQuasicoherent :=
    ‹P.IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage Φ)).X₃.IsQuasicoherent :=
    ‹(Abelian.image Φ).IsQuasicoherent›
  have : (ShortComplex.kernelSequence (Abelian.factorThruImage Φ)).X₁.IsQuasicoherent :=
    isQuasicoherent_X₁_of_shortExact hS
  have hI : (Abelian.image Φ).IsCoherent := isCoherent_X₃_of_shortExact hS
  -- `G ⟶ P ⟶ image Φ` is bijective over `U` when `G ⟶ P ⟶ Q` is
  have key : ∀ {G : Z.Modules} (a : G ⟶ P), Function.Bijective ((a ≫ Φ).app U) →
      Function.Bijective ((a ≫ Abelian.factorThruImage Φ).app U) := by
    intro G a ha
    have hinj : Function.Injective ((Abelian.image.ι Φ).app U) :=
      app_injective_of_mono (Abelian.image.ι Φ) U
    have hfac : ∀ x, (Abelian.image.ι Φ).app U ((a ≫ Abelian.factorThruImage Φ).app U x) =
        (a ≫ Φ).app U x := fun x ↦ by
      rw [← Scheme.Modules.Hom.comp_app_apply, Category.assoc, Abelian.image.fac]
    refine ⟨fun x y hxy ↦ ha.1 ?_, fun t ↦ ?_⟩
    · rw [← hfac, ← hfac, hxy]
    · obtain ⟨x, hx⟩ := ha.2 ((Abelian.image.ι Φ).app U t)
      exact ⟨x, hinj (by rw [hfac, hx])⟩
  rw [additive_eq_of_bijective_app lam hadd IH (a₁ ≫ Abelian.factorThruImage Φ) hU hne (key a₁ h₁),
    additive_eq_of_bijective_app lam hadd IH (a₂ ≫ Abelian.factorThruImage Φ) hU hne (key a₂ h₂)]

omit [IsLocallyNoetherian Z] in
include hadd in
/-- **`λ` is additive on finite biproducts**, given that it vanishes on modules with no nonzero
section. -/
theorem additive_biproduct
    (h0 : ∀ N : Z.Modules, N.IsCoherent → (∀ (V : Z.Opens) (s : Γ(N, V)), s = 0) → lam N = 0) :
    ∀ (n : ℕ) (J : Type) [Fintype J], Fintype.card J = n → ∀ (F : J → Z.Modules)
      [∀ j, (F j).IsCoherent], lam (⨁ F) = ∑ j, lam (F j) := by
  intro n
  induction n with
  | zero =>
    intro J _ hJ F _
    have : IsEmpty J := Fintype.card_eq_zero_iff.mp hJ
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine h0 _ (isCoherent_biproduct F) fun V s ↦ (biproductSections_bijective F V).1 ?_
    funext j
    exact isEmptyElim j
  | succ n ih =>
    intro J _ hJ F hF
    classical
    obtain ⟨j₀⟩ : Nonempty J := Fintype.card_pos_iff.mp (by omega)
    let p : J → Prop := fun j ↦ j ≠ j₀
    have hcard : Fintype.card {j // p j} = n := by
      simp [p, Fintype.card_subtype_compl, hJ]
    have : ∀ j : {j // p j}, (Subtype.restrict p F j).IsCoherent := fun j ↦ hF j.1
    have hc₁ : (⨁ Subtype.restrict p F).IsCoherent := isCoherent_biproduct _
    have hc₂ : (⨁ F).IsCoherent := isCoherent_biproduct _
    let S : ShortComplex Z.Modules :=
      ShortComplex.mk (biproduct.fromSubtype F p) (biproduct.π F j₀) (by simp [p])
    let σ : S.Splitting :=
      { r := biproduct.toSubtype F p
        s := biproduct.ι F j₀
        f_r := biproduct.fromSubtype_toSubtype F p
        s_g := biproduct.ι_π_self F j₀
        id := by
          refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun k ↦ ?_
          change biproduct.ι F j ≫ (biproduct.toSubtype F p ≫ biproduct.fromSubtype F p +
            biproduct.π F j₀ ≫ biproduct.ι F j₀) ≫ biproduct.π F k =
              biproduct.ι F j ≫ 𝟙 _ ≫ biproduct.π F k
          rw [Preadditive.add_comp, Preadditive.comp_add, biproduct.toSubtype_fromSubtype,
            biproduct.ι_map_assoc, Category.assoc, biproduct.ι_π_assoc, Category.id_comp]
          by_cases hj : j = j₀
          · subst hj
            simp [p]
          · simp [p, hj, biproduct.ι_π] }
    have e := hadd S σ.shortExact hc₁ hc₂ inferInstance
    change lam (⨁ F) = lam (⨁ Subtype.restrict p F) + lam (F j₀) at e
    rw [e, ih {j // p j} hcard (Subtype.restrict p F)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j₀)]
    congr 1
    exact (Finset.sum_subtype (Finset.univ.erase j₀) (p := p) (fun j ↦ by simp [p])
      (fun j ↦ lam (F j))).symm

end Additive

section Rank

variable [IsIntegral Z] [IsNoetherian Z] (lam : Z.Modules → ℤ)
  (hadd : ∀ S : ShortComplex Z.Modules, S.ShortExact → S.X₁.IsCoherent → S.X₂.IsCoherent →
    S.X₃.IsCoherent → lam S.X₂ = lam S.X₁ + lam S.X₃)
  (IH : ∀ N : Z.Modules, N.IsCoherent → ∀ T' : Set Z, IsClosed T' → T' ≠ Set.univ →
    VanishesOff N T' → lam N = 0)

include hadd IH in
/-- **`λ G = r · λ 𝒪_Z`** (EGA III 3.2.1, proof; Stacks Tag 01YF): on an integral noetherian
scheme `Z`, let `λ` be additive on short exact sequences of coherent modules and vanish on those
supported in proper closed subsets. Then for every coherent `G` there is a nonempty affine open `U`
with `Γ(U, G)` free of rank `n` over `Γ(U, 𝒪_Z)` (the generic rank of `G`) and
`λ G = n · λ 𝒪_Z`; in particular, if `n = 0`, then `G` has no nonzero section over `U`. -/
theorem exists_additive_eq_mul_unitModule (G : Z.Modules) [G.IsCoherent] :
    ∃ (n : ℕ) (U : Z.Opens), IsAffineOpen U ∧ (U : Set Z).Nonempty ∧
      Module.Free Γ(Z, U) Γ(G, U) ∧ Module.finrank Γ(Z, U) Γ(G, U) = n ∧
      (n = 0 → ∀ s : Γ(G, U), s = 0) ∧ lam G = n * lam (unitModule Z) := by
  have : G.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : G.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  -- `λ` vanishes on modules with no nonzero section
  have h0 : ∀ N : Z.Modules, N.IsCoherent → (∀ (V : Z.Opens) (s : Γ(N, V)), s = 0) →
      lam N = 0 := fun N hN hs ↦
    IH N hN ∅ isClosed_empty Set.empty_ne_univ fun V _ s ↦ hs V s
  -- a nonempty affine open `U₀`, and a basic open `U = D(r)` over which `G` is free
  obtain ⟨z⟩ : Nonempty Z := inferInstance
  obtain ⟨U₀, hU₀, hzU₀, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens)
    (show z ∈ (⊤ : Z.Opens) from Set.mem_univ z)
  have : Nonempty U₀ := ⟨⟨z, hzU₀⟩⟩
  have : IsNoetherianRing Γ(Z, U₀) := IsLocallyNoetherian.component_noetherian ⟨U₀, hU₀⟩
  have : Module.Finite Γ(Z, U₀) Γ(G, U₀) := finite_sections_of_isFiniteType G hU₀
  obtain ⟨r, hr, hfree⟩ :=
    Module.exists_ne_zero_free_of_isLocalizedModule.{u} (A := Γ(Z, U₀)) (M := Γ(G, U₀))
  let U := Z.basicOpen r
  have hU : IsAffineOpen U := hU₀.basicOpen r
  have hne : (U : Set Z).Nonempty := by
    by_contra h
    exact hr ((basicOpen_eq_bot_iff r).mp ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).mp h))
  let i : U ⟶ U₀ := homOfLE (Z.basicOpen_le r)
  let _ : Algebra Γ(Z, U₀) Γ(Z, U) := (Z.presheaf.map i.op).hom.toAlgebra
  have : IsLocalization.Away r Γ(Z, U) := hU₀.isLocalization_basicOpen r
  let _ : Module Γ(Z, U₀) Γ(G, U) := Module.compHom Γ(G, U) (algebraMap Γ(Z, U₀) Γ(Z, U))
  have : IsScalarTower Γ(Z, U₀) Γ(Z, U) Γ(G, U) := ⟨fun a b m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let res : Γ(G, U₀) →ₗ[Γ(Z, U₀)] Γ(G, U) :=
    { toFun := G.presheaf.map i.op
      map_add' := map_add _
      map_smul' := fun a m ↦ Scheme.Modules.map_smul _ _ _ _ }
  have : IsLocalizedModule (.powers r) res := by
    constructor
    · rintro ⟨_, k, rfl⟩
      obtain ⟨v, hv⟩ : IsUnit (algebraMap Γ(Z, U₀) Γ(Z, U) (r ^ k)) := by
        rw [map_pow]
        exact (Z.toRingedSpace.isUnit_res_basicOpen r).pow k
      have e : ∀ m : Γ(G, U),
          algebraMap Γ(Z, U₀) (Module.End Γ(Z, U₀) Γ(G, U)) (r ^ k) m = (v : Γ(Z, U)) • m :=
        fun m ↦ by rw [hv]; rfl
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b hab ↦ ?_, fun b ↦ ⟨(↑v⁻¹ : Γ(Z, U)) • b, ?_⟩⟩
      · rw [e, e] at hab
        have h := congrArg ((↑v⁻¹ : Γ(Z, U)) • ·) hab
        simp only [smul_smul, Units.inv_mul, one_smul] at h
        exact h
      · rw [e, smul_smul, Units.mul_inv, one_smul]
    · intro y
      obtain ⟨m, k, hm⟩ := exists_pow_smul_eq_map G hU₀ r y
      exact ⟨⟨m, ⟨r ^ k, k, rfl⟩⟩, hm⟩
    · intro m₁ m₂ h
      obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero G hU₀ r (m₁ - m₂) (by
        change res (m₁ - m₂) = 0
        rw [map_sub, h, sub_self])
      exact ⟨⟨r ^ k, k, rfl⟩, sub_eq_zero.mp (by rw [← smul_sub]; exact hk)⟩
  have : Nonempty U := ⟨⟨hne.some, hne.some_mem⟩⟩
  have : Module.Free Γ(Z, U) Γ(G, U) := hfree Γ(Z, U) Γ(G, U) res
  have : Module.Finite Γ(Z, U) Γ(G, U) := finite_sections_of_isFiniteType G hU
  let n := Module.finrank Γ(Z, U) Γ(G, U)
  let b : Module.Basis (Fin n) Γ(Z, U) Γ(G, U) := Module.finBasis Γ(Z, U) Γ(G, U)
  -- the common target `Q = j_* j^* G`
  let Q := (Scheme.Modules.pushforward U.ι).obj ((Scheme.Modules.pullback U.ι).obj G)
  have : Q.IsQuasicoherent := isQuasicoherent_pushforward_ι U _
  let η := unitPushPull U.ι G
  have hη : Function.Bijective (η.app U) :=
    Scheme.Modules.pullbackApp_bijective_of_isOpenImmersion U.ι G U
      (by rw [Scheme.Opens.opensRange_ι])
  have hρ : Function.Bijective (Q.presheaf.map (homOfLE le_top : U ⟶ ⊤).op) :=
    TopCat.Presheaf.map_bijective_of_eq ((Scheme.Modules.pullback U.ι).obj G).presheaf
      ((Opens.map U.ι.base).map (homOfLE le_top : U ⟶ ⊤))
      (by rw [Scheme.Opens.ι_preimage_self]; exact (Scheme.Hom.preimage_top _).symm)
  let e : Fin n → Γ(Q, ⊤) := fun i ↦ Function.surjInv hρ.2 (η.app U (b i))
  have he : ∀ i, Q.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (e i) = η.app U (b i) :=
    fun i ↦ Function.surjInv_eq hρ.2 _
  -- `𝒪^{⊕n} ⟶ Q`, given by the basis
  let F' : Fin n → Z.Modules := fun _ ↦ unitModule Z
  let Ψ : ⨁ F' ⟶ Q := biproduct.desc fun i ↦ homOfSection Q (e i)
  have hΨ : Function.Bijective (Ψ.app U) := by
    have key : ∀ x : Γ(⨁ F', U),
        Ψ.app U x = η.app U (b.equivFun.symm (biproductSections F' U x)) := by
      intro x
      have htot : ∑ j, (biproduct.ι F' j).app U ((biproduct.π F' j).app U x) = x := by
        have h := congrArg (fun φ : ⨁ F' ⟶ ⨁ F' ↦ φ.app U x) (biproduct.total (f := F'))
        simp only at h
        rw [modules_sum_app_apply] at h
        exact h
      conv_lhs => rw [← htot]
      rw [map_sum]
      erw [Module.Basis.equivFun_symm_apply]
      rw [map_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [← Scheme.Modules.Hom.comp_app_apply, biproduct.ι_desc]
      have hs : ∀ y : Γ(Z, U), (homOfSection Q (e j)).app U y = y • η.app U (b j) :=
        fun y ↦ by rw [homOfSection_app, he]
      exact (hs _).trans (Scheme.Modules.Hom.app_smul η ((biproduct.π F' j).app U x) (b j)).symm
    rw [show ⇑(Ψ.app U) = ⇑(η.app U) ∘ ⇑b.equivFun.symm ∘ ⇑(biproductSections F' U) from
      funext key]
    exact hη.comp (b.equivFun.symm.bijective.comp (biproductSections_bijective F' U))
  -- the common source `G ⊕ 𝒪^{⊕n}`
  let F : Option (Fin n) → Z.Modules := fun o ↦ o.elim G fun _ ↦ unitModule Z
  have : ∀ o, (F o).IsCoherent := fun o ↦ match o with
    | none => (inferInstance : G.IsCoherent)
    | some _ => (inferInstance : (unitModule Z).IsCoherent)
  have : (⨁ F).IsCoherent := isCoherent_biproduct F
  have : (⨁ F').IsCoherent := isCoherent_biproduct F'
  let Φ : ⨁ F ⟶ Q := biproduct.desc fun o ↦
    Option.rec (motive := fun o ↦ F o ⟶ Q) η (fun i ↦ homOfSection Q (e i)) o
  let a₁ : G ⟶ ⨁ F := biproduct.ι F none
  let a₂ : ⨁ F' ⟶ ⨁ F := biproduct.desc fun i ↦ (biproduct.ι F (some i) : unitModule Z ⟶ ⨁ F)
  have ha₁ : a₁ ≫ Φ = η := biproduct.ι_desc _ _
  have ha₂ : a₂ ≫ Φ = Ψ := biproduct.hom_ext' _ _ fun i ↦ by
    dsimp only [a₂, Φ, Ψ]
    erw [biproduct.ι_desc_assoc, biproduct.ι_desc, biproduct.ι_desc]
  have e₁ := additive_eq_of_bijective_app_comp lam hadd IH Φ a₁ a₂ hU hne (ha₁ ▸ hη) (ha₂ ▸ hΨ)
  have e₂ := additive_biproduct lam hadd h0 n (Fin n) (Fintype.card_fin n) F'
  refine ⟨n, U, hU, hne, inferInstance, rfl, fun hn s ↦ ?_, ?_⟩
  · have : IsEmpty (Fin n) := by rw [hn]; infer_instance
    exact b.ext_elem fun i ↦ isEmptyElim i
  · rw [e₁, e₂]
    simp only [F', Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Rank

end AlgebraicGeometry.CohomologyAux
