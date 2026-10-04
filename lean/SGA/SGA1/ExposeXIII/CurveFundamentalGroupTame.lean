/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.NormalCompleteLocalBase
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupPresentation
import SGA.SGA1.ExposeXIII.MultiplicativeGroup
import SGA.SGA1.ExposeXIII.TameRamification

/-!
# SGA 1, XIII.2.3 b) for Galois coverings of degree prime to `p`

A Galois étale covering of degree `n` prime to `p` is tamely ramified (XIII.2.3 b); this is the
inclusion `tameKernel ≤ proLKernel p'` of `PrimeToPCoveringsTameStatement`). Over the field of
fractions `K` of a local ring `R` at a point of the boundary, such a covering is `Spec L` for an
étale `K`-algebra `L` on which the Galois group `G` acts simply transitively on the geometric
points. This file proves the algebra:

* `isGalois_quotient_of_bijective`: if a group `S` of `K`-automorphisms of a finite unramified
  `K`-algebra `A` acts simply transitively on the geometric points `A →ₐ[K] Ω` (`Ω` algebraically
  closed), every residue field `A ⧸ m` is Galois over `K` and its degree divides `|S|` (it is the
  order of the stabilizer of `m`);
* a Galois extension of `K` of degree prime to the residue characteristic of `R` is tamely
  ramified over `R` (XIII 2.0: its inertia groups have order dividing the degree;
  `isTameExtension_of_isGalois`, in `SGA.SGA1.ExposeXIII.TameRamification`);
* `isTameAlgebra_of_bijective`: so `A` is tamely ramified over `R` (`IsTameAlgebra`) when `|S|` is
  prime to the residue characteristic.

The geometry: for a Galois covering `E` of `U` and `κ : Spec K ⟶ U`, `Aut E` acts on the algebra
`pullbackAlgebra E κ` of `E ×_U Spec K` (`autHom`), simply transitively on its geometric points
(`bijective_comp_range`, from the Galois property through the fibre functors), and the inverse
image of the sheaf represented by `E` is represented by its spectrum (`etalePullbackYonedaIso`).
Hence `galoisCoveringsTameStatement` (Galois coverings of degree prime to `p` are tame,
`GaloisCoveringsTameStatement`) and, with V.5.11, `primeToPCoveringsTameStatement`
(`tameKernel ≤ proLKernel p'`). Consequently XIII.2.12 implies its "in other words" form
unconditionally (`tameCurvePrimeToPStatement_of_tameCurveFundamentalGroupStatement'`).
-/

universe u

open Module

namespace SGA.SGA1.ExposeXIII.TameGaloisAlgebra

section Galois

variable {K A Ω : Type*} [Field K] [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
  [IsAlgClosed Ω] (S : Subgroup (A ≃ₐ[K] A))

/-- The `K`-automorphisms in `S` stabilizing the ideal `m`. -/
def stabilizer (m : Ideal A) : Subgroup S where
  carrier := {g | m.comap ((g : A ≃ₐ[K] A) : A →+* A) = m}
  one_mem' := Ideal.comap_id m
  mul_mem' {g h} hg hh := by
    change m.comap (((g * h : S) : A ≃ₐ[K] A) : A →+* A) = m
    change m.comap ((g : A ≃ₐ[K] A) : A →+* A) = m at hg
    change m.comap ((h : A ≃ₐ[K] A) : A →+* A) = m at hh
    have : (((g * h : S) : A ≃ₐ[K] A) : A →+* A) =
        ((g : A ≃ₐ[K] A) : A →+* A).comp ((h : A ≃ₐ[K] A) : A →+* A) := rfl
    rw [this, ← Ideal.comap_comap, hg, hh]
  inv_mem' {g} hg := by
    change m.comap ((g : A ≃ₐ[K] A) : A →+* A) = m at hg
    change m.comap (((g⁻¹ : S) : A ≃ₐ[K] A) : A →+* A) = m
    conv_lhs => rw [← hg]
    rw [Ideal.comap_comap]
    convert Ideal.comap_id m
    ext a
    exact (g : A ≃ₐ[K] A).apply_symm_apply a

variable {S}

lemma mem_stabilizer_iff {m : Ideal A} {g : S} :
    g ∈ stabilizer S m ↔ m.comap ((g : A ≃ₐ[K] A) : A →+* A) = m :=
  Iff.rfl

lemma eq_map_of_mem_stabilizer {m : Ideal A} {g : S} (hg : g ∈ stabilizer S m) :
    m = m.map ((g : A ≃ₐ[K] A) : A →+* A) := by
  have := Ideal.map_comap_of_surjective ((g : A ≃ₐ[K] A) : A →+* A) (g : A ≃ₐ[K] A).surjective m
  rw [mem_stabilizer_iff.mp hg] at this
  exact this.symm

variable (hS : ∀ φ : A →ₐ[K] Ω, Function.Bijective fun g : S ↦ φ.comp (g : A ≃ₐ[K] A).toAlgHom)
  [Module.Finite K A] [Algebra.FormallyUnramified K A] (m : Ideal A) [m.IsMaximal]

include hS in
/-- If a group `S` of `K`-automorphisms of a finite unramified `K`-algebra `A` acts simply
transitively on the geometric points `A →ₐ[K] Ω`, the stabilizer of a maximal ideal `m` has
`[A ⧸ m : K]` elements, and acts faithfully on `A ⧸ m`; so `A ⧸ m` is Galois over `K`, of degree
dividing `|S|`. -/
theorem isGalois_quotient_of_bijective :
    letI := Ideal.Quotient.field m
    IsGalois K (A ⧸ m) ∧ finrank K (A ⧸ m) ∣ Nat.card S := by
  let := Ideal.Quotient.field m
  have : Algebra.FormallyUnramified K (A ⧸ m) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ K m)
      (Ideal.Quotient.mkₐ_surjective K m)
  have : Algebra.IsSeparable K (A ⧸ m) := Algebra.FormallyUnramified.isSeparable K (A ⧸ m)
  have : Algebra.IsAlgebraic K (A ⧸ m) := Algebra.IsIntegral.isAlgebraic
  let ψ₀ : (A ⧸ m) →ₐ[K] Ω := IsAlgClosed.lift
  let φ₀ : A →ₐ[K] Ω := ψ₀.comp (Ideal.Quotient.mkₐ K m)
  -- the kernel of a geometric point factoring through `A ⧸ m`
  have hker : ∀ ψ : (A ⧸ m) →ₐ[K] Ω, RingHom.ker (ψ.comp (Ideal.Quotient.mkₐ K m)) = m := by
    intro ψ
    ext a
    simp only [RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [map_eq_zero_iff ψ (RingHom.injective (ψ : (A ⧸ m) →+* Ω)), Ideal.Quotient.eq_zero_iff_mem]
  -- `g ↦ φ₀ ∘ g` identifies the stabilizer of `m` with the geometric points of `A ⧸ m`
  have hfac : ∀ g ∈ stabilizer S m, ∀ a ∈ m, (φ₀.comp (g : A ≃ₐ[K] A).toAlgHom) a = 0 := by
    intro g hg a ha
    have : (g : A ≃ₐ[K] A) a ∈ m := by
      rw [mem_stabilizer_iff] at hg
      rw [← hg] at ha
      exact ha
    change ψ₀ (Ideal.Quotient.mk m ((g : A ≃ₐ[K] A) a)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr this, map_zero]
  let Θ : stabilizer S m → ((A ⧸ m) →ₐ[K] Ω) := fun g ↦
    Ideal.Quotient.liftₐ m (φ₀.comp (g.1 : A ≃ₐ[K] A).toAlgHom) (hfac g.1 g.2)
  have hΘ : ∀ g, (Θ g).comp (Ideal.Quotient.mkₐ K m) = φ₀.comp (g.1 : A ≃ₐ[K] A).toAlgHom := by
    intro g
    ext a
    rfl
  have hΘbij : Function.Bijective Θ := by
    refine ⟨fun g g' h ↦ Subtype.ext ((hS φ₀).1 ?_), fun ψ ↦ ?_⟩
    · change φ₀.comp (g.1 : A ≃ₐ[K] A).toAlgHom = φ₀.comp (g'.1 : A ≃ₐ[K] A).toAlgHom
      rw [← hΘ, ← hΘ, h]
    · obtain ⟨g, hg⟩ := (hS φ₀).2 (ψ.comp (Ideal.Quotient.mkₐ K m))
      have hgm : g ∈ stabilizer S m := by
        rw [mem_stabilizer_iff]
        have h1 := hker ψ
        rw [← hg] at h1
        have h2 : RingHom.ker (φ₀.comp (g : A ≃ₐ[K] A).toAlgHom) =
            (RingHom.ker φ₀).comap ((g : A ≃ₐ[K] A) : A →+* A) := by
          ext a
          rfl
        rw [h2, hker ψ₀] at h1
        exact h1
      refine ⟨⟨g, hgm⟩, ?_⟩
      apply AlgHom.ext
      intro z
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact congrArg (fun f : A →ₐ[K] Ω ↦ f a) hg
  have hcard : Nat.card (stabilizer S m) = finrank K (A ⧸ m) := by
    rw [Nat.card_eq_of_bijective Θ hΘbij, Nat.card_eq_fintype_card, AlgHom.card]
  -- the stabilizer acts faithfully on `A ⧸ m`
  let ρ : stabilizer S m → Gal((A ⧸ m)/K) := fun g ↦
    Ideal.quotientEquivAlg m m (g.1 : A ≃ₐ[K] A) (eq_map_of_mem_stabilizer g.2)
  have hρ : Function.Injective ρ := by
    intro g g' h
    apply Subtype.ext
    apply (hS φ₀).1
    change φ₀.comp (g.1 : A ≃ₐ[K] A).toAlgHom = φ₀.comp (g'.1 : A ≃ₐ[K] A).toAlgHom
    ext a
    have := congrArg (fun e : Gal((A ⧸ m)/K) ↦ ψ₀ (e (Ideal.Quotient.mk m a))) h
    exact this
  have hle : finrank K (A ⧸ m) ≤ Nat.card Gal((A ⧸ m)/K) := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective ρ hρ
  refine ⟨IsGalois.of_card_aut_eq_finrank K (A ⧸ m) (le_antisymm ?_ hle), ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact AlgEquiv.card_le
  · rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _

end Galois

section Tame

variable {K : Type*} [Field K] (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R K]

/-- XIII.2.3 b), algebra: let `S` be a group of `K`-automorphisms of a finite unramified
`K`-algebra `A` acting simply transitively on the geometric points `A →ₐ[K] Ω` (`Ω` algebraically
closed), with `|S|` prime to the residue characteristic of the local ring `R`. Then `A` is tamely
ramified over `R`: each factor `A ⧸ m` is Galois over `K` of degree dividing `|S|`. -/
theorem isTameAlgebra_of_bijective {A Ω : Type*} [CommRing A] [Algebra K A] [Field Ω] [Algebra K Ω]
    [IsAlgClosed Ω] [Algebra R A] [IsScalarTower R K A] [Module.Finite K A]
    [Algebra.FormallyUnramified K A] {S : Subgroup (A ≃ₐ[K] A)}
    (hS : ∀ φ : A →ₐ[K] Ω, Function.Bijective fun g : S ↦ φ.comp (g : A ≃ₐ[K] A).toAlgHom)
    (h : ¬ ringChar (IsLocalRing.ResidueField R) ∣ Nat.card S) :
    IsTameAlgebra R (K := K) A := by
  intro m hm
  let := Ideal.Quotient.field m
  obtain ⟨_, hdvd⟩ := isGalois_quotient_of_bijective hS m
  exact isTameExtension_of_isGalois R (A ⧸ m) fun h' ↦ h (h'.trans hdvd)

end Tame

end SGA.SGA1.ExposeXIII.TameGaloisAlgebra

namespace SGA.SGA1.ExposeXIII.TameGaloisAlgebra

open CategoryTheory AlgebraicGeometry ExposeV PreGaloisCategory

section Pullback

variable {U : Scheme.{u}} (E : FEt U) {K : Type u} [Field K] (κ : Spec (.of K) ⟶ U)

/-- The finite étale `K`-algebra of the base change `E ×_U Spec K` of an étale covering `E` of
`U` to a field `K`. -/
noncomputable abbrev pullbackAlgebra : CommAlgCat.FiniteEtale.{u} (CommRingCat.of K) :=
  ((specEquivalence (.of K)).inverse.obj ((FEt.pullback κ).obj E)).unop

/-- The automorphisms of `E` act on the algebra of `E ×_U Spec K` (by `g ↦ (g⁻¹)^*`). -/
noncomputable def autHom :
    Aut E →* ((pullbackAlgebra E κ).obj ≃ₐ[K] (pullbackAlgebra E κ).obj) :=
  (AffineLinePGroups.autOpMulEquivAlgEquiv (pullbackAlgebra E κ)).toMonoidHom.comp
    ((MulEquiv.inv' _).toMonoidHom.comp
      ((FEt.pullback κ ⋙ (specEquivalence (.of K)).inverse).mapAut E))

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (η : Spec (.of Ω) ⟶ Spec (.of K))

/-- The fibre of `E` at `η ≫ κ` is the set of geometric points of `E ×_U Spec K` over `η`. -/
noncomputable def fiberIso :
    letI := algebraOfPoint (.of K) Ω η
    FEt.fiber Ω (η ≫ κ) ≅ FEt.pullback κ ⋙ geometricFiber (.of K) Ω :=
  letI := algebraOfPoint (.of K) Ω η
  (FEt.pullbackFiberIso Ω κ η).symm ≪≫ Functor.isoWhiskerLeft _ (FEt.fiberSpecIso (.of K) Ω η)

omit [IsSepClosed Ω] in
lemma comp_autHom (g : Aut E) :
    letI := algebraOfPoint (.of K) Ω η
    ∀ φ : (pullbackAlgebra E κ).obj →ₐ[K] Ω, φ.comp (autHom E κ g).toAlgHom =
      (FEt.pullback κ ⋙ geometricFiber (.of K) Ω).map (g⁻¹).hom φ := by
  intro φ
  rfl

variable [ConnectedSpace U] [IsGalois E]

/-- For a Galois covering `E` of `U`, the automorphisms of `E` act simply transitively on the
geometric points of the algebra of `E ×_U Spec K`. -/
lemma bijective_comp_autHom :
    letI := algebraOfPoint (.of K) Ω η
    ∀ φ : (pullbackAlgebra E κ).obj →ₐ[K] Ω,
      Function.Bijective fun g : Aut E ↦ φ.comp (autHom E κ g).toAlgHom := by
  let := algebraOfPoint (.of K) Ω η
  intro φ
  set α := fiberIso κ Ω η
  let x := (α.app E).inv φ
  have hbij := evaluation_aut_bijective_of_isGalois (FEt.fiber Ω (η ≫ κ)) E x
  have key : (fun g : Aut E ↦ φ.comp (autHom E κ g).toAlgHom) =
      (α.app E).hom ∘ (fun g : Aut E ↦ (FEt.fiber Ω (η ≫ κ)).map g.hom x) ∘ (fun g ↦ g⁻¹) := by
    funext g
    simp only [Function.comp_apply, comp_autHom]
    have h1 := congrArg (fun f ↦ f x) (α.hom.naturality (g⁻¹).hom)
    simp only [FintypeCat.comp_apply] at h1
    have h2 : α.hom.app E x = φ := FintypeCat.inv_hom_id_apply (α.app E) φ
    rw [h2] at h1
    exact h1.symm
  rw [key]
  exact (FintypeCat.equivEquivIso.symm (α.app E)).bijective.comp
    (hbij.comp (Equiv.inv _).bijective)

/-- The image of `Aut E` in the `K`-automorphisms of the algebra of `E ×_U Spec K` acts simply
transitively on its geometric points, and has `|Aut E|` elements. -/
lemma bijective_comp_range :
    letI := algebraOfPoint (.of K) Ω η
    ∀ φ : (pullbackAlgebra E κ).obj →ₐ[K] Ω,
      Function.Bijective fun s : (autHom E κ).range ↦ φ.comp s.1.toAlgHom := by
  let := algebraOfPoint (.of K) Ω η
  intro φ
  have h := bijective_comp_autHom E κ Ω η φ
  refine ⟨?_, fun ψ ↦ ?_⟩
  · rintro ⟨_, g, rfl⟩ ⟨_, g', rfl⟩ hgg'
    exact Subtype.ext (congrArg (autHom E κ) (h.1 hgg'))
  · obtain ⟨g, rfl⟩ := h.2 ψ
    exact ⟨⟨_, g, rfl⟩, rfl⟩

lemma card_range_autHom : Nat.card (autHom E κ).range = Nat.card (Aut E) := by
  let Ω := AlgebraicClosure K
  let η : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let := algebraOfPoint (.of K) Ω η
  have hinj : Function.Injective (autHom E κ) := by
    obtain ⟨x⟩ := nonempty_fiber_of_isConnected (FEt.fiber Ω (η ≫ κ)) E
    let φ : (pullbackAlgebra E κ).obj →ₐ[K] Ω := (fiberIso κ Ω η).hom.app E x
    exact fun g g' hgg' ↦ (bijective_comp_autHom E κ Ω η φ).1 (by simp only [hgg'])
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

/-- XIII.2.3 b), algebra of a Galois covering over a field: for a Galois étale covering `E` of
`U` and `κ : Spec K ⟶ U`, the algebra of `E ×_U Spec K` is tamely ramified over every local ring
`R` with field of fractions `K` whose residue characteristic does not divide `|Aut E|` (the degree
of `E`). -/
theorem isTameAlgebra_pullbackAlgebra (R : Type*) [CommRing R] [IsLocalRing R] [Algebra R K]
    [Algebra R (pullbackAlgebra E κ).obj] [IsScalarTower R K (pullbackAlgebra E κ).obj]
    (h : ¬ ringChar (IsLocalRing.ResidueField R) ∣ Nat.card (Aut E)) :
    IsTameAlgebra R (K := K) (pullbackAlgebra E κ).obj := by
  let Ω := AlgebraicClosure K
  let η : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let := algebraOfPoint (.of K) Ω η
  exact isTameAlgebra_of_bijective R (bijective_comp_range E κ Ω η)
    (by rwa [card_range_autHom])

end Pullback

section Sheaf

variable {U : Scheme.{u}} (E : FEt U) {K : Type u} [Field K] (κ : Spec (.of K) ⟶ U)

/-- The base change `E ×_U Spec K`, as an étale `K`-scheme, is `Spec` of the algebra
`pullbackAlgebra E κ`. -/
noncomputable def pullbackEtaleIso :
    haveI : Etale E.hom := E.prop.2
    (Scheme.Etale.pullback κ).obj (Scheme.Etale.mk E.hom) ≅
      etaleSpec K (pullbackAlgebra E κ).obj :=
  haveI : Etale E.hom := E.prop.2
  let c := (specEquivalence (.of K)).counitIso.app ((FEt.pullback κ).obj E)
  let c' := (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mapIso c
  MorphismProperty.Over.isoMk c'.symm
    (by exact Over.w ((MorphismProperty.Over.forget _ ⊤ (Spec (.of K))).map c.inv))

/-- The inverse image of the sheaf represented by `E` along `κ : Spec K ⟶ U` is represented by
`Spec` of the algebra of `E ×_U Spec K`. -/
noncomputable def etalePullbackYonedaIso :
    haveI : Etale E.hom := E.prop.2
    ((Scheme.etalePullback κ).obj ((Scheme.etaleYoneda U).obj (Scheme.Etale.mk E.hom))).obj ≅
      yoneda.obj (etaleSpec K (pullbackAlgebra E κ).obj) :=
  haveI : Etale E.hom := E.prop.2
  (sheafToPresheaf _ _).mapIso (Scheme.etalePullbackYonedaIso κ (Scheme.Etale.mk E.hom)) ≪≫
    yoneda.mapIso (pullbackEtaleIso E κ)

end Sheaf


end SGA.SGA1.ExposeXIII.TameGaloisAlgebra

namespace SGA.SGA1.ExposeXIII

open CategoryTheory AlgebraicGeometry ExposeV PreGaloisCategory

/-- XIII.2.3 b), for Galois coverings (statement; proved as `galoisCoveringsTameStatement`
below): with the notation of `PrimeToPCoveringsTameStatement`, a Galois étale covering `E` of `U`
whose degree (the number of points of its geometric fibres) is prime to the characteristic of `k`
is tamely ramified along `X - U` (`IsTamelyRamifiedCovering`). The algebraic core, over the field
of fractions of a local ring at a boundary point, is `TameGaloisAlgebra.isTameAlgebra_of_bijective`.
`U` is assumed connected, which holds whenever it is nonempty (`X` is integral), so that `FEt U` is
a Galois category. -/
def GaloisCoveringsTameStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsSepClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [ConnectedSpace X] (U : X.Opens) (_ : Set.Finite (U : Set X)ᶜ)
    [ConnectedSpace (U : Scheme.{u})] (E : FEt (U : Scheme.{u})) [IsGalois E] (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})),
    ((Nat.card ((FEt.fiber Ω ξ).obj E) : ℕ) : k) ≠ 0 →
    haveI : Etale E.hom := E.prop.2
    IsTamelyRamifiedCovering f ((U : Set X)ᶜ) U (Scheme.Etale.mk E.hom)

/-- XIII.2.3 b) for the coverings used in XIII.2.12: if the Galois coverings of degree prime to
`p` are tamely ramified (`GaloisCoveringsTameStatement`), then `tameKernel ≤ proLKernel p'`
(`PrimeToPCoveringsTameStatement`): every open normal subgroup `N` of `π₁(U)` of index prime to
`p` is the stabilizer of a point of such a covering (V.5.11), which is tame. -/
theorem primeToPCoveringsTameStatement_of_galoisCoveringsTameStatement
    (h : GaloisCoveringsTameStatement.{u}) : PrimeToPCoveringsTameStatement.{u} := by
  intro k _ _ X f _ _ _ U hU Ω _ _ ξ
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have : IsIntegral X := (ExposeX.isIntegral_and_isNormalScheme_of_smooth k f).1
  have : Nonempty (U : Scheme.{u}) := ⟨ξ (Classical.arbitrary _)⟩
  have : IsIntegral (U : Scheme.{u}) := isIntegral_of_isOpenImmersion U.ι
  refine fun γ hγ ↦ mem_proLKernel.mpr fun N hN ho hL ↦ ?_
  obtain ⟨E, x, hE, hx⟩ := exists_isGalois_stabilizer_eq (FEt.fiber Ω ξ) ⟨N, ho⟩ hN
  replace hx : MulAction.stabilizer (etaleFundamentalGroup Ω ξ) x = N := hx
  have hcard : Nat.card ((FEt.fiber Ω ξ).obj E) = N.index := by
    rw [← hx, MulAction.index_stabilizer_of_transitive]
  have htame := h k X f U hU E Ω ξ
    (hcard ▸ natCast_ne_zero_of_primesDifferentFrom hL.1 hL.2)
  have := tameKernel_le_stabilizer f U ξ E htame x hγ
  rwa [hx] at this

/-- XIII.2.3 b) for Galois coverings (`GaloisCoveringsTameStatement`): a Galois étale covering of
`U` of degree prime to the characteristic is tamely ramified along `X - U`. Over the field of
fractions `K` of a local ring of `X_s̄` at a boundary point, the covering is `Spec L` with `L` the
algebra of `E ×_U Spec K` (`TameGaloisAlgebra.etalePullbackYonedaIso`); `Aut E` acts simply
transitively on its geometric points (`TameGaloisAlgebra.bijective_comp_range`), so its factors are
Galois of degree dividing `|Aut E|` and are tame
(`TameGaloisAlgebra.isTameAlgebra_pullbackAlgebra`). -/
theorem galoisCoveringsTameStatement : GaloisCoveringsTameStatement.{u} := by
  intro k _ _ X f _ _ _ U hU _ E _ Ω _ _ ξ hdeg Ω' _ _ s y _ K _ _ _ κ _
  let R := (Limits.pullback f s).presheaf.stalk y
  have hchar : ringChar (IsLocalRing.ResidueField R) = ringChar k := by
    let ι : k →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Limits.pullback.fst f s ≫ f).appTop ≫
        (Limits.pullback f s).presheaf.germ ⊤ y trivial).hom
    let := ι.toAlgebra
    exact (Algebra.ringChar_eq k _).symm
  have hcard : Nat.card (Aut E) = Nat.card ((FEt.fiber Ω ξ).obj E) := by
    obtain ⟨x⟩ := nonempty_fiber_of_isConnected (FEt.fiber Ω ξ) E
    exact Nat.card_congr (evaluationEquivOfIsGalois (FEt.fiber Ω ξ) E x)
  have hp : ¬ ringChar (IsLocalRing.ResidueField R) ∣ Nat.card (Aut E) := by
    rw [hchar, hcard, ← CharP.cast_eq_zero_iff k (ringChar k)]
    exact hdeg
  let L := (TameGaloisAlgebra.pullbackAlgebra E κ).obj
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact ⟨L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    TameGaloisAlgebra.isTameAlgebra_pullbackAlgebra E κ R hp,
    ⟨TameGaloisAlgebra.etalePullbackYonedaIso E κ⟩⟩

/-- XIII.2.3 b) for the coverings used in XIII.2.12 (`PrimeToPCoveringsTameStatement`): the
kernel of `π₁(U) → π₁^tame(U)` is contained in that of `π₁(U) → π₁^{p'}(U)`, i.e. étale coverings
of `U` trivialized by a Galois covering of degree prime to `p` are tamely ramified along `X - U`. -/
theorem primeToPCoveringsTameStatement : PrimeToPCoveringsTameStatement.{u} :=
  primeToPCoveringsTameStatement_of_galoisCoveringsTameStatement galoisCoveringsTameStatement

/-- XIII.2.12 implies its "in other words" form `TameCurvePrimeToPStatement`: the presentation of
`π₁^tame(U)` passes to its quotient `π₁^{p'}(U)`, since the Galois coverings of degree prime to
`p` are tame, so that `tameKernel ≤ proLKernel p'` (`primeToPCoveringsTameStatement`). (A
non-Galois covering of degree prime to `p` need not be tame.) -/
theorem tameCurvePrimeToPStatement_of_tameCurveFundamentalGroupStatement'
    (h : TameCurveFundamentalGroupStatement.{u}) : TameCurvePrimeToPStatement.{u} :=
  tameCurvePrimeToPStatement_of_tameCurveFundamentalGroupStatement h primeToPCoveringsTameStatement

end SGA.SGA1.ExposeXIII
