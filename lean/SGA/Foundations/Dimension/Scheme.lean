/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.Dimension.Smooth

/-!
# Dimension of schemes at a point, and dimension of fibres

For a scheme `X` and `x ∈ X`, `topologicalKrullDimAt X x` is the dimension of `X` at `x`
(EGA 0_IV §14.1). On an affine open `U ∋ x` it is computed in `Spec Γ(X, U)`
(`AlgebraicGeometry.IsAffineOpen.topologicalKrullDimAt_eq`). For a morphism `f : X ⟶ Y`,
`f.fiberDimAt x` is the dimension at `x` of the fibre `f⁻¹(f(x))` (EGA IV §13.1, SGA 1 II.1.5).

Main results:

* `AlgebraicGeometry.IsAffineOpen.topologicalKrullDimAt_eq_height_add_coheight`: if `X` is
  locally of finite type over a field `K` and `U` is an affine open with `Γ(X, U)` of finite type
  over `K`, then `dim_x X = ht 𝔭ₓ + dim Γ(X, U)/𝔭ₓ`;
* `AlgebraicGeometry.topologicalKrullDimAt_eq_ringKrullDim_stalk_add_residueFieldTrdeg`: for `X`
  locally of finite type over a field `k`, `dim_x X = dim 𝒪_{X,x} + trdeg_k κ(x)`, where
  `f.residueFieldTrdeg x` is the transcendence degree of `κ(x)` over `κ(f(x))`;
* `AlgebraicGeometry.Scheme.Hom.fiberDimAt_eq_ringKrullDim_add_residueFieldTrdeg`: for `f`
  locally of finite type, `dim_x f⁻¹(f(x)) = dim 𝒪_{f⁻¹(f(x)),x} + trdeg_{κ(f(x))} κ(x)`;
* `AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`: a scheme smooth of
  relative dimension `n` over a field has dimension `n` at every point;
* `AlgebraicGeometry.Scheme.Hom.fiberDimAt_eq_of_smoothOfRelativeDimension`: the fibres of a
  morphism smooth of relative dimension `n` have dimension `n` at every point (SGA 1 II.1.5:
  the relative dimension of a smooth morphism is the dimension of its fibres), and every
  irreducible component of a noetherian open part of a fibre has dimension `n`.
-/

universe u

open CategoryTheory Order PrimeSpectrum TopologicalSpace Topology

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- On an affine open `U` containing `x`, the dimension of `X` at `x` is the dimension of
`Spec Γ(X, U)` at the prime ideal of `x`. -/
theorem IsAffineOpen.topologicalKrullDimAt_eq {U : X.Opens} (hU : IsAffineOpen U) {x : X}
    (hx : x ∈ U) :
    topologicalKrullDimAt X x = topologicalKrullDimAt (PrimeSpectrum Γ(X, U))
      (hU.primeIdealOf ⟨x, hx⟩) := by
  have h := hU.fromSpec.isOpenEmbedding.topologicalKrullDimAt_eq (hU.primeIdealOf ⟨x, hx⟩)
  rw [hU.fromSpec_primeIdealOf] at h
  exact h

/-- If `U` is an affine open whose ring of sections is of finite type over a field `K`, then for
`x ∈ U` with prime ideal `𝔭ₓ`, `dim_x X = ht 𝔭ₓ + dim Γ(X, U)/𝔭ₓ` (EGA IV §5.2). -/
theorem IsAffineOpen.topologicalKrullDimAt_eq_height_add_coheight (K : Type*) [Field K]
    {U : X.Opens} (hU : IsAffineOpen U) [Algebra K Γ(X, U)] [Algebra.FiniteType K Γ(X, U)]
    {x : X} (hx : x ∈ U) :
    topologicalKrullDimAt X x = ((height (hU.primeIdealOf ⟨x, hx⟩) +
      coheight (hU.primeIdealOf ⟨x, hx⟩) : ℕ∞) : WithBot ℕ∞) := by
  rw [hU.topologicalKrullDimAt_eq hx, Algebra.FiniteType.topologicalKrullDimAt_eq K]

/-- The dimension of `X` at `x` is the height of `𝔭ₓ` plus the transcendence degree of the
residue field, computed on an affine open whose ring of sections is of finite type over a field
(EGA IV §5.2). -/
theorem IsAffineOpen.topologicalKrullDimAt_eq_ringKrullDim_stalk_add_trdeg (K : Type*) [Field K]
    {U : X.Opens} (hU : IsAffineOpen U) [Algebra K Γ(X, U)] [Algebra.FiniteType K Γ(X, U)]
    {x : X} (hx : x ∈ U) :
    topologicalKrullDimAt X x = ringKrullDim (X.presheaf.stalk x) +
      (Algebra.trdeg K (hU.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField).toENat := by
  let := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  rw [hU.topologicalKrullDimAt_eq hx,
    IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
      (X.presheaf.stalk x),
    Algebra.FiniteType.topologicalKrullDimAt_eq_height_add_trdeg K, WithBot.coe_add]

/-- A scheme smooth of relative dimension `n` over (the spectrum of) a field has dimension `n`
at every point. -/
theorem topologicalKrullDimAt_eq_of_smoothOfRelativeDimension {R : CommRingCat.{u}}
    (hR : IsField R) (f : X ⟶ Spec R) (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    topologicalKrullDimAt X x = n := by
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) x
  let := hR.toField
  have hU' : U = ⊤ := by
    refine eq_top_iff.mpr fun y _ ↦ ?_
    have : Subsingleton (Spec R) := inferInstanceAs (Subsingleton (PrimeSpectrum R))
    exact Subsingleton.elim (f x) y ▸ e hx
  subst hU'
  have hfield : IsField Γ(Spec R, ⊤) :=
    MulEquiv.isField hR (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv
  let := hfield.toField
  algebraize [(f.appLE ⊤ V e).hom]
  rw [hV.topologicalKrullDimAt_eq hx]
  exact Algebra.IsStandardSmoothOfRelativeDimension.topologicalKrullDimAt_eq Γ(Spec R, ⊤) n _

namespace Scheme.Hom

/-- The transcendence degree of the residue field extension `κ(x) / κ(f(x))`. -/
noncomputable def residueFieldTrdeg (f : X ⟶ Y) (x : X) : Cardinal.{u} :=
  letI := (f.residueFieldMap x).hom.toAlgebra
  Algebra.trdeg (Y.residueField (f x)) (X.residueField x)

/-- Transcendence degrees of residue field extensions add up along compositions. -/
theorem residueFieldTrdeg_comp {Z : Scheme.{u}} (h : Z ⟶ X) (f : X ⟶ Y) (z : Z) :
    (h ≫ f).residueFieldTrdeg z = f.residueFieldTrdeg (h z) + h.residueFieldTrdeg z := by
  let _ : Algebra (Y.residueField (f (h z))) (X.residueField (h z)) :=
    (f.residueFieldMap (h z)).hom.toAlgebra
  let _ : Algebra (X.residueField (h z)) (Z.residueField z) := (h.residueFieldMap z).hom.toAlgebra
  let _ : Algebra (Y.residueField (f (h z))) (Z.residueField z) :=
    (f.residueFieldMap (h z) ≫ h.residueFieldMap z).hom.toAlgebra
  have : IsScalarTower (Y.residueField (f (h z))) (X.residueField (h z)) (Z.residueField z) :=
    .of_algebraMap_eq' rfl
  have : FaithfulSMul (Y.residueField (f (h z))) (X.residueField (h z)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.residueFieldMap (h z)).hom.injective
  have : FaithfulSMul (X.residueField (h z)) (Z.residueField z) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (h.residueFieldMap z).hom.injective
  have e := lift_trdeg_add_eq (Y.residueField (f (h z))) (X.residueField (h z))
    (Z.residueField z)
  rw [Cardinal.lift_id, Cardinal.lift_id, Cardinal.lift_id] at e
  rw [residueFieldTrdeg, residueFieldTrdeg, residueFieldTrdeg, Scheme.residueFieldMap_comp]
  exact e.symm

/-- A morphism which is surjective on stalks (e.g. a preimmersion) induces surjections of residue
fields. -/
theorem residueFieldMap_surjective {Z : Scheme.{u}} (h : Z ⟶ X) [SurjectiveOnStalks h] (z : Z) :
    Function.Surjective (h.residueFieldMap z) := by
  intro w
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨t, rfl⟩ := SurjectiveOnStalks.stalkMap_surjective h z s
  exact ⟨IsLocalRing.residue _ t, rfl⟩

/-- If the residue field map is surjective (e.g. for a preimmersion), the residue field extension
has transcendence degree `0`. -/
theorem residueFieldTrdeg_eq_zero_of_surjective {Z : Scheme.{u}} (h : Z ⟶ X) (z : Z)
    (hs : Function.Surjective (h.residueFieldMap z)) : h.residueFieldTrdeg z = 0 := by
  let _ : Algebra (X.residueField (h z)) (Z.residueField z) := (h.residueFieldMap z).hom.toAlgebra
  have : Algebra.IsIntegral (X.residueField (h z)) (Z.residueField z) :=
    Algebra.IsIntegral.of_surjective (f := Algebra.ofId _ _) hs
  exact trdeg_eq_zero

/-- The residue field of the fibre `f⁻¹(f(x))` at `x` has the same transcendence degree over
`κ(f(x))` as `κ(x)`. -/
theorem residueFieldTrdeg_fiberToSpecResidueField (f : X ⟶ Y) (x : X) :
    (f.fiberToSpecResidueField (f x)).residueFieldTrdeg (f.asFiber x) = f.residueFieldTrdeg x := by
  have h := congrArg (fun φ : f.fiber (f x) ⟶ Y ↦ φ.residueFieldTrdeg (f.asFiber x))
    (f.fiber_fac (f x))
  simp only [residueFieldTrdeg_comp] at h
  rw [residueFieldTrdeg_eq_zero_of_surjective (f.fiberι (f x)) _
      (residueFieldMap_surjective _ _),
    residueFieldTrdeg_eq_zero_of_surjective (Y.fromSpecResidueField (f x)) _
      (residueFieldMap_surjective _ _), add_zero, zero_add, f.fiberι_asFiber] at h
  exact h.symm

end Scheme.Hom

/-- Let `f : X ⟶ Y`, `U ⊆ Y` and `V ⊆ X` affine opens with `V ≤ f⁻¹(U)`, and `x ∈ V` with prime
ideal `𝔮` of `Γ(X, V)`. Then `κ(𝔮)` and `κ(x)` are isomorphic as `Γ(Y, U)`-algebras, where
`Γ(Y, U)` acts on `κ(x)` through `κ(f(x))`. -/
theorem IsAffineOpen.trdeg_residueField_primeIdealOf_eq (f : X ⟶ Y) {U : Y.Opens} {V : X.Opens}
    (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U) {x : X} (hx : x ∈ V) :
    letI := (f.appLE U V e).hom.toAlgebra
    letI := ((Y.evaluation U (f x) (e hx)) ≫ f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal.ResidueField =
      Algebra.trdeg Γ(Y, U) (X.residueField x) := by
  let := (f.appLE U V e).hom.toAlgebra
  let := ((Y.evaluation U (f x) (e hx)) ≫ f.residueFieldMap x).hom.toAlgebra
  set q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hV.isLocalization_stalk ⟨x, hx⟩
  let ε : Localization.AtPrime q ≃ₐ[Γ(X, V)] X.presheaf.stalk x :=
    IsLocalization.algEquiv q.primeCompl _ _
  let ψ : q.ResidueField ≃+* X.residueField x := IsLocalRing.ResidueField.mapEquiv ε.toRingEquiv
  have hψ : ∀ a : Γ(Y, U), ψ (algebraMap Γ(Y, U) q.ResidueField a) =
      algebraMap Γ(Y, U) (X.residueField x) a := by
    intro a
    change ψ (IsLocalRing.residue _ (algebraMap Γ(Y, U) (Localization.AtPrime q) a)) = _
    rw [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization.AtPrime q)]
    change IsLocalRing.residue _ (ε (algebraMap Γ(X, V) _ (algebraMap Γ(Y, U) Γ(X, V) a))) = _
    rw [AlgEquiv.commutes]
    change X.evaluation V x hx (f.appLE U V e a) =
      f.residueFieldMap x (Y.evaluation U (f x) (e hx) a)
    refine Eq.trans ?_ (Scheme.evaluation_naturality_apply f x (e hx) a).symm
    rw [Scheme.Hom.appLE, CommRingCat.comp_apply]
    simp only [Scheme.evaluation, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  exact (AlgEquiv.ofRingEquiv (f := ψ) hψ).trdeg_eq

/-- If `Γ(Y, U) → κ(f(x))` is bijective (e.g. `Y` is the spectrum of a field, `U = Y`), then the
transcendence degree of `κ(x)` over `Γ(Y, U)` is that of `κ(x)` over `κ(f(x))`. -/
theorem Scheme.Hom.trdeg_eq_residueFieldTrdeg (f : X ⟶ Y) {U : Y.Opens} {x : X} (hx : f x ∈ U)
    (h : Function.Bijective (Y.evaluation U (f x) hx)) :
    letI := ((Y.evaluation U (f x) hx) ≫ f.residueFieldMap x).hom.toAlgebra
    Algebra.trdeg Γ(Y, U) (X.residueField x) = f.residueFieldTrdeg x := by
  let _ : Algebra Γ(Y, U) (Y.residueField (f x)) := (Y.evaluation U (f x) hx).hom.toAlgebra
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let _ : Algebra Γ(Y, U) (X.residueField x) :=
    ((Y.evaluation U (f x) hx) ≫ f.residueFieldMap x).hom.toAlgebra
  have : IsScalarTower Γ(Y, U) (Y.residueField (f x)) (X.residueField x) :=
    .of_algebraMap_eq' rfl
  have : Nontrivial Γ(Y, U) := h.2.nontrivial
  have : Algebra.IsIntegral Γ(Y, U) (Y.residueField (f x)) :=
    Algebra.IsIntegral.of_surjective (f := Algebra.ofId _ _) h.2
  have : FaithfulSMul Γ(Y, U) (Y.residueField (f x)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr h.1
  have : FaithfulSMul (Y.residueField (f x)) (X.residueField x) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (f.residueFieldMap x).hom.injective
  have e := lift_trdeg_add_eq Γ(Y, U) (Y.residueField (f x)) (X.residueField x)
  rw [trdeg_eq_zero (R := Γ(Y, U)) (A := Y.residueField (f x)), Cardinal.lift_zero,
    zero_add, Cardinal.lift_id, Cardinal.lift_id] at e
  exact e.symm

set_option backward.isDefEq.respectTransparency.types false in
/-- For a field `R`, the evaluation `Γ(Spec R, ⊤) → κ(x)` at the point of `Spec R` is
bijective. -/
theorem Spec.evaluation_top_bijective_of_isField {R : CommRingCat.{u}} (hR : IsField R)
    (x : Spec R) : Function.Bijective ((Spec R).evaluation ⊤ x trivial) := by
  have hΓ : IsField Γ(Spec R, ⊤) :=
    MulEquiv.isField hR (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv
  let := hΓ.toField
  refine ⟨RingHom.injective _, fun z ↦ ?_⟩
  have hsurj : Function.Surjective (algebraMap R x.asIdeal.ResidueField) := by
    let := hR.toField
    intro w
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective w
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective x.asIdeal.primeCompl y
    have hs : IsUnit (s : R) :=
      isUnit_iff_ne_zero.mpr fun h0 ↦ s.2 (h0 ▸ x.asIdeal.zero_mem)
    refine ⟨a * ↑hs.unit⁻¹, ?_⟩
    rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime x.asIdeal),
      IsLocalRing.ResidueField.algebraMap_eq]
    congr 1
    rw [eq_comm, IsLocalization.mk'_eq_iff_eq_mul, ← map_mul, mul_assoc, IsUnit.val_inv_mul,
      mul_one]
  obtain ⟨r, hr⟩ := hsurj ((Scheme.Spec.residueFieldIso R x).hom z)
  refine ⟨(Scheme.ΓSpecIso R).inv r, ?_⟩
  have h := congrArg (fun φ ↦ φ r) (congrArg CommRingCat.Hom.hom
    (Scheme.Spec.algebraMap_residueFieldIso_inv R x))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
  change (Spec R).residue x ((Spec R).presheaf.germ ⊤ x trivial ((Scheme.ΓSpecIso R).inv r)) = z
  rw [← h, hr]
  simp

/-- **`dim_x X = dim 𝒪_{X,x} + trdeg_k κ(x)`** (EGA IV §5.2): for a
scheme `X` locally of finite type over a field `k` (the spectrum of `R`) and `x ∈ X`, the
dimension of `X` at `x` is the dimension of the local ring `𝒪_{X,x}` plus the transcendence
degree of `κ(x)` over `k`. -/
theorem topologicalKrullDimAt_eq_ringKrullDim_stalk_add_residueFieldTrdeg {R : CommRingCat.{u}}
    (hR : IsField R) (f : X ⟶ Spec R) [LocallyOfFiniteType f] (x : X) :
    topologicalKrullDimAt X x =
      ringKrullDim (X.presheaf.stalk x) + (f.residueFieldTrdeg x).toENat := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have e : V ≤ f ⁻¹ᵁ ⊤ := le_top
  have hft : (f.appLE ⊤ V e).hom.FiniteType :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨V, hV⟩ e
  have hΓ : IsField Γ(Spec R, ⊤) :=
    MulEquiv.isField hR (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.toMulEquiv
  let := hΓ.toField
  let := (f.appLE ⊤ V e).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec R, ⊤) Γ(X, V) := hft
  rw [hV.topologicalKrullDimAt_eq_ringKrullDim_stalk_add_trdeg Γ(Spec R, ⊤) hxV,
    hV.trdeg_residueField_primeIdealOf_eq f e hxV,
    Scheme.Hom.trdeg_eq_residueFieldTrdeg f (e hxV)
      (Spec.evaluation_top_bijective_of_isField hR (f x))]

namespace Scheme.Hom

/-- The dimension at `x` of the fibre of `f` through `x`, i.e. of `f⁻¹(f(x))` at `x`
(EGA IV §13.1). -/
noncomputable def fiberDimAt (f : X ⟶ Y) (x : X) : WithBot ℕ∞ :=
  topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x)

/-- The fibre dimension is the dimension at `x` of the subspace `f⁻¹(f(x))`. -/
theorem fiberDimAt_eq (f : X ⟶ Y) (x : X) :
    f.fiberDimAt x = topologicalKrullDimAt (f ⁻¹' {f x}) ⟨x, rfl⟩ := by
  rw [fiberDimAt, ← (f.fiberHomeo (f x)).topologicalKrullDimAt_eq]
  congr 1
  exact (f.fiberHomeo (f x)).apply_symm_apply _

set_option backward.isDefEq.respectTransparency.types false in
instance smoothOfRelativeDimension_fiberToSpecResidueField (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] (y : Y) :
    SmoothOfRelativeDimension n (f.fiberToSpecResidueField y) :=
  have := smoothOfRelativeDimension_isStableUnderBaseChange (n := n)
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension n) _ _ inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance locallyOfFiniteType_fiberToSpecResidueField (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
  MorphismProperty.pullback_snd _ _ inferInstance

/-- The dimension at `x` of the fibre of a morphism locally of finite type is
`dim 𝒪_{f⁻¹(f(x)), x} + trdeg_{κ(f(x))} κ(x)` (EGA IV §5.2 applied to the fibre). -/
theorem fiberDimAt_eq_ringKrullDim_add_residueFieldTrdeg (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) : f.fiberDimAt x = ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) +
      (f.residueFieldTrdeg x).toENat := by
  rw [fiberDimAt, topologicalKrullDimAt_eq_ringKrullDim_stalk_add_residueFieldTrdeg
    (Field.toIsField _) (f.fiberToSpecResidueField (f x)),
    residueFieldTrdeg_fiberToSpecResidueField]

/-- **SGA 1 II.1.5**: the fibres of a morphism smooth of relative dimension `n` have dimension
`n` at every point. -/
theorem fiberDimAt_eq_of_smoothOfRelativeDimension (f : X ⟶ Y) (n : ℕ)
    [SmoothOfRelativeDimension n f] (x : X) : f.fiberDimAt x = n :=
  topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (Field.toIsField _)
    (f.fiberToSpecResidueField (f x)) n _

/-- The fibres `f⁻¹(y)` of a morphism smooth of relative dimension `n`, as subspaces of `X`,
have dimension `n` at each of their points. -/
theorem topologicalKrullDimAt_preimage_singleton_of_smoothOfRelativeDimension (f : X ⟶ Y)
    (n : ℕ) [SmoothOfRelativeDimension n f] {y : Y} (z : f ⁻¹' {y}) :
    topologicalKrullDimAt (f ⁻¹' {y}) z = n := by
  obtain ⟨x, hx⟩ := z
  obtain rfl : f x = y := hx
  rw [← fiberDimAt_eq_of_smoothOfRelativeDimension f n x, fiberDimAt_eq]

/-- If `f` is smooth of relative dimension `n` and `U ⊆ X` is open, then `f⁻¹(y) ∩ U` has
dimension `n` at each of its points. -/
theorem topologicalKrullDimAt_preimage_singleton_inter_of_smoothOfRelativeDimension
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f] {y : Y} {U : Set X} (hU : IsOpen U)
    (z : ↥(f ⁻¹' {y} ∩ U)) : topologicalKrullDimAt ↥(f ⁻¹' {y} ∩ U) z = n := by
  rw [topologicalKrullDimAt_inter_of_isOpen hU,
    topologicalKrullDimAt_preimage_singleton_of_smoothOfRelativeDimension f n]

/-- If `f` is smooth of relative dimension `n` and `U ⊆ X` is open with `f⁻¹(y) ∩ U` noetherian
(e.g. `U` affine and `Y` locally noetherian), then every irreducible component of `f⁻¹(y) ∩ U`
has dimension `n` (the equidimensionality of smooth morphisms, SGA 1 II.2.3, necessity). -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents_preimage_singleton_inter
    (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f] {y : Y} {U : Set X} (hU : IsOpen U)
    [NoetherianSpace ↥(f ⁻¹' {y} ∩ U)] {C : Set ↥(f ⁻¹' {y} ∩ U)}
    (hC : C ∈ irreducibleComponents ↥(f ⁻¹' {y} ∩ U)) : topologicalKrullDim C = n :=
  topologicalKrullDim_eq_of_mem_irreducibleComponents
    (topologicalKrullDimAt_preimage_singleton_inter_of_smoothOfRelativeDimension f n hU) hC

/-- **SGA 1 II.1.5**, local ring form: if `f` is smooth of relative dimension `n`, then
`dim 𝒪_{f⁻¹(f(x)), x} + trdeg_{κ(f(x))} κ(x) = n`; in particular the local ring of a point
closed in its fibre (`κ(x)` algebraic over `κ(f(x))`) has dimension `n`. -/
theorem ringKrullDim_stalk_fiber_add_residueFieldTrdeg_of_smoothOfRelativeDimension (f : X ⟶ Y)
    (n : ℕ) [SmoothOfRelativeDimension n f] (x : X) :
    ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) +
      (f.residueFieldTrdeg x).toENat = n := by
  have : LocallyOfFiniteType f := by
    have := SmoothOfRelativeDimension.smooth n f
    infer_instance
  rw [← fiberDimAt_eq_ringKrullDim_add_residueFieldTrdeg,
    fiberDimAt_eq_of_smoothOfRelativeDimension f n]

end Scheme.Hom

/-- Every irreducible component of a noetherian scheme smooth of relative dimension `n` over a
field has dimension `n`. -/
theorem topologicalKrullDim_eq_of_mem_irreducibleComponents_of_smoothOfRelativeDimension
    {R : CommRingCat.{u}} (hR : IsField R) (f : X ⟶ Spec R) (n : ℕ)
    [SmoothOfRelativeDimension n f] [NoetherianSpace X] {C : Set X}
    (hC : C ∈ irreducibleComponents X) : topologicalKrullDim C = n :=
  topologicalKrullDim_eq_of_mem_irreducibleComponents
    (topologicalKrullDimAt_eq_of_smoothOfRelativeDimension hR f n) hC

end AlgebraicGeometry
