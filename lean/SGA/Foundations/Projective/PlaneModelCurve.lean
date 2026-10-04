/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.PlaneModel
import SGA.Foundations.NormalizationFiniteDimension

/-!
# The plane curve through `(1 : x : y)` is integral, with function field `k(x, y)`

Let `k ⊆ K` be fields and `x, y ∈ K` with `K = k(x, y)`. The plane curve
`D = AlgebraicGeometry.planeCurve k x y = Proj (k[X₀, X₁, X₂] ⧸ 𝔭)` of
`SGA.Foundations.Projective.PlaneModel` is integral, its function field is `K`, and its
dimension is `trdeg_k K`:

* `AlgebraicGeometry.Proj.isReduced_of_isDomain`: `Proj` of a graded domain is reduced (its local
  rings are subrings of localizations of the domain);
* `AlgebraicGeometry.PlaneCurve.isIntegral`: `D` is integral;
* `AlgebraicGeometry.PlaneCurve.functionFieldHom`: the map `K(D) → K` through which the `K`-point
  `(1 : x : y)` (`PlaneCurve.kPoint`) factors (`PlaneCurve.SpecMap_functionFieldHom`); it is a
  `k`-algebra map (`PlaneCurve.functionFieldHom_comp`) and bijective when `K = k(x, y)`
  (`PlaneCurve.bijective_functionFieldHom`);
* `AlgebraicGeometry.PlaneCurve.topologicalKrullDim_eq`: `dim D = trdeg_k K` when `K = k(x, y)`.

## References

* [R. Hartshorne, *Algebraic Geometry*, I.3 and II.2][Hartshorne]
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization AlgebraicGeometry ProjectiveSpace

namespace AlgebraicGeometry

/-- `Proj` of a graded domain is reduced: its local rings are homogeneous localizations, which are
subrings of localizations of the domain. -/
theorem Proj.isReduced_of_isDomain {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [IsDomain A] (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : IsReduced (Proj 𝒜) := by
  suffices ∀ x : Proj 𝒜, _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) from
    isReduced_of_isReduced_stalk _
  intro x
  have : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have : IsDomain (Localization.AtPrime x.asHomogeneousIdeal.toIdeal) :=
    IsLocalization.isDomain_localization x.asHomogeneousIdeal.toIdeal.primeCompl_le_nonZeroDivisors
  let φ : AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal →+* Localization.AtPrime
      x.asHomogeneousIdeal.toIdeal :=
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  have : IsDomain (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain φ (HomogeneousLocalization.val_injective _)
  have : _root_.IsReduced (AtPrime 𝒜 x.asHomogeneousIdeal.toIdeal) := inferInstance
  have e := (Proj.stalkIso 𝒜 x).commRingCatIsoToRingEquiv
  exact isReduced_of_injective e.toRingHom e.injective

/-- A morphism `f : Spec R ⟶ X` from a local ring factors through `Spec 𝒪_{X, y}` for every
generization `y` of the image of the closed point. -/
lemma Scheme.SpecMap_stalkSpecializes_stalkClosedPointTo {X : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (f : Spec R ⟶ X) {y : X} (h : f (IsLocalRing.closedPoint R) ⤳ y) :
    Spec.map (X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo f) ≫ X.fromSpecStalk y =
      f := by
  rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

/-- The image of the stalk map of `Spec R ⟶ Spec A` at the closed point contains the image of
`A → R`. -/
lemma Scheme.mem_range_stalkClosedPointTo_Spec {A R : CommRingCat.{u}} [IsLocalRing R]
    (φ : A ⟶ R) (a : A) : φ a ∈ Set.range (Scheme.stalkClosedPointTo (Spec.map φ)) := by
  refine ⟨(Spec A).presheaf.germ ⊤ _ trivial ((Scheme.ΓSpecIso A).inv a), ?_⟩
  have e := congrArg (fun g ↦ g.hom ((Scheme.ΓSpecIso A).inv a))
    (Scheme.germ_stalkClosedPointTo_Spec φ)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  exact e.trans (congrArg φ.hom (Iso.inv_hom_id_apply (Scheme.ΓSpecIso A) a))

/-- Composing with an open immersion does not change the image of the stalk map at the closed
point. -/
lemma Scheme.mem_range_stalkClosedPointTo_comp {X Y : Scheme.{u}} {R : CommRingCat.{u}}
    [IsLocalRing R] (g : Spec R ⟶ Y) (ι : Y ⟶ X) [IsOpenImmersion ι] {z : R}
    (hz : z ∈ Set.range (Scheme.stalkClosedPointTo g)) :
    z ∈ Set.range (Scheme.stalkClosedPointTo (g ≫ ι)) := by
  obtain ⟨s, rfl⟩ := hz
  refine ⟨inv (ι.stalkMap _) s, ?_⟩
  have h : ι.stalkMap _ (inv (ι.stalkMap (g (IsLocalRing.closedPoint R))) s) = s :=
    IsIso.inv_hom_id_apply _ s
  rw [Scheme.stalkClosedPointTo_comp]
  exact congrArg (Scheme.stalkClosedPointTo g) h

namespace PlaneCurve

variable (k : Type u) [Field k] {K : Type u} [Field K] [Algebra k K] (x y : K)

instance isReduced : IsReduced (planeCurve k x y) :=
  Proj.isReduced_of_isDomain _

instance isIntegral : IsIntegral (planeCurve k x y) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

lemma genericPoint_eq : genericPoint (planeCurve k x y) = genericPt k x y :=
  (genericPoint_spec (planeCurve k x y)).eq (isGenericPoint_genericPt k x y)

lemma kPoint_closedPoint :
    kPoint k x y (IsLocalRing.closedPoint (CommRingCat.of K)) = genericPoint (planeCurve k x y) :=
  (kPoint_apply k x y _).trans (genericPoint_eq k x y).symm

/-- The map of fields `K(D) → K` through which the `K`-point `(1 : x : y)` of the plane curve `D`
factors (`SpecMap_functionFieldHom`). -/
noncomputable def functionFieldHom : (planeCurve k x y).functionField ⟶ .of K :=
  ((planeCurve k x y).presheaf.stalkCongr (Inseparable.of_eq (kPoint_closedPoint k x y).symm)).hom ≫
    Scheme.stalkClosedPointTo (kPoint k x y)

lemma SpecMap_functionFieldHom :
    Spec.map (functionFieldHom k x y) ≫ (planeCurve k x y).fromSpecStalk _ = kPoint k x y :=
  Scheme.SpecMap_stalkSpecializes_stalkClosedPointTo (kPoint k x y)
    (Inseparable.of_eq (kPoint_closedPoint k x y).symm).ge

/-- `functionFieldHom` is a `k`-algebra map: composed with `k → K(D)` (induced by the structure
morphism) it is `algebraMap k K`. -/
lemma functionFieldHom_comp :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k x y).appTop ≫
      (planeCurve k x y).presheaf.germ ⊤ (genericPoint _) trivial) ≫ functionFieldHom k x y =
      CommRingCat.ofHom (algebraMap k K) := by
  apply Spec.map_injective
  have h : (planeCurve k x y).fromSpecStalk (genericPoint _) ≫ toSpec k x y =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k x y).appTop ≫
        (planeCurve k x y).presheaf.germ ⊤ (genericPoint _) trivial) := by
    rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ_assoc, Category.assoc,
      Category.assoc, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp,
      Iso.inv_hom_id, Spec.map_id, Category.comp_id]
  rw [Spec.map_comp, ← h, ← Category.assoc, SpecMap_functionFieldHom, kPoint_toSpec]

/-- The image of `functionFieldHom` contains `k[x, y]`. -/
lemma mem_range_functionFieldHom {z : K} (hz : z ∈ Algebra.adjoin k {x, y}) :
    z ∈ Set.range (functionFieldHom k x y) := by
  rw [← range_chartAlgHom] at hz
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨s, hs⟩ := Scheme.mem_range_stalkClosedPointTo_comp _
    (Proj.awayι (ideal k x y).quotientGrading (X₀ k x y) (X₀_mem k x y) one_pos)
    (Scheme.mem_range_stalkClosedPointTo_Spec (CommRingCat.ofHom (chartHom k x y)) a)
  let E := (planeCurve k x y).presheaf.stalkCongr
    (Inseparable.of_eq (kPoint_closedPoint k x y).symm)
  refine ⟨E.inv s, ?_⟩
  have h : E.hom (E.inv s) = s := Iso.inv_hom_id_apply E s
  change (Scheme.stalkClosedPointTo (kPoint k x y)) (E.hom (E.inv s)) = _
  rw [h]
  exact hs

/-- `K(D) → K` is bijective when `K = k(x, y)`. -/
lemma bijective_functionFieldHom (hxy : IntermediateField.adjoin k {x, y} = ⊤) :
    Function.Bijective (functionFieldHom k x y) := by
  refine ⟨(functionFieldHom k x y).hom.injective, ?_⟩
  -- the image is a subfield containing `k`, `x` and `y`
  let ψ : (planeCurve k x y).functionField →+* K := (functionFieldHom k x y).hom
  have hk (r : k) : algebraMap k K r ∈ ψ.fieldRange := by
    refine RingHom.mem_fieldRange.mpr ⟨((Scheme.ΓSpecIso (.of k)).inv ≫ (toSpec k x y).appTop ≫
      (planeCurve k x y).presheaf.germ ⊤ (genericPoint _) trivial) r, ?_⟩
    have e := congrArg (fun g ↦ g.hom r) (functionFieldHom_comp k x y)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
    exact e
  let F : IntermediateField k K :=
    { ψ.fieldRange with
      algebraMap_mem' := hk }
  have hle : IntermediateField.adjoin k {x, y} ≤ F := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨w, hw⟩ := mem_range_functionFieldHom k x y (Algebra.subset_adjoin hz)
    exact ⟨w, hw⟩
  intro z
  have : z ∈ F := hle (hxy ▸ IntermediateField.mem_top)
  obtain ⟨w, hw⟩ := this
  exact ⟨w, hw⟩

/-- **The dimension of the plane curve**: `dim D = trdeg_k K` when `K = k(x, y)` (so `D` is a curve
exactly when `trdeg_k K = 1`). -/
theorem topologicalKrullDim_eq (hxy : IntermediateField.adjoin k {x, y} = ⊤) :
    topologicalKrullDim (planeCurve k x y) = (Algebra.trdeg k K).toENat := by
  let α : k →+* (planeCurve k x y).functionField := ((Scheme.ΓSpecIso (.of k)).inv ≫
    (toSpec k x y).appTop ≫ (planeCurve k x y).presheaf.germ ⊤ (genericPoint _) trivial).hom
  let _ : Algebra k (planeCurve k x y).functionField := α.toAlgebra
  have : LocallyOfFiniteType (toSpec k x y) := inferInstance
  rw [topologicalKrullDim_eq_trdeg_functionField (toSpec k x y) rfl]
  let e : (planeCurve k x y).functionField ≃ₐ[k] K :=
    { RingEquiv.ofBijective (functionFieldHom k x y).hom (bijective_functionFieldHom k x y hxy) with
      commutes' := fun r ↦ by
        have e := congrArg (fun g ↦ g.hom r) (functionFieldHom_comp k x y)
        simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at e
        exact e }
  rw [e.trdeg_eq]

end PlaneCurve

end AlgebraicGeometry
