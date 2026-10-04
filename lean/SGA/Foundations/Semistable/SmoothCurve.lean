/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import SGA.Foundations.Dimension.Scheme

/-!
# Local rings of smooth curves at closed points

A first step towards "a smooth special fibre is a semistable curve" (registry row A21): for `Y`
smooth of relative dimension `1` over an algebraically closed field `k`, the residue field of a
closed point is `k` (mathlib's `AlgebraicGeometry.residueFieldIsoBase`), the residue field
extension has transcendence degree `0`
(`AlgebraicGeometry.residueFieldTrdeg_eq_zero_of_isClosed`) and the local ring has dimension `1`
(`AlgebraicGeometry.ringKrullDim_stalk_eq_one`), from the dimension formula
`dim_y Y = dim 𝒪_y + trdeg_k κ(y)` of `SGA.Foundations.Dimension.Scheme`.

For a scheme `Y` over `Spec A` (`A` any ring, for instance `k`) we also give the `A`-algebra
structure of the local rings, `AlgebraicGeometry.stalkStructureMap f y : A ⟶ 𝒪_{Y,y}` (the ring
map with `Spec (𝒪_{Y,y}) ⟶ Y ⟶ Spec A` as its spectrum), and show that at a closed point of a scheme
locally of finite type over an algebraically closed `k`, the composite `k → 𝒪_{Y,y} → κ(y)` is
mathlib's isomorphism `residueFieldIsoBase` (`AlgebraicGeometry.stalkStructureMap_residue`), hence
bijective (`AlgebraicGeometry.bijective_residue_comp_stalkStructureMap`).

## References

* [A. Grothendieck, *EGA* IV, 5.2 and 17.10.2]
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

section StructureMap

section Ring

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of A))

/-- The structure map `A → 𝒪_{Y,y}` of a scheme `Y` over `Spec A` (for instance a field `k`): the
ring map whose spectrum is `Spec 𝒪_{Y,y} ⟶ Y ⟶ Spec A`. -/
noncomputable def stalkStructureMap (y : Y) : CommRingCat.of A ⟶ Y.presheaf.stalk y :=
  Spec.preimage (Y.fromSpecStalk y ≫ f)

@[simp]
lemma Spec_map_stalkStructureMap (y : Y) :
    Spec.map (stalkStructureMap f y) = Y.fromSpecStalk y ≫ f :=
  Spec.map_preimage _

end Ring

variable {k : Type u} [Field k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
the composite `k → 𝒪_{Y,y} → κ(y)` is the inverse of mathlib's `residueFieldIsoBase`. -/
lemma stalkStructureMap_residue [IsAlgClosed k] [LocallyOfFiniteType f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    stalkStructureMap f y ≫ Y.residue y = (residueFieldIsoBase f y hy).inv := by
  apply Spec.map_injective
  rw [Spec.map_comp, Spec_map_stalkStructureMap, SpecMap_residueFieldIsoBase_inv,
    Scheme.fromSpecResidueField, Category.assoc]

/-- At a closed point of a scheme locally of finite type over an algebraically closed field `k`,
the composite `k → 𝒪_{Y,y} → κ(y)` is bijective. -/
lemma bijective_residue_comp_stalkStructureMap [IsAlgClosed k] [LocallyOfFiniteType f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    Function.Bijective
      (IsLocalRing.residue (Y.presheaf.stalk y) ∘ (stalkStructureMap f y).hom) := by
  have h := congrArg (fun φ ↦ ⇑(CommRingCat.Hom.hom φ)) (stalkStructureMap_residue f y hy)
  simp only [CommRingCat.hom_comp, RingHom.coe_comp] at h
  change Function.Bijective ((Y.residue y).hom ∘ (stalkStructureMap f y).hom)
  rw [h]
  exact ConcreteCategory.bijective_of_isIso (residueFieldIsoBase f y hy).inv

end StructureMap

variable {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k))

/-- At a closed point of a scheme locally of finite type over an algebraically closed field, the
residue field extension has transcendence degree `0`. -/
lemma residueFieldTrdeg_eq_zero_of_isClosed [LocallyOfFiniteType f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) : f.residueFieldTrdeg y = 0 := by
  set p := pointOfClosedPoint f y hy
  obtain ⟨z⟩ : Nonempty (Spec (.of k)) := inferInstance
  have hc := Scheme.Hom.residueFieldTrdeg_comp p f z
  have hid : (p ≫ f).residueFieldTrdeg z = 0 := by
    rw [pointOfClosedPoint_comp]
    refine Scheme.Hom.residueFieldTrdeg_eq_zero_of_surjective _ z ?_
    rw [Scheme.residueFieldMap_id]
    exact Function.surjective_id
  rw [hid, pointOfClosedPoint_apply] at hc
  exact (add_eq_zero.mp hc.symm).1

/-- The local ring of a smooth curve over an algebraically closed field at a closed point has
dimension `1` (SGA 1 II.1.5 / EGA IV 5.2: `dim 𝒪_y + trdeg_k κ(y) = 1` and `κ(y) = k`). -/
lemma ringKrullDim_stalk_eq_one [SmoothOfRelativeDimension 1 f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) : ringKrullDim (Y.presheaf.stalk y) = 1 := by
  have : LocallyOfFiniteType f := by
    have := SmoothOfRelativeDimension.smooth 1 f
    infer_instance
  have h1 := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension (Field.toIsField k) f 1 y
  have h2 := topologicalKrullDimAt_eq_ringKrullDim_stalk_add_residueFieldTrdeg
    (Field.toIsField k) f y
  rw [residueFieldTrdeg_eq_zero_of_isClosed f y hy, h1] at h2
  simpa using h2.symm

end AlgebraicGeometry
