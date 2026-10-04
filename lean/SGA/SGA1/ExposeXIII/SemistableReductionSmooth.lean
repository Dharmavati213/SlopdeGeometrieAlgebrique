/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.Semistable.SmoothCurve
import SGA.SGA1.ExposeII.Field
import SGA.SGA1.ExposeII.RegularSequence
import SGA.SGA1.ExposeII.RegularSystemFiltration
import SGA.SGA1.ExposeXIII.AbhyankarAffineLine
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# Smooth curves over an algebraically closed field: local rings at closed points

A step towards "a smooth special fibre is a semistable curve" (`IsSemistableCurve`, used in
`SemistableReductionStatement`, the input of Raynaud's case B of XIII.2.13): the local ring of a
smooth curve over an algebraically closed field at a closed point is a discrete valuation ring
(`SGA.SGA1.ExposeXIII.isDiscreteValuationRing_stalk_of_smooth`). It is regular by II.5.3
(`ExposeII.isRegularLocalRing_stalk_of_smooth_field`) and of dimension `1`
(`AlgebraicGeometry.ringKrullDim_stalk_eq_one`).

Its completion is `k⟦t⟧` (`SGA.SGA1.ExposeXIII.nonempty_ringEquiv_powerSeries_of_smooth`): with
a uniformizer `π` (a regular sequence of length one, hence a regular system of generators of
`𝔪 = (π)` by II.4.14, `ExposeII.isRegularSystemOfGenerators_of_isWeaklyRegular`) and the
`k`-algebra structure `AlgebraicGeometry.stalkStructureMap` (`k → 𝒪_y → κ(y)` bijective), II.4.14
in completed form (`ExposeII.isRegularSystemOfGenerators_iff_bijective_powerSeriesMap`) gives
`k⟦t⟧ ≅ 𝒪̂_y`. Hence a smooth curve over an algebraically closed field is a semistable curve
(`SGA.SGA1.ExposeXIII.isSemistableCurve_of_smooth`).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

/-- The local ring of a smooth curve over an algebraically closed field at a closed point is a
discrete valuation ring (a domain, and a DVR). -/
theorem isDiscreteValuationRing_stalk_of_smooth {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    ∃ _ : IsDomain (Y.presheaf.stalk y), IsDiscreteValuationRing (Y.presheaf.stalk y) := by
  have : Smooth f := SmoothOfRelativeDimension.smooth 1 f
  have := ExposeII.isRegularLocalRing_stalk_of_smooth_field k f y
  exact ⟨inferInstance,
    IsRegularLocalRing.isDiscreteValuationRing (ringKrullDim_stalk_eq_one f y hy)⟩

/-- The completed local ring of a smooth curve over an algebraically closed field `k` at a closed
point is isomorphic to `k⟦t⟧` as a ring (only a ring isomorphism is asserted, as in
`IsSemistableCurve`). -/
theorem nonempty_ringEquiv_powerSeries_of_smooth {k : Type u} [Field k] [IsAlgClosed k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] (y : Y)
    (hy : IsClosed ({y} : Set Y)) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Y.presheaf.stalk y))
      (Y.presheaf.stalk y) ≃+* PowerSeries k) := by
  have : LocallyOfFiniteType f := by
    have := SmoothOfRelativeDimension.smooth 1 f
    infer_instance
  obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_of_smooth f y hy
  let : Algebra k (Y.presheaf.stalk y) := (stalkStructureMap f y).hom.toAlgebra
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Y.presheaf.stalk y)
  let x : Fin [π].length → Y.presheaf.stalk y := fun i ↦ [π][i]
  have hreg : RingTheory.Sequence.IsWeaklyRegular (Y.presheaf.stalk y) [π] := by
    rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    exact IsSMulRegular.of_ne_zero hπ.ne_zero
  have hx : ExposeII.IsRegularSystemOfGenerators x :=
    ExposeII.isRegularSystemOfGenerators_of_isWeaklyRegular [π] hreg
  have hI : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal (Y.presheaf.stalk y) := by
    rw [hπ.maximalIdeal_eq]
    congr 1
    ext z
    simp [x]
  have hB : Function.Bijective
      (algebraMap k (Y.presheaf.stalk y ⧸ Ideal.span (Set.range x))) := by
    rw [hI]
    exact bijective_residue_comp_stalkStructureMap f y hy
  have hbij := (ExposeII.isRegularSystemOfGenerators_iff_bijective_powerSeriesMap hB).mp hx
  rw [← hI]
  exact ⟨(RingEquiv.ofBijective _ hbij).symm.trans
    (MvPowerSeries.renameEquiv k (Equiv.equivPUnit (Fin 1) : Fin [π].length ≃ Unit)).toRingEquiv⟩

/-- A smooth curve over an algebraically closed field `k` is a semistable curve in the sense of
`IsSemistableCurve`: every completed local ring at a closed point is `k⟦t⟧`. -/
theorem isSemistableCurve_of_smooth {k : Type u} [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 f] : IsSemistableCurve k Y :=
  fun y hy ↦ Or.inl (nonempty_ringEquiv_powerSeries_of_smooth f y hy)

end SGA.SGA1.ExposeXIII
