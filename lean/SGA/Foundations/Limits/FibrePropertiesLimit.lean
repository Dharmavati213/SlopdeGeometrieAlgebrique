/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.FibreProperties
import SGA.Foundations.Limits.FibrePropertiesDescent
import SGA.Foundations.Limits.PropertiesLimitSurjective

/-!
# Geometrically connected fibres over a limit, from EGA IV 9.7.7

* `AlgebraicGeometry.Scheme.geometricallyConnectedLimitStatement_of_geometricFibresConstructible`
  (**conditional** on EGA IV 9.7.7, `Scheme.GeometricFibresConstructibleStatement`, which is not
  proved): `Scheme.GeometricallyConnectedLimitStatement`. The set `T ⊆ E j` of points with
  geometrically connected fibre is constructible (9.7.7); the fibres of `X ⟶ c.pt` and of the
  `X_j ×_{E j} E k ⟶ E k` are base changes of fibres of `X_j ⟶ E j` along field extensions, and
  geometric connectedness of a fibre is invariant under field extension
  (`geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback`); so the preimage of `T` in
  `c.pt` is everything, and the same holds in some `E k` (EGA IV 8.3.4,
  `Scheme.exists_preimage_eq_univ_of_isConstructible`).

## References

* [EGA IV₃, 8.3.4, 9.7.7][EGA4]
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 for geometrically connected fibres, **assuming EGA IV 9.7.7**
(`Scheme.GeometricFibresConstructibleStatement`, not proved): over the limit of a cofiltered
diagram of quasi-compact and quasi-separated schemes with affine transition maps, a morphism of
finite presentation `X_j ⟶ E j` whose base change to the limit has geometrically connected fibres
has a base change to some `E k` with geometrically connected fibres. -/
theorem Scheme.geometricallyConnectedLimitStatement_of_geometricFibresConstructible
    (H : Scheme.GeometricFibresConstructibleStatement.{u}) :
    Scheme.GeometricallyConnectedLimitStatement.{u} := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  have : GeometricallyConnected q := hq
  let T : Set (E.obj j) := {t | GeometricallyConnected (qj.fiberToSpecResidueField t)}
  have hT : IsConstructible T := (H qj).1.isConstructible
  have hpre : c.π.app j ⁻¹' T = Set.univ := Set.eq_univ_of_forall fun y ↦
    (geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback h y).mp inferInstance
  obtain ⟨k, hk⟩ := Scheme.exists_preimage_eq_univ_of_isConstructible hc hT hpre
  refine ⟨k.left, k.hom, ?_⟩
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro z
  have hz : E.map k.hom z ∈ T := by
    rw [← Set.mem_preimage, hk]
    trivial
  exact (geometricallyConnected_fiberToSpecResidueField_iff_of_isPullback
    (IsPullback.of_hasPullback qj (E.map k.hom)) z).mpr hz

end AlgebraicGeometry
