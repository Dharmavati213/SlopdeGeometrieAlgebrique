/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.MorphismComparisonPoints
import SGA.SGA1.ExposeXII.MorphismComparisonGlobal
import SGA.SGA1.ExposeXII.RiemannFull
import SGA.SGA1.ExposeXII.GAGA

/-!
# SGA 1, Exposé XII, 3.1 (ix): `f` is an isomorphism iff `f^an` is

For a quasi-compact morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type,
`f` is an isomorphism iff `f^an : X^an → Y^an` is an isomorphism of locally ringed spaces
(`AnalyticGluing.isIso_iff_isIso_analyticMap`).

The direct implication is functoriality (`AnalyticGluing.isIso_analyticMap`). For the converse,
SGA argues "(ix) follows from (xi) and XII.3.2 (i)". Here: the stalk maps of `f^an` are
isomorphisms, so `f` is étale by XII.3.1 (iii) (`AnalyticGluing.etale_iff_forall_analyticMap`);
`f^an` is bijective on points, so `f` is bijective on `ℂ`-points (`analyticMap_base_eq`); and an
étale, quasi-compact, quasi-separated morphism bijective on `ℂ`-points is an isomorphism
(xii51's `SchemePoints.isIso_of_bijective_map`, by the Jacobson property).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]

/-- XII.3.1 (ix), direct implication: if `f` is an isomorphism, so is `f^an`. -/
instance isIso_analyticMap [IsIso f] : IsIso (analyticMap f) := by
  have : (inv f).IsOver (Spec (.of ℂ)) := ⟨by rw [IsIso.inv_comp_eq, CategoryTheory.comp_over]⟩
  refine ⟨analyticMap (inv f), ?_, ?_⟩
  · rw [← analyticMap_comp, analyticMap_congr (IsIso.hom_inv_id f), analyticMap_id]
  · rw [← analyticMap_comp, analyticMap_congr (IsIso.inv_hom_id f), analyticMap_id]

/-- XII.3.1 (ix), converse: for `f` quasi-compact, if `f^an` is an isomorphism, so is `f`.
Deviations from SGA: SGA does not assume `X`, `Y` separated (here `X^an` is only built for
separated schemes) nor `f` quasi-compact. -/
theorem isIso_of_isIso_analyticMap [QuasiCompact f] [IsIso (analyticMap f)] : IsIso f := by
  have hét : Etale f := by
    refine (etale_iff_forall_analyticMap f).mpr fun x => ?_
    have hbij : Function.Bijective ((analyticMap f).stalkMap x).hom :=
      ConcreteCategory.bijective_of_isIso ((analyticMap f).stalkMap x)
    exact ⟨RingHom.Flat.of_bijective hbij, map_maximalIdeal_of_surjective _ hbij.2⟩
  have : IsIso (analyticMap f).base :=
    inferInstanceAs (IsIso (LocallyRingedSpace.forgetToTop.map (analyticMap f)))
  have hbase : Function.Bijective (analyticMap f).base :=
    ConcreteCategory.bijective_of_isIso (analyticMap f).base
  have hbij : Function.Bijective (SchemePoints.map (K := ℂ) f) := by
    rw [analyticMap_base_eq] at hbase
    have h := (((pointsHomeomorph Y).bijective.comp hbase).comp
      (pointsHomeomorph X).symm.bijective)
    convert h using 1
    funext p
    simp
  have : IsSeparated (f ≫ (Y ↘ Spec (.of ℂ))) := by
    rw [CategoryTheory.comp_over]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of ℂ))
  exact SchemePoints.isIso_of_bijective_map f hbij

/-- **XII.3.1 (ix)**: a quasi-compact morphism `f` of separated `ℂ`-schemes locally of finite
type is an isomorphism iff `f^an` is an isomorphism of locally ringed spaces. Deviations from SGA:
SGA does not assume `X`, `Y` separated nor `f` quasi-compact. -/
theorem isIso_iff_isIso_analyticMap [QuasiCompact f] : IsIso f ↔ IsIso (analyticMap f) :=
  ⟨fun _ => inferInstance, fun _ => isIso_of_isIso_analyticMap f⟩

end AnalyticGluing

end SGA.SGA1.ExposeXII
