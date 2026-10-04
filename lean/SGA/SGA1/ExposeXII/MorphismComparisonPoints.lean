/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.AnalyticGluingPoints
import SGA.SGA1.ExposeXII.ClosureComparison
import SGA.Foundations.Analytic.Morphisms

/-!
# SGA 1, Exposé XII, 3.1 (vii) and 3.2 (i), (ii), (v), (vi) for `f^an`

The point-set properties of `f^an : X^an → Y^an` (for separated `ℂ`-schemes locally of finite type)
are those of `f(ℂ) : X(ℂ) → Y(ℂ)`, transported along `AnalyticGluing.pointsHomeomorph`
(`pointsHomeomorph_analyticMap`). From the results on points in `SchemePoints.lean`:

* XII.3.2 (i): for `f` quasi-compact, `f` is surjective iff `f^an` is
  (`AnalyticGluing.surjective_analyticMap_iff`);
* XII.3.2 (ii): for `f` quasi-compact, `f` is dominant iff `f^an` has dense image
  (`AnalyticGluing.denseRange_analyticMap_iff`);
* XII.3.2 (v), direct implication, topological part: if `f` is proper, `f^an` is a proper map
  of topological spaces (`AnalyticGluing.isProperMap_analyticMap`); SGA's analytic properness
  also asks `f^an` to be separated, which needs fibre products of analytic spaces;
* XII.3.2 (vi), direct implication, topological form: if `f` is finite, `f^an` is a finite
  morphism of analytic spaces in the sense of `AnalyticGeometry.IsFiniteMap` (a proper map with
  finite fibres; Cartan, exp. 19 §5) (`AnalyticGluing.isFiniteMap_analyticMap`);
* XII.3.1 (vii), one direction: if `f` is injective, so is `f^an`
  (`AnalyticGluing.injective_analyticMap_of_injective`). The converse needs the local
  constructibility of the set of points with radicial fibres (EGA IV 9.6.1), not formalized.
-/

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

open SchemePoints

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]

/-- On points, `f^an` is `f(ℂ)` up to the homeomorphisms `X^an ≃ₜ X(ℂ)`, `Y^an ≃ₜ Y(ℂ)`. -/
lemma analyticMap_base_eq :
    ⇑(analyticMap f).base =
      (pointsHomeomorph Y).symm ∘ SchemePoints.map f ∘ pointsHomeomorph X := by
  funext x
  simp only [Function.comp_apply, ← pointsHomeomorph_analyticMap, Homeomorph.symm_apply_apply]

/-- XII.3.2 (i): a quasi-compact morphism `f` of separated `ℂ`-schemes locally of finite type is
surjective if and only if `f^an` is. Deviations from SGA: SGA does not assume `X`, `Y` separated
(here `X^an` is only built for separated schemes), and asks `f` to be of finite type, of which only
quasi-compactness is used (`f` is locally of finite type automatically). -/
theorem surjective_analyticMap_iff [QuasiCompact f] :
    Function.Surjective (analyticMap f).base ↔ Function.Surjective f := by
  rw [analyticMap_base_eq, ← surjective_map_iff (K := ℂ) f]
  simp only [EquivLike.comp_surjective, EquivLike.surjective_comp]

/-- XII.3.2 (ii): a quasi-compact morphism `f` of separated `ℂ`-schemes locally of finite type is
dominant if and only if `f^an` has dense image. Deviations from SGA: SGA does not assume `X`, `Y`
separated (here `X^an` is only built for separated schemes), and asks `f` to be of finite type, of
which only quasi-compactness is used (`f` is locally of finite type automatically). -/
theorem denseRange_analyticMap_iff [QuasiCompact f] :
    DenseRange (analyticMap f).base ↔ DenseRange f := by
  rw [analyticMap_base_eq, ← denseRange_map_iff' f, DenseRange, DenseRange, Set.range_comp,
    Set.range_comp, (pointsHomeomorph X).surjective.range_eq, Set.image_univ,
    (pointsHomeomorph Y).symm.isDenseEmbedding.dense_image]

/-- XII.3.2 (v), direct implication, topological part: if `f` is proper, `f^an` is a proper map of
the underlying topological spaces. -/
theorem isProperMap_analyticMap [IsProper f] : IsProperMap (analyticMap f).base := by
  rw [analyticMap_base_eq]
  exact (pointsHomeomorph Y).symm.isProperMap.comp
    ((isProperMap_map_of_isProper (K := ℂ) f).comp (pointsHomeomorph X).isProperMap)

/-- XII.3.1 (vii), one direction: if `f` is injective, so is `f^an`. -/
theorem injective_analyticMap_of_injective (hf : Function.Injective f) :
    Function.Injective (analyticMap f).base := by
  rw [analyticMap_base_eq]
  exact (pointsHomeomorph Y).symm.injective.comp
    ((injective_map_of_injective f hf).comp (pointsHomeomorph X).injective)

/-- XII.3.2 (vi), direct implication: if `f` is finite, then `f^an` is finite in the sense of
`AnalyticGeometry.IsFiniteMap` (a proper map with finite fibres). The converse is not proved. -/
theorem isFiniteMap_analyticMap [IsFinite f] : AnalyticGeometry.IsFiniteMap (analyticMap f) := by
  refine ⟨isProperMap_analyticMap f, fun y => ?_⟩
  have : (analyticMap f).base ⁻¹' {y} =
      pointsHomeomorph X ⁻¹' (SchemePoints.map f ⁻¹' {pointsHomeomorph Y y}) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, analyticMap_base_eq, Function.comp_apply,
      Homeomorph.symm_apply_eq]
  rw [this]
  exact (finite_map_preimage_of_isFinite f _).preimage (pointsHomeomorph X).injective.injOn

end AnalyticGluing

end SGA.SGA1.ExposeXII
