/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.AnalyticGluingMap
import SGA.SGA1.ExposeXII.Nullstellensatz

/-!
# SGA 1, Exposé XII, 1.1: the underlying space of `X^an` is `X(ℂ)`

The repository has two models of the analytic space of a `ℂ`-scheme `X` locally of finite type:
the space of points `X(ℂ)` (`SchemePoints ℂ X`, with the topology glued from the affine charts, and
its reduced structure sheaf `SchemePoints.analytification ℂ X`), and, for separated `X`, the
non-reduced analytic space `X^an = AnalyticGluing.analyticSpace X`. This file identifies their
underlying spaces:

* `AnalyticGluing.pointsHomeomorph X : X^an ≃ₜ X(ℂ)`, sending `x` to the `ℂ`-point at the closed
  point `φ(x)` (`pt_pointsHomeomorph`), and the chart `U^an` to the chart `U(ℂ)`
  (`pointsHomeomorph_ι`);
* it is compatible with morphisms: `f^an` corresponds to `f(ℂ) : X(ℂ) → Y(ℂ)`
  (`pointsHomeomorph_analyticMap`).

Topological facts about `X(ℂ)` (local path-connectedness, Hausdorffness, compactness, the
comparison of fundamental groups, …) are proved for `SchemePoints ℂ X`; transport them along
`pointsHomeomorph` rather than proving them again for `X^an`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AnalyticGeometry Topology Filter

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

open AffineAnalytification SchemePoints

attribute [local instance] sectionsAlgebra finitePresentation_sections

variable {X : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]

/-- A `ℂ`-point of `X` is determined by its underlying point. -/
lemma pt_injective :
    Function.Injective (SchemePoints.pt : SchemePoints ℂ X → X) := fun _ _ h ↦
  equivClosedPoints.injective (Subtype.ext h)

variable [IsSeparated (X ↘ Spec (.of ℂ))]

variable (X) in
/-- The `ℂ`-point of `X` at the closed point `φ(x)`, for `x ∈ X^an`. -/
def toPoints (x : analyticSpace X) : SchemePoints ℂ X :=
  equivClosedPoints.symm ⟨(toScheme X).base x, (range_toScheme_base (X := X)) ▸ ⟨x, rfl⟩⟩

@[simp]
lemma pt_toPoints (x : analyticSpace X) : (toPoints X x).pt = (toScheme X).base x := by
  rw [← coe_equivClosedPoints, toPoints, Equiv.apply_symm_apply]

/-- On the chart of an affine open `U`, `toPoints` is the chart `U(ℂ) → X(ℂ)`. -/
lemma toPoints_ι (U : X.affineOpens) (p : Points ℂ Γ(X, U)) :
    toPoints X ((ι U).base (affinePointsHomeomorph ℂ Γ(X, U) p)) =
      SchemePoints.chart (isAffineOpen U) p := by
  apply pt_injective
  rw [pt_toPoints, ← comp_base_apply', ι_toScheme, pt_chart_eq]
  change (fromSpecLRS U).base ((affineToSpec ℂ Γ(X, U)).base _) = _
  rw [affineToSpec_base_affinePointsHomeomorph]
  rfl

lemma bijective_toPoints : Function.Bijective (toPoints X) := by
  refine ⟨fun x y h ↦ injective_toScheme_base ?_, fun p ↦ ?_⟩
  · rw [← pt_toPoints, ← pt_toPoints, h]
  · have hp : p.pt ∈ Set.range (toScheme X).base := by
      rw [range_toScheme_base, ← coe_equivClosedPoints]
      exact (equivClosedPoints p).2
    obtain ⟨x, hx⟩ := hp
    exact ⟨x, pt_injective (by rw [pt_toPoints, hx])⟩

/-- On the chart of an affine open `U`, `toPoints ∘ ι U` is the chart `U(ℂ) → X(ℂ)` read through
`U^an ≃ₜ U(ℂ)`. -/
lemma toPoints_comp_ι (U : X.affineOpens) :
    toPoints X ∘ (ι U).base =
      SchemePoints.chart (isAffineOpen U) ∘ (affinePointsHomeomorph ℂ Γ(X, U)).symm := by
  funext y
  obtain ⟨p, rfl⟩ := (affinePointsHomeomorph ℂ Γ(X, U)).surjective y
  simp only [Function.comp_apply, Homeomorph.symm_apply_apply]
  exact toPoints_ι U p

lemma isOpenEmbedding_ι_base (U : X.affineOpens) : IsOpenEmbedding (ι U).base :=
  (inferInstance : LocallyRingedSpace.IsOpenImmersion (ι U)).base_open

lemma continuous_toPoints : Continuous (toPoints X) := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  obtain ⟨U, y, rfl⟩ := ι_jointly_surjective x
  rw [← (isOpenEmbedding_ι_base U).continuousAt_iff, toPoints_comp_ι]
  exact ((SchemePoints.isOpenEmbedding_chart (isAffineOpen U)).continuous.comp
    (affinePointsHomeomorph ℂ Γ(X, U)).symm.continuous).continuousAt

lemma isOpenMap_toPoints : IsOpenMap (toPoints X) := by
  refine isOpenMap_iff_nhds_le.mpr fun x ↦ ?_
  obtain ⟨U, y, rfl⟩ := ι_jointly_surjective x
  obtain ⟨p, rfl⟩ := (affinePointsHomeomorph ℂ Γ(X, U)).surjective y
  have e₁ : Filter.map ((ι U).base ∘ affinePointsHomeomorph ℂ Γ(X, U)) (𝓝 p) =
      𝓝 ((ι U).base (affinePointsHomeomorph ℂ Γ(X, U) p)) :=
    ((isOpenEmbedding_ι_base U).comp
      (affinePointsHomeomorph ℂ Γ(X, U)).isOpenEmbedding).map_nhds_eq p
  have e₂ := (SchemePoints.isOpenEmbedding_chart (isAffineOpen U)).map_nhds_eq p
  have hc : toPoints X ∘ ((ι U).base ∘ affinePointsHomeomorph ℂ Γ(X, U)) =
      SchemePoints.chart (isAffineOpen U) := by
    rw [← Function.comp_assoc, toPoints_comp_ι, Function.comp_assoc,
      Homeomorph.symm_comp_self, Function.comp_id]
  rw [← e₁, Filter.map_map, hc, e₂, toPoints_ι]

variable (X) in
/-- XII.1.1: the underlying space of `X^an` is the space `X(ℂ)` of `ℂ`-points of `X`. -/
def pointsHomeomorph : analyticSpace X ≃ₜ SchemePoints ℂ X :=
  (Equiv.ofBijective _ bijective_toPoints).toHomeomorphOfContinuousOpen continuous_toPoints
    isOpenMap_toPoints

@[simp]
lemma pointsHomeomorph_apply (x : analyticSpace X) : pointsHomeomorph X x = toPoints X x := rfl

/-- XII.1.1: the point of `X(ℂ)` attached to `x ∈ X^an` lies over `φ(x)`. -/
lemma pt_pointsHomeomorph (x : analyticSpace X) :
    (pointsHomeomorph X x).pt = (toScheme X).base x :=
  pt_toPoints x

/-- XII.1.1: the chart `U^an ⊆ X^an` of an affine open `U` corresponds to the chart
`U(ℂ) ⊆ X(ℂ)`. -/
lemma pointsHomeomorph_ι (U : X.affineOpens) (p : Points ℂ Γ(X, U)) :
    pointsHomeomorph X ((ι U).base (affinePointsHomeomorph ℂ Γ(X, U) p)) =
      SchemePoints.chart (isAffineOpen U) p :=
  toPoints_ι U p

variable {Y : Scheme.{0}} [Y.Over (Spec (.of ℂ))] [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))]
  [IsSeparated (Y ↘ Spec (.of ℂ))] (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]

/-- XII.1.2: under `X^an ≃ₜ X(ℂ)`, `f^an` is the map `f(ℂ) : X(ℂ) → Y(ℂ)`. -/
theorem pointsHomeomorph_analyticMap (x : analyticSpace X) :
    pointsHomeomorph Y ((analyticMap f).base x) = SchemePoints.map f (pointsHomeomorph X x) := by
  apply pt_injective
  rw [pt_pointsHomeomorph, pt_map, pt_pointsHomeomorph, ← comp_base_apply',
    analyticMap_toScheme]
  rfl

end AnalyticGluing

end SGA.SGA1.ExposeXII
