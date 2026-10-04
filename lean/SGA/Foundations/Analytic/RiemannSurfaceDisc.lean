/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Montel
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Disc charts on Riemann surfaces, and smoothness in charts

Let `M` be a complex manifold of dimension one (`ChartedSpace ℂ M`, `IsManifold 𝓘(ℂ) ω M`).

* `AnalyticGeometry.isManifold_real_of_complex`: `M` is also a smooth real manifold modelled on
  `ℂ = ℝ²` (`IsManifold 𝓘(ℝ, ℂ) ∞ M`): holomorphic coordinate changes are real smooth. This gives
  smooth partitions of unity on `M` (`SmoothPartitionOfUnity`).
* `AnalyticGeometry.contDiffAt_chart_of_mdifferentiableOn`,
  `AnalyticGeometry.contDiffAt_chart_of_contMDiff`: holomorphic functions and real smooth functions
  on `M` are real smooth in every chart.
* `AnalyticGeometry.DiscChart`: a chart `φ = extChartAt 𝓘(ℂ) p` with a radius `ρ` such that the
  closed disc of radius `ρ` around `φ p` lies in the chart target, and its discs
  `D.disc s = φ⁻¹ (B(φ p, s ρ))` for `0 < s ≤ 1`: open, with compact closure contained in
  `D.disc t` for `s < t ≤ 1` (`DiscChart.closure_disc_subset_disc`).
* `AnalyticGeometry.DiscChart.exists_image_closedBall_subset`: small disc charts exist at every
  point, inside any given neighbourhood.
* `AnalyticGeometry.boundedHolomorphic.mk`: a bounded holomorphic function on an open set, as an
  element of `𝒪ᵇ(W)`.

These are the charts of Forster's proof of the finiteness of `H¹(M, 𝒪)` (*Lectures on Riemann
surfaces*, 14.9).
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff BoundedContinuousFunction

namespace AnalyticGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-- A complex manifold of dimension one is a smooth real manifold modelled on `ℂ`. -/
theorem isManifold_real_of_complex (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] : IsManifold 𝓘(ℝ, ℂ) ∞ M :=
  isManifold_of_contDiffOn _ _ _ fun e e' he he' => by
    have h := HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
    have h1 := h.1
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      range_id, preimage_id_eq, id_eq, inter_univ, Function.id_comp, Function.comp_id] at h1 ⊢
    exact (h1.restrict_scalars ℝ).of_le le_top

/-- A function holomorphic on an open set `W ⊆ M` is real smooth in every chart, at points of
the chart target lying over `W`. -/
theorem contDiffAt_chart_of_mdifferentiableOn [IsManifold 𝓘(ℂ) 1 M] {f : M → ℂ} {W : Set M}
    (hW : IsOpen W) (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) (p : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) p).target) (hzW : (extChartAt 𝓘(ℂ) p).symm z ∈ W) :
    ContDiffAt ℝ ∞ (f ∘ (extChartAt 𝓘(ℂ) p).symm) z := by
  have hO := isOpen_extChartAt_target_inter_preimage hW p
  have hd := MDifferentiableOn.differentiableOn_chart hW hf p
  exact ((hd.contDiffOn (n := ∞) hO).restrict_scalars ℝ).contDiffAt (hO.mem_nhds ⟨hz, hzW⟩)

/-- A function holomorphic on an open set `W ⊆ M` is complex differentiable in every chart, at
points of the chart target lying over `W`. -/
theorem differentiableAt_chart_of_mdifferentiableOn [IsManifold 𝓘(ℂ) 1 M] {f : M → ℂ}
    {W : Set M} (hW : IsOpen W) (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) (p : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) p).target) (hzW : (extChartAt 𝓘(ℂ) p).symm z ∈ W) :
    DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ) p).symm) z :=
  (MDifferentiableOn.differentiableOn_chart hW hf p).differentiableAt
    ((isOpen_extChartAt_target_inter_preimage hW p).mem_nhds ⟨hz, hzW⟩)

/-- A real smooth function on `M` is real smooth in every chart. -/
theorem contDiffAt_chart_of_contMDiff [IsManifold 𝓘(ℝ, ℂ) ∞ M] {χ : M → ℝ}
    (hχ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ χ) (p : M) {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ) p).target) :
    ContDiffAt ℝ ∞ (χ ∘ (extChartAt 𝓘(ℂ) p).symm) z := by
  have hsrc : (extChartAt 𝓘(ℂ) p).symm z ∈ (chartAt ℂ p).source := by
    rw [← extChartAt_source (I := 𝓘(ℂ))]; exact (extChartAt 𝓘(ℂ) p).map_target hz
  have h := ((contMDiffAt_iff_of_mem_source (I := 𝓘(ℝ, ℂ)) (I' := 𝓘(ℝ))
    (y := χ ((extChartAt 𝓘(ℂ) p).symm z)) hsrc (by simp)).mp (hχ _)).2
  have he : extChartAt 𝓘(ℝ, ℂ) p = extChartAt 𝓘(ℂ) p := rfl
  rw [extChartAt_model_space_eq_id, he, (extChartAt 𝓘(ℂ) p).right_inv hz] at h
  simpa [modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ] using h

/-- A disc chart on a Riemann surface: the chart `extChartAt 𝓘(ℂ) center` and a radius `ρ > 0`
such that the closed disc of radius `ρ` around the image of the center lies in the chart
target. -/
structure DiscChart (M : Type*) [TopologicalSpace M] [ChartedSpace ℂ M] where
  /-- The center of the disc. -/
  center : M
  /-- The radius of the disc, in the chart. -/
  radius : ℝ
  radius_pos : 0 < radius
  closedBall_subset :
    closedBall (extChartAt 𝓘(ℂ) center center) radius ⊆ (extChartAt 𝓘(ℂ) center).target

namespace DiscChart

variable (D : DiscChart M)

/-- The chart of a disc chart. -/
abbrev chart : PartialEquiv M ℂ := extChartAt 𝓘(ℂ) D.center

/-- The image of the center in the chart. -/
abbrev c : ℂ := D.chart D.center

/-- The disc of relative radius `s`: the points of the chart source whose image lies in the ball
of radius `s ρ` around `c`. -/
def disc (s : ℝ) : Set M := D.chart.source ∩ D.chart ⁻¹' ball D.c (s * D.radius)

lemma isOpen_disc (s : ℝ) : IsOpen (D.disc s) :=
  isOpen_extChartAt_preimage' _ isOpen_ball

lemma mem_disc {s : ℝ} {x : M} :
    x ∈ D.disc s ↔ x ∈ D.chart.source ∧ D.chart x ∈ ball D.c (s * D.radius) :=
  Iff.rfl

lemma center_mem_disc {s : ℝ} (hs : 0 < s) : D.center ∈ D.disc s :=
  ⟨mem_extChartAt_source _, mem_ball_self (mul_pos hs D.radius_pos)⟩

lemma disc_subset_source (s : ℝ) : D.disc s ⊆ D.chart.source := inter_subset_left

lemma disc_mono {s t : ℝ} (hst : s ≤ t) : D.disc s ⊆ D.disc t :=
  inter_subset_inter_right _ (preimage_mono
    (ball_subset_ball (mul_le_mul_of_nonneg_right hst D.radius_pos.le)))

lemma closedBall_subset_target {s : ℝ} (hs : s ≤ 1) :
    closedBall D.c (s * D.radius) ⊆ D.chart.target :=
  (closedBall_subset_closedBall (by nlinarith [D.radius_pos])).trans D.closedBall_subset

lemma ball_subset_target {s : ℝ} (hs : s ≤ 1) : ball D.c (s * D.radius) ⊆ D.chart.target :=
  ball_subset_closedBall.trans (D.closedBall_subset_target hs)

lemma disc_subset_image {s : ℝ} : D.disc s ⊆ D.chart.symm '' closedBall D.c (s * D.radius) :=
  fun x hx => ⟨D.chart x, ball_subset_closedBall hx.2, D.chart.left_inv hx.1⟩

lemma isCompact_image_closedBall {s : ℝ} (hs : s ≤ 1) :
    IsCompact (D.chart.symm '' closedBall D.c (s * D.radius)) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((continuousOn_extChartAt_symm _).mono (D.closedBall_subset_target hs))

lemma image_closedBall_subset_disc {s t : ℝ} (hst : s < t) (ht : t ≤ 1) :
    D.chart.symm '' closedBall D.c (s * D.radius) ⊆ D.disc t := by
  rintro _ ⟨z, hz, rfl⟩
  have hzt : z ∈ D.chart.target := D.closedBall_subset_target (hst.le.trans ht) hz
  refine ⟨D.chart.map_target hzt, ?_⟩
  rw [mem_preimage, D.chart.right_inv hzt]
  exact closedBall_subset_ball (mul_lt_mul_of_pos_right hst D.radius_pos) hz

variable [T2Space M]

lemma closure_disc_subset_image {s : ℝ} (hs : s ≤ 1) :
    closure (D.disc s) ⊆ D.chart.symm '' closedBall D.c (s * D.radius) :=
  closure_minimal D.disc_subset_image (D.isCompact_image_closedBall hs).isClosed

lemma isCompact_closure_disc {s : ℝ} (hs : s ≤ 1) : IsCompact (closure (D.disc s)) :=
  (D.isCompact_image_closedBall hs).of_isClosed_subset isClosed_closure
    (D.closure_disc_subset_image hs)

lemma closure_disc_subset_disc {s t : ℝ} (hst : s < t) (ht : t ≤ 1) :
    closure (D.disc s) ⊆ D.disc t :=
  (D.closure_disc_subset_image (hst.le.trans ht)).trans (D.image_closedBall_subset_disc hst ht)

end DiscChart

/-- Every point `p` is the center of a disc chart whose closed disc lies in a given neighbourhood
`N` of `p`. -/
theorem DiscChart.exists_image_closedBall_subset (p : M) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ D : DiscChart M, D.center = p ∧
      D.chart.symm '' closedBall D.c D.radius ⊆ N := by
  set φ := extChartAt 𝓘(ℂ) p
  have h1 : φ.target ∈ 𝓝 (φ p) := extChartAt_target_mem_nhds p
  have h2 : φ.symm ⁻¹' N ∈ 𝓝 (φ p) := by
    refine (continuousAt_extChartAt_symm p).preimage_mem_nhds ?_
    rwa [extChartAt_to_inv]
  obtain ⟨ε, hε, hεs⟩ := Metric.mem_nhds_iff.mp (inter_mem h1 h2)
  refine ⟨⟨p, ε / 2, half_pos hε, fun z hz => (hεs (closedBall_subset_ball (half_lt_self hε)
    hz)).1⟩, rfl, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (hεs (closedBall_subset_ball (half_lt_self hε) hz)).2

/-- A bounded holomorphic function on an open set `W`, as an element of `𝒪ᵇ(W)`. -/
def boundedHolomorphic.mk [IsManifold 𝓘(ℂ) 1 M] (f : M → ℂ) {W : Set M}
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) (hb : ∃ C, ∀ x ∈ W, ‖f x‖ ≤ C) :
    boundedHolomorphic W :=
  ⟨BoundedContinuousFunction.ofNormedAddCommGroup (fun x : W => f x)
      (continuousOn_iff_continuous_domRestrict.mp hf.continuousOn) hb.choose
      (fun x => hb.choose_spec x x.2),
    hf.congr fun x hx => by rw [extendByZero_of_mem _ hx]; rfl⟩

@[simp]
lemma boundedHolomorphic.extendByZero_mk [IsManifold 𝓘(ℂ) 1 M] (f : M → ℂ) {W : Set M}
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) (hb : ∃ C, ∀ x ∈ W, ‖f x‖ ≤ C) {x : M}
    (hx : x ∈ W) :
    extendByZero ((boundedHolomorphic.mk f hf hb : boundedHolomorphic W) : W →ᵇ ℂ) x = f x := by
  rw [extendByZero_of_mem _ hx]
  rfl

end AnalyticGeometry
