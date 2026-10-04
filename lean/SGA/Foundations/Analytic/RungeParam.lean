/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Osgood
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# Circle integrals depending holomorphically on parameters

Let `E` be a complex normed space and `G : E → ℂ → ℂ` a function which is analytic, jointly in
`(z, ζ)`, at every point of `{z₀} × S(c, |R|)`. Then `z ↦ ∮_{|ζ - c| = R} G(z, ζ) dζ` is complex
differentiable at `z₀`, with the derivative obtained by differentiating under the integral sign
(`AnalyticGeometry.hasFDerivAt_circleIntegral_param`). For `E = ℂ^σ` (`σ` finite) the integral is
analytic at `z₀` (`AnalyticGeometry.analyticAt_circleIntegral_param`), by
`AnalyticGeometry.analyticAt_of_differentiableOn` (`DifferentiableOn ℂ` on an open subset of
`ℂ^σ` implies analytic).

This is the parametric form of the Cauchy integral used for Laurent expansions with holomorphic
parameters (Runge approximation on products of annuli, `SGA.Foundations.Analytic.RungeProduct`).

Reference: Hörmander, *An introduction to complex analysis in several variables*, 2.2 (holomorphy
of integrals depending on parameters); Gunning–Rossi, *Analytic functions of several complex
variables*, I.A.
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

section Param

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Uniform control along a compact set: if `G` is analytic at every point of `{z₀} × K` (`K ⊆ ℂ`
compact), then for `z` near `z₀`, `G` is analytic at every point of `{z} × K`, with a uniform
bound on its derivative there. -/
lemma exists_eventually_analyticAt_of_isCompact {G : E × ℂ → ℂ} {K : Set ℂ} (hK : IsCompact K)
    {z₀ : E} (hG : ∀ ζ ∈ K, AnalyticAt ℂ G (z₀, ζ)) :
    ∃ B : ℝ, ∀ᶠ z in 𝓝 z₀, ∀ ζ ∈ K, AnalyticAt ℂ G (z, ζ) ∧ ‖fderiv ℂ G (z, ζ)‖ < B := by
  have hcont : ContinuousOn (fun ζ ↦ fderiv ℂ G (z₀, ζ)) K := fun ζ hζ ↦
    ((hG ζ hζ).fderiv.continuousAt.comp
      (by fun_prop : Continuous fun ζ : ℂ ↦ (z₀, ζ)).continuousAt).continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hcont
  refine ⟨B + 1, hK.eventually_forall_of_forall_eventually fun ζ hζ ↦ ?_⟩
  have h1 : ∀ᶠ p in 𝓝 (z₀, ζ), AnalyticAt ℂ G p :=
    (isOpen_analyticAt ℂ G).mem_nhds (hG ζ hζ)
  have h2 : ∀ᶠ p in 𝓝 (z₀, ζ), ‖fderiv ℂ G p‖ < B + 1 :=
    (hG ζ hζ).fderiv.continuousAt.norm.eventually (gt_mem_nhds (by linarith [hB ζ hζ]))
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- **Differentiation under the integral along a path**: let `γ : ℝ → ℂ` be continuous with values
in a compact set `K`, `φ : ℝ → ℂ` continuous, and `G` jointly analytic at every point of
`{z₀} × K`. Then `z ↦ ∫_a^b φ(t) G(z, γ(t)) dt` has the derivative
`∫_a^b φ(t) ∂_z G(z₀, γ(t)) dt` at `z₀`. -/
theorem hasFDerivAt_intervalIntegral_param {G : E → ℂ → ℂ} {γ : ℝ → ℂ} (hγ : Continuous γ)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) (hγK : ∀ t, γ t ∈ K)
    (a b : ℝ) {z₀ : E} (hG : ∀ ζ ∈ K, AnalyticAt ℂ (fun p : E × ℂ ↦ G p.1 p.2) (z₀, ζ)) :
    HasFDerivAt (fun z ↦ ∫ t in a..b, φ t • G z (γ t))
      (∫ t in a..b, φ t •
        (fderiv ℂ (fun p : E × ℂ ↦ G p.1 p.2) (z₀, γ t)).comp
          (ContinuousLinearMap.inl ℂ E ℂ)) z₀ := by
  set G' : E × ℂ → ℂ := fun p ↦ G p.1 p.2 with hG'
  obtain ⟨B, hB⟩ := exists_eventually_analyticAt_of_isCompact hK hG
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hB
  have hcontG : ∀ z ∈ ball z₀ ε, Continuous fun t ↦ G z (γ t) := fun z hz ↦
    continuous_iff_continuousAt.mpr fun t ↦
      (hball z hz _ (hγK t)).1.continuousAt.comp (f := fun t ↦ (z, γ t))
        (by fun_prop : Continuous fun t ↦ (z, γ t)).continuousAt
  have hF'cont : Continuous fun t ↦ φ t •
      (fderiv ℂ G' (z₀, γ t)).comp (ContinuousLinearMap.inl ℂ E ℂ) := by
    have h1 : Continuous fun t ↦ fderiv ℂ G' (z₀, γ t) :=
      continuous_iff_continuousAt.mpr fun t ↦
        (hball z₀ (mem_ball_self hε) _ (hγK t)).1.fderiv.continuousAt.comp
          (f := fun t ↦ (z₀, γ t))
          (by fun_prop : Continuous fun t ↦ (z₀, γ t)).continuousAt
    exact hφ.smul (h1.clm_comp continuous_const)
  exact intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℂ) (μ := volume)
    (F := fun z t ↦ φ t • G z (γ t))
    (F' := fun z t ↦ φ t • (fderiv ℂ G' (z, γ t)).comp (ContinuousLinearMap.inl ℂ E ℂ))
    (bound := fun t ↦ ‖φ t‖ * B) (ball_mem_nhds z₀ hε)
    (by
      filter_upwards [ball_mem_nhds z₀ hε] with z hz
      exact (hφ.smul (hcontG z hz)).aestronglyMeasurable)
    ((hφ.smul (hcontG z₀ (mem_ball_self hε))).intervalIntegrable _ _)
    hF'cont.aestronglyMeasurable
    (Eventually.of_forall fun t _ z hz ↦ by
      have h1 : ‖(fderiv ℂ G' (z, γ t)).comp (ContinuousLinearMap.inl ℂ E ℂ)‖ ≤ B :=
        calc _ ≤ ‖fderiv ℂ G' (z, γ t)‖ * ‖ContinuousLinearMap.inl ℂ E ℂ‖ :=
              ContinuousLinearMap.opNorm_comp_le _ _
          _ ≤ B * 1 := mul_le_mul (hball z hz _ (hγK t)).2.le
              (ContinuousLinearMap.norm_inl_le_one ℂ E ℂ) (norm_nonneg _)
              ((norm_nonneg _).trans (hball z hz _ (hγK t)).2.le)
          _ = B := mul_one B
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _))
    ((hφ.norm.mul continuous_const).intervalIntegrable _ _)
    (Eventually.of_forall fun t _ z hz ↦ by
      have hd : HasFDerivAt G' (fderiv ℂ G' (z, γ t)) (z, γ t) :=
        (hball z hz _ (hγK t)).1.differentiableAt.hasFDerivAt
      exact (hd.comp z (hasFDerivAt_prodMk_left (𝕜 := ℂ) z (γ t))).const_smul (φ t))

/-- **Differentiation under the circle integral**: if `G` is jointly analytic at every point of
`{z₀} × S(c, |R|)`, then `z ↦ ∮_{C(c, R)} G(z, ζ) dζ` has the derivative
`∮_{C(c, R)} ∂_z G(z₀, ζ) dζ` at `z₀`. -/
theorem hasFDerivAt_circleIntegral_param {G : E → ℂ → ℂ} {c : ℂ} {R : ℝ} {z₀ : E}
    (hG : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ (fun p : E × ℂ ↦ G p.1 p.2) (z₀, ζ)) :
    HasFDerivAt (fun z ↦ ∮ ζ in C(c, R), G z ζ)
      (∫ θ in (0)..2 * π, deriv (circleMap c R) θ •
        (fderiv ℂ (fun p : E × ℂ ↦ G p.1 p.2) (z₀, circleMap c R θ)).comp
          (ContinuousLinearMap.inl ℂ E ℂ)) z₀ := by
  have hderiv : Continuous (deriv (circleMap c R)) := by
    rw [show deriv (circleMap c R) = fun θ ↦ circleMap 0 R θ * I from
      funext (deriv_circleMap c R)]
    fun_prop
  exact hasFDerivAt_intervalIntegral_param (continuous_circleMap c R) hderiv
    (isCompact_sphere c |R|) (circleMap_mem_sphere' c R) 0 (2 * π) hG

/-- Under the hypotheses of `hasFDerivAt_circleIntegral_param`, the circle integral is complex
differentiable at `z₀`. -/
theorem differentiableAt_circleIntegral_param {G : E → ℂ → ℂ} {c : ℂ} {R : ℝ} {z₀ : E}
    (hG : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ (fun p : E × ℂ ↦ G p.1 p.2) (z₀, ζ)) :
    DifferentiableAt ℂ (fun z ↦ ∮ ζ in C(c, R), G z ζ) z₀ :=
  (hasFDerivAt_circleIntegral_param hG).differentiableAt

end Param

section Analytic

variable {σ : Type*} [Fintype σ]

/-- **Integrals along paths of holomorphic functions with holomorphic parameters are
holomorphic**: let `γ : ℝ → ℂ` be continuous with values in a compact set `K`, `φ : ℝ → ℂ`
continuous, and `G : ℂ^σ → ℂ → ℂ` jointly analytic at every point of `{z₀} × K`. Then
`z ↦ ∫_a^b φ(t) G(z, γ(t)) dt` is analytic at `z₀`. -/
theorem analyticAt_intervalIntegral_param {G : (σ → ℂ) → ℂ → ℂ} {γ : ℝ → ℂ} (hγ : Continuous γ)
    {φ : ℝ → ℂ} (hφ : Continuous φ) {K : Set ℂ} (hK : IsCompact K) (hγK : ∀ t, γ t ∈ K)
    (a b : ℝ) {z₀ : σ → ℂ}
    (hG : ∀ ζ ∈ K, AnalyticAt ℂ (fun p : (σ → ℂ) × ℂ ↦ G p.1 p.2) (z₀, ζ)) :
    AnalyticAt ℂ (fun z ↦ ∫ t in a..b, φ t • G z (γ t)) z₀ := by
  set U : Set (σ → ℂ) :=
    {z | ∀ ζ ∈ K, AnalyticAt ℂ (fun p : (σ → ℂ) × ℂ ↦ G p.1 p.2) (z, ζ)}
  have hU : IsOpen U := isOpen_iff_mem_nhds.mpr fun z hz ↦ by
    obtain ⟨B, hB⟩ := exists_eventually_analyticAt_of_isCompact hK hz
    filter_upwards [hB] with y hy ζ hζ using (hy ζ hζ).1
  exact analyticAt_of_differentiableOn hU
    (fun z hz ↦ (hasFDerivAt_intervalIntegral_param hγ hφ hK hγK a b hz).differentiableAt
      |>.differentiableWithinAt) hG

/-- **Circle integrals of holomorphic functions with holomorphic parameters are holomorphic**:
if `G : ℂ^σ → ℂ → ℂ` is jointly analytic at every point of `{z₀} × S(c, |R|)`, then
`z ↦ ∮_{C(c, R)} G(z, ζ) dζ` is analytic at `z₀`. -/
theorem analyticAt_circleIntegral_param {G : (σ → ℂ) → ℂ → ℂ} {c : ℂ} {R : ℝ} {z₀ : σ → ℂ}
    (hG : ∀ ζ ∈ sphere c |R|, AnalyticAt ℂ (fun p : (σ → ℂ) × ℂ ↦ G p.1 p.2) (z₀, ζ)) :
    AnalyticAt ℂ (fun z ↦ ∮ ζ in C(c, R), G z ζ) z₀ := by
  have hderiv : Continuous (deriv (circleMap c R)) := by
    rw [show deriv (circleMap c R) = fun θ ↦ circleMap 0 R θ * I from
      funext (deriv_circleMap c R)]
    fun_prop
  exact analyticAt_intervalIntegral_param (continuous_circleMap c R) hderiv
    (isCompact_sphere c |R|) (circleMap_mem_sphere' c R) 0 (2 * π) hG

end Analytic

/-! ### Updating one coordinate -/

section Update

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-- `(z, ζ) ↦ z₍ⱼ←ζ₎` is analytic. -/
lemma analyticAt_update_prod (j : σ) (p : (σ → ℂ) × ℂ) :
    AnalyticAt ℂ (fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2) p := by
  refine analyticAt_pi_iff.mpr fun i ↦ ?_
  by_cases hij : i = j
  · subst hij
    simpa using analyticAt_snd
  · simp only [Function.update_of_ne hij]
    exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) i).analyticAt _).comp
      analyticAt_fst

/-- `ζ ↦ z₍ⱼ←ζ₎` is analytic. -/
lemma analyticAt_update_right (z : σ → ℂ) (j : σ) (ζ : ℂ) :
    AnalyticAt ℂ (fun ζ ↦ Function.update z j ζ) ζ :=
  (analyticAt_update_prod j (z, ζ)).comp (analyticAt_const.prod analyticAt_id)

end Update

end AnalyticGeometry
