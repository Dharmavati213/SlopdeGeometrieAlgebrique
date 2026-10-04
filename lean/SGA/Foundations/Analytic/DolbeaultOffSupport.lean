/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultBound
import SGA.Foundations.Analytic.Osgood
import Mathlib.Analysis.Complex.Liouville

/-!
# The Cauchy transform is holomorphic off the support

Let `g : ℂ → ℂ` be integrable. Its Cauchy transform `(T g)(z) = (1/π) ∫ g(t) / (z - t) dA(t)` is
complex differentiable at every point `z₀` near which `g` vanishes almost everywhere, with
derivative `-(1/π) ∫ g(t) / (z₀ - t)² dA(t)`
(`AnalyticGeometry.hasDerivAt_cauchyTransform_of_ae_eq_zero`); so `T g` is holomorphic on every
open set on which `g = 0` a.e. (`AnalyticGeometry.differentiableOn_cauchyTransform_of_ae_eq_zero`).
No smoothness of `g` is needed: differentiate under the integral sign, the kernel being
holomorphic and bounded together with its derivative away from the support.

With parameters (`AnalyticGeometry.OffSupportData`): let `h : ℂ^σ → ℂ` and `U ⊆ ℂ^σ` open such
that, for `z ∈ U`, the function `t ↦ h(z₍ₘ←t₎)` is measurable, bounded by a constant `M`,
vanishes for `t` outside a fixed compact set `k` and for `|t - zₘ| < r` (a fixed `r > 0`), and
`z ↦ h(z₍ₘ←t₎)` is complex differentiable on `U` for every `t`. Then the Cauchy transform in the
variable `zₘ`, `Tₘh(z) = (1/π) ∫ h(z₍ₘ←t₎) / (zₘ - t) dA(t)`, is analytic on `U`
(`AnalyticGeometry.OffSupportData.analyticAt_cauchyTransformIn`): it is continuous (dominated
convergence), holomorphic in `zₘ` (the one-variable result) and in each other variable
(differentiation under the integral sign, with Cauchy's estimate for the derivative of the
integrand), hence analytic by Osgood's lemma
(`AnalyticGeometry.analyticAt_of_continuousOn_of_separately`).

These are the inputs (T2'), (T3') of the additive Cousin problem with bounds on adjacent boxes,
where the integrand `h ∂χ/∂z̄ₘ · 1_strip` is not smooth along the horizontal edges of the strip.

Reference: Hörmander, *An introduction to complex analysis in several variables*, Theorem 1.2.2
and its proof (the Cauchy transform of a compactly supported function is holomorphic off its
support); Gunning–Rossi, *Analytic functions of several complex variables*, I.D.
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

/-! ### One variable -/

lemma measurable_cauchyKernel : Measurable cauchyKernel :=
  (measurable_const.mul measurable_id).inv

/-- The Cauchy kernel is bounded by `(π r)⁻¹` at distance `≥ r` from `0`. -/
lemma norm_cauchyKernel_le {w : ℂ} {r : ℝ} (hr : 0 < r) (hw : r ≤ ‖w‖) :
    ‖cauchyKernel w‖ ≤ (π * r)⁻¹ := by
  rw [cauchyKernel, norm_inv, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hw Real.pi_pos.le)

/-- A measurable function bounded by `M` and vanishing outside a compact set is integrable. -/
lemma integrable_of_norm_le_of_eq_zero {g : ℂ → ℂ} {k : Set ℂ} (hk : IsCompact k)
    (hg : AEStronglyMeasurable g volume) {M : ℝ} (hM : ∀ t, ‖g t‖ ≤ M)
    (h0 : ∀ t ∉ k, g t = 0) : Integrable g := by
  have hb : Integrable (k.indicator fun _ : ℂ ↦ M) volume :=
    (integrable_indicator_iff hk.measurableSet).mpr (integrableOn_const hk.measure_lt_top.ne)
  refine hb.mono' hg (Eventually.of_forall fun t ↦ ?_)
  by_cases ht : t ∈ k
  · simpa [indicator_of_mem ht] using hM t
  · simp [indicator_of_notMem ht, h0 t ht]

/-- **The Cauchy transform is holomorphic off the support** (pointwise form): if `g` is
integrable and vanishes on the disc `B(z₀, r)`, `r > 0`, then `T g` has complex derivative
`-(1/π) ∫ g(t) / (z₀ - t)² dA(t)` at `z₀`. -/
theorem hasDerivAt_cauchyTransform_of_eq_zero {g : ℂ → ℂ} (hg : Integrable g) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (h0 : ∀ t ∈ ball z₀ r, g t = 0) :
    HasDerivAt (cauchyTransform g) (∫ t, g t * -((π : ℂ) * (z₀ - t) ^ 2)⁻¹) z₀ := by
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  -- at distance `≥ r / 2` from `z`
  have hfar : ∀ t, g t ≠ 0 → ∀ z ∈ ball z₀ (r / 2), r / 2 ≤ ‖z - t‖ := by
    intro t ht z hz
    have htr : r ≤ dist t z₀ := not_lt.mp fun h ↦ ht (h0 t (mem_ball.mpr h))
    have hz' : dist z z₀ < r / 2 := hz
    have h1 := dist_triangle t z z₀
    have h2 : dist t z = ‖z - t‖ := by rw [dist_comm, dist_eq_norm]
    linarith
  have hmeas : ∀ z, AEStronglyMeasurable (fun t ↦ g t * cauchyKernel (z - t)) volume := fun z ↦
    hg.aestronglyMeasurable.mul
      (measurable_cauchyKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun t ↦ g t * -((π : ℂ) * (z₀ - t) ^ 2)⁻¹) volume :=
    hg.aestronglyMeasurable.mul (((measurable_const.mul
      ((measurable_const.sub measurable_id).pow_const 2)).inv).neg).aestronglyMeasurable
  have hdiff : ∀ t, ∀ z ∈ ball z₀ (r / 2), HasDerivAt (fun z ↦ g t * cauchyKernel (z - t))
      (g t * -((π : ℂ) * (z - t) ^ 2)⁻¹) z := by
    intro t z hz
    by_cases ht : g t = 0
    · simp only [ht, zero_mul]
      exact hasDerivAt_const z 0
    · have hne : (π : ℂ) * (z - t) ≠ 0 := mul_ne_zero hπ fun h ↦ by
        have := hfar t ht z hz
        rw [h, norm_zero] at this
        linarith
      have hd : HasDerivAt (fun z ↦ (π : ℂ) * (z - t)) (π * 1) z :=
        ((hasDerivAt_id z).sub_const t).const_mul _
      refine (hd.inv hne).const_mul (g t) |>.congr_deriv ?_
      have hzt : z - t ≠ 0 := right_ne_zero_of_mul hne
      field_simp
  have hbound : ∀ t, ∀ z ∈ ball z₀ (r / 2),
      ‖g t * -((π : ℂ) * (z - t) ^ 2)⁻¹‖ ≤ ‖g t‖ * (π * (r / 2) ^ 2)⁻¹ := by
    intro t z hz
    by_cases ht : g t = 0
    · simp [ht]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      rw [norm_neg, norm_inv, norm_mul, norm_pow, norm_real, Real.norm_eq_abs,
        abs_of_pos Real.pi_pos]
      exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (hfar t ht z hz) 2) Real.pi_pos.le)
  have hint : Integrable (fun t ↦ g t * cauchyKernel (z₀ - t)) volume := by
    refine (hg.norm.mul_const (π * r)⁻¹).mono' (hmeas z₀) (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : g t = 0
    · simp [ht]
    · rw [norm_mul]
      refine mul_le_mul_of_nonneg_left (norm_cauchyKernel_le hr ?_) (norm_nonneg _)
      have : r ≤ dist t z₀ := not_lt.mp fun h ↦ ht (h0 t (mem_ball.mpr h))
      rwa [dist_eq_norm, ← norm_neg, neg_sub] at this
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun z t ↦ g t * cauchyKernel (z - t))
    (F' := fun z t ↦ g t * -((π : ℂ) * (z - t) ^ 2)⁻¹) (x₀ := z₀)
    (ball_mem_nhds z₀ (by positivity : 0 < r / 2)) (Eventually.of_forall hmeas) hint hmeas'
    (Eventually.of_forall hbound) (hg.norm.mul_const _) (Eventually.of_forall hdiff)
  exact key.2

/-- **The Cauchy transform is holomorphic off the support**: if `g` is integrable and vanishes
almost everywhere on the disc `B(z₀, r)`, `r > 0`, then `T g` has complex derivative
`-(1/π) ∫ g(t) / (z₀ - t)² dA(t)` at `z₀`. -/
theorem hasDerivAt_cauchyTransform_of_ae_eq_zero {g : ℂ → ℂ} (hg : Integrable g) {z₀ : ℂ}
    {r : ℝ} (hr : 0 < r) (h0 : ∀ᵐ t, t ∈ ball z₀ r → g t = 0) :
    HasDerivAt (cauchyTransform g) (∫ t, g t * -((π : ℂ) * (z₀ - t) ^ 2)⁻¹) z₀ := by
  set g' : ℂ → ℂ := (ball z₀ r)ᶜ.indicator g
  have hgg' : g =ᵐ[volume] g' := by
    filter_upwards [h0] with t ht
    change g t = (ball z₀ r)ᶜ.indicator g t
    by_cases htb : t ∈ ball z₀ r
    · rw [ht htb, indicator_of_notMem (notMem_compl_iff.mpr htb)]
    · rw [indicator_of_mem (mem_compl htb)]
  have hT : cauchyTransform g = cauchyTransform g' := by
    funext z
    simp only [cauchyTransform_apply]
    exact integral_congr_ae (hgg'.mul EventuallyEq.rfl)
  have hI : ∫ t, g t * -((π : ℂ) * (z₀ - t) ^ 2)⁻¹ = ∫ t, g' t * -((π : ℂ) * (z₀ - t) ^ 2)⁻¹ :=
    integral_congr_ae (hgg'.mul EventuallyEq.rfl)
  rw [hT, hI]
  exact hasDerivAt_cauchyTransform_of_eq_zero ((integrable_congr hgg').mp hg) hr
    fun t ht ↦ indicator_of_notMem (notMem_compl_iff.mpr ht) g

theorem differentiableAt_cauchyTransform_of_ae_eq_zero {g : ℂ → ℂ} (hg : Integrable g) {z₀ : ℂ}
    {r : ℝ} (hr : 0 < r) (h0 : ∀ᵐ t, t ∈ ball z₀ r → g t = 0) :
    DifferentiableAt ℂ (cauchyTransform g) z₀ :=
  (hasDerivAt_cauchyTransform_of_ae_eq_zero hg hr h0).differentiableAt

/-- **The Cauchy transform is holomorphic off the support**: if `g` is integrable and vanishes
almost everywhere on the open set `U`, then `T g` is holomorphic on `U`. -/
theorem differentiableOn_cauchyTransform_of_ae_eq_zero {g : ℂ → ℂ} (hg : Integrable g)
    {U : Set ℂ} (hU : IsOpen U) (h0 : ∀ᵐ t, t ∈ U → g t = 0) :
    DifferentiableOn ℂ (cauchyTransform g) U := by
  intro z hz
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  refine (differentiableAt_cauchyTransform_of_ae_eq_zero hg hr ?_).differentiableWithinAt
  filter_upwards [h0] with t ht htb using ht (hrU htb)

/-! ### With holomorphic parameters -/

variable {σ : Type} [DecidableEq σ]

/-- The hypotheses for the Cauchy transform in the variable `zₘ` to be analytic on `U`: `U` is
open; for `z ∈ U`, `t ↦ h(z₍ₘ←t₎)` is a.e. strongly measurable, bounded by `M`, vanishes for `t`
outside the compact set `k` and for `|t - zₘ| < r`; and `z ↦ h(z₍ₘ←t₎)` is complex
differentiable at every point of `U`, for every `t`. -/
structure OffSupportData (m : σ) (h : (σ → ℂ) → ℂ) (U : Set (σ → ℂ)) (k : Set ℂ) (r M : ℝ) :
    Prop where
  isOpen : IsOpen U
  isCompact : IsCompact k
  pos : 0 < r
  aestronglyMeasurable : ∀ z ∈ U, AEStronglyMeasurable (fun t ↦ h (Function.update z m t)) volume
  norm_le : ∀ z ∈ U, ∀ t, ‖h (Function.update z m t)‖ ≤ M
  eq_zero_of_notMem : ∀ z ∈ U, ∀ t ∉ k, h (Function.update z m t) = 0
  eq_zero_of_mem_ball : ∀ z ∈ U, ∀ t ∈ ball (z m) r, h (Function.update z m t) = 0
  differentiableAt : ∀ z ∈ U, ∀ t, DifferentiableAt ℂ (fun z ↦ h (Function.update z m t)) z

namespace OffSupportData

variable {m : σ} {h : (σ → ℂ) → ℂ} {U : Set (σ → ℂ)} {k : Set ℂ} {r M : ℝ}
  (H : OffSupportData m h U k r M)
include H

/-- The bound for the integrand: `M (π r)⁻¹` on `k`, `0` outside. -/
private lemma norm_integrand_le {z : σ → ℂ} (hz : z ∈ U) (t : ℂ) :
    ‖h (Function.update z m t) * cauchyKernel (z m - t)‖ ≤
      k.indicator (fun _ ↦ M * (π * r)⁻¹) t := by
  by_cases htk : t ∈ k
  · rw [indicator_of_mem htk, norm_mul]
    by_cases htb : t ∈ ball (z m) r
    · rw [H.eq_zero_of_mem_ball z hz t htb, norm_zero, zero_mul]
      have hM : 0 ≤ M := (norm_nonneg _).trans (H.norm_le z hz t)
      have := H.pos
      positivity
    · refine mul_le_mul (H.norm_le z hz t) (norm_cauchyKernel_le H.pos ?_) (norm_nonneg _)
        ((norm_nonneg _).trans (H.norm_le z hz t))
      rw [mem_ball, dist_eq_norm, not_lt] at htb
      rwa [← norm_neg, neg_sub]
  · rw [indicator_of_notMem htk, H.eq_zero_of_notMem z hz t htk, zero_mul, norm_zero]

private lemma integrable_bound : Integrable (k.indicator fun _ : ℂ ↦ M * (π * r)⁻¹) volume :=
  (integrable_indicator_iff H.isCompact.measurableSet).mpr
    (integrableOn_const H.isCompact.measure_lt_top.ne)

private lemma aestronglyMeasurable_integrand {z : σ → ℂ} (hz : z ∈ U) (w : ℂ) :
    AEStronglyMeasurable (fun t ↦ h (Function.update z m t) * cauchyKernel (w - t)) volume :=
  (H.aestronglyMeasurable z hz).mul
    (measurable_cauchyKernel.comp (measurable_const.sub measurable_id)).aestronglyMeasurable

lemma integrable_slice {z : σ → ℂ} (hz : z ∈ U) : Integrable fun t ↦ h (Function.update z m t) :=
  integrable_of_norm_le_of_eq_zero H.isCompact (H.aestronglyMeasurable z hz) (H.norm_le z hz)
    (H.eq_zero_of_notMem z hz)

/-- The Cauchy transform in `zₘ` is continuous on `U`. -/
theorem continuousOn_cauchyTransformIn [Finite σ] : ContinuousOn (cauchyTransformIn m h) U := by
  have := Fintype.ofFinite σ
  intro z₀ hz₀
  refine ContinuousAt.continuousWithinAt ?_
  have hU : ∀ᶠ z in 𝓝 z₀, z ∈ U := H.isOpen.mem_nhds hz₀
  have hcont : ∀ᵐ t, ContinuousAt (fun z ↦ h (Function.update z m t) * cauchyKernel (z m - t))
      z₀ := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (z₀ m))] with t ht
    have hne : z₀ m - t ≠ 0 := sub_ne_zero.mpr fun h ↦ ht (h ▸ rfl)
    have hπ : (π : ℂ) * (z₀ m - t) ≠ 0 :=
      mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hne
    refine (H.differentiableAt z₀ hz₀ t).continuousAt.mul ?_
    exact (continuousAt_const.mul ((continuous_apply m).continuousAt.sub
      continuousAt_const)).inv₀ hπ
  have := continuousAt_of_dominated (μ := volume)
    (F := fun z t ↦ h (Function.update z m t) * cauchyKernel (z m - t))
    (hU.mono fun z hz ↦ H.aestronglyMeasurable_integrand hz (z m))
    (hU.mono fun z hz ↦ Eventually.of_forall (H.norm_integrand_le hz)) H.integrable_bound hcont
  exact this

/-- The Cauchy transform in `zₘ` is holomorphic in `zₘ` on `U`. -/
theorem differentiableAt_cauchyTransformIn_update_self {z : σ → ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ (fun t ↦ cauchyTransformIn m h (Function.update z m t)) (z m) := by
  simp_rw [cauchyTransformIn_update]
  exact differentiableAt_cauchyTransform_of_ae_eq_zero (H.integrable_slice hz) H.pos
    (Eventually.of_forall fun t ht ↦ H.eq_zero_of_mem_ball z hz t ht)

/-- The Cauchy transform in `zₘ` is holomorphic in every other variable `zⱼ` on `U`
(differentiation under the integral sign). -/
theorem differentiableAt_cauchyTransformIn_update_of_ne [Finite σ] {j : σ} (hjm : j ≠ m)
    {z : σ → ℂ} (hz : z ∈ U) :
    DifferentiableAt ℂ (fun l ↦ cauchyTransformIn m h (Function.update z j l)) (z j) := by
  have := Fintype.ofFinite σ
  -- a disc of radius `3ε` around `zⱼ` along the `j`-th coordinate line stays in `U`
  obtain ⟨ε₀, hε₀, hε₀U⟩ := Metric.isOpen_iff.mp H.isOpen z hz
  set ε := ε₀ / 3 with hε
  have hεpos : 0 < ε := by positivity
  have hmemU : ∀ l ∈ ball (z j) (3 * ε), Function.update z j l ∈ U := by
    intro l hl
    refine hε₀U ?_
    rw [mem_ball, dist_pi_lt_iff hε₀]
    intro i
    by_cases hi : i = j
    · subst hi
      simp only [Function.update_self]
      have : dist l (z i) < 3 * ε := hl
      rw [hε] at this
      linarith
    · rw [Function.update_of_ne hi, dist_self]
      exact hε₀
  -- the integrand as a function of the `j`-th coordinate
  set φ : ℂ → ℂ → ℂ := fun t l ↦ h (Function.update (Function.update z j l) m t) with hφ
  have hupd : ∀ l, (Function.update z j l) m = z m := fun l ↦ Function.update_of_ne hjm.symm _ _
  have hφdiff : ∀ t, ∀ l ∈ ball (z j) (3 * ε), DifferentiableAt ℂ (φ t) l := by
    intro t l hl
    have h1 := H.differentiableAt _ (hmemU l hl) t
    have h2 : DifferentiableAt ℂ (fun l' : ℂ ↦ Function.update z j l') l :=
      (hasFDerivAt_update z l).differentiableAt
    exact h1.comp l h2
  have hφzero : ∀ t, (t ∉ k ∨ t ∈ ball (z m) r) → ∀ l ∈ ball (z j) (3 * ε), φ t l = 0 := by
    intro t ht l hl
    rcases ht with ht | ht
    · exact H.eq_zero_of_notMem _ (hmemU l hl) t ht
    · exact H.eq_zero_of_mem_ball _ (hmemU l hl) t (by rwa [hupd])
  -- Cauchy's estimate for the derivative of the integrand
  have hφderiv : ∀ t, ∀ l ∈ ball (z j) ε, ‖deriv (φ t) l‖ ≤ M / ε := by
    intro t l hl
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hεpos ?_ fun w hw ↦ ?_
    · refine DifferentiableOn.diffContOnCl_ball (U := ball (z j) (3 * ε)) ?_ ?_
      · exact fun w hw ↦ (hφdiff t w hw).differentiableWithinAt
      · refine closedBall_subset_ball' ?_
        have : dist l (z j) < ε := hl
        linarith
    · have hw' : w ∈ ball (z j) (3 * ε) := by
        have : dist w l = ε := hw
        have : dist l (z j) < ε := hl
        rw [mem_ball]
        linarith [dist_triangle w l (z j)]
      exact H.norm_le _ (hmemU w hw') t
  have hφderiv0 : ∀ t, (t ∉ k ∨ t ∈ ball (z m) r) → ∀ l ∈ ball (z j) ε, deriv (φ t) l = 0 := by
    intro t ht l hl
    have hl3 : ball l (2 * ε) ⊆ ball (z j) (3 * ε) := by
      refine ball_subset_ball' ?_
      have : dist l (z j) < ε := hl
      linarith
    have : φ t =ᶠ[𝓝 l] fun _ ↦ 0 := by
      filter_upwards [ball_mem_nhds l (by positivity : 0 < 2 * ε)] with w hw
      exact hφzero t ht w (hl3 hw)
    rw [this.deriv_eq, deriv_const]
  -- rewrite the function as a parametric integral
  have hfun : (fun l ↦ cauchyTransformIn m h (Function.update z j l)) =
      fun l ↦ ∫ t, φ t l * cauchyKernel (z m - t) := by
    funext l
    simp only [cauchyTransformIn, cauchyTransform_apply, hupd, hφ]
  rw [hfun]
  set bound : ℂ → ℝ := k.indicator fun _ ↦ M / ε * (π * r)⁻¹
  have hM : 0 ≤ M := (norm_nonneg _).trans (H.norm_le z hz 0)
  have hbound : ∀ t, ∀ l ∈ ball (z j) ε, ‖deriv (φ t) l * cauchyKernel (z m - t)‖ ≤ bound t := by
    intro t l hl
    by_cases ht : t ∉ k ∨ t ∈ ball (z m) r
    · rw [hφderiv0 t ht l hl, zero_mul, norm_zero]
      simp only [bound]
      exact indicator_nonneg (fun _ _ ↦ by have := H.pos; positivity) _
    · push Not at ht
      simp only [bound]
      rw [indicator_of_mem ht.1, norm_mul]
      refine mul_le_mul (hφderiv t l hl) (norm_cauchyKernel_le H.pos ?_) (norm_nonneg _)
        (by positivity)
      have := ht.2
      rw [mem_ball, dist_eq_norm, not_lt] at this
      rwa [← norm_neg, neg_sub]
  have hbound_int : Integrable bound volume :=
    (integrable_indicator_iff H.isCompact.measurableSet).mpr
      (integrableOn_const H.isCompact.measure_lt_top.ne)
  -- measurability of the derivative, as a limit of difference quotients
  have hslope_meas : AEStronglyMeasurable (fun t ↦ deriv (φ t) (z j)) volume := by
    set δ : ℕ → ℂ := fun n ↦ ((ε / (n + 1) : ℝ) : ℂ)
    have hδ0 : ∀ n, δ n ≠ 0 := fun n ↦ ofReal_ne_zero.mpr (by positivity)
    have hδ : Tendsto (fun n ↦ z j + δ n) atTop (𝓝[≠] (z j)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have : Tendsto δ atTop (𝓝 0) := by
          have := (tendsto_const_div_atTop_nhds_zero_nat ε).comp (tendsto_add_atTop_nat 1)
          have h2 := (continuous_ofReal.tendsto 0).comp this
          simpa [δ, Function.comp_def, Nat.cast_add, Nat.cast_one] using h2
        simpa using tendsto_const_nhds.add this
      · simpa using hδ0 n
    have hδmem : ∀ n, z j + δ n ∈ ball (z j) (3 * ε) := by
      intro n
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity)]
      calc ε / (n + 1) ≤ ε := div_le_self hεpos.le (by linarith [n.cast_nonneg (α := ℝ)])
        _ < 3 * ε := by linarith
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun n t ↦ slope (φ t) (z j) (z j + δ n)) (fun n ↦ ?_)
      (Eventually.of_forall fun t ↦ ?_)
    · simp only [slope_def_module]
      have h1 := H.aestronglyMeasurable _ (hmemU _ (hδmem n))
      have h2 := H.aestronglyMeasurable _ (hmemU (z j) (mem_ball_self (by positivity)))
      exact (h1.sub h2).const_smul ((z j + δ n - z j)⁻¹ : ℂ)
    · have hd := (hφdiff t (z j) (mem_ball_self (by positivity))).hasDerivAt
      exact (hasDerivAt_iff_tendsto_slope.mp hd).comp hδ
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun l t ↦ φ t l * cauchyKernel (z m - t))
    (F' := fun l t ↦ deriv (φ t) l * cauchyKernel (z m - t)) (x₀ := z j)
    (ball_mem_nhds (z j) hεpos)
    (eventually_of_mem (ball_mem_nhds (z j) (by positivity : 0 < 3 * ε)) fun l hl ↦ ?_) ?_
    (hslope_meas.mul (measurable_cauchyKernel.comp
      (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Eventually.of_forall hbound) hbound_int
    (Eventually.of_forall fun t l hl ↦ ?_)
  · exact key.2.differentiableAt
  · have := H.aestronglyMeasurable_integrand (hmemU l hl) (z m)
    simpa [hupd, φ] using this
  · have hzU := hmemU (z j) (mem_ball_self (by positivity))
    have hmeas := H.aestronglyMeasurable_integrand hzU (z m)
    refine Integrable.mono' H.integrable_bound hmeas (Eventually.of_forall fun t ↦ ?_)
    have := H.norm_integrand_le hzU t
    simpa [hupd, φ] using this
  · exact ((hφdiff t l (ball_subset_ball (by linarith) hl)).hasDerivAt).mul_const _

/-- **The Cauchy transform with holomorphic parameters is analytic off the support**: under
`OffSupportData m h U k r M`, `Tₘh` is analytic at every point of `U` (Osgood's lemma). -/
theorem analyticAt_cauchyTransformIn [Fintype σ] {z : σ → ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ (cauchyTransformIn m h) z :=
  analyticAt_of_continuousOn_of_separately H.isOpen H.continuousOn_cauchyTransformIn
    (fun y hy j ↦ by
      by_cases hj : j = m
      · subst hj
        exact H.differentiableAt_cauchyTransformIn_update_self hy
      · exact H.differentiableAt_cauchyTransformIn_update_of_ne hj hy) hz

end OffSupportData

end AnalyticGeometry
