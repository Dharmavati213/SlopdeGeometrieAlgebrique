/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultParam
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Sup-norm bounds for the Cauchy transform

Let `g : ℂ → ℂ` vanish outside a closed disc `D̄(c, ρ)` and satisfy `|g| ≤ M`. Then its Cauchy
transform `(T g)(z) = (1/π) ∫ g(t) / (z - t) dA(t)` satisfies `|T g(z)| ≤ C(ρ) M` for every
`z ∈ ℂ`, with `C(ρ) = ∫_{|t| < ρ} |π t|⁻¹ dA(t) + ρ` (`AnalyticGeometry.cauchyTransformBound`,
a finite constant depending only on `ρ`; its value, `3ρ`, is not computed here). Split the
integral into the part over the disc `|t - z| < ρ` (bounded by `∫_{|t| < ρ} |π t|⁻¹ dA(t)`
after translation) and the rest, where `|z - t| ≥ ρ` (bounded by `area(D̄(c, ρ)) / (πρ) = ρ`).
The bound is uniform in the parameters for the Cauchy transform in one variable with the others
as parameters (`AnalyticGeometry.norm_cauchyTransformIn_le`).

This is the quantitative input of the additive Cousin problem with bounds (the additive half of
Cartan's matrix lemma). Reference: Hörmander, *An introduction to complex analysis in several
variables*, Theorem 1.2.2 and its proof; Gunning–Rossi, *Analytic functions of several complex
variables*, I.D.
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

/-- The constant `C(ρ) = ∫_{|t| < ρ} |π t|⁻¹ dA(t) + ρ` of the sup-norm bound for Cauchy
transforms of functions supported in a closed disc of radius `ρ`. -/
def cauchyTransformBound (ρ : ℝ) : ℝ := (∫ t in ball (0 : ℂ) ρ, ‖cauchyKernel t‖) + ρ

lemma integrableOn_norm_cauchyKernel_ball (ρ : ℝ) :
    IntegrableOn (fun t ↦ ‖cauchyKernel t‖) (ball (0 : ℂ) ρ) :=
  ((locallyIntegrable_cauchyKernel.integrableOn_isCompact (isCompact_closedBall 0 ρ)).mono_set
    ball_subset_closedBall).norm

lemma cauchyTransformBound_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) : 0 ≤ cauchyTransformBound ρ :=
  add_nonneg (setIntegral_nonneg measurableSet_ball fun _ _ ↦ norm_nonneg _) hρ

/-- **Sup-norm bound for the Cauchy transform**: if `g` vanishes outside the closed disc
`D̄(c, ρ)` (`ρ > 0`) and `‖g‖ ≤ M`, then `‖T g(z)‖ ≤ cauchyTransformBound ρ * M` for every `z`. -/
theorem norm_cauchyTransform_le {g : ℂ → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    (hg0 : ∀ t ∉ closedBall c ρ, g t = 0) (hgM : ∀ t, ‖g t‖ ≤ M) (z : ℂ) :
    ‖cauchyTransform g z‖ ≤ cauchyTransformBound ρ * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  set F₁ : ℂ → ℝ := fun t ↦ (ball (0 : ℂ) ρ).indicator (fun s ↦ ‖cauchyKernel s‖) (z - t)
    with hF₁
  set F₂ : ℂ → ℝ := (closedBall c ρ).indicator fun _ ↦ (π * ρ)⁻¹ with hF₂
  have hF₁int : Integrable F₁ :=
    ((integrable_indicator_iff measurableSet_ball).mpr
      (integrableOn_norm_cauchyKernel_ball ρ)).comp_sub_left z
  have hF₂int : Integrable F₂ :=
    (integrable_indicator_iff measurableSet_closedBall).mpr
      (integrableOn_const (measure_closedBall_lt_top).ne)
  -- the pointwise bound
  have hpt : ∀ t, ‖g t * cauchyKernel (z - t)‖ ≤ M * (F₁ t + F₂ t) := fun t ↦ by
    have hF₁0 : 0 ≤ F₁ t := indicator_nonneg (fun _ _ ↦ norm_nonneg _) _
    have hF₂0 : 0 ≤ F₂ t := indicator_nonneg (fun _ _ ↦ by positivity) _
    by_cases htc : t ∈ closedBall c ρ
    · rw [norm_mul]
      refine mul_le_mul (hgM t) ?_ (norm_nonneg _) hM
      by_cases htz : z - t ∈ ball (0 : ℂ) ρ
      · have : F₁ t = ‖cauchyKernel (z - t)‖ := by simp only [hF₁, indicator_of_mem htz]
        linarith
      · have hd : ρ ≤ ‖z - t‖ := by simpa using htz
        have : ‖cauchyKernel (z - t)‖ ≤ (π * ρ)⁻¹ := by
          rw [cauchyKernel, norm_inv, norm_mul, norm_real, Real.norm_eq_abs,
            abs_of_pos Real.pi_pos]
          exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hd Real.pi_pos.le)
        have h2 : F₂ t = (π * ρ)⁻¹ := by simp only [hF₂, indicator_of_mem htc]
        linarith
    · rw [hg0 t htc, zero_mul, norm_zero]
      positivity
  calc ‖cauchyTransform g z‖ = ‖∫ t, g t * cauchyKernel (z - t)‖ := by
        rw [cauchyTransform_apply]
    _ ≤ ∫ t, ‖g t * cauchyKernel (z - t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, M * (F₁ t + F₂ t) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ norm_nonneg _)
          ((hF₁int.add hF₂int).const_mul M) (Eventually.of_forall hpt)
    _ = M * ((∫ t in ball (0 : ℂ) ρ, ‖cauchyKernel t‖) + (π * ρ ^ 2) * (π * ρ)⁻¹) := by
        rw [integral_const_mul, integral_add hF₁int hF₂int]
        congr 2
        · rw [hF₁, integral_sub_left_eq_self
            (fun s ↦ (ball (0 : ℂ) ρ).indicator (fun s ↦ ‖cauchyKernel s‖) s) volume z,
            integral_indicator measurableSet_ball]
        · rw [hF₂, integral_indicator_const _ measurableSet_closedBall, smul_eq_mul,
            measureReal_def, Complex.volume_closedBall]
          simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hρ.le,
            ENNReal.coe_toReal, NNReal.coe_real_pi]
          ring
    _ = cauchyTransformBound ρ * M := by
        rw [cauchyTransformBound]
        have : (π * ρ ^ 2) * (π * ρ)⁻¹ = ρ := by
          field_simp
        rw [this]
        ring

variable {σ : Type} [DecidableEq σ]

/-- **Sup-norm bound for the Cauchy transform with parameters**: if `t ↦ h(z₍ₘ←t₎)` vanishes
outside the closed disc `D̄(c, ρ)` (`ρ > 0`) and is bounded by `M`, then
`‖Tₘh(z)‖ ≤ cauchyTransformBound ρ * M`. The constant depends only on `ρ`. -/
theorem norm_cauchyTransformIn_le {m : σ} {h : (σ → ℂ) → ℂ} {c : ℂ} {ρ M : ℝ} (hρ : 0 < ρ)
    {z : σ → ℂ} (h0 : ∀ t ∉ closedBall c ρ, h (Function.update z m t) = 0)
    (hM : ∀ t, ‖h (Function.update z m t)‖ ≤ M) :
    ‖cauchyTransformIn m h z‖ ≤ cauchyTransformBound ρ * M :=
  norm_cauchyTransform_le hρ h0 hM (z m)

end AnalyticGeometry
