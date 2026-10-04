/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod

/-!
# The `∂̄`-equation in one variable for compactly supported data

For a function `f : ℂ → ℂ` which is differentiable in the real sense, the Wirtinger derivative
`∂f/∂z̄ = (∂f/∂x + i ∂f/∂y) / 2` is `dbar f`. It vanishes exactly where `f` is complex
differentiable (`dbar_eq_zero_iff`).

The main result is the solution of the inhomogeneous Cauchy–Riemann equation `∂u/∂z̄ = g` for
compactly supported `g` (Dolbeault's lemma for compact support): the Cauchy transform
`u = cauchyTransform g`, `u(z) = (1/π) ∫ g(ζ) / (z - ζ) dA(ζ)`, is `Cⁿ` when `g` is `Cⁿ`
(`contDiff_cauchyTransform`) and satisfies `dbar u = g` when `n ≥ 1` (`dbar_cauchyTransform`).
The key input is the generalized Cauchy integral formula for compactly supported `C¹` functions,
`∫ (∂G/∂z̄)(w) / (w - z) dA(w) = -π G(z)` (`integral_dbar_div_sub`), proved in polar coordinates.

References: Forster, *Lectures on Riemann surfaces*, 13.1–13.2; Hörmander, *An introduction to
complex analysis in several variables*, Theorem 1.2.2.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology
open scoped Real Convolution

namespace AnalyticGeometry

/-- The Wirtinger derivative `∂f/∂z̄ = (∂f/∂x + i ∂f/∂y) / 2` of `f : ℂ → ℂ` at `z`, computed
from the real derivative. -/
def dbar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) * (fderiv ℝ f z 1 + I * fderiv ℝ f z I)

variable {f g : ℂ → ℂ} {z : ℂ}

/-- An `ℝ`-linear map `ℂ → ℂ` is determined by its values at `1` and `I`. -/
lemma realLinear_apply_eq (L : ℂ →L[ℝ] ℂ) (w : ℂ) : L w = w.re * L 1 + w.im * L I := by
  have hw : w = w.re • (1 : ℂ) + w.im • I := by simp [real_smul, re_add_im]
  conv_lhs => rw [hw]
  rw [map_add, L.map_smul, L.map_smul, real_smul, real_smul]

/-- `∂f/∂z̄ = 0` at a point where `f` is real differentiable iff `f` is complex differentiable
there (the Cauchy–Riemann equations). -/
theorem dbar_eq_zero_iff (hf : DifferentiableAt ℝ f z) :
    dbar f z = 0 ↔ DifferentiableAt ℂ f z := by
  constructor
  · intro h
    have hI : fderiv ℝ f z I = I * fderiv ℝ f z 1 := by
      have h' : fderiv ℝ f z 1 + I * fderiv ℝ f z I = 0 := by
        simpa [dbar] using h
      linear_combination (-I) * h' + (fderiv ℝ f z I) * I_sq
    let L : ℂ →L[ℂ] ℂ := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (fderiv ℝ f z 1)
    have hL : L.restrictScalars ℝ = fderiv ℝ f z := by
      ext1 w
      rw [realLinear_apply_eq (fderiv ℝ f z) w, hI]
      simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
        one_apply_eq_self, L, smul_eq_mul]
      conv_lhs => rw [← re_add_im w]
      ring
    exact (hasFDerivAt_of_restrictScalars ℝ (hL ▸ hf.hasFDerivAt) rfl).differentiableAt
  · intro h
    rw [dbar, h.fderiv_restrictScalars ℝ]
    simp only [ContinuousLinearMap.coe_restrictScalars']
    rw [show (fderiv ℂ f z) I = I * fderiv ℂ f z 1 by
      rw [← smul_eq_mul, ← (fderiv ℂ f z).map_smul, smul_eq_mul, mul_one]]
    ring_nf
    simp

lemma dbar_sub (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbar (f - g) z = dbar f z - dbar g z := by
  simp only [dbar, fderiv_sub hf hg, sub_apply]
  ring

lemma dbar_congr {f g : ℂ → ℂ} (h : f =ᶠ[𝓝 z] g) : dbar f z = dbar g z := by
  simp only [dbar, h.fderiv_eq]

/-- If two real differentiable functions have the same `∂/∂z̄` at `z`, their difference is complex
differentiable at `z`. -/
theorem differentiableAt_sub_of_dbar_eq (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) (h : dbar f z = dbar g z) : DifferentiableAt ℂ (f - g) z :=
  (dbar_eq_zero_iff (hf.sub hg)).mp (by rw [dbar_sub hf hg, h, sub_self])

/-! ### The generalized Cauchy integral formula -/

section CauchyFormula

variable {G : ℂ → ℂ}

private lemma polarCoord_symm_eq (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 * cexp (p.2 * I) := by
  rw [Complex.polarCoord_symm_apply, exp_mul_I, ← ofReal_cos, ← ofReal_sin]

/-- The integrand of the generalized Cauchy formula in polar coordinates. -/
private lemma ofReal_mul_dbar_div_eq (L : ℂ →L[ℝ] ℂ) {r : ℝ} (hr : r ≠ 0) (θ : ℝ) :
    (r : ℂ) * ((1 / 2 : ℂ) * (L 1 + I * L I) / (r * cexp (θ * I))) =
      (1 / 2 : ℂ) * (L (cexp (θ * I)) + I * L (I * cexp (θ * I))) := by
  rw [realLinear_apply_eq L (cexp (θ * I)), realLinear_apply_eq L (I * cexp (θ * I))]
  simp only [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, mul_re, mul_im, I_re, I_im, zero_mul,
    one_mul, zero_sub, zero_add, ofReal_neg]
  have hcs : (Real.cos θ : ℂ) ^ 2 + (Real.sin θ : ℂ) ^ 2 = 1 := by
    rw [← ofReal_pow, ← ofReal_pow, ← ofReal_add, Real.cos_sq_add_sin_sq, ofReal_one]
  have he : cexp (θ * I) = (Real.cos θ : ℂ) + Real.sin θ * I := by
    rw [exp_mul_I, ofReal_cos, ofReal_sin]
  have he0 : (Real.cos θ : ℂ) + Real.sin θ * I ≠ 0 := he ▸ exp_ne_zero _
  rw [he]
  generalize (Real.cos θ : ℂ) = c at hcs he0 ⊢
  generalize (Real.sin θ : ℂ) = s at hcs he0 ⊢
  have hr' : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr
  rw [mul_div_assoc', mul_comm (r : ℂ) (c + s * I), ← div_div, mul_div_assoc,
    mul_div_cancel_left₀ _ hr', div_eq_iff he0]
  linear_combination (-(1 / 2 : ℂ)) * (L 1 + I * L I) * hcs +
    (1 / 2 : ℂ) * (s ^ 2 * L 1 - c * s * L I) * I_sq

/-- A continuous function on `ℝ × ℝ` vanishing on `S` outside a compact set is integrable on
`S`. -/
private lemma integrableOn_of_continuous_of_eq_zero {F : ℝ × ℝ → ℂ} (hF : Continuous F)
    {S K : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hK : IsCompact K)
    (h : ∀ p ∈ S, p ∉ K → F p = 0) : IntegrableOn F S :=
  (hF.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero hS fun p hp => h p hp.1 hp.2

/-- **The generalized Cauchy integral formula** at `0` for a compactly supported `C¹` function
`G`: `∫ (∂G/∂z̄)(w) / w dA(w) = -π G(0)`. -/
theorem integral_dbar_div (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) :
    ∫ w, dbar G w / w = -(π * G 0) := by
  set A : ℝ × ℝ → ℂ := fun p => fderiv ℝ G (p.1 * cexp (p.2 * I)) (cexp (p.2 * I)) with hAdef
  set B : ℝ × ℝ → ℂ := fun p => fderiv ℝ G (p.1 * cexp (p.2 * I)) (I * cexp (p.2 * I))
    with hBdef
  obtain ⟨R, -, hR⟩ := hc.fderiv (𝕜 := ℝ) |>.exists_pos_le_norm
  have hcont : Continuous (fun p : ℝ × ℝ => fderiv ℝ G (p.1 * cexp (p.2 * I))) :=
    (hG.continuous_fderiv one_ne_zero).comp (by fun_prop)
  have hAc : Continuous A := by
    simp only [hAdef]
    exact hcont.clm_apply (by fun_prop)
  have hBc : Continuous B := by
    simp only [hBdef]
    exact hcont.clm_apply (by fun_prop)
  have hnorm : ∀ p : ℝ × ℝ, ‖(p.1 : ℂ) * cexp (p.2 * I)‖ = |p.1| := fun p => by
    rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, norm_real, Real.norm_eq_abs]
  have hA0 : ∀ p : ℝ × ℝ, R < |p.1| → A p = 0 := fun p hp => by
    simp only [hAdef]; rw [hR _ (by rw [hnorm]; exact hp.le)]; rfl
  have hB0 : ∀ p : ℝ × ℝ, R < |p.1| → B p = 0 := fun p hp => by
    simp only [hBdef]; rw [hR _ (by rw [hnorm]; exact hp.le)]; rfl
  have hK : IsCompact (Icc (-R) R ×ˢ Icc (-π) π) := isCompact_Icc.prod isCompact_Icc
  have hint : ∀ F : ℝ × ℝ → ℂ, Continuous F → (∀ p : ℝ × ℝ, R < |p.1| → F p = 0) →
      IntegrableOn F (Ioi 0 ×ˢ Ioo (-π) π) := fun F hF hF0 =>
    integrableOn_of_continuous_of_eq_zero hF (measurableSet_Ioi.prod measurableSet_Ioo) hK
      fun p hp hpK => hF0 p (by
        by_contra hle
        exact hpK ⟨abs_le.mp (not_lt.mp hle), Ioo_subset_Icc_self hp.2⟩)
  have hint' : ∀ F : ℝ × ℝ → ℂ, Continuous F → (∀ p : ℝ × ℝ, R < |p.1| → F p = 0) →
      IntegrableOn (fun q : ℝ × ℝ => F q.swap) (Ioo (-π) π ×ˢ Ioi 0) := fun F hF hF0 =>
    integrableOn_of_continuous_of_eq_zero (hF.comp continuous_swap)
      (measurableSet_Ioo.prod measurableSet_Ioi) (isCompact_Icc.prod isCompact_Icc)
      (K := Icc (-π) π ×ˢ Icc (-R) R) fun p hp hpK => hF0 p.swap (by
        by_contra hle
        exact hpK ⟨Ioo_subset_Icc_self hp.1, abs_le.mp (not_lt.mp hle)⟩)
  -- polar coordinates
  rw [← Complex.integral_comp_polarCoord_symm]
  have h1 : ∫ p in polarCoord.target, p.1 • (dbar G (Complex.polarCoord.symm p) /
      Complex.polarCoord.symm p) = ∫ p in polarCoord.target, (1 / 2 : ℂ) * (A p + I * B p) := by
    refine setIntegral_congr_fun polarCoord.open_target.measurableSet fun p hp => ?_
    rw [polarCoord_symm_eq, real_smul, dbar]
    exact ofReal_mul_dbar_div_eq _ hp.1.ne' _
  rw [h1, integral_const_mul, polarCoord_target,
    integral_add (hint A hAc hA0) ((hint B hBc hB0).const_mul I), integral_const_mul]
  -- the radial part
  have hA : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, A p = -(2 * π * G 0) := by
    rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod _
      (by rw [← Measure.volume_eq_prod]; exact hint' A hAc hA0)]
    have hθ : ∀ θ : ℝ, ∫ r in Ioi (0 : ℝ), A (r, θ) = -G 0 := fun θ => by
      have hd : ∀ r : ℝ, HasDerivAt (fun r : ℝ => G (r * cexp (θ * I))) (A (r, θ)) r := by
        intro r
        have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) * cexp (θ * I)) (cexp (θ * I)) r := by
          simpa using ((hasDerivAt_id r).ofReal_comp).mul_const (cexp (θ * I))
        exact (hG.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt r h1
      have hsupp : HasCompactSupport (fun r : ℝ => G (r * cexp (θ * I))) := by
        obtain ⟨R', -, hR'⟩ := hc.exists_pos_le_norm
        refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R') fun r hr => hR' _ ?_
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hr
        rw [hnorm (r, θ)]
        exact hr.le
      have hlin : ContDiff ℝ 1 fun r : ℝ => (r : ℂ) * cexp (θ * I) :=
        ofRealCLM.contDiff.mul contDiff_const
      have := HasCompactSupport.integral_Ioi_deriv_eq (hG.comp hlin) hsupp 0
      simp only [Function.comp_def, ofReal_zero, zero_mul] at this
      rw [← this]
      exact setIntegral_congr_fun measurableSet_Ioi fun r _ => (hd r).deriv.symm
    simp only [Prod.swap_prod_mk, hθ, setIntegral_const, Real.volume_real_Ioo, real_smul]
    rw [max_eq_left (by linarith [Real.pi_pos])]
    push_cast
    ring
  -- the angular part
  have hB : ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, B p = 0 := by
    rw [Measure.volume_eq_prod, setIntegral_prod _
      (by rw [← Measure.volume_eq_prod]; exact hint B hBc hB0)]
    refine (setIntegral_congr_fun measurableSet_Ioi fun r (hr : 0 < r) => ?_).trans
      (integral_zero _ _)
    have hd : ∀ θ : ℝ, HasDerivAt (fun θ : ℝ => G (r * cexp (θ * I))) (r * B (r, θ)) θ := by
      intro θ
      have h2 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * I) I θ := by
        simpa using ((hasDerivAt_id θ).ofReal_comp).mul_const I
      have h1 : HasDerivAt (fun θ : ℝ => (r : ℂ) * cexp (θ * I)) (r • (I * cexp (θ * I))) θ := by
        exact (h2.cexp.const_mul (r : ℂ)).congr_deriv (by rw [real_smul]; ring)
      refine ((hG.differentiable one_ne_zero _).hasFDerivAt.comp_hasDerivAt θ h1).congr_deriv ?_
      rw [ContinuousLinearMap.map_smul, real_smul]
    have hzero : ∫ θ in Ioo (-π) π, (r : ℂ) * B (r, θ) = 0 := by
      rw [← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hd θ)
          ((continuous_const.mul (hBc.comp (by fun_prop))).intervalIntegrable _ _)]
      have hm : cexp (↑(-π) * I) = cexp (↑π * I) := by
        rw [ofReal_neg, neg_mul, exp_neg_pi_mul_I, exp_pi_mul_I]
      simp only [hm, sub_self]
    rw [integral_const_mul] at hzero
    exact (mul_eq_zero.mp hzero).resolve_left (ofReal_ne_zero.mpr hr.ne')
  rw [hA, hB]
  ring

/-- **The generalized Cauchy integral formula** for a compactly supported `C¹` function `G`:
`∫ (∂G/∂z̄)(w) / (w - z) dA(w) = -π G(z)`. -/
theorem integral_dbar_div_sub (hG : ContDiff ℝ 1 G) (hc : HasCompactSupport G) (z : ℂ) :
    ∫ w, dbar G w / (w - z) = -(π * G z) := by
  have h := integral_dbar_div (G := fun w => G (w + z))
    (hG.comp (contDiff_id.add contDiff_const)) (hc.comp_homeomorph (Homeomorph.addRight z))
  have hd : ∀ w, dbar (fun w => G (w + z)) w = dbar G (w + z) := fun w => by
    simp only [dbar, fderiv_comp_add_right]
  simp only [hd, zero_add] at h
  rw [← h, ← integral_add_right_eq_self (fun w => dbar G w / (w - z)) z]
  simp

end CauchyFormula

/-! ### The Cauchy transform -/

section CauchyTransform

/-- The `ℝ`-linear functional `L ↦ (L 1 + i L i) / 2`, so that `dbar f z = dbarCLM (fderiv ℝ f z)`
(`dbar_eq_dbarCLM`). -/
def dbarCLM : (ℂ →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.apply ℝ ℂ (1 : ℂ) + I • ContinuousLinearMap.apply ℝ ℂ I)

lemma dbarCLM_apply (L : ℂ →L[ℝ] ℂ) : dbarCLM L = (1 / 2 : ℂ) * (L 1 + I * L I) := by
  simp [dbarCLM, smul_eq_mul]
  ring

lemma dbar_eq_dbarCLM (f : ℂ → ℂ) (z : ℂ) : dbar f z = dbarCLM (fderiv ℝ f z) :=
  (dbarCLM_apply _).symm

/-- The Cauchy kernel `w ↦ 1 / (π w)`. -/
def cauchyKernel (w : ℂ) : ℂ := ((π : ℂ) * w)⁻¹

lemma locallyIntegrable_cauchyKernel : LocallyIntegrable cauchyKernel volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := π⁻¹) (α := 1)
    (by simp [Complex.finrank_real_complex]) (by simp [Complex.finrank_real_complex])
    (Eventually.of_forall fun w => ?_)
    (measurable_const.mul measurable_id).inv.aestronglyMeasurable
  rw [cauchyKernel, norm_inv, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Real.rpow_neg_one, mul_inv]

/-- The Cauchy transform `(T g)(z) = (1/π) ∫ g(ζ) / (z - ζ) dA(ζ)` of `g : ℂ → ℂ`, the convolution
of `g` with the Cauchy kernel. -/
def cauchyTransform (g : ℂ → ℂ) : ℂ → ℂ :=
  g ⋆[ContinuousLinearMap.mul ℝ ℂ, volume] cauchyKernel

lemma cauchyTransform_apply (g : ℂ → ℂ) (z : ℂ) :
    cauchyTransform g z = ∫ t, g t * cauchyKernel (z - t) :=
  rfl

/-- The Cauchy transform of a compactly supported `Cⁿ` function is `Cⁿ`. -/
theorem contDiff_cauchyTransform {n : ℕ∞} (hc : HasCompactSupport g) (hg : ContDiff ℝ n g) :
    ContDiff ℝ n (cauchyTransform g) :=
  hc.contDiff_convolution_left _ hg locallyIntegrable_cauchyKernel

/-- **Dolbeault's lemma for compact support**: the Cauchy transform `u` of a compactly supported
`C¹` function `g` solves `∂u/∂z̄ = g`. -/
theorem dbar_cauchyTransform (hc : HasCompactSupport g) (hg : ContDiff ℝ 1 g) (z : ℂ) :
    dbar (cauchyTransform g) z = g z := by
  have hder := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℂ) hg
    locallyIntegrable_cauchyKernel z
  have hint := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℂ).precompL ℂ) (hg.continuous_fderiv one_ne_zero)
    locallyIntegrable_cauchyKernel z
  rw [dbar_eq_dbarCLM, cauchyTransform, hder.fderiv, convolution_def,
    ← dbarCLM.integral_comp_comm hint]
  have hpt : ∀ t, dbarCLM (((ContinuousLinearMap.mul ℝ ℂ).precompL ℂ) (fderiv ℝ g t)
      (cauchyKernel (z - t))) = -(π : ℂ)⁻¹ * (dbar g t / (t - z)) := fun t => by
    rw [dbarCLM_apply, dbar, cauchyKernel]
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.mul_apply',
      mul_inv, ← neg_sub t z, inv_neg, div_eq_mul_inv]
    ring
  simp only [hpt, integral_const_mul, integral_dbar_div_sub hg hc z]
  have : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

/-- **Dolbeault's lemma on a smaller disc**: if `w` is `Cⁿ` (`n ≥ 1`) on the disc `B(c, R)` and
`r < R`, there is a `Cⁿ` function `u` on `ℂ` with `∂u/∂z̄ = w` on `B(c, r)`. (Multiply `w` by a
bump function which is `1` on `B(c, r)` and apply `dbar_cauchyTransform`.) For the whole disc see
`exists_contDiffOn_dbar_eq_ball`. -/
theorem exists_contDiff_dbar_eq_on_ball {n : ℕ∞} (hn : 1 ≤ n) {w : ℂ → ℂ} {c : ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r < R) (hw : ContDiffOn ℝ n w (Metric.ball c R)) :
    ∃ u : ℂ → ℂ, ContDiff ℝ n u ∧ ∀ z ∈ Metric.ball c r, dbar u z = w z := by
  let χ : ContDiffBump c := ⟨r, (r + R) / 2, hr, by linarith⟩
  set g : ℂ → ℂ := fun z => (χ z : ℂ) * w z with hg
  have hχ : ContDiff ℝ n fun z => (χ z : ℂ) := ofRealCLM.contDiff.comp χ.contDiff
  have hsub : tsupport χ ⊆ Metric.ball c R := by
    rw [χ.tsupport_eq]
    exact Metric.closedBall_subset_ball (by simp only [χ]; linarith)
  have hgc : HasCompactSupport g := by
    refine (χ.hasCompactSupport.comp_left (g := ofReal) ofReal_zero).mul_right
  have hgd : ContDiff ℝ n g := by
    refine contDiff_iff_contDiffAt.mpr fun z => ?_
    by_cases hz : z ∈ Metric.ball c R
    · exact (hχ.contDiffAt.mul (hw.contDiffAt (Metric.isOpen_ball.mem_nhds hz)))
    · have h0 : g =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport χ).isOpen_compl.mem_nhds
          fun h => hz (hsub h)] with y hy
        simp [hg, image_eq_zero_of_notMem_tsupport hy]
      exact contDiffAt_const.congr_of_eventuallyEq h0
  refine ⟨cauchyTransform g, contDiff_cauchyTransform hgc hgd, fun z hz => ?_⟩
  rw [dbar_cauchyTransform hgc (hgd.of_le (by exact_mod_cast hn)), hg]
  simp only [χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), ofReal_one, one_mul]

end CauchyTransform

end AnalyticGeometry
