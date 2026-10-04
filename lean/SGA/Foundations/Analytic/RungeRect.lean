/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeScheme
import SGA.Foundations.Analytic.RungeLaurent
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-!
# Cauchy's formula on rectangles and polynomial approximation on rectangles

For a closed rectangle `Q = [p, q]` (lower left corner `p`, upper right corner `q`) we write
`rectIntegral f p q` for the integral of `f` over the boundary of `Q`, in the form of mathlib's
Cauchy–Goursat theorem for rectangles
(`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`).

* **Winding number**: `rectIntegral (fun ζ ↦ (ζ - w)⁻¹) p q = 2πi` for `w` in the open rectangle
  (`AnalyticGeometry.rectIntegral_sub_inv`), computed side by side with branches of the logarithm.
* **Cauchy's integral formula on rectangles** (`AnalyticGeometry.rectIntegral_sub_inv_mul`):
  `rectIntegral (fun ζ ↦ (ζ - w)⁻¹ * f ζ) p q = 2πi f(w)` if `f` is complex differentiable on `Q`.
* **Polynomial approximation with holomorphic parameters** (`AnalyticGeometry.rectScheme`): for
  closed rectangles `K ⊆ interior L`, expanding the Cauchy kernel on each side of `L` around a
  far away centre gives a one-variable approximation scheme on `K` by polynomials
  (`AnalyticGeometry.ApproxScheme`).

Reference: Ahlfors, *Complex analysis*, 4.2 (Cauchy's theorem for a rectangle) and 4.2.3; Gunning–
Rossi, *Analytic functions of several complex variables*, I.D (Runge approximation on boxes).
-/

noncomputable section

open Complex Set Metric Filter Topology intervalIntegral
open scoped Real ComplexOrder Interval

namespace AnalyticGeometry

/-- The closed rectangle with lower left corner `p` and upper right corner `q`. -/
def closedRect (p q : ℂ) : Set ℂ := Icc p.re q.re ×ℂ Icc p.im q.im

/-- The integral of `f` over the boundary of the rectangle with corners `p`, `q`, in the form of
mathlib's Cauchy–Goursat theorem (counterclockwise if `p.re ≤ q.re` and `p.im ≤ q.im`). -/
def rectIntegral (f : ℂ → ℂ) (p q : ℂ) : ℂ :=
  (∫ x : ℝ in p.re..q.re, f (x + p.im * I)) - (∫ x : ℝ in p.re..q.re, f (x + q.im * I)) +
    I * (∫ y : ℝ in p.im..q.im, f (q.re + y * I)) - I * ∫ y : ℝ in p.im..q.im, f (p.re + y * I)

/-! ### The winding number of a rectangle -/

section Winding

variable {w : ℂ}

private lemma log_I_mul {u : ℂ} (hu : u.im < 0) : log (I * u) = π / 2 * I + log u := by
  have hu0 : u ≠ 0 := fun h ↦ by simp [h] at hu
  have harg : arg u < 0 := arg_neg_iff.mpr hu
  rw [(log_mul_eq_add_log_iff I_ne_zero hu0).mpr, log_I]
  rw [arg_I]
  constructor <;> linarith [neg_pi_lt_arg u, Real.pi_pos]

private lemma log_neg_I_mul {u : ℂ} (hu : 0 < u.im) : log (-I * u) = -(π / 2) * I + log u := by
  have hu0 : u ≠ 0 := fun h ↦ by simp [h] at hu
  have harg : 0 ≤ arg u := arg_nonneg_iff.mpr hu.le
  rw [(log_mul_eq_add_log_iff (neg_ne_zero.mpr I_ne_zero) hu0).mpr, log_neg_I]
  rw [arg_neg_I]
  constructor <;> linarith [arg_le_pi u, Real.pi_pos]

private lemma log_neg_of_im_neg {u : ℂ} (hu : u.im < 0) : log (-u) = π * I + log u := by
  have hu0 : u ≠ 0 := fun h ↦ by simp [h] at hu
  have harg : arg u < 0 := arg_neg_iff.mpr hu
  rw [show -u = -1 * u by ring, (log_mul_eq_add_log_iff (by norm_num) hu0).mpr, log_neg_one]
  rw [arg_neg_one]
  constructor <;> linarith [neg_pi_lt_arg u, Real.pi_pos]

private lemma log_neg_of_im_pos {u : ℂ} (hu : 0 < u.im) : log (-u) = log u - π * I := by
  have h := log_neg_of_im_neg (u := -u) (by simpa using hu)
  rw [neg_neg] at h
  rw [h]
  ring

/-- The integral of `(ζ - w)⁻¹` along a horizontal segment below `w`. -/
private lemma integral_bottom {a b c : ℝ} (hc : c < w.im) :
    ∫ x : ℝ in a..b, ((x : ℂ) + c * I - w)⁻¹ =
      log (I * ((b : ℂ) + c * I - w)) - log (I * ((a : ℂ) + c * I - w)) := by
  have him : ∀ x : ℝ, ((x : ℂ) + c * I - w).im < 0 := fun x ↦ by simpa using hc
  have hne : ∀ x : ℝ, (x : ℂ) + c * I - w ≠ 0 := fun x h ↦ by
    have := him x
    rw [h, zero_im] at this
    exact lt_irrefl _ this
  refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ log (I * ((t : ℂ) + c * I - w)))
    (fun x _ ↦ ?_) ?_
  · have hd : HasDerivAt (fun t : ℝ ↦ I * ((t : ℂ) + c * I - w)) (I * 1) x :=
      (((hasDerivAt_id x).ofReal_comp).add_const _ |>.sub_const _).const_mul I
    have hs : I * ((x : ℂ) + c * I - w) ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simpa using him x
    exact (hd.clog_real hs).congr_deriv (by field_simp [hne x])
  · exact (continuous_iff_continuousAt.mpr fun x ↦
      ((continuous_ofReal.add continuous_const |>.sub continuous_const).continuousAt).inv₀
        (hne x)).intervalIntegrable _ _

/-- The integral of `(ζ - w)⁻¹` along a horizontal segment above `w`. -/
private lemma integral_top {a b d : ℝ} (hd : w.im < d) :
    ∫ x : ℝ in a..b, ((x : ℂ) + d * I - w)⁻¹ =
      log (-I * ((b : ℂ) + d * I - w)) - log (-I * ((a : ℂ) + d * I - w)) := by
  have him : ∀ x : ℝ, 0 < ((x : ℂ) + d * I - w).im := fun x ↦ by simpa using hd
  have hne : ∀ x : ℝ, (x : ℂ) + d * I - w ≠ 0 := fun x h ↦ by
    have := him x
    rw [h, zero_im] at this
    exact lt_irrefl _ this
  refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ log (-I * ((t : ℂ) + d * I - w)))
    (fun x _ ↦ ?_) ?_
  · have hder : HasDerivAt (fun t : ℝ ↦ -I * ((t : ℂ) + d * I - w)) (-I * 1) x :=
      (((hasDerivAt_id x).ofReal_comp).add_const _ |>.sub_const _).const_mul (-I)
    have hs : -I * ((x : ℂ) + d * I - w) ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simpa using him x
    exact (hder.clog_real hs).congr_deriv (by field_simp [hne x])
  · exact (continuous_iff_continuousAt.mpr fun x ↦
      ((continuous_ofReal.add continuous_const |>.sub continuous_const).continuousAt).inv₀
        (hne x)).intervalIntegrable _ _

/-- `I` times the integral of `(ζ - w)⁻¹` along a vertical segment right of `w`. -/
private lemma integral_right {c d b : ℝ} (hb : w.re < b) :
    I * ∫ y : ℝ in c..d, ((b : ℂ) + y * I - w)⁻¹ =
      log ((b : ℂ) + d * I - w) - log ((b : ℂ) + c * I - w) := by
  have hre : ∀ y : ℝ, 0 < ((b : ℂ) + y * I - w).re := fun y ↦ by simpa using hb
  have hne : ∀ y : ℝ, (b : ℂ) + y * I - w ≠ 0 := fun y h ↦ by
    have := hre y
    rw [h, zero_re] at this
    exact lt_irrefl _ this
  rw [← integral_const_mul]
  refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ log ((b : ℂ) + t * I - w))
    (fun y _ ↦ ?_) ?_
  · have hder : HasDerivAt (fun t : ℝ ↦ (b : ℂ) + t * I - w) (1 * I) y :=
      ((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add _).sub_const _
    have hs : (b : ℂ) + y * I - w ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      exact Or.inl (hre y)
    exact (hder.clog_real hs).congr_deriv (by field_simp [hne y])
  · exact (continuous_const.mul (continuous_iff_continuousAt.mpr fun y ↦
      ((continuous_const.add (continuous_ofReal.mul continuous_const) |>.sub
        continuous_const).continuousAt).inv₀ (hne y))).intervalIntegrable _ _

/-- `I` times the integral of `(ζ - w)⁻¹` along a vertical segment left of `w`. -/
private lemma integral_left {c d a : ℝ} (ha : a < w.re) :
    I * ∫ y : ℝ in c..d, ((a : ℂ) + y * I - w)⁻¹ =
      log (-((a : ℂ) + d * I - w)) - log (-((a : ℂ) + c * I - w)) := by
  have hre : ∀ y : ℝ, ((a : ℂ) + y * I - w).re < 0 := fun y ↦ by simpa using ha
  have hne : ∀ y : ℝ, (a : ℂ) + y * I - w ≠ 0 := fun y h ↦ by
    have := hre y
    rw [h, zero_re] at this
    exact lt_irrefl _ this
  rw [← integral_const_mul]
  refine integral_eq_sub_of_hasDerivAt (f := fun t : ℝ ↦ log (-((a : ℂ) + t * I - w)))
    (fun y _ ↦ ?_) ?_
  · have hder : HasDerivAt (fun t : ℝ ↦ -((a : ℂ) + t * I - w)) (-(1 * I)) y :=
      (((((hasDerivAt_id y).ofReal_comp).mul_const I).const_add _).sub_const _).neg
    have hs : -((a : ℂ) + y * I - w) ∈ slitPlane := by
      rw [mem_slitPlane_iff]
      left
      simpa using hre y
    exact (hder.clog_real hs).congr_deriv (by field_simp [hne y])
  · exact (continuous_const.mul (continuous_iff_continuousAt.mpr fun y ↦
      ((continuous_const.add (continuous_ofReal.mul continuous_const) |>.sub
        continuous_const).continuousAt).inv₀ (hne y))).intervalIntegrable _ _

/-- **The winding number of a rectangle**: for `w` in the open rectangle with corners `p`, `q`,
`∮_{∂Q} (ζ - w)⁻¹ dζ = 2πi`. -/
theorem rectIntegral_sub_inv {p q : ℂ} (h1 : p.re < w.re) (h2 : w.re < q.re) (h3 : p.im < w.im)
    (h4 : w.im < q.im) : rectIntegral (fun ζ ↦ (ζ - w)⁻¹) p q = 2 * π * I := by
  simp only [rectIntegral]
  rw [integral_bottom h3, integral_top h4, integral_right h2, integral_left h1]
  set u₁ : ℂ := (q.re : ℂ) + p.im * I - w
  set u₂ : ℂ := (q.re : ℂ) + q.im * I - w
  set u₃ : ℂ := (p.re : ℂ) + q.im * I - w
  set u₄ : ℂ := (p.re : ℂ) + p.im * I - w
  have hu₁ : u₁.im < 0 := by simp [u₁]; linarith
  have hu₂ : 0 < u₂.im := by simp [u₂]; linarith
  have hu₃ : 0 < u₃.im := by simp [u₃]; linarith
  have hu₄ : u₄.im < 0 := by simp [u₄]; linarith
  rw [log_I_mul hu₁, log_I_mul hu₄, log_neg_I_mul hu₂, log_neg_I_mul hu₃, log_neg_of_im_pos hu₃,
    log_neg_of_im_neg hu₄]
  ring

end Winding

/-! ### Cauchy's integral formula on rectangles -/

section Cauchy

/-- Splitting an integral along a path. -/
private lemma integral_comp_eq_sub_mul {F G H : ℂ → ℂ} {γ : ℝ → ℂ} {a b : ℝ} (c : ℂ)
    (hγ : Continuous γ) (hG : ∀ t ∈ uIcc a b, ContinuousAt G (γ t))
    (hH : ∀ t ∈ uIcc a b, ContinuousAt H (γ t))
    (hFGH : ∀ t ∈ uIcc a b, F (γ t) = G (γ t) - c * H (γ t)) :
    ∫ t in a..b, F (γ t) = (∫ t in a..b, G (γ t)) - c * ∫ t in a..b, H (γ t) := by
  have hGi : IntervalIntegrable (fun t ↦ G (γ t)) MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦ ((hG t ht).comp hγ.continuousAt).continuousWithinAt
  have hHi : IntervalIntegrable (fun t ↦ c * H (γ t)) MeasureTheory.volume a b :=
    ContinuousOn.intervalIntegrable fun t ht ↦
      (continuousAt_const.mul ((hH t ht).comp hγ.continuousAt)).continuousWithinAt
  rw [integral_congr hFGH, integral_sub hGi hHi, integral_const_mul]

/-- **Cauchy's integral formula on a rectangle**: if `f` is complex differentiable at every point
of the closed rectangle with corners `p`, `q` and `w` lies in the open rectangle, then
`∮_{∂Q} (ζ - w)⁻¹ f(ζ) dζ = 2πi f(w)`. -/
theorem rectIntegral_sub_inv_mul {f : ℂ → ℂ} {p q w : ℂ} (h1 : p.re < w.re) (h2 : w.re < q.re)
    (h3 : p.im < w.im) (h4 : w.im < q.im) (hf : ∀ ζ ∈ closedRect p q, DifferentiableAt ℂ f ζ) :
    rectIntegral (fun ζ ↦ (ζ - w)⁻¹ * f ζ) p q = 2 * π * I * f w := by
  have hre : p.re ≤ q.re := by linarith
  have him : p.im ≤ q.im := by linarith
  have hrect : uIcc p.re q.re ×ℂ uIcc p.im q.im = closedRect p q := by
    rw [closedRect, uIcc_of_le hre, uIcc_of_le him]
  have hfw : DifferentiableAt ℂ f w := hf w ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
  -- Cauchy–Goursat for `dslope f w`
  have hCG := integral_boundary_rect_eq_zero_of_differentiable_on_off_countable (dslope f w) p q
    {w} (countable_singleton w) (fun ζ hζ ↦ by
      rw [hrect] at hζ
      by_cases hζw : ζ = w
      · subst hζw
        exact (continuousAt_dslope_same.mpr hfw).continuousWithinAt
      · exact ((continuousAt_dslope_of_ne hζw).mpr (hf ζ hζ).continuousAt).continuousWithinAt)
    fun ζ hζ ↦ (differentiableAt_dslope_of_ne hζ.2).mpr (hf ζ (by
      rw [min_eq_left hre, max_eq_right hre, min_eq_left him, max_eq_right him] at hζ
      exact ⟨⟨hζ.1.1.1.le, hζ.1.1.2.le⟩, ⟨hζ.1.2.1.le, hζ.1.2.2.le⟩⟩))
  simp only [smul_eq_mul] at hCG
  -- on the boundary, `dslope f w ζ = (ζ - w)⁻¹ f ζ - f w (ζ - w)⁻¹`
  have hsplit : ∀ ζ, ζ ≠ w → dslope f w ζ = (ζ - w)⁻¹ * f ζ - f w * (ζ - w)⁻¹ := fun ζ hζ ↦ by
    rw [dslope_of_ne f hζ, slope_def_field]
    ring
  have hcG : ∀ ζ ∈ closedRect p q, ζ ≠ w → ContinuousAt (fun ζ ↦ (ζ - w)⁻¹ * f ζ) ζ :=
    fun ζ hζ hζw ↦ ((continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hζw)).mul
      (hf ζ hζ).continuousAt
  have hcH : ∀ ζ, ζ ≠ w → ContinuousAt (fun ζ ↦ (ζ - w)⁻¹) ζ :=
    fun ζ hζw ↦ (continuousAt_id.sub continuousAt_const).inv₀ (sub_ne_zero.mpr hζw)
  -- the four sides
  have hb : ∀ t ∈ uIcc p.re q.re, (t : ℂ) + p.im * I ∈ closedRect p q ∧ (t : ℂ) + p.im * I ≠ w :=
    fun t ht ↦ by
      rw [uIcc_of_le hre] at ht
      refine ⟨⟨by simpa using ht, by simp [him]⟩, fun h ↦ ?_⟩
      have := congrArg Complex.im h
      simp at this
      linarith
  have ht : ∀ t ∈ uIcc p.re q.re, (t : ℂ) + q.im * I ∈ closedRect p q ∧ (t : ℂ) + q.im * I ≠ w :=
    fun t ht ↦ by
      rw [uIcc_of_le hre] at ht
      refine ⟨⟨by simpa using ht, by simp [him]⟩, fun h ↦ ?_⟩
      have := congrArg Complex.im h
      simp at this
      linarith
  have hr : ∀ t ∈ uIcc p.im q.im, (q.re : ℂ) + t * I ∈ closedRect p q ∧ (q.re : ℂ) + t * I ≠ w :=
    fun t ht ↦ by
      rw [uIcc_of_le him] at ht
      refine ⟨⟨by simp [hre], by simpa using ht⟩, fun h ↦ ?_⟩
      have := congrArg Complex.re h
      simp at this
      linarith
  have hl : ∀ t ∈ uIcc p.im q.im, (p.re : ℂ) + t * I ∈ closedRect p q ∧ (p.re : ℂ) + t * I ≠ w :=
    fun t ht ↦ by
      rw [uIcc_of_le him] at ht
      refine ⟨⟨by simp [hre], by simpa using ht⟩, fun h ↦ ?_⟩
      have := congrArg Complex.re h
      simp at this
      linarith
  have e1 := integral_comp_eq_sub_mul (F := dslope f w) (G := fun ζ ↦ (ζ - w)⁻¹ * f ζ)
    (H := fun ζ ↦ (ζ - w)⁻¹) (γ := fun t : ℝ ↦ (t : ℂ) + p.im * I) (a := p.re) (b := q.re) (f w)
    (by fun_prop) (fun t h ↦ hcG _ (hb t h).1 (hb t h).2) (fun t h ↦ hcH _ (hb t h).2)
    (fun t h ↦ hsplit _ (hb t h).2)
  have e2 := integral_comp_eq_sub_mul (F := dslope f w) (G := fun ζ ↦ (ζ - w)⁻¹ * f ζ)
    (H := fun ζ ↦ (ζ - w)⁻¹) (γ := fun t : ℝ ↦ (t : ℂ) + q.im * I) (a := p.re) (b := q.re) (f w)
    (by fun_prop) (fun t h ↦ hcG _ (ht t h).1 (ht t h).2) (fun t h ↦ hcH _ (ht t h).2)
    (fun t h ↦ hsplit _ (ht t h).2)
  have e3 := integral_comp_eq_sub_mul (F := dslope f w) (G := fun ζ ↦ (ζ - w)⁻¹ * f ζ)
    (H := fun ζ ↦ (ζ - w)⁻¹) (γ := fun t : ℝ ↦ (q.re : ℂ) + t * I) (a := p.im) (b := q.im) (f w)
    (by fun_prop) (fun t h ↦ hcG _ (hr t h).1 (hr t h).2) (fun t h ↦ hcH _ (hr t h).2)
    (fun t h ↦ hsplit _ (hr t h).2)
  have e4 := integral_comp_eq_sub_mul (F := dslope f w) (G := fun ζ ↦ (ζ - w)⁻¹ * f ζ)
    (H := fun ζ ↦ (ζ - w)⁻¹) (γ := fun t : ℝ ↦ (p.re : ℂ) + t * I) (a := p.im) (b := q.im) (f w)
    (by fun_prop) (fun t h ↦ hcG _ (hl t h).1 (hl t h).2) (fun t h ↦ hcH _ (hl t h).2)
    (fun t h ↦ hsplit _ (hl t h).2)
  have hwind := rectIntegral_sub_inv h1 h2 h3 h4
  simp only [rectIntegral] at hwind ⊢
  rw [e1, e2, e3, e4] at hCG
  linear_combination hCG + f w * hwind

end Cauchy

/-! ### Far away centres for the sides of a rectangle -/

section Centre

/-- A far away centre `-ρ` on the real axis: if `w` lies in the strip `-X ≤ Re w ≤ β`,
`|Im w| ≤ X`, and `Re ζ ≥ β' > β`, then `|w + ρ| ≤ θ |ζ + ρ|` with `θ < 1` independent of `w`,
`ζ`. -/
lemma exists_centre_right {β β' X : ℝ} (hβ : β < β') :
    ∃ ρ θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ (∀ ζ : ℂ, β' ≤ ζ.re → 0 < ‖ζ + ρ‖) ∧
      ∀ w ζ : ℂ, -X ≤ w.re → w.re ≤ β → |w.im| ≤ X → β' ≤ ζ.re → ‖w + ρ‖ ≤ θ * ‖ζ + ρ‖ := by
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = β' - β := ⟨_, rfl⟩
  have hDpos : 0 < D := by rw [hD]; exact sub_pos.mpr hβ
  obtain ⟨q, hqdef⟩ : ∃ q : ℝ, q = (X ^ 2 + 1) / D := ⟨_, rfl⟩
  have hq : 0 ≤ q := by rw [hqdef]; positivity
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = q + |β| + |β'| + |X| + 1 := ⟨_, rfl⟩
  have hab := abs_nonneg β
  have hab' := abs_nonneg β'
  have habX := abs_nonneg X
  have hβρ : 1 ≤ β + ρ := by linarith [neg_abs_le β, abs_nonneg β', abs_nonneg X]
  have hβ'ρ : β + ρ < β' + ρ := by linarith
  have hkey : (β + ρ) ^ 2 + X ^ 2 < (β' + ρ) ^ 2 := by
    have h1 : (β' + ρ) ^ 2 - (β + ρ) ^ 2 = D * (β' + β + 2 * ρ) := by rw [hD]; ring
    have h2 : 2 * (X ^ 2 + 1) / D ≤ β' + β + 2 * ρ := by
      have : β' + β + 2 * ρ ≥ 2 * q := by
        linarith [neg_abs_le β, neg_abs_le β']
      rw [mul_div_assoc, ← hqdef]
      linarith
    have h3 : D * (2 * (X ^ 2 + 1) / D) = 2 * (X ^ 2 + 1) := by field_simp
    have h4 : D * (2 * (X ^ 2 + 1) / D) ≤ D * (β' + β + 2 * ρ) :=
      mul_le_mul_of_nonneg_left h2 hDpos.le
    nlinarith
  obtain ⟨θ2, hθ2⟩ : ∃ θ2 : ℝ, θ2 = ((β + ρ) ^ 2 + X ^ 2) / (β' + ρ) ^ 2 := ⟨_, rfl⟩
  have hβ'ρpos : 0 < β' + ρ := by linarith
  have hθ2nn : 0 ≤ θ2 := by rw [hθ2]; positivity
  have hθ2lt : θ2 < 1 := by rw [hθ2]; exact (div_lt_one (by positivity)).mpr hkey
  refine ⟨ρ, Real.sqrt θ2, Real.sqrt_nonneg _, ?_, fun ζ hζ ↦ ?_, fun w ζ hw1 hw2 hw3 hζ ↦ ?_⟩
  · rw [Real.sqrt_lt' one_pos, one_pow]
    exact hθ2lt
  · have := re_le_norm (ζ + ρ)
    simp only [add_re, ofReal_re] at this
    linarith
  · have hζρ : β' + ρ ≤ ‖ζ + ρ‖ := by
      have := re_le_norm (ζ + ρ)
      simp only [add_re, ofReal_re] at this
      linarith
    have hwρ : ‖w + ρ‖ ^ 2 ≤ (β + ρ) ^ 2 + X ^ 2 := by
      rw [Complex.sq_norm, normSq_apply]
      simp only [add_re, ofReal_re, add_im, ofReal_im, add_zero]
      have h1 : 0 ≤ w.re + ρ := by linarith [le_abs_self X]
      have h2 : w.re + ρ ≤ β + ρ := by linarith
      have h3 : w.im * w.im ≤ X ^ 2 := by
        rw [← sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) hw3 2
      nlinarith
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero, mul_pow,
      Real.sq_sqrt hθ2nn]
    calc ‖w + ρ‖ ^ 2 ≤ (β + ρ) ^ 2 + X ^ 2 := hwρ
      _ = θ2 * (β' + ρ) ^ 2 := by rw [hθ2]; field_simp
      _ ≤ θ2 * ‖ζ + ρ‖ ^ 2 := by gcongr

end Centre

/-! ### The four sides of a rectangle -/

section Sides

/-- `t` clamped to `[a, b]`. -/
def clampIcc (a b t : ℝ) : ℝ := max a (min b t)

lemma clampIcc_of_mem {a b t : ℝ} (ht : t ∈ Icc a b) : clampIcc a b t = t := by
  simp [clampIcc, ht.1, ht.2]

lemma clampIcc_mem {a b : ℝ} (hab : a ≤ b) (t : ℝ) : clampIcc a b t ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

lemma continuous_clampIcc (a b : ℝ) : Continuous (clampIcc a b) := by
  unfold clampIcc
  fun_prop

/-- The four sides of the rectangle with corners `p`, `q`, clamped to their parameter intervals:
bottom, top (parametrized by the real part), right, left (parametrized by the imaginary part). -/
def rectSide (p q : ℂ) : Fin 4 → ℝ → ℂ :=
  ![fun t ↦ (clampIcc p.re q.re t : ℂ) + p.im * I, fun t ↦ (clampIcc p.re q.re t : ℂ) + q.im * I,
    fun t ↦ (q.re : ℂ) + (clampIcc p.im q.im t : ℂ) * I,
    fun t ↦ (p.re : ℂ) + (clampIcc p.im q.im t : ℂ) * I]

/-- The left ends of the parameter intervals of the sides. -/
def rectSideA (p _q : ℂ) : Fin 4 → ℝ := ![p.re, p.re, p.im, p.im]

/-- The right ends of the parameter intervals of the sides. -/
def rectSideB (_p q : ℂ) : Fin 4 → ℝ := ![q.re, q.re, q.im, q.im]

/-- The orientation factors of the sides in `rectIntegral`. -/
def rectSideε : Fin 4 → ℂ := ![1, -1, I, -I]

section Eval

variable (p q : ℂ)

@[simp] lemma rectSide_zero :
    rectSide p q 0 = fun t ↦ (clampIcc p.re q.re t : ℂ) + p.im * I := rfl
@[simp] lemma rectSide_one :
    rectSide p q 1 = fun t ↦ (clampIcc p.re q.re t : ℂ) + q.im * I := rfl
@[simp] lemma rectSide_two :
    rectSide p q 2 = fun t ↦ (q.re : ℂ) + (clampIcc p.im q.im t : ℂ) * I := rfl
@[simp] lemma rectSide_three :
    rectSide p q 3 = fun t ↦ (p.re : ℂ) + (clampIcc p.im q.im t : ℂ) * I := rfl
@[simp] lemma rectSideA_zero : rectSideA p q 0 = p.re := rfl
@[simp] lemma rectSideA_one : rectSideA p q 1 = p.re := rfl
@[simp] lemma rectSideA_two : rectSideA p q 2 = p.im := rfl
@[simp] lemma rectSideA_three : rectSideA p q 3 = p.im := rfl
@[simp] lemma rectSideB_zero : rectSideB p q 0 = q.re := rfl
@[simp] lemma rectSideB_one : rectSideB p q 1 = q.re := rfl
@[simp] lemma rectSideB_two : rectSideB p q 2 = q.im := rfl
@[simp] lemma rectSideB_three : rectSideB p q 3 = q.im := rfl
@[simp] lemma rectSideε_zero : rectSideε 0 = 1 := rfl
@[simp] lemma rectSideε_one : rectSideε 1 = -1 := rfl
@[simp] lemma rectSideε_two : rectSideε 2 = I := rfl
@[simp] lemma rectSideε_three : rectSideε 3 = -I := rfl

end Eval

lemma continuous_rectSide (p q : ℂ) (s : Fin 4) : Continuous (rectSide p q s) := by
  have h1 := continuous_clampIcc p.re q.re
  have h2 := continuous_clampIcc p.im q.im
  fin_cases s
  · exact (continuous_ofReal.comp h1).add continuous_const
  · exact (continuous_ofReal.comp h1).add continuous_const
  · exact continuous_const.add ((continuous_ofReal.comp h2).mul continuous_const)
  · exact continuous_const.add ((continuous_ofReal.comp h2).mul continuous_const)

lemma isCompact_closedRect (p q : ℂ) : IsCompact (closedRect p q) :=
  isCompact_Icc.reProdIm isCompact_Icc

lemma rectSide_mem {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (s : Fin 4) (t : ℝ) :
    rectSide p q s t ∈ closedRect p q := by
  have h1 := clampIcc_mem hre t
  have h2 := clampIcc_mem him t
  fin_cases s <;> simp [closedRect, Complex.mem_reProdIm, h1.1, h1.2, h2.1, h2.2, hre, him]

/-- `rectIntegral` is the sum of the integrals over the four (clamped) sides. -/
lemma rectIntegral_eq_sum_sides {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (F : ℂ → ℂ) :
    rectIntegral F p q = ∑ s : Fin 4,
      rectSideε s * ∫ t in rectSideA p q s..rectSideB p q s, F (rectSide p q s t) := by
  have hc1 : ∀ t ∈ uIcc p.re q.re, clampIcc p.re q.re t = t := fun t ht ↦
    clampIcc_of_mem (by rwa [uIcc_of_le hre] at ht)
  have hc2 : ∀ t ∈ uIcc p.im q.im, clampIcc p.im q.im t = t := fun t ht ↦
    clampIcc_of_mem (by rwa [uIcc_of_le him] at ht)
  rw [Fin.sum_univ_four]
  simp only [rectSide_zero, rectSide_one, rectSide_two, rectSide_three, rectSideA_zero,
    rectSideA_one, rectSideA_two, rectSideA_three, rectSideB_zero, rectSideB_one, rectSideB_two,
    rectSideB_three, rectSideε_zero, rectSideε_one, rectSideε_two, rectSideε_three, rectIntegral]
  have e1 : ∫ t in p.re..q.re, F ((clampIcc p.re q.re t : ℂ) + p.im * I) =
      ∫ t in p.re..q.re, F ((t : ℂ) + p.im * I) :=
    integral_congr fun t ht ↦ by simp only [hc1 t ht]
  have e2 : ∫ t in p.re..q.re, F ((clampIcc p.re q.re t : ℂ) + q.im * I) =
      ∫ t in p.re..q.re, F ((t : ℂ) + q.im * I) :=
    integral_congr fun t ht ↦ by simp only [hc1 t ht]
  have e3 : ∫ t in p.im..q.im, F ((q.re : ℂ) + (clampIcc p.im q.im t : ℂ) * I) =
      ∫ t in p.im..q.im, F ((q.re : ℂ) + (t : ℂ) * I) :=
    integral_congr fun t ht ↦ by simp only [hc2 t ht]
  have e4 : ∫ t in p.im..q.im, F ((p.re : ℂ) + (clampIcc p.im q.im t : ℂ) * I) =
      ∫ t in p.im..q.im, F ((p.re : ℂ) + (t : ℂ) * I) :=
    integral_congr fun t ht ↦ by simp only [hc2 t ht]
  rw [e1, e2, e3, e4]
  ring

end Sides

/-! ### Centres for the four sides -/

section Centres

/-- For closed rectangles `K = [p, q] ⊆ interior [p', q']`, every side of `[p', q']` has a far
away centre `c` with `‖w - c‖ ≤ θ ‖ζ - c‖` (`θ < 1`) for `w ∈ K` and `ζ` on that side. -/
lemma exists_rect_centres {p q p' q' : ℂ} (h1 : p'.re < p.re) (h2 : q.re < q'.re)
    (h3 : p'.im < p.im) (h4 : q.im < q'.im) :
    ∃ (c : Fin 4 → ℂ) (θ : Fin 4 → ℝ), (∀ s, 0 ≤ θ s) ∧ (∀ s, θ s < 1) ∧
      (∀ s t, rectSide p' q' s t ≠ c s) ∧
      ∀ s t, ∀ w ∈ closedRect p q, ‖w - c s‖ ≤ θ s * ‖rectSide p' q' s t - c s‖ := by
  set X : ℝ := |p.re| + |q.re| + |p.im| + |q.im| with hX
  have hwX : ∀ w ∈ closedRect p q, |w.re| ≤ X ∧ |w.im| ≤ X := fun w hw ↦ by
    obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩ := hw
    constructor <;> rw [abs_le] <;> constructor <;>
      linarith [neg_abs_le p.re, le_abs_self q.re, neg_abs_le p.im, le_abs_self q.im,
        abs_nonneg p.re, abs_nonneg q.re, abs_nonneg p.im, abs_nonneg q.im]
  obtain ⟨ρ₀, θ₀, h0₀, h1₀, hp₀, hi₀⟩ := exists_centre_right (X := X) (neg_lt_neg h3)
  obtain ⟨ρ₁, θ₁, h0₁, h1₁, hp₁, hi₁⟩ := exists_centre_right (X := X) h4
  obtain ⟨ρ₂, θ₂, h0₂, h1₂, hp₂, hi₂⟩ := exists_centre_right (X := X) h2
  obtain ⟨ρ₃, θ₃, h0₃, h1₃, hp₃, hi₃⟩ := exists_centre_right (X := X) (neg_lt_neg h1)
  have hnI : ∀ x : ℂ, ‖I * x‖ = ‖x‖ := fun x ↦ by rw [norm_mul, norm_I, one_mul]
  have hnmI : ∀ x : ℂ, ‖-I * x‖ = ‖x‖ := fun x ↦ by rw [norm_mul, norm_neg, norm_I, one_mul]
  have e₀ : ∀ x : ℂ, I * x + ρ₀ = I * (x - ρ₀ * I) := fun x ↦ by
    linear_combination (ρ₀ : ℂ) * I_sq
  have e₁ : ∀ x : ℂ, -I * x + ρ₁ = -I * (x - -ρ₁ * I) := fun x ↦ by
    linear_combination (ρ₁ : ℂ) * I_sq
  have e₂ : ∀ x : ℂ, x + ρ₂ = x - -(ρ₂ : ℂ) := fun x ↦ by ring
  have e₃ : ∀ x : ℂ, -x + ρ₃ = -(x - ρ₃) := fun x ↦ by ring
  have hc0 : ∀ t, rectSide p' q' 0 t ≠ ρ₀ * I := fun t h ↦ by
    have := hp₀ (I * rectSide p' q' 0 t) (by simp)
    rw [e₀, hnI, h, sub_self, norm_zero] at this
    exact lt_irrefl _ this
  have hc1 : ∀ t, rectSide p' q' 1 t ≠ -ρ₁ * I := fun t h ↦ by
    have := hp₁ (-I * rectSide p' q' 1 t) (by simp)
    rw [e₁, hnmI, h, sub_self, norm_zero] at this
    exact lt_irrefl _ this
  have hc2 : ∀ t, rectSide p' q' 2 t ≠ -(ρ₂ : ℂ) := fun t h ↦ by
    have := hp₂ (rectSide p' q' 2 t) (by simp)
    rw [e₂, h, sub_self, norm_zero] at this
    exact lt_irrefl _ this
  have hc3 : ∀ t, rectSide p' q' 3 t ≠ (ρ₃ : ℂ) := fun t h ↦ by
    have := hp₃ (-rectSide p' q' 3 t) (by simp)
    rw [e₃, norm_neg, h, sub_self, norm_zero] at this
    exact lt_irrefl _ this
  have hw0 : ∀ t, ∀ w ∈ closedRect p q,
      ‖w - ρ₀ * I‖ ≤ θ₀ * ‖rectSide p' q' 0 t - ρ₀ * I‖ := fun t w hw ↦ by
    obtain ⟨hre, him⟩ := hwX w hw
    obtain ⟨-, ⟨hw3, -⟩⟩ := hw
    have := hi₀ (I * w) (I * rectSide p' q' 0 t) (by simp; linarith [le_abs_self w.im])
      (by simp; linarith) (by simpa using hre) (by simp)
    rwa [e₀, e₀, hnI, hnI] at this
  have hw1 : ∀ t, ∀ w ∈ closedRect p q,
      ‖w - -ρ₁ * I‖ ≤ θ₁ * ‖rectSide p' q' 1 t - -ρ₁ * I‖ := fun t w hw ↦ by
    obtain ⟨hre, him⟩ := hwX w hw
    obtain ⟨-, ⟨-, hw4⟩⟩ := hw
    have := hi₁ (-I * w) (-I * rectSide p' q' 1 t) (by simp; linarith [neg_abs_le w.im])
      (by simp; linarith) (by simpa using hre) (by simp)
    rwa [e₁, e₁, hnmI, hnmI] at this
  have hw2 : ∀ t, ∀ w ∈ closedRect p q,
      ‖w - -(ρ₂ : ℂ)‖ ≤ θ₂ * ‖rectSide p' q' 2 t - -(ρ₂ : ℂ)‖ := fun t w hw ↦ by
    obtain ⟨hre, him⟩ := hwX w hw
    obtain ⟨⟨-, hw2⟩, -⟩ := hw
    have := hi₂ w (rectSide p' q' 2 t) (by linarith [neg_abs_le w.re]) hw2 him (by simp)
    rwa [e₂, e₂] at this
  have hw3 : ∀ t, ∀ w ∈ closedRect p q,
      ‖w - ρ₃‖ ≤ θ₃ * ‖rectSide p' q' 3 t - ρ₃‖ := fun t w hw ↦ by
    obtain ⟨hre, him⟩ := hwX w hw
    obtain ⟨⟨hw1, -⟩, -⟩ := hw
    have := hi₃ (-w) (-rectSide p' q' 3 t) (by simp; linarith [le_abs_self w.re])
      (by simp; linarith) (by simpa using him) (by simp)
    rwa [e₃, e₃, norm_neg, norm_neg] at this
  refine ⟨![ρ₀ * I, -ρ₁ * I, -(ρ₂ : ℂ), ρ₃], ![θ₀, θ₁, θ₂, θ₃], ?_, ?_, ?_, ?_⟩
  · intro s
    fin_cases s
    exacts [h0₀, h0₁, h0₂, h0₃]
  · intro s
    fin_cases s
    exacts [h1₀, h1₁, h1₂, h1₃]
  · intro s t
    fin_cases s
    exacts [hc0 t, hc1 t, hc2 t, hc3 t]
  · intro s t w hw
    fin_cases s
    exacts [hw0 t w hw, hw1 t w hw, hw2 t w hw, hw3 t w hw]

end Centres

/-! ### The rectangle scheme -/

section Scheme

/-- The decomposition of an index `m < 4N` into a side `s` and an exponent `k < N`. -/
def blockIdx (N m : ℕ) : Fin 4 × ℕ :=
  if m < N then (0, m) else if m < N + N then (1, m - N) else
    if m < N + N + N then (2, m - (N + N)) else (3, m - (N + N + N))

lemma sum_range_blockIdx (F : Fin 4 → ℕ → ℂ) (N : ℕ) :
    ∑ m ∈ Finset.range (N + N + N + N), F (blockIdx N m).1 (blockIdx N m).2 =
      ∑ s : Fin 4, ∑ k ∈ Finset.range N, F s k := by
  rw [Finset.sum_range_add, Finset.sum_range_add, Finset.sum_range_add, Fin.sum_univ_four]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_
  · exact Finset.sum_congr rfl fun k hk ↦ by
      simp [blockIdx, Finset.mem_range.mp hk]
  · exact Finset.sum_congr rfl fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      simp [blockIdx, hk']
  · exact Finset.sum_congr rfl fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      simp only [blockIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
      congr 1
      omega
  · exact Finset.sum_congr rfl fun k hk ↦ by
      have hk' := Finset.mem_range.mp hk
      simp only [blockIdx]
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      congr 1
      omega

/-- Far away centres for the four sides of `[p', q']`, relative to `[p, q]`
(`exists_rect_centres`). -/
structure RectCentres (p q p' q' : ℂ) where
  /-- The centres. -/
  c : Fin 4 → ℂ
  /-- The contraction ratios. -/
  θ : Fin 4 → ℝ
  θ_nonneg : ∀ s, 0 ≤ θ s
  θ_lt_one : ∀ s, θ s < 1
  ne : ∀ s t, rectSide p' q' s t ≠ c s
  le : ∀ s t, ∀ w ∈ closedRect p q, ‖w - c s‖ ≤ θ s * ‖rectSide p' q' s t - c s‖

/-- A choice of centres. -/
def RectCentres.choose {p q p' q' : ℂ} (h1 : p'.re < p.re) (h2 : q.re < q'.re)
    (h3 : p'.im < p.im) (h4 : q.im < q'.im) : RectCentres p q p' q' :=
  let h := exists_rect_centres h1 h2 h3 h4
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.1, h.choose_spec.choose_spec.2.1,
    h.choose_spec.choose_spec.2.2.1, h.choose_spec.choose_spec.2.2.2⟩

/-- The coefficient of `(w - c_s)ᵏ` from the side `s`:
`(2πi)⁻¹ ε_s ∫_{side s} (ζ - c_s)^{-(k+1)} g(ζ) dζ`. -/
def rectCoeff (p' q' : ℂ) (c : Fin 4 → ℂ) (s : Fin 4) (k : ℕ) (g : ℂ → ℂ) : ℂ :=
  (2 * π * I)⁻¹ * rectSideε s * ∫ t in rectSideA p' q' s..rectSideB p' q' s,
    (rectSide p' q' s t - c s)⁻¹ ^ (k + 1) * g (rectSide p' q' s t)

lemma norm_rectSideε (s : Fin 4) : ‖rectSideε s‖ = 1 := by
  fin_cases s <;> simp

lemma rectSide_mem_image {p q : ℂ} (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (s : Fin 4) (t : ℝ) :
    rectSide p q s t ∈ rectSide p q s '' Icc (rectSideA p q s) (rectSideB p q s) := by
  have hc1 := clampIcc_mem hre t
  have hc2 := clampIcc_mem him t
  have hi1 := clampIcc_of_mem hc1
  have hi2 := clampIcc_of_mem hc2
  fin_cases s
  · exact ⟨clampIcc p.re q.re t, hc1, by simp [hi1]⟩
  · exact ⟨clampIcc p.re q.re t, hc1, by simp [hi1]⟩
  · exact ⟨clampIcc p.im q.im t, hc2, by simp [hi2]⟩
  · exact ⟨clampIcc p.im q.im t, hc2, by simp [hi2]⟩

/-- The distance between `[p, q]` and the boundary of `[p', q']`, from below. -/
def rectGap (p q p' q' : ℂ) : ℝ :=
  min (min (p.re - p'.re) (q'.re - q.re)) (min (p.im - p'.im) (q'.im - q.im))

lemma rectGap_pos {p q p' q' : ℂ} (h1 : p'.re < p.re) (h2 : q.re < q'.re) (h3 : p'.im < p.im)
    (h4 : q.im < q'.im) : 0 < rectGap p q p' q' := by
  unfold rectGap
  refine lt_min (lt_min ?_ ?_) (lt_min ?_ ?_) <;> linarith

lemma rectGap_le_norm {p q p' q' : ℂ} (h1 : p'.re < p.re) (h2 : q.re < q'.re)
    (h3 : p'.im < p.im) (h4 : q.im < q'.im) (s : Fin 4) (t : ℝ) {w : ℂ}
    (hw : w ∈ closedRect p q) : rectGap p q p' q' ≤ ‖rectSide p' q' s t - w‖ := by
  obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩ := hw
  have hg1 : rectGap p q p' q' ≤ p.re - p'.re := (min_le_left _ _).trans (min_le_left _ _)
  have hg2 : rectGap p q p' q' ≤ q'.re - q.re := (min_le_left _ _).trans (min_le_right _ _)
  have hg3 : rectGap p q p' q' ≤ p.im - p'.im := (min_le_right _ _).trans (min_le_left _ _)
  have hg4 : rectGap p q p' q' ≤ q'.im - q.im := (min_le_right _ _).trans (min_le_right _ _)
  have e0 : rectGap p q p' q' ≤ ‖rectSide p' q' 0 t - w‖ := by
    have := abs_im_le_norm (rectSide p' q' 0 t - w)
    have him : (rectSide p' q' 0 t - w).im = p'.im - w.im := by simp
    rw [him, abs_sub_comm, abs_of_nonneg (by linarith)] at this
    linarith
  have e1 : rectGap p q p' q' ≤ ‖rectSide p' q' 1 t - w‖ := by
    have := abs_im_le_norm (rectSide p' q' 1 t - w)
    have him : (rectSide p' q' 1 t - w).im = q'.im - w.im := by simp
    rw [him, abs_of_nonneg (by linarith)] at this
    linarith
  have e2 : rectGap p q p' q' ≤ ‖rectSide p' q' 2 t - w‖ := by
    have := abs_re_le_norm (rectSide p' q' 2 t - w)
    have hre : (rectSide p' q' 2 t - w).re = q'.re - w.re := by simp
    rw [hre, abs_of_nonneg (by linarith)] at this
    linarith
  have e3 : rectGap p q p' q' ≤ ‖rectSide p' q' 3 t - w‖ := by
    have := abs_re_le_norm (rectSide p' q' 3 t - w)
    have hre : (rectSide p' q' 3 t - w).re = p'.re - w.re := by simp
    rw [hre, abs_sub_comm, abs_of_nonneg (by linarith)] at this
    linarith
  fin_cases s
  exacts [e0, e1, e2, e3]

/-- **The expansion along one side**: for `w ∈ [p, q]`, the Cauchy integral of `g` over the side
`s` of `[p', q']` is the truncated expansion around the centre `c_s` plus a remainder. -/
lemma side_expansion {p q p' q' : ℂ} (h1 : p'.re < p.re) (h2 : q.re < q'.re) (h3 : p'.im < p.im)
    (h4 : q.im < q'.im) (hre : p.re ≤ q.re) (him : p.im ≤ q.im) (C : RectCentres p q p' q')
    {g : ℂ → ℂ} (hg : ∀ ζ ∈ closedRect p' q', ContinuousAt g ζ) {w : ℂ}
    (hw : w ∈ closedRect p q) (s : Fin 4) (N : ℕ) :
    (2 * π * I)⁻¹ * rectSideε s * ∫ t in rectSideA p' q' s..rectSideB p' q' s,
        (rectSide p' q' s t - w)⁻¹ * g (rectSide p' q' s t) =
      ∑ k ∈ Finset.range N, rectCoeff p' q' C.c s k g * (w - C.c s) ^ k +
        (2 * π * I)⁻¹ * rectSideε s * ∫ t in rectSideA p' q' s..rectSideB p' q' s,
          ((w - C.c s) / (rectSide p' q' s t - C.c s)) ^ N * (rectSide p' q' s t - w)⁻¹ *
            g (rectSide p' q' s t) := by
  set γ := rectSide p' q' s with hγ
  set c := C.c s with hc
  have hre' : p'.re ≤ q'.re := by linarith
  have him' : p'.im ≤ q'.im := by linarith
  have hγc : Continuous γ := continuous_rectSide p' q' s
  have hne : ∀ t, γ t - c ≠ 0 := fun t ↦ sub_ne_zero.mpr (C.ne s t)
  have hnw : ∀ t, γ t - w ≠ 0 := fun t h ↦ by
    have h0 := rectGap_le_norm h1 h2 h3 h4 s t hw
    rw [← hγ, h, norm_zero] at h0
    exact (rectGap_pos h1 h2 h3 h4).not_ge h0
  have hgc : Continuous fun t ↦ g (γ t) := continuous_iff_continuousAt.mpr fun t ↦
    (hg _ (rectSide_mem hre' him' s t)).comp hγc.continuousAt
  have hinvc : Continuous fun t ↦ (γ t - c)⁻¹ :=
    continuous_iff_continuousAt.mpr fun t ↦
      ((hγc.sub continuous_const).continuousAt).inv₀ (hne t)
  have hinvw : Continuous fun t ↦ (γ t - w)⁻¹ :=
    continuous_iff_continuousAt.mpr fun t ↦
      ((hγc.sub continuous_const).continuousAt).inv₀ (hnw t)
  -- the pointwise expansion
  have hpt : ∀ t, (γ t - w)⁻¹ * g (γ t) =
      ∑ k ∈ Finset.range N, (w - c) ^ k * ((γ t - c)⁻¹ ^ (k + 1) * g (γ t)) +
        ((w - c) / (γ t - c)) ^ N * (γ t - w)⁻¹ * g (γ t) := fun t ↦ by
    have hid := inv_sub_eq_sum_add (w := w - c) (hne t)
      (fun h ↦ hnw t (by linear_combination h)) N
    rw [show γ t - c - (w - c) = γ t - w by ring] at hid
    conv_lhs => rw [hid]
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have hint1 : ∀ k ∈ Finset.range N, IntervalIntegrable
      (fun t ↦ (w - c) ^ k * ((γ t - c)⁻¹ ^ (k + 1) * g (γ t))) MeasureTheory.volume
      (rectSideA p' q' s) (rectSideB p' q' s) := fun k _ ↦
    (continuous_const.mul ((hinvc.pow _).mul hgc)).intervalIntegrable _ _
  have hint2 : IntervalIntegrable
      (fun t ↦ ((w - c) / (γ t - c)) ^ N * (γ t - w)⁻¹ * g (γ t)) MeasureTheory.volume
      (rectSideA p' q' s) (rectSideB p' q' s) :=
    ((((continuous_const.div (hγc.sub continuous_const) hne).pow N).mul hinvw).mul
      hgc).intervalIntegrable _ _
  rw [integral_congr (g := fun t ↦ ∑ k ∈ Finset.range N, (w - c) ^ k *
      ((γ t - c)⁻¹ ^ (k + 1) * g (γ t)) + ((w - c) / (γ t - c)) ^ N * (γ t - w)⁻¹ * g (γ t))
      fun t _ ↦ hpt t]
  have hint1' : IntervalIntegrable (fun t ↦ ∑ k ∈ Finset.range N,
      (w - c) ^ k * ((γ t - c)⁻¹ ^ (k + 1) * g (γ t))) MeasureTheory.volume
      (rectSideA p' q' s) (rectSideB p' q' s) :=
    (continuous_finsetSum _ fun k _ ↦
      continuous_const.mul ((hinvc.pow _).mul hgc)).intervalIntegrable _ _
  rw [integral_add hint1' hint2, integral_finsetSum hint1]
  simp only [integral_const_mul]
  rw [mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [rectCoeff, ← hγ, ← hc]
  ring

/-- The approximating polynomials `(w - c_s)ᵏ` of the rectangle scheme. -/
def rectScheme.ψ (c : Fin 4 → ℂ) (N m : ℕ) (w : ℂ) : ℂ :=
  (w - c (blockIdx N m).1) ^ (blockIdx N m).2

/-- The coefficients of the rectangle scheme. -/
def rectScheme.coeff (p' q' : ℂ) (c : Fin 4 → ℂ) (N m : ℕ) (g : ℂ → ℂ) : ℂ :=
  rectCoeff p' q' c (blockIdx N m).1 (blockIdx N m).2 g

/-- The error bound of the rectangle scheme. -/
def rectScheme.err (p q p' q' : ℂ) (θ : Fin 4 → ℝ) (N : ℕ) : ℝ :=
  ∑ s : Fin 4, (2 * π)⁻¹ *
    (|rectSideB p' q' s - rectSideA p' q' s| * (θ s ^ N * (rectGap p q p' q')⁻¹))

/-- **Polynomial approximation on a rectangle**, with holomorphic parameters: for closed
rectangles `[p, q] ⊆ interior [p', q']` (`[p, q]` nonempty), the Cauchy integral over the boundary
of `[p', q']`, with the kernel expanded around a far away centre on each side, is a one-variable
approximation scheme on `[p, q]` by polynomials, for functions holomorphic on `[p', q']`. -/
def rectScheme {p q p' q' : ℂ} (Ω : Set ℂ) (h1 : p'.re < p.re) (h2 : q.re < q'.re)
    (h3 : p'.im < p.im) (h4 : q.im < q'.im) (hre : p.re ≤ q.re) (him : p.im ≤ q.im) :
    ApproxScheme (closedRect p q) (closedRect p' q') Ω :=
  let C := RectCentres.choose h1 h2 h3 h4
  { Γ := closedRect p' q'
    isCompact_Γ := isCompact_closedRect p' q'
    Γ_subset := subset_rfl
    card := fun N ↦ N + N + N + N
    ψ := rectScheme.ψ C.c
    analyticAt_ψ := fun N m _ _ ↦ (analyticAt_id.sub analyticAt_const).pow _
    coeff := rectScheme.coeff p' q' C.c
    analyticAt_coeff := by
      intro σ _ _ N m j h z hh
      have hre' : p'.re ≤ q'.re := by linarith
      have him' : p'.im ≤ q'.im := by linarith
      set s := (blockIdx N m).1
      set k := (blockIdx N m).2
      simp only [rectScheme.coeff, rectCoeff]
      refine analyticAt_const.mul ?_
      have hK : IsCompact (rectSide p' q' s '' Icc (rectSideA p' q' s) (rectSideB p' q' s)) :=
        isCompact_Icc.image (continuous_rectSide p' q' s)
      have := analyticAt_intervalIntegral_param (σ := σ)
        (G := fun z ζ ↦ (ζ - C.c s)⁻¹ ^ (k + 1) * h (Function.update z j ζ))
        (continuous_rectSide p' q' s) (φ := fun _ ↦ (1 : ℂ)) continuous_const hK
        (rectSide_mem_image hre' him' s) (rectSideA p' q' s) (rectSideB p' q' s) (z₀ := z)
        (fun ζ hζ ↦ by
          obtain ⟨t, -, rfl⟩ := hζ
          have hne : rectSide p' q' s t - C.c s ≠ 0 := sub_ne_zero.mpr (C.ne s t)
          exact (((analyticAt_snd.sub analyticAt_const).inv hne).pow _).mul
            (AnalyticAt.comp (g := h) (f := fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2)
              (hh _ (rectSide_mem hre' him' s t)) (analyticAt_update_prod j _)))
      simpa only [one_smul] using this
    err := rectScheme.err p q p' q' C.θ
    tendsto_err := by
      have h0 : Tendsto (fun N : ℕ ↦ rectScheme.err p q p' q' C.θ N) atTop
          (𝓝 (∑ _s : Fin 4, (0 : ℝ))) :=
        tendsto_finsetSum _ fun s _ ↦ by
          have hθ := tendsto_pow_atTop_nhds_zero_of_lt_one (C.θ_nonneg s) (C.θ_lt_one s)
          simpa using ((hθ.mul_const (rectGap p q p' q')⁻¹).const_mul
            |rectSideB p' q' s - rectSideA p' q' s|).const_mul (2 * π)⁻¹
      simpa using h0
    approx := by
      intro N g M hg hM w hw
      have hre' : p'.re ≤ q'.re := by linarith
      have him' : p'.im ≤ q'.im := by linarith
      obtain ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩ := hw
      have hwK : w ∈ closedRect p q := ⟨⟨hw1, hw2⟩, ⟨hw3, hw4⟩⟩
      have hwL : w ∈ closedRect p' q' :=
        ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM w hwL)
      have hδ := rectGap_pos h1 h2 h3 h4
      have hgc : ∀ ζ ∈ closedRect p' q', ContinuousAt g ζ := fun ζ hζ ↦ (hg ζ hζ).continuousAt
      -- Cauchy's formula and the four sides
      have hcauchy := rectIntegral_sub_inv_mul (f := g) (p := p') (q := q') (w := w)
        (by linarith) (by linarith) (by linarith) (by linarith) hg
      rw [rectIntegral_eq_sum_sides hre' him'] at hcauchy
      have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
      have hgw : g w = ∑ s : Fin 4, (2 * π * I)⁻¹ * rectSideε s *
          ∫ t in rectSideA p' q' s..rectSideB p' q' s,
            (rectSide p' q' s t - w)⁻¹ * g (rectSide p' q' s t) := by
        have e : ∑ s : Fin 4, (2 * π * I)⁻¹ * rectSideε s *
            ∫ t in rectSideA p' q' s..rectSideB p' q' s,
              (rectSide p' q' s t - w)⁻¹ * g (rectSide p' q' s t) =
            (2 * π * I)⁻¹ * ∑ s : Fin 4, rectSideε s *
              ∫ t in rectSideA p' q' s..rectSideB p' q' s,
                (rectSide p' q' s t - w)⁻¹ * g (rectSide p' q' s t) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ ↦ by ring
        rw [e, hcauchy, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
      simp only [side_expansion h1 h2 h3 h4 hre him C hgc hwK _ N, Finset.sum_add_distrib] at hgw
      have hsum : ∑ m ∈ Finset.range (N + N + N + N),
          rectScheme.coeff p' q' C.c N m g * rectScheme.ψ C.c N m w =
          ∑ s : Fin 4, ∑ k ∈ Finset.range N, rectCoeff p' q' C.c s k g * (w - C.c s) ^ k :=
        sum_range_blockIdx (fun s k ↦ rectCoeff p' q' C.c s k g * (w - C.c s) ^ k) N
      change ‖g w - ∑ m ∈ Finset.range (N + N + N + N),
          rectScheme.coeff p' q' C.c N m g * rectScheme.ψ C.c N m w‖ ≤
        M * rectScheme.err p q p' q' C.θ N
      rw [hsum, hgw, add_sub_cancel_left, rectScheme.err, Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ ↦ ?_)
      -- the remainder of one side
      have hnorm : ‖(2 * π * I : ℂ)⁻¹ * rectSideε s‖ = (2 * π)⁻¹ := by
        rw [norm_mul, norm_rectSideε, mul_one]
        simp [Real.pi_pos.le]
      rw [norm_mul, hnorm]
      have hbound : ∀ t ∈ Ι (rectSideA p' q' s) (rectSideB p' q' s),
          ‖((w - C.c s) / (rectSide p' q' s t - C.c s)) ^ N * (rectSide p' q' s t - w)⁻¹ *
            g (rectSide p' q' s t)‖ ≤ C.θ s ^ N * (rectGap p q p' q')⁻¹ * M := fun t _ ↦ by
        have hpos : 0 < ‖rectSide p' q' s t - C.c s‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr (C.ne s t))
        have hratio : ‖w - C.c s‖ / ‖rectSide p' q' s t - C.c s‖ ≤ C.θ s :=
          div_le_of_le_mul₀ hpos.le (C.θ_nonneg s) (C.le s t w hwK)
        have hgap := rectGap_le_norm h1 h2 h3 h4 s t hwK
        rw [norm_mul, norm_mul, norm_pow, norm_div, norm_inv]
        refine mul_le_mul (mul_le_mul (pow_le_pow_left₀ (by positivity) hratio N)
          (inv_anti₀ hδ hgap) (by positivity) (pow_nonneg (C.θ_nonneg s) N))
          (hM _ (rectSide_mem hre' him' s t)) (norm_nonneg _) (by
            have := C.θ_nonneg s
            positivity)
      calc (2 * π)⁻¹ * ‖∫ t in rectSideA p' q' s..rectSideB p' q' s,
            ((w - C.c s) / (rectSide p' q' s t - C.c s)) ^ N * (rectSide p' q' s t - w)⁻¹ *
              g (rectSide p' q' s t)‖
          ≤ (2 * π)⁻¹ * (C.θ s ^ N * (rectGap p q p' q')⁻¹ * M *
            |rectSideB p' q' s - rectSideA p' q' s|) :=
            mul_le_mul_of_nonneg_left (norm_integral_le_of_norm_le_const hbound) (by positivity)
        _ = M * ((2 * π)⁻¹ * (|rectSideB p' q' s - rectSideA p' q' s| *
            (C.θ s ^ N * (rectGap p q p' q')⁻¹))) := by ring }

end Scheme

end AnalyticGeometry
