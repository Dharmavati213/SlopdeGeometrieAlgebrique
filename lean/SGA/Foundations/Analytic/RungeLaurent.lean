/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Cauchy's formula on an annulus and truncated Laurent expansions

Let `0 ≤ r < R` and let `f : ℂ → ℂ` be complex differentiable at every point of the closed
annulus `A(r, R) = {r ≤ |ζ| ≤ R}` (the closed disc of radius `R` when `r = 0`). For `r < |w| < R`
(or `|w| < R` when `r = 0`):

* **Cauchy's formula on the annulus** (`AnalyticGeometry.circleIntegral_sub_circleIntegral_eq`):
  `∮_{|ζ|=R} f(ζ)/(ζ - w) dζ - ∮_{|ζ|=r} f(ζ)/(ζ - w) dζ = 2πi f(w)`;
* **Truncated Laurent expansion with explicit remainder**
  (`AnalyticGeometry.eq_laurentTrunc_add`, `AnalyticGeometry.norm_sub_laurentTrunc_le`): with
  `aₖ = (2πi)⁻¹ ∮_{|ζ|=R} f(ζ) ζ^{-k-1} dζ` and `bₖ = (2πi)⁻¹ ∮_{|ζ|=r} f(ζ) ζ^k dζ`,
  `|f(w) - ∑_{k<N} aₖ wᵏ - ∑_{k<N} bₖ w^{-k-1}|` is at most
  `M (R (|w|/R)^N / (R - |w|) + r (r/|w|)^N / (|w| - r))` if `|f| ≤ M` on the two circles. Only
  finite geometric sums are used.
* A version uniform on a smaller closed annulus `A(r₀, R₀)`, `r < r₀`, `R₀ < R`
  (`AnalyticGeometry.norm_sub_laurentTrunc_le_of_mem`), and the choice of a truncation order
  (`AnalyticGeometry.exists_laurentTrunc_order`).

These are the one-variable inputs of Runge approximation on products of discs and annuli
(`SGA.Foundations.Analytic.RungeProduct`).

Reference: Ahlfors, *Complex analysis*, 5.1.3 (Laurent series); Conway, *Functions of one complex
variable*, V.1.11.
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

/-! ### Closed annuli -/

/-- The closed annulus `{z | r ≤ ‖z‖ ≤ R}` in `ℂ`, centred at `0`; for `r ≤ 0` it is the closed
disc of radius `R`. -/
def closedAnnulus (r R : ℝ) : Set ℂ := {z | r ≤ ‖z‖ ∧ ‖z‖ ≤ R}

lemma mem_closedAnnulus {r R : ℝ} {z : ℂ} : z ∈ closedAnnulus r R ↔ r ≤ ‖z‖ ∧ ‖z‖ ≤ R :=
  Iff.rfl

lemma isCompact_closedAnnulus (r R : ℝ) : IsCompact (closedAnnulus r R) :=
  (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const))
    fun _ hz ↦ mem_closedBall_zero_iff.mpr hz.2

/-- `A(r, R)` is empty unless `0 ≤ R` and `r ≤ R`. -/
lemma closedAnnulus_eq_empty {r R : ℝ} (h : ¬(0 ≤ R ∧ r ≤ R)) : closedAnnulus r R = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun z hz ↦ h ⟨(norm_nonneg z).trans hz.2, hz.1.trans hz.2⟩

lemma closedAnnulus_mono {r R r' R' : ℝ} (hr : r' ≤ r) (hR : R ≤ R') :
    closedAnnulus r R ⊆ closedAnnulus r' R' :=
  fun _ hz ↦ ⟨hr.trans hz.1, hz.2.trans hR⟩

/-- The open annulus `r < ‖z‖ < R` lies in the interior of the closed one. -/
lemma subset_interior_closedAnnulus (r R : ℝ) :
    {z : ℂ | r < ‖z‖ ∧ ‖z‖ < R} ⊆ interior (closedAnnulus r R) :=
  interior_maximal (fun _ hz ↦ ⟨hz.1.le, hz.2.le⟩)
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))

/-- For `r ≤ 0`, the open disc of radius `R` lies in the interior of `A(r, R)`. -/
lemma ball_subset_interior_closedAnnulus {r : ℝ} (hr : r ≤ 0) (R : ℝ) :
    ball (0 : ℂ) R ⊆ interior (closedAnnulus r R) :=
  interior_maximal (fun z hz ↦ ⟨hr.trans (norm_nonneg z), (mem_ball_zero_iff.mp hz).le⟩) isOpen_ball

lemma sphere_subset_closedAnnulus_outer {r R : ℝ} (h : r ≤ R) :
    sphere (0 : ℂ) R ⊆ closedAnnulus r R := fun z hz ↦ by
  rw [mem_sphere_zero_iff_norm] at hz
  exact ⟨hz ▸ h, hz.le⟩

lemma sphere_subset_closedAnnulus_inner {r R : ℝ} (h : r ≤ R) :
    sphere (0 : ℂ) r ⊆ closedAnnulus r R := fun z hz ↦ by
  rw [mem_sphere_zero_iff_norm] at hz
  exact ⟨hz.ge, hz ▸ h⟩

/-! ### Cauchy's formula on an annulus -/

/-- `∮_{|ζ| = ρ} (ζ - w)⁻¹ dζ = 0` when `ρ < |w|`. -/
lemma circleIntegral_sub_inv_eq_zero {ρ : ℝ} {w : ℂ} (hρ : 0 ≤ ρ) (hw : ρ < ‖w‖) :
    (∮ ζ in C(0, ρ), (ζ - w)⁻¹) = 0 := by
  have hne : ∀ ζ ∈ closedBall (0 : ℂ) ρ, ζ - w ≠ 0 := fun ζ hζ h ↦ by
    rw [sub_eq_zero] at h
    subst h
    rw [mem_closedBall_zero_iff] at hζ
    linarith
  exact circleIntegral_eq_zero_of_differentiable_on_off_countable hρ countable_empty
    (fun ζ hζ ↦ ((continuousAt_id.sub continuousAt_const).inv₀ (hne ζ hζ)).continuousWithinAt)
    fun ζ hζ ↦ (differentiableAt_id.sub_const w).inv (hne ζ (ball_subset_closedBall hζ.1))

/-- On a circle not through `w`, the integral of `dslope f w` splits. -/
private lemma circleIntegral_dslope {f : ℂ → ℂ} {ρ : ℝ} {w : ℂ} (hρ : 0 ≤ ρ) (hw : ‖w‖ ≠ ρ)
    (hf : ContinuousOn f (sphere 0 ρ)) :
    (∮ ζ in C(0, ρ), dslope f w ζ) =
      (∮ ζ in C(0, ρ), (ζ - w)⁻¹ * f ζ) - (∮ ζ in C(0, ρ), (ζ - w)⁻¹) * f w := by
  have hne : ∀ ζ ∈ sphere (0 : ℂ) ρ, ζ ≠ w := fun ζ hζ h ↦ by
    rw [mem_sphere_zero_iff_norm, h] at hζ
    exact hw hζ
  have hi : ContinuousOn (fun ζ : ℂ ↦ (ζ - w)⁻¹) (sphere 0 ρ) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ ↦ sub_ne_zero.mpr (hne ζ hζ)
  calc (∮ ζ in C(0, ρ), dslope f w ζ)
      = ∮ ζ in C(0, ρ), ((ζ - w)⁻¹ * f ζ - (ζ - w)⁻¹ * f w) := by
        refine circleIntegral.integral_congr hρ fun ζ hζ ↦ ?_
        rw [dslope_of_ne f (hne ζ hζ), slope_def_field]
        ring
    _ = _ := by
        rw [circleIntegral.integral_sub (f := fun ζ ↦ (ζ - w)⁻¹ * f ζ)
          (g := fun ζ ↦ (ζ - w)⁻¹ * f w) ((hi.mul hf).circleIntegrable hρ)
          ((hi.mul continuousOn_const).circleIntegrable hρ)]
        congr 1
        exact circleIntegral.integral_smul_const _ _ _ _

/-- **Cauchy's integral formula on a closed annulus** `A(r, R)` (on the closed disc of radius `R`
if `r = 0`): if `f` is complex differentiable at every point of `A(r, R)` and `r < |w| < R` (or
`|w| < R` and `r = 0`), then
`∮_{|ζ|=R} (ζ - w)⁻¹ f(ζ) dζ - ∮_{|ζ|=r} (ζ - w)⁻¹ f(ζ) dζ = 2πi f(w)`. -/
theorem circleIntegral_sub_circleIntegral_eq {f : ℂ → ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedAnnulus r R, DifferentiableAt ℂ f ζ) {w : ℂ} (hwR : ‖w‖ < R)
    (hwr : r = 0 ∨ r < ‖w‖) :
    (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ) - (∮ ζ in C(0, r), (ζ - w)⁻¹ * f ζ) =
      2 * π * I * f w := by
  rcases hr.eq_or_lt with rfl | hr0
  · rw [circleIntegral.integral_radius_zero, sub_zero]
    have hd : DifferentiableOn ℂ f (closedBall 0 R) := fun ζ hζ ↦
      (hf ζ ⟨norm_nonneg ζ, mem_closedBall_zero_iff.mp hζ⟩).differentiableWithinAt
    simpa only [smul_eq_mul] using hd.circleIntegral_sub_inv_smul (mem_ball_zero_iff.mpr hwR)
  have hwr' : r < ‖w‖ := hwr.resolve_left hr0.ne'
  have hrR : r ≤ R := (hwr'.trans hwR).le
  have hRpos : 0 < R := hr0.trans_le hrR
  have hfw : DifferentiableAt ℂ f w := hf w ⟨hwr'.le, hwR.le⟩
  have hgc : ContinuousOn (dslope f w) (closedBall 0 R \ ball 0 r) := fun ζ hζ ↦ by
    have hζA : ζ ∈ closedAnnulus r R :=
      ⟨by simpa using hζ.2, mem_closedBall_zero_iff.mp hζ.1⟩
    by_cases hζw : ζ = w
    · subst hζw
      exact (continuousAt_dslope_same.mpr hfw).continuousWithinAt
    · exact ((continuousAt_dslope_of_ne hζw).mpr (hf ζ hζA).continuousAt).continuousWithinAt
  have hgd : ∀ ζ ∈ (ball 0 R \ closedBall 0 r) \ {w}, DifferentiableAt ℂ (dslope f w) ζ :=
    fun ζ hζ ↦ (differentiableAt_dslope_of_ne hζ.2).mpr
      (hf ζ ⟨(not_le.mp (by simpa using hζ.1.2)).le, (mem_ball_zero_iff.mp hζ.1.1).le⟩)
  have h := circleIntegral_eq_of_differentiable_on_annulus_off_countable hr0 hrR
    (countable_singleton w) hgc hgd
  have hcR : ContinuousOn f (sphere 0 R) := fun ζ hζ ↦
    (hf ζ (sphere_subset_closedAnnulus_outer hrR hζ)).continuousAt.continuousWithinAt
  have hcr : ContinuousOn f (sphere 0 r) := fun ζ hζ ↦
    (hf ζ (sphere_subset_closedAnnulus_inner hrR hζ)).continuousAt.continuousWithinAt
  rw [circleIntegral_dslope hRpos.le hwR.ne hcR, circleIntegral_dslope hr0.le hwr'.ne' hcr,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_zero_iff.mpr hwR),
    circleIntegral_sub_inv_eq_zero hr0.le hwr', zero_mul, sub_zero] at h
  linear_combination h

/-! ### Truncated Laurent expansions -/

/-- The finite geometric expansion of the Cauchy kernel: for `ζ ≠ 0`, `ζ ≠ w`,
`(ζ - w)⁻¹ = ∑_{k < N} wᵏ ζ^{-(k+1)} + (w/ζ)ᴺ (ζ - w)⁻¹`. -/
lemma inv_sub_eq_sum_add {ζ w : ℂ} (hζ : ζ ≠ 0) (hζw : ζ ≠ w) (N : ℕ) :
    (ζ - w)⁻¹ = ∑ k ∈ Finset.range N, w ^ k * ζ⁻¹ ^ (k + 1) + (w / ζ) ^ N * (ζ - w)⁻¹ := by
  have hsub : ζ - w ≠ 0 := sub_ne_zero.mpr hζw
  have hsum : ∑ k ∈ Finset.range N, w ^ k * ζ⁻¹ ^ (k + 1) =
      ζ⁻¹ * ∑ k ∈ Finset.range N, (w / ζ) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [div_eq_mul_inv, mul_pow, pow_succ]
    ring
  have h1 : (ζ - w) * ζ⁻¹ = 1 - w / ζ := by
    field_simp
  have key : (ζ - w) * (ζ⁻¹ * ∑ k ∈ Finset.range N, (w / ζ) ^ k) = 1 - (w / ζ) ^ N := by
    rw [← mul_assoc, h1, mul_neg_geom_sum]
  rw [hsum]
  calc (ζ - w)⁻¹ = (ζ - w)⁻¹ * ((ζ - w) * (ζ⁻¹ * ∑ k ∈ Finset.range N, (w / ζ) ^ k)) +
        (w / ζ) ^ N * (ζ - w)⁻¹ := by rw [key]; ring
    _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hsub, one_mul]

/-- The nonnegative Laurent coefficients `aₖ = (2πi)⁻¹ ∮_{|ζ|=R} ζ^{-(k+1)} f(ζ) dζ`. -/
def laurentCoeffPos (f : ℂ → ℂ) (R : ℝ) (k : ℕ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, R), ζ⁻¹ ^ (k + 1) * f ζ

/-- The negative Laurent coefficients `bₖ = (2πi)⁻¹ ∮_{|ζ|=r} ζᵏ f(ζ) dζ` (coefficient of
`w^{-(k+1)}`). They vanish for `r = 0`. -/
def laurentCoeffNeg (f : ℂ → ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  (2 * π * I)⁻¹ * ∮ ζ in C(0, r), ζ ^ k * f ζ

/-- The truncated Laurent expansion `∑_{k<N} aₖ wᵏ + ∑_{k<N} bₖ w^{-(k+1)}`. -/
def laurentTrunc (f : ℂ → ℂ) (r R : ℝ) (N : ℕ) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N, laurentCoeffPos f R k * w ^ k +
    ∑ k ∈ Finset.range N, laurentCoeffNeg f r k * w⁻¹ ^ (k + 1)

@[simp] lemma laurentCoeffNeg_zero (f : ℂ → ℂ) (k : ℕ) : laurentCoeffNeg f 0 k = 0 := by
  simp [laurentCoeffNeg]

/-- **Truncated Laurent expansion with integral remainder.** -/
theorem eq_laurentTrunc_add {f : ℂ → ℂ} {r R : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedAnnulus r R, DifferentiableAt ℂ f ζ) {w : ℂ} (hwR : ‖w‖ < R)
    (hwr : r = 0 ∨ r < ‖w‖) (N : ℕ) :
    f w = laurentTrunc f r R N w + (2 * π * I)⁻¹ *
      ((∮ ζ in C(0, R), (w / ζ) ^ N * (ζ - w)⁻¹ * f ζ) +
        ∮ ζ in C(0, r), (ζ / w) ^ N * (w - ζ)⁻¹ * f ζ) := by
  have hRpos : 0 < R := (norm_nonneg w).trans_lt hwR
  have hrR : r ≤ R := by
    rcases hwr with h | h
    · exact h ▸ hRpos.le
    · exact (h.trans hwR).le
  have hcR : ContinuousOn f (sphere 0 R) := fun ζ hζ ↦
    (hf ζ (sphere_subset_closedAnnulus_outer hrR hζ)).continuousAt.continuousWithinAt
  have hcr : ContinuousOn f (sphere 0 r) := fun ζ hζ ↦
    (hf ζ (sphere_subset_closedAnnulus_inner hrR hζ)).continuousAt.continuousWithinAt
  have hC := circleIntegral_sub_circleIntegral_eq hr hf hwR hwr
  -- the outer integral
  have hneR : ∀ ζ ∈ sphere (0 : ℂ) R, ζ ≠ 0 ∧ ζ ≠ w := fun ζ hζ ↦ by
    rw [mem_sphere_zero_iff_norm] at hζ
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · rw [h, norm_zero] at hζ
      exact hRpos.ne hζ
    · rw [h] at hζ
      exact hwR.ne hζ
  have hinvR : ContinuousOn (fun ζ : ℂ ↦ ζ⁻¹) (sphere 0 R) :=
    continuousOn_id.inv₀ fun ζ hζ ↦ (hneR ζ hζ).1
  have hsubR : ContinuousOn (fun ζ : ℂ ↦ (ζ - w)⁻¹) (sphere 0 R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ ↦ sub_ne_zero.mpr (hneR ζ hζ).2
  have hA : (∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ) =
      (∑ k ∈ Finset.range N, w ^ k * (∮ ζ in C(0, R), ζ⁻¹ ^ (k + 1) * f ζ)) +
        ∮ ζ in C(0, R), (w / ζ) ^ N * (ζ - w)⁻¹ * f ζ := by
    rw [circleIntegral.integral_congr hRpos.le (g := fun ζ ↦
      ∑ k ∈ Finset.range N, w ^ k * (ζ⁻¹ ^ (k + 1) * f ζ) + (w / ζ) ^ N * (ζ - w)⁻¹ * f ζ)
      fun ζ hζ ↦ by
        conv_lhs => rw [inv_sub_eq_sum_add (hneR ζ hζ).1 (hneR ζ hζ).2 N]
        rw [add_mul, Finset.sum_mul]
        simp only [mul_assoc]]
    rw [circleIntegral.integral_add, circleIntegral.integral_fun_sum]
    · simp only [circleIntegral.integral_const_mul]
    · exact fun k _ ↦ (continuousOn_const.mul ((hinvR.pow _).mul hcR)).circleIntegrable hRpos.le
    · exact (continuousOn_finsetSum _ fun k _ ↦
        continuousOn_const.mul ((hinvR.pow _).mul hcR)).circleIntegrable hRpos.le
    · exact (((continuousOn_const.div continuousOn_id fun ζ hζ ↦ (hneR ζ hζ).1).pow _).mul
        hsubR |>.mul hcR).circleIntegrable hRpos.le
  -- the inner integral
  have hB : -(∮ ζ in C(0, r), (ζ - w)⁻¹ * f ζ) =
      (∑ k ∈ Finset.range N, w⁻¹ ^ (k + 1) * (∮ ζ in C(0, r), ζ ^ k * f ζ)) +
        ∮ ζ in C(0, r), (ζ / w) ^ N * (w - ζ)⁻¹ * f ζ := by
    rcases hr.eq_or_lt with rfl | hr0
    · simp [circleIntegral.integral_radius_zero]
    have hwr' : r < ‖w‖ := hwr.resolve_left hr0.ne'
    have hw0 : w ≠ 0 := norm_pos_iff.mp (hr0.trans hwr')
    have hner : ∀ ζ ∈ sphere (0 : ℂ) r, w ≠ ζ := fun ζ hζ h ↦ by
      rw [mem_sphere_zero_iff_norm, ← h] at hζ
      exact hwr'.ne' hζ
    have hsubr : ContinuousOn (fun ζ : ℂ ↦ (w - ζ)⁻¹) (sphere 0 r) :=
      (continuousOn_const.sub continuousOn_id).inv₀ fun ζ hζ ↦ sub_ne_zero.mpr (hner ζ hζ)
    have hsubr' : ContinuousOn (fun ζ : ℂ ↦ (ζ - w)⁻¹) (sphere 0 r) :=
      (continuousOn_id.sub continuousOn_const).inv₀ fun ζ hζ ↦
        sub_ne_zero.mpr fun h ↦ hner ζ hζ h.symm
    have hneg : (∮ ζ in C(0, r), (ζ - w)⁻¹ * f ζ) + ∮ ζ in C(0, r), (w - ζ)⁻¹ * f ζ = 0 := by
      rw [← circleIntegral.integral_add (f := fun ζ ↦ (ζ - w)⁻¹ * f ζ)
        (g := fun ζ ↦ (w - ζ)⁻¹ * f ζ) (hsubr'.mul hcr |>.circleIntegrable hr0.le)
        (hsubr.mul hcr |>.circleIntegrable hr0.le)]
      rw [circleIntegral.integral_congr hr0.le (g := fun _ ↦ (0 : ℂ)) fun ζ hζ ↦ by
        simp only
        rw [← add_mul, ← neg_sub w ζ, inv_neg, neg_add_cancel, zero_mul]]
      simp [circleIntegral]
    rw [neg_eq_of_add_eq_zero_right hneg]
    rw [circleIntegral.integral_congr hr0.le (g := fun ζ ↦
      ∑ k ∈ Finset.range N, w⁻¹ ^ (k + 1) * (ζ ^ k * f ζ) + (ζ / w) ^ N * (w - ζ)⁻¹ * f ζ)
      fun ζ hζ ↦ by
        conv_lhs => rw [inv_sub_eq_sum_add hw0 (hner ζ hζ) N]
        rw [add_mul, Finset.sum_mul]
        congr 1
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring]
    rw [circleIntegral.integral_add, circleIntegral.integral_fun_sum]
    · simp only [circleIntegral.integral_const_mul]
    · exact fun k _ ↦ (continuousOn_const.mul ((continuousOn_id.pow _).mul hcr)).circleIntegrable
        hr0.le
    · exact (continuousOn_finsetSum _ fun k _ ↦
        continuousOn_const.mul ((continuousOn_id.pow _).mul hcr)).circleIntegrable hr0.le
    · exact (((continuousOn_id.div continuousOn_const fun _ _ ↦ hw0).pow _).mul hsubr |>.mul
        hcr).circleIntegrable hr0.le
  have h2π : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  have hfw : f w = (2 * π * I)⁻¹ * ((∮ ζ in C(0, R), (ζ - w)⁻¹ * f ζ) +
      -(∮ ζ in C(0, r), (ζ - w)⁻¹ * f ζ)) := by
    rw [← sub_eq_add_neg, hC, ← mul_assoc, inv_mul_cancel₀ h2π, one_mul]
  have e1 : ∑ k ∈ Finset.range N, (2 * π * I)⁻¹ * (∮ ζ in C(0, R), ζ⁻¹ ^ (k + 1) * f ζ) * w ^ k =
      (2 * π * I)⁻¹ * ∑ k ∈ Finset.range N, w ^ k * (∮ ζ in C(0, R), ζ⁻¹ ^ (k + 1) * f ζ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  have e2 : ∑ k ∈ Finset.range N, (2 * π * I)⁻¹ * (∮ ζ in C(0, r), ζ ^ k * f ζ) * w⁻¹ ^ (k + 1) =
      (2 * π * I)⁻¹ * ∑ k ∈ Finset.range N, w⁻¹ ^ (k + 1) * (∮ ζ in C(0, r), ζ ^ k * f ζ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ by ring
  rw [hfw, hA, hB]
  simp only [laurentTrunc, laurentCoeffPos, laurentCoeffNeg]
  rw [e1, e2]
  ring

/-- **Truncated Laurent expansion with an explicit error bound.** If `f` is complex differentiable
on the closed annulus `A(r, R)` (`0 ≤ r`, the closed disc for `r = 0`) and `|f| ≤ M` on the two
boundary circles, then for `r < |w| < R` (or `|w| < R` if `r = 0`)
`|f(w) - laurentTrunc f r R N w| ≤ R (|w|/R)ᴺ (R - |w|)⁻¹ M + r (r/|w|)ᴺ (|w| - r)⁻¹ M`. -/
theorem norm_sub_laurentTrunc_le {f : ℂ → ℂ} {r R M : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedAnnulus r R, DifferentiableAt ℂ f ζ)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) R ∪ sphere 0 r, ‖f ζ‖ ≤ M) {w : ℂ} (hwR : ‖w‖ < R)
    (hwr : r = 0 ∨ r < ‖w‖) (N : ℕ) :
    ‖f w - laurentTrunc f r R N w‖ ≤
      R * ((‖w‖ / R) ^ N * (R - ‖w‖)⁻¹ * M) + r * ((r / ‖w‖) ^ N * (‖w‖ - r)⁻¹ * M) := by
  have hRpos : 0 < R := (norm_nonneg w).trans_lt hwR
  rw [eq_laurentTrunc_add hr hf hwR hwr N, add_sub_cancel_left, mul_add]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [← smul_eq_mul]
    refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hRpos.le
      fun ζ hζ ↦ ?_
    have hζR : ‖ζ‖ = R := mem_sphere_zero_iff_norm.mp hζ
    have hd : R - ‖w‖ ≤ ‖ζ - w‖ := by
      have := norm_sub_norm_le ζ w
      rwa [hζR] at this
    have hM' := hM ζ (Or.inl hζ)
    rw [norm_mul, norm_mul, norm_pow, norm_div, hζR, norm_inv]
    gcongr
  · rcases hr.eq_or_lt with rfl | hr0
    · simp [circleIntegral.integral_radius_zero]
    have hwr' : r < ‖w‖ := hwr.resolve_left hr0.ne'
    rw [← smul_eq_mul]
    refine circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hr0.le
      fun ζ hζ ↦ ?_
    have hζr : ‖ζ‖ = r := mem_sphere_zero_iff_norm.mp hζ
    have hd : ‖w‖ - r ≤ ‖w - ζ‖ := by
      have := norm_sub_norm_le w ζ
      rwa [hζr] at this
    have hM' := hM ζ (Or.inr hζ)
    rw [norm_mul, norm_mul, norm_pow, norm_div, hζr, norm_inv]
    gcongr

/-- **Uniform truncation error on a smaller closed annulus**: if `f` is complex differentiable on
`A(r, R)`, `|f| ≤ M` on its boundary circles, `w ∈ A(r₀, R₀)` with `R₀ < R` and either `r = 0` or
`0 < r < r₀`, then
`|f(w) - laurentTrunc f r R N w| ≤ M (R (R - R₀)⁻¹ (R₀/R)ᴺ + r (r₀ - r)⁻¹ (r/r₀)ᴺ)`. -/
theorem norm_sub_laurentTrunc_le_of_mem {f : ℂ → ℂ} {r R r₀ R₀ M : ℝ} (hr : 0 ≤ r)
    (hf : ∀ ζ ∈ closedAnnulus r R, DifferentiableAt ℂ f ζ)
    (hM : ∀ ζ ∈ sphere (0 : ℂ) R ∪ sphere 0 r, ‖f ζ‖ ≤ M) (hRR : R₀ < R)
    (hrr : r = 0 ∨ r < r₀) {w : ℂ} (hw : w ∈ closedAnnulus r₀ R₀) (N : ℕ) :
    ‖f w - laurentTrunc f r R N w‖ ≤
      M * (R * (R - R₀)⁻¹ * (R₀ / R) ^ N + r * (r₀ - r)⁻¹ * (r / r₀) ^ N) := by
  have hwR : ‖w‖ < R := hw.2.trans_lt hRR
  have hRpos : 0 < R := (norm_nonneg w).trans_lt hwR
  have hR₀ : 0 ≤ R₀ := (norm_nonneg w).trans hw.2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (R : ℂ) (Or.inl (by
    simp [abs_of_pos hRpos])))
  have hwr : r = 0 ∨ r < ‖w‖ := hrr.imp_right fun h ↦ h.trans_le hw.1
  refine (norm_sub_laurentTrunc_le hr hf hM hwR hwr N).trans ?_
  have hw2 : ‖w‖ ≤ R₀ := hw.2
  have h1 : R * ((‖w‖ / R) ^ N * (R - ‖w‖)⁻¹ * M) ≤ M * (R * (R - R₀)⁻¹ * (R₀ / R) ^ N) := by
    have ha : (‖w‖ / R) ^ N ≤ (R₀ / R) ^ N :=
      pow_le_pow_left₀ (div_nonneg (norm_nonneg _) hRpos.le)
        (div_le_div_of_nonneg_right hw2 hRpos.le) N
    have hb : (R - ‖w‖)⁻¹ ≤ (R - R₀)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    calc R * ((‖w‖ / R) ^ N * (R - ‖w‖)⁻¹ * M)
        ≤ R * ((R₀ / R) ^ N * (R - R₀)⁻¹ * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul ha hb
            (inv_nonneg.mpr (by linarith)) (pow_nonneg (div_nonneg hR₀ hRpos.le) N)) hM0)
            hRpos.le
      _ = M * (R * (R - R₀)⁻¹ * (R₀ / R) ^ N) := by ring
  have h2 : r * ((r / ‖w‖) ^ N * (‖w‖ - r)⁻¹ * M) ≤ M * (r * (r₀ - r)⁻¹ * (r / r₀) ^ N) := by
    rcases hr.eq_or_lt with rfl | hr0
    · simp
    have hrr' : r < r₀ := hrr.resolve_left hr0.ne'
    have hw1 : r₀ ≤ ‖w‖ := hw.1
    have ha : (r / ‖w‖) ^ N ≤ (r / r₀) ^ N :=
      pow_le_pow_left₀ (div_nonneg hr (norm_nonneg _))
        (div_le_div_of_nonneg_left hr (hr0.trans hrr') hw1) N
    have hb : (‖w‖ - r)⁻¹ ≤ (r₀ - r)⁻¹ := inv_anti₀ (by linarith) (by linarith)
    calc r * ((r / ‖w‖) ^ N * (‖w‖ - r)⁻¹ * M)
        ≤ r * ((r / r₀) ^ N * (r₀ - r)⁻¹ * M) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul ha hb
            (inv_nonneg.mpr (by linarith)) (pow_nonneg (div_nonneg hr (hr0.trans hrr').le) N))
            hM0) hr
      _ = M * (r * (r₀ - r)⁻¹ * (r / r₀) ^ N) := by ring
  linarith

/-- The truncation error bound of `norm_sub_laurentTrunc_le_of_mem` tends to `0`: for
`0 ≤ R₀ < R` and `r = 0 ∨ 0 ≤ r < r₀`. -/
theorem tendsto_laurentTrunc_err {r R r₀ R₀ : ℝ} (hr : 0 ≤ r) (hR₀ : 0 ≤ R₀) (hRR : R₀ < R)
    (hrr : r = 0 ∨ r < r₀) :
    Tendsto (fun N : ℕ ↦ R * (R - R₀)⁻¹ * (R₀ / R) ^ N + r * (r₀ - r)⁻¹ * (r / r₀) ^ N) atTop
      (𝓝 0) := by
  have hRpos : 0 < R := hR₀.trans_lt hRR
  have h1 : Tendsto (fun N : ℕ ↦ (R₀ / R) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR₀ hRpos.le)
      ((div_lt_one hRpos).mpr hRR)
  have h2 : Tendsto (fun N : ℕ ↦ (r / r₀) ^ N) atTop (𝓝 0) := by
    rcases hrr with rfl | hrr
    · simp only [zero_div]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one le_rfl zero_lt_one
    · have hr₀ : 0 < r₀ := hr.trans_lt hrr
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hr₀.le)
        ((div_lt_one hr₀).mpr hrr)
  simpa using (h1.const_mul (R * (R - R₀)⁻¹)).add (h2.const_mul (r * (r₀ - r)⁻¹))

/-- The truncation error bound of `norm_sub_laurentTrunc_le_of_mem` becomes small: for
`0 ≤ R₀ < R`, `r = 0 ∨ 0 ≤ r < r₀` and every `M`, `ε > 0`, some order `N` makes it `< ε`. -/
theorem exists_laurentTrunc_order {r R r₀ R₀ M ε : ℝ} (hr : 0 ≤ r) (hR₀ : 0 ≤ R₀) (hRR : R₀ < R)
    (hrr : r = 0 ∨ r < r₀) (hε : 0 < ε) :
    ∃ N : ℕ, M * (R * (R - R₀)⁻¹ * (R₀ / R) ^ N + r * (r₀ - r)⁻¹ * (r / r₀) ^ N) < ε := by
  have hRpos : 0 < R := hR₀.trans_lt hRR
  have h1 : Tendsto (fun N : ℕ ↦ (R₀ / R) ^ N) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hR₀ hRpos.le)
      ((div_lt_one hRpos).mpr hRR)
  have h2 : Tendsto (fun N : ℕ ↦ (r / r₀) ^ N) atTop (𝓝 0) := by
    rcases hrr with rfl | hrr
    · simp only [zero_div]
      exact tendsto_pow_atTop_nhds_zero_of_lt_one le_rfl zero_lt_one
    · have hr₀ : 0 < r₀ := hr.trans_lt hrr
      exact tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hr hr₀.le)
        ((div_lt_one hr₀).mpr hrr)
  have ht : Tendsto (fun N : ℕ ↦
      M * (R * (R - R₀)⁻¹ * (R₀ / R) ^ N + r * (r₀ - r)⁻¹ * (r / r₀) ^ N)) atTop (𝓝 0) := by
    have := ((h1.const_mul (R * (R - R₀)⁻¹)).add (h2.const_mul (r * (r₀ - r)⁻¹))).const_mul M
    simpa using this
  exact (ht.eventually (gt_mem_nhds hε)).exists

end AnalyticGeometry
