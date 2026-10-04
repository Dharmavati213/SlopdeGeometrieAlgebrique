/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Differential calculus of polynomial functions on `𝕜^σ`

* `MvPolynomial.hasFDerivAt_eval`: the derivative of `x ↦ p(x)` is
  `h ↦ ∑ᵢ (∂ᵢ p)(x) hᵢ`, where `∂ᵢ p = pderiv i p` is the formal partial derivative;
* `MvPolynomial.exists_lipschitz_bound`: on a compact convex set, a real polynomial function is
  Lipschitz;
* `MvPolynomial.exists_taylor_bound`: on a compact convex set, the first-order Taylor remainder of
  a real polynomial function is `O(‖y - x‖²)`.
-/

open Set Metric

namespace MvPolynomial

variable {σ : Type*} [Fintype σ]

section Field

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The derivative of a polynomial function: `D p(x) h = ∑ᵢ (∂ᵢ p)(x) hᵢ`. -/
theorem hasFDerivAt_eval (p : MvPolynomial σ 𝕜) (x : σ → 𝕜) :
    HasFDerivAt (fun y ↦ eval y p)
      (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i) x := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    simpa [pderiv_C] using hasFDerivAt_const (eval x (C a)) x
  | add p q hp hq =>
    simp only [map_add, add_smul, Finset.sum_add_distrib]
    exact hp.add hq
  | mul_X p i hp =>
    have hX := (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i).hasFDerivAt (x := x)
    have hf : (fun y : σ → 𝕜 ↦ eval y (p * X i)) =
        (fun y ↦ eval y p) * ⇑(ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i) := by
      funext y
      simp
    rw [hf]
    refine (hp.mul hX).congr_fderiv (ContinuousLinearMap.ext fun h ↦ ?_)
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, eval_X, FunLike.coe_sum,
      Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.proj_apply,
      smul_eq_mul, _root_.add_apply, add_mul, Finset.sum_add_distrib]
    rw [add_comm]
    congr 1
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        simp [Ne.symm hj]
      · simp

theorem continuous_fderiv_eval (p : MvPolynomial σ 𝕜) :
    Continuous fun x : σ → 𝕜 ↦
      ∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : σ ↦ 𝕜) i :=
  continuous_finsetSum _ fun i _ ↦ ((pderiv i p).continuous_eval).smul continuous_const

end Field

/-- On a compact convex set, a real polynomial function is Lipschitz. -/
theorem exists_lipschitz_bound (p : MvPolynomial σ ℝ) {s : Set (σ → ℝ)} (hs : IsCompact s)
    (hc : Convex ℝ s) : ∃ K, 0 ≤ K ∧ ∀ x ∈ s, ∀ y ∈ s, |eval y p - eval x p| ≤ K * ‖y - x‖ := by
  obtain ⟨K, hK⟩ := hs.exists_bound_of_continuousOn (continuous_fderiv_eval p).continuousOn
  refine ⟨max K 0, le_max_right _ _, fun x hx y hy ↦ ?_⟩
  have := hc.norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ ↦ (MvPolynomial.hasFDerivAt_eval p z).hasFDerivWithinAt)
    (fun z hz ↦ (hK z hz).trans (le_max_left K 0)) hx hy
  simpa [Real.norm_eq_abs] using this

/-- On a compact convex set, the first-order Taylor remainder of a real polynomial function is
`O(‖y - x‖²)`. -/
theorem exists_taylor_bound (p : MvPolynomial σ ℝ) {s : Set (σ → ℝ)} (hs : IsCompact s)
    (hc : Convex ℝ s) : ∃ L, 0 ≤ L ∧ ∀ x ∈ s, ∀ y ∈ s,
      |eval y p - eval x p - ∑ i, eval x (pderiv i p) * (y i - x i)| ≤ L * ‖y - x‖ ^ 2 := by
  choose K hK0 hK using fun i ↦ exists_lipschitz_bound (pderiv i p) hs hc
  refine ⟨∑ i, K i, Finset.sum_nonneg fun i _ ↦ hK0 i, fun x hx y hy ↦ ?_⟩
  set D : (σ → ℝ) → (σ → ℝ) →L[ℝ] ℝ := fun z ↦
    ∑ i, eval z (pderiv i p) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : σ ↦ ℝ) i
  have hseg : segment ℝ x y ⊆ s := hc.segment_subset hx hy
  have hDh (w h : σ → ℝ) : D w h = ∑ i, eval w (pderiv i p) * h i := by
    simp [D]
  have hKs : 0 ≤ ∑ i, K i := Finset.sum_nonneg fun i _ ↦ hK0 i
  have hbound : ∀ z ∈ segment ℝ x y, ‖D z - D x‖ ≤ (∑ i, K i) * ‖y - x‖ := by
    intro z hz
    have hzx : ‖z - x‖ ≤ ‖y - x‖ := by
      obtain ⟨a, b, ha, hb, hab, rfl⟩ := hz
      obtain rfl : a = 1 - b := by linarith
      have : (1 - b) • x + b • y - x = b • (y - x) := by module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hKs (norm_nonneg _)) fun h ↦ ?_
    rw [show (D z - D x) h = D z h - D x h from rfl, hDh, hDh, ← Finset.sum_sub_distrib]
    simp only [← sub_mul]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ ↦ ?_
    rw [norm_mul, Real.norm_eq_abs]
    calc |eval z (pderiv i p) - eval x (pderiv i p)| * ‖h i‖
        ≤ (K i * ‖z - x‖) * ‖h‖ :=
          mul_le_mul (hK i x hx z (hseg hz)) (norm_le_pi_norm h i) (norm_nonneg _)
            (mul_nonneg (hK0 i) (norm_nonneg _))
      _ ≤ K i * ‖y - x‖ * ‖h‖ := by gcongr; exact hK0 i
  have := (convex_segment x y).norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z _ ↦ (MvPolynomial.hasFDerivAt_eval p z).hasFDerivWithinAt) hbound
    (left_mem_segment ℝ x y)
    (right_mem_segment ℝ x y)
  rw [hDh, Real.norm_eq_abs] at this
  simp only [Pi.sub_apply] at this
  calc _ ≤ (∑ i, K i) * ‖y - x‖ * ‖y - x‖ := this
    _ = _ := by ring

end MvPolynomial
