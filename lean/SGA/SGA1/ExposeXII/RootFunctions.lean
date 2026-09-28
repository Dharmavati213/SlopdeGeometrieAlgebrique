/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.CauchyBound

/-!
# Roots of polynomials depending on a complex parameter

* `differentiableAt_of_isRoot`: a continuous root of a family of polynomials with complex
  differentiable coefficients, simple at `s₀`, is complex differentiable at `s₀`;
* `differentiableAt_coeff_prod_X_sub_C`: the coefficients of `∏ (X - ρᵢ(s))` are complex
  differentiable where the `ρᵢ` are;
* bounds: `norm_coeff_prod_X_sub_C_le` (coefficients of `∏ (X - tᵢ)`) and
  `norm_le_of_isRoot_of_monic` (Cauchy's bound for the roots of a monic polynomial).

Used in the proof of XII.2.4 (`RootLocus.lean`).
-/

open Polynomial Filter Topology Set

namespace SGA.SGA1.ExposeXII

/-- A continuous root `ρ` of a family of polynomials `p s` with coefficients complex differentiable
at `s₀`, simple at `s₀`, is complex differentiable at `s₀` (a one-variable implicit function
theorem). -/
theorem differentiableAt_of_isRoot {p : ℂ → ℂ[X]} {d : ℕ} {s₀ : ℂ}
    (hdeg : ∀ s, (p s).natDegree ≤ d) (hcoeff : ∀ k, DifferentiableAt ℂ (fun s ↦ (p s).coeff k) s₀)
    {ρ : ℂ → ℂ} (hρ : ContinuousAt ρ s₀) (hroot : ∀ᶠ s in 𝓝 s₀, (p s).IsRoot (ρ s))
    (hsimple : (p s₀).derivative.eval (ρ s₀) ≠ 0) : DifferentiableAt ℂ ρ s₀ := by
  set a : ℕ → ℂ → ℂ := fun k s ↦ (p s).coeff k
  set α : ℕ → ℂ → ℂ := fun k ↦ dslope (a k) s₀
  set ρ₀ := ρ s₀
  set D : ℂ → ℂ := dslope (fun y ↦ (p s₀).eval y) ρ₀
  have hevalsum (s y : ℂ) : (p s).eval y = ∑ k ∈ Finset.range (d + 1), a k s * y ^ k :=
    eval_eq_sum_range' (Nat.lt_succ_of_le (hdeg s)) y
  -- the key identity
  have hid (s : ℂ) (hs : (p s).IsRoot (ρ s)) :
      (s - s₀) * ∑ k ∈ Finset.range (d + 1), α k s * ρ s ^ k + (ρ s - ρ₀) * D (ρ s) = 0 := by
    have h1 : (s - s₀) * ∑ k ∈ Finset.range (d + 1), α k s * ρ s ^ k =
        (p s).eval (ρ s) - (p s₀).eval (ρ s) := by
      rw [hevalsum, hevalsum, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      have := sub_smul_dslope (a k) s₀ s
      simp only [smul_eq_mul] at this
      rw [← sub_mul, ← this, mul_assoc]
    have h2 : (ρ s - ρ₀) * D (ρ s) = (p s₀).eval (ρ s) - (p s₀).eval ρ₀ := by
      have := sub_smul_dslope (fun y ↦ (p s₀).eval y) ρ₀ (ρ s)
      simpa only [smul_eq_mul] using this
    have hs0 : (p s₀).eval ρ₀ = 0 := hroot.self_of_nhds
    rw [h1, h2, hs0, hs.eq_zero]
    ring
  -- limits
  have hαc (k : ℕ) : ContinuousAt (α k) s₀ := continuousAt_dslope_same.mpr (hcoeff k)
  have hA : Tendsto (fun s ↦ ∑ k ∈ Finset.range (d + 1), α k s * ρ s ^ k) (𝓝 s₀)
      (𝓝 (∑ k ∈ Finset.range (d + 1), α k s₀ * ρ₀ ^ k)) :=
    tendsto_finsetSum _ fun k _ ↦ (hαc k).tendsto.mul (hρ.tendsto.pow k)
  have hDc : ContinuousAt D ρ₀ :=
    continuousAt_dslope_same.mpr (Polynomial.differentiableAt _)
  have hD0 : D ρ₀ = (p s₀).derivative.eval ρ₀ := by
    simp only [D, dslope_same, Polynomial.deriv]
  have hDρ : Tendsto (fun s ↦ D (ρ s)) (𝓝 s₀) (𝓝 (D ρ₀)) := hDc.tendsto.comp hρ.tendsto
  have hD0' : D ρ₀ ≠ 0 := hD0 ▸ hsimple
  suffices H : HasDerivAt ρ (-(∑ k ∈ Finset.range (d + 1), α k s₀ * ρ₀ ^ k) / D ρ₀) s₀ from
    H.differentiableAt
  rw [hasDerivAt_iff_tendsto_slope]
  have hlim : Tendsto (fun s ↦ -(∑ k ∈ Finset.range (d + 1), α k s * ρ s ^ k) / D (ρ s))
      (𝓝[≠] s₀) (𝓝 (-(∑ k ∈ Finset.range (d + 1), α k s₀ * ρ₀ ^ k) / D ρ₀)) :=
    ((hA.neg.div hDρ hD0').mono_left nhdsWithin_le_nhds)
  refine hlim.congr' ?_
  filter_upwards [nhdsWithin_le_nhds hroot, nhdsWithin_le_nhds (hDρ.eventually_ne hD0'),
    self_mem_nhdsWithin] with s hs hDs hss
  have hss' : s - s₀ ≠ 0 := sub_ne_zero.mpr hss
  have := hid s hs
  rw [slope_def_field, div_eq_div_iff hDs hss']
  linear_combination -this


/-- The coefficients of `∏ (X - tᵢ)` are bounded by `∏ (1 + ‖tᵢ‖)`. -/
lemma norm_coeff_prod_X_sub_C_le {ι : Type*} (J : Finset ι) (t : ι → ℂ) (m : ℕ) :
    ‖(∏ i ∈ J, (X - C (t i))).coeff m‖ ≤ ∏ i ∈ J, (1 + ‖t i‖) := by
  classical
  induction J using Finset.induction_on generalizing m with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]
    split_ifs <;> simp
  | insert a J haJ ih =>
    rw [Finset.prod_insert haJ, Finset.prod_insert haJ, mul_comm (X - C (t a))]
    have hQ : 0 ≤ ∏ i ∈ J, (1 + ‖t i‖) := Finset.prod_nonneg fun i _ ↦ by positivity
    rcases m with _ | m
    · rw [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg, norm_neg,
        norm_mul]
      calc ‖(∏ i ∈ J, (X - C (t i))).coeff 0‖ * ‖t a‖ ≤ (∏ i ∈ J, (1 + ‖t i‖)) * ‖t a‖ :=
            mul_le_mul_of_nonneg_right (ih 0) (norm_nonneg _)
        _ ≤ _ := by rw [mul_comm]; gcongr; linarith
    · rw [coeff_mul_X_sub_C]
      calc ‖(∏ i ∈ J, (X - C (t i))).coeff m - (∏ i ∈ J, (X - C (t i))).coeff (m + 1) * t a‖
          ≤ ‖(∏ i ∈ J, (X - C (t i))).coeff m‖ +
              ‖(∏ i ∈ J, (X - C (t i))).coeff (m + 1)‖ * ‖t a‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul]
        _ ≤ (∏ i ∈ J, (1 + ‖t i‖)) + (∏ i ∈ J, (1 + ‖t i‖)) * ‖t a‖ := by
            gcongr
            · exact ih m
            · exact ih (m + 1)
        _ = (1 + ‖t a‖) * ∏ i ∈ J, (1 + ‖t i‖) := by ring

/-- Cauchy's bound for the roots of a monic polynomial. -/
lemma norm_le_of_isRoot_of_monic {p : ℂ[X]} (hp : p.Monic) {t : ℂ} (ht : p.IsRoot t) :
    ‖t‖ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖ := by
  have h := IsRoot.norm_lt_cauchyBound hp.ne_zero ht
  rw [cauchyBound, hp.leadingCoeff, nnnorm_one, div_one] at h
  have h' : (Finset.range p.natDegree).sup (‖p.coeff ·‖₊) ≤
      ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊ :=
    Finset.sup_le fun i hi ↦ Finset.single_le_sum (f := fun i ↦ ‖p.coeff i‖₊)
      (fun _ _ ↦ zero_le) hi
  have : ‖t‖₊ ≤ 1 + ∑ i ∈ Finset.range p.natDegree, ‖p.coeff i‖₊ := by
    rw [add_comm]; exact h.le.trans (add_le_add_left h' 1)
  have h2 := NNReal.coe_le_coe.mpr this
  push_cast at h2
  exact h2

/-- The coefficients of `∏ (X - ρᵢ(s))` are complex differentiable where the `ρᵢ` are. -/
lemma differentiableAt_coeff_prod_X_sub_C {ι : Type*} (J : Finset ι) {ρ : ι → ℂ → ℂ} {s₀ : ℂ}
    (hρ : ∀ i ∈ J, DifferentiableAt ℂ (ρ i) s₀) (m : ℕ) :
    DifferentiableAt ℂ (fun s ↦ (∏ i ∈ J, (X - C (ρ i s))).coeff m) s₀ := by
  classical
  induction J using Finset.induction_on generalizing m with
  | empty =>
    simp only [Finset.prod_empty, coeff_one]
    exact differentiableAt_const _
  | insert a J haJ ih =>
    have ih' := ih fun i hi ↦ hρ i (Finset.mem_insert_of_mem hi)
    have ha := hρ a (Finset.mem_insert_self a J)
    simp only [Finset.prod_insert haJ, mul_comm (X - C (ρ a _))]
    rcases m with _ | m
    · simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub, mul_neg]
      exact ((ih' 0).mul ha).neg
    · simp only [coeff_mul_X_sub_C]
      exact (ih' m).sub ((ih' (m + 1)).mul ha)

end SGA.SGA1.ExposeXII
