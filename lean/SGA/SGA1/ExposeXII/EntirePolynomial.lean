/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Entire functions of polynomial growth

Two elementary facts of one-variable complex analysis used in the proof of XII.2.4
(`RootLocus.lean`): an entire function `F` with `‖F s‖ ≤ C (1 + ‖s‖)ᴺ` is a polynomial of degree
at most `N` (`exists_polynomial_of_differentiable`, from Liouville's theorem), and the same holds
for a function complex differentiable off a finite set with this growth
(`exists_polynomial_of_differentiableOn`, by Riemann's removable singularity theorem).
-/

open Polynomial Filter Topology Set Metric

namespace SGA.SGA1.ExposeXII

/-- An entire function of polynomial growth `‖F s‖ ≤ C (1 + ‖s‖)ᴺ` is a polynomial of degree at
most `N` (Liouville). -/
theorem exists_polynomial_of_differentiable {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {N : ℕ} (hb : ∀ s, ‖F s‖ ≤ C * (1 + ‖s‖) ^ N) :
    ∃ q : ℂ[X], q.natDegree ≤ N ∧ ∀ s, F s = q.eval s := by
  induction N generalizing F C with
  | zero =>
    obtain ⟨c, hc⟩ := hF.exists_eq_const_of_bounded (by
      rw [isBounded_iff_forall_norm_le]
      exact ⟨C, by rintro _ ⟨s, rfl⟩; simpa using hb s⟩)
    exact ⟨Polynomial.C c, by simp, fun s ↦ by simp [hc]⟩
  | succ N ih =>
    have hC : 0 ≤ C := by
      have := (norm_nonneg _).trans (hb 0)
      simpa using this
    let G := dslope F 0
    have hG : Differentiable ℂ G := by
      rw [← differentiableOn_univ, Complex.differentiableOn_dslope univ_mem]
      exact hF.differentiableOn
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
      hG.continuous.continuousOn
    have hGb : ∀ s, ‖G s‖ ≤ (max M 0 + 2 * C + ‖F 0‖) * (1 + ‖s‖) ^ N := by
      intro s
      have h1 : 1 ≤ (1 + ‖s‖) ^ N := one_le_pow₀ (by linarith [norm_nonneg s])
      by_cases hs : ‖s‖ ≤ 1
      · have := hM s (by simpa using hs)
        have h2 : 0 ≤ 2 * C + ‖F 0‖ := by positivity
        calc ‖G s‖ ≤ max M 0 := this.trans (le_max_left _ _)
          _ ≤ max M 0 + 2 * C + ‖F 0‖ := by linarith
          _ ≤ _ := le_mul_of_one_le_right (by positivity) h1
      · push Not at hs
        have hs0 : s ≠ 0 := by rintro rfl; simp at hs; linarith
        have hGs : G s = s⁻¹ * (F s - F 0) := by
          simp only [G, dslope_of_ne _ hs0, slope_def_field, sub_zero]
          field_simp
        have hsn : 0 < ‖s‖ := by linarith
        rw [hGs, norm_mul, norm_inv]
        have h3 : ‖F s - F 0‖ ≤ C * (1 + ‖s‖) ^ (N + 1) + ‖F 0‖ :=
          (norm_sub_le _ _).trans (by linarith [hb s])
        have h4 : (1 + ‖s‖) ≤ 2 * ‖s‖ := by linarith
        rw [inv_mul_le_iff₀ hsn]
        have h5 : (1 : ℝ) ≤ ‖s‖ * (1 + ‖s‖) ^ N := by
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ ‖s‖ * (1 + ‖s‖) ^ N := mul_le_mul hs.le h1 zero_le_one (norm_nonneg _)
        have h6 : C * (1 + ‖s‖) ≤ C * (2 * ‖s‖) := mul_le_mul_of_nonneg_left h4 hC
        have h7 : 0 ≤ (1 + ‖s‖) ^ N := by positivity
        calc ‖F s - F 0‖ ≤ C * (1 + ‖s‖) ^ (N + 1) + ‖F 0‖ := h3
          _ = C * (1 + ‖s‖) * (1 + ‖s‖) ^ N + ‖F 0‖ := by ring
          _ ≤ C * (2 * ‖s‖) * (1 + ‖s‖) ^ N + ‖F 0‖ * (‖s‖ * (1 + ‖s‖) ^ N) := by
            gcongr
            exact le_mul_of_one_le_right (norm_nonneg _) h5
          _ ≤ ‖s‖ * ((max M 0 + 2 * C + ‖F 0‖) * (1 + ‖s‖) ^ N) := by
            have : 0 ≤ max M 0 * (‖s‖ * (1 + ‖s‖) ^ N) := by positivity
            nlinarith
    obtain ⟨q, hq, hGq⟩ := ih hG hGb
    refine ⟨Polynomial.C (F 0) + X * q, ?_, fun s ↦ ?_⟩
    · refine (natDegree_add_le _ _).trans (max_le (by simp) ?_)
      refine (natDegree_mul_le).trans ?_
      have : (X : ℂ[X]).natDegree ≤ 1 := natDegree_X_le
      omega
    · have := sub_smul_dslope F 0 s
      simp only [sub_zero, smul_eq_mul] at this
      simp only [eval_add, eval_C, eval_mul, eval_X, ← hGq]
      change F s = F 0 + s * G s
      rw [this]
      ring

/-- A function complex differentiable off a finite set `E ⊆ ℂ`, of polynomial growth
`‖F s‖ ≤ C (1 + ‖s‖)ᴺ` off `E`, agrees off `E` with a polynomial of degree at most `N`
(removable singularities and Liouville). -/
theorem exists_polynomial_of_differentiableOn {C : ℝ} {N : ℕ} (E : Finset ℂ) :
    ∀ {F : ℂ → ℂ}, DifferentiableOn ℂ F (↑E)ᶜ → (∀ s ∉ E, ‖F s‖ ≤ C * (1 + ‖s‖) ^ N) →
      ∃ q : ℂ[X], q.natDegree ≤ N ∧ ∀ s ∉ E, F s = q.eval s := by
  classical
  induction E using Finset.induction_on with
  | empty =>
    intro F hF hb
    simp only [Finset.coe_empty, compl_empty] at hF
    obtain ⟨q, hq, hFq⟩ := exists_polynomial_of_differentiable (differentiableOn_univ.mp hF)
      (fun s ↦ hb s (Finset.notMem_empty s))
    exact ⟨q, hq, fun s _ ↦ hFq s⟩
  | insert c E hcE ih =>
    intro F hF hb
    have hopen : IsOpen ((↑E : Set ℂ)ᶜ) := E.finite_toSet.isClosed.isOpen_compl
    obtain ⟨ε, hε, hεE⟩ := Metric.isOpen_iff.mp hopen c (by simpa using hcE)
    have hsub : ball c ε \ {c} ⊆ ((↑(insert c E) : Set ℂ))ᶜ := by
      intro s ⟨hs, hsc⟩
      simp only [Finset.coe_insert, mem_compl_iff, mem_insert_iff, not_or]
      exact ⟨hsc, hεE hs⟩
    let F₁ := Function.update F c (limUnder (𝓝[≠] c) F)
    have hbdd : BddAbove (norm ∘ F '' (ball c ε \ {c})) := by
      refine ⟨C * (1 + (‖c‖ + ε)) ^ N, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      have hs' : s ∉ insert c E := by simpa using hsub hs
      have hC : 0 ≤ C := by
        have := (norm_nonneg _).trans (hb s hs')
        exact nonneg_of_mul_nonneg_left this (by positivity)
      refine (hb s hs').trans (mul_le_mul_of_nonneg_left ?_ hC)
      have : ‖s‖ ≤ ‖c‖ + ε := by
        have := hs.1
        rw [mem_ball, dist_eq_norm] at this
        linarith [norm_le_insert' s c]
      gcongr
    have hF₁ball : DifferentiableOn ℂ F₁ (ball c ε) :=
      Complex.differentiableOn_update_limUnder_of_bddAbove (ball_mem_nhds c hε)
        (hF.mono hsub) hbdd
    have hF₁ : DifferentiableOn ℂ F₁ (↑E)ᶜ := by
      intro s hs
      by_cases hsb : s ∈ ball c ε
      · exact (hF₁ball s hsb).differentiableAt (isOpen_ball.mem_nhds hsb) |>.differentiableWithinAt
      · have hsc : s ≠ c := by rintro rfl; exact hsb (mem_ball_self hε)
        have hs' : s ∈ ((↑(insert c E) : Set ℂ))ᶜ := by
          simp only [Finset.coe_insert, mem_compl_iff, mem_insert_iff, not_or]
          exact ⟨hsc, hs⟩
        have hopen' : IsOpen ((↑(insert c E) : Set ℂ))ᶜ :=
          (insert c E).finite_toSet.isClosed.isOpen_compl
        have hd : DifferentiableAt ℂ F s := (hF s hs').differentiableAt (hopen'.mem_nhds hs')
        have heq : F₁ =ᶠ[𝓝 s] F := by
          filter_upwards [isOpen_compl_singleton.mem_nhds hsc] with y hy
          exact Function.update_of_ne hy _ _
        exact (hd.congr_of_eventuallyEq heq).differentiableWithinAt
    have hb₁ : ∀ s ∉ E, ‖F₁ s‖ ≤ C * (1 + ‖s‖) ^ N := by
      intro s hs
      by_cases hsc : s = c
      · subst hsc
        have hcont : ContinuousAt F₁ s :=
          (hF₁ball s (mem_ball_self hε)).continuousWithinAt.continuousAt
            (ball_mem_nhds s hε)
        refine le_of_tendsto_of_tendsto (b := 𝓝[≠] s)
          (hcont.tendsto.mono_left nhdsWithin_le_nhds).norm
          ((continuous_const.mul ((continuous_const.add continuous_norm).pow N)).tendsto s
            |>.mono_left nhdsWithin_le_nhds) ?_
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds s hε)]
          with y hy hyb
        have hy' : y ∉ insert s E := by simpa using hsub ⟨hyb, hy⟩
        rw [show F₁ y = F y from Function.update_of_ne hy _ _]
        exact hb y hy'
      · rw [show F₁ s = F s from Function.update_of_ne hsc _ _]
        exact hb s (by simp [hsc, hs])
    obtain ⟨q, hq, hF₁q⟩ := ih hF₁ hb₁
    refine ⟨q, hq, fun s hs ↦ ?_⟩
    have hsc : s ≠ c := by rintro rfl; simp at hs
    have hsE : s ∉ E := by simp_all
    rw [← hF₁q s hsE]
    exact (Function.update_of_ne hsc _ _).symm

end SGA.SGA1.ExposeXII
