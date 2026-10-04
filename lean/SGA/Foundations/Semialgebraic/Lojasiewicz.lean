/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.Choice
import SGA.Foundations.Semialgebraic.Monotonicity
import SGA.Foundations.Semialgebraic.PolynomialCalculus
import SGA.Foundations.Semialgebraic.GradientRetraction

/-!
# The Kurdyka–Łojasiewicz inequality for polynomials, and local contractibility of real algebraic
sets

**Kurdyka–Łojasiewicz inequality** (`MvPolynomial.exists_kurdykaLojasiewicz`): let `f ≥ 0` be a
real polynomial on `ℝⁿ` and `p` a point. For every `R > 0` there are `ε > 0` and a nondecreasing
`φ : [0, ε) → ℝ`, continuous at `0` with `φ 0 = 0`, such that for `x` in the closed ball `B` of
radius `R` around `p` with `f x < ε` and `0 ≤ v ≤ f x`,
`f x - v ≤ |∇f(x)| (φ (f x) - φ v)`.

Proof. Let `ψ(s)` be the least value of `|∇f|²` on the level set `B ∩ {f = s}` and `γ(s)` a point
where it is attained, chosen semialgebraically (`IsSemialgebraic.exists_section_of_isCompact`).
By the monotonicity theorem `ψ` and the coordinates of `γ` are continuous and monotone on some
`(0, ε)`. Along `γ`, Taylor's formula gives
`s' - s ≤ |∇f(γ s)| ∑ᵢ |γᵢ s' - γᵢ s| + O(|γ s' - γ s|²)`; summing over fine subdivisions,
`u - v ≤ √ψ(u) ∑ᵢ |γᵢ u - γᵢ v|` if `ψ` is nondecreasing, so
`φ(u) = ∑ᵢ |γᵢ u - γᵢ(0⁺)|` works (the coordinates being monotone, `∑ᵢ |γᵢ u - γᵢ v|` telescopes);
if `ψ` is nonincreasing, `ψ` is bounded below by a positive constant `c²` near `0` and
`φ(u) = u / c` works. This is Kurdyka's argument (*On gradients of functions definable in
o-minimal structures*, 1998) with a curve of minimal gradient instead of a definable choice of
gradient lengths.

With the gradient-descent retraction (`exists_retraction_of_kurdykaLojasiewicz`) this gives the
**local contractibility of real algebraic sets**
(`MvPolynomial.locallyContractibleSpace_setOf_eval_eq_zero`):
the zero set of a real polynomial is locally contractible in the classical sense, hence locally
path-connected and semilocally simply connected.

## References

* [K. Kurdyka, *On gradients of functions definable in o-minimal structures*, Ann. Inst. Fourier
  48 (1998)][Kurdyka1998]
* [S. Łojasiewicz, *Ensembles semi-analytiques*, IHES notes, 1965][Lojasiewicz1965]
* [L. van den Dries, *Tame topology and o-minimal structures*, Chapter 3][vdD]
-/

open Set Filter Topology Metric

namespace MvPolynomial

namespace KurdykaLojasiewiczAux

/-- Telescoping for a monotone or antitone function along a subdivision. -/
private lemma sum_abs_sub_eq {f : ℝ → ℝ} {a b : ℝ} (s : ℕ → ℝ) (N : ℕ)
    (hs : ∀ k ≤ N, s k ∈ Icc a b) (hmono : ∀ k < N, s k ≤ s (k + 1))
    (hf : MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b)) :
    ∑ k ∈ Finset.range N, |f (s (k + 1)) - f (s k)| = |f (s N) - f (s 0)| := by
  rcases hf with hf | hf
  · have hnn (k : ℕ) (hk : k < N) : 0 ≤ f (s (k + 1)) - f (s k) :=
      sub_nonneg.mpr (hf (hs k hk.le) (hs (k + 1) hk) (hmono k hk))
    rw [Finset.sum_congr rfl fun k hk ↦ abs_of_nonneg (hnn k (Finset.mem_range.mp hk)),
      Finset.sum_range_sub (fun k ↦ f (s k)), abs_of_nonneg]
    exact (Finset.sum_range_sub (fun k ↦ f (s k)) N) ▸
      Finset.sum_nonneg fun k hk ↦ hnn k (Finset.mem_range.mp hk)
  · have hnp (k : ℕ) (hk : k < N) : f (s (k + 1)) - f (s k) ≤ 0 :=
      sub_nonpos.mpr (hf (hs k hk.le) (hs (k + 1) hk) (hmono k hk))
    rw [Finset.sum_congr rfl fun k hk ↦ abs_of_nonpos (hnp k (Finset.mem_range.mp hk)),
      Finset.sum_neg_distrib, Finset.sum_range_sub (fun k ↦ f (s k)), abs_of_nonpos]
    exact (Finset.sum_range_sub (fun k ↦ f (s k)) N) ▸
      Finset.sum_nonpos fun k hk ↦ hnp k (Finset.mem_range.mp hk)

/-- Summing an infinitesimal inequality along a curve with monotone coordinates: if
`s' - s ≤ A ∑ᵢ |γᵢ s' - γᵢ s| + L ‖γ s' - γ s‖²` on `[a, b]`, then
`b - a ≤ A ∑ᵢ |γᵢ b - γᵢ a|`. -/
lemma sub_le_of_forall_sub_le {n : ℕ} {γ : ℝ → Fin n → ℝ} {a b A L : ℝ} (hab : a ≤ b)
    (hL : 0 ≤ L) (hc : ContinuousOn γ (Icc a b))
    (hm : ∀ i, MonotoneOn (fun s ↦ γ s i) (Icc a b) ∨ AntitoneOn (fun s ↦ γ s i) (Icc a b))
    (h : ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, s ≤ s' →
      s' - s ≤ A * ∑ i, |γ s' i - γ s i| + L * ‖γ s' - γ s‖ ^ 2) :
    b - a ≤ A * ∑ i, |γ b i - γ a i| := by
  set D := ∑ i, |γ b i - γ a i|
  have hD : 0 ≤ D := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  rcases hab.eq_or_lt with rfl | hab'
  · simp [D]
  -- it suffices to show `b - a ≤ A * D + L * η * D` for all `η > 0`
  suffices key : ∀ η > 0, b - a ≤ A * D + L * η * D by
    refine le_of_forall_pos_lt_add fun e he ↦ ?_
    have hη : 0 < e / (L * D + 1) := div_pos he (by positivity)
    refine (key _ hη).trans_lt ?_
    have : L * (e / (L * D + 1)) * D < e := by
      rw [mul_comm L, mul_assoc, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [mul_nonneg hL hD]
    linarith
  intro η hη
  obtain ⟨ρ, hρ, hρη⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc).uniformContinuousOn_of_continuous hc) η hη
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / ρ)
  have hN0 : 0 < N := by
    have : 0 < (b - a) / ρ := div_pos (by linarith) hρ
    exact_mod_cast this.trans hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN0
  set s : ℕ → ℝ := fun k ↦ a + k * ((b - a) / N)
  have hstep : (b - a) / N < ρ := by
    rw [div_lt_iff₀ hNr]
    rw [div_lt_iff₀ hρ] at hN
    linarith
  have hs (k : ℕ) (hk : k ≤ N) : s k ∈ Icc a b := by
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    refine ⟨le_add_of_nonneg_right (by positivity), ?_⟩
    calc a + k * ((b - a) / N) ≤ a + N * ((b - a) / N) := by gcongr
      _ = b := by field_simp; ring
  have hsN : s N = b := by simp only [s]; field_simp; ring_nf
  have hs0 : s 0 = a := by simp [s]
  have hsucc (k : ℕ) : s (k + 1) - s k = (b - a) / N := by simp only [s]; push_cast; ring
  have hmono (k : ℕ) (_ : k < N) : s k ≤ s (k + 1) := by
    have := hsucc k
    have : 0 ≤ (b - a) / N := by positivity
    linarith
  -- each small step
  have hstepk (k : ℕ) (hk : k < N) : s (k + 1) - s k ≤
      (A + L * η) * ∑ i, |γ (s (k + 1)) i - γ (s k) i| := by
    have h1 := h _ (hs k hk.le) _ (hs (k + 1) hk) (hmono k hk)
    have hnorm : ‖γ (s (k + 1)) - γ (s k)‖ ≤ ∑ i, |γ (s (k + 1)) i - γ (s k) i| := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)).mpr
        fun i ↦ ?_
      rw [Real.norm_eq_abs, Pi.sub_apply]
      exact Finset.single_le_sum (f := fun i ↦ |γ (s (k + 1)) i - γ (s k) i|)
        (fun i _ ↦ abs_nonneg _) (Finset.mem_univ i)
    have hsmall : ‖γ (s (k + 1)) - γ (s k)‖ < η := by
      rw [← dist_eq_norm]
      refine hρη _ (hs (k + 1) hk) _ (hs k hk.le) ?_
      rw [Real.dist_eq, hsucc, abs_of_nonneg (by positivity)]
      exact hstep
    have h2 : ‖γ (s (k + 1)) - γ (s k)‖ ^ 2 ≤ η * ∑ i, |γ (s (k + 1)) i - γ (s k) i| := by
      rw [sq]
      exact mul_le_mul hsmall.le hnorm (norm_nonneg _) hη.le
    nlinarith
  -- sum the steps
  have htel : b - a = ∑ k ∈ Finset.range N, (s (k + 1) - s k) := by
    rw [Finset.sum_range_sub s, hsN, hs0]
  have hsum := Finset.sum_le_sum fun k hk ↦ hstepk k (Finset.mem_range.mp hk)
  rw [← htel, ← Finset.mul_sum, Finset.sum_comm] at hsum
  have hcoord (i : Fin n) : ∑ k ∈ Finset.range N, |γ (s (k + 1)) i - γ (s k) i| =
      |γ b i - γ a i| := by
    rw [sum_abs_sub_eq (f := fun t ↦ γ t i) s N hs hmono (hm i), hsN, hs0]
  simp only [hcoord] at hsum
  linarith

/-- A bounded function, monotone or antitone on `(0, ε)`, has a limit at `0⁺`. -/
private lemma exists_tendsto_nhdsGT {f : ℝ → ℝ} {ε C : ℝ} (hε : 0 < ε)
    (hm : MonotoneOn f (Ioo 0 ε) ∨ AntitoneOn f (Ioo 0 ε)) (hC : ∀ s ∈ Ioo 0 ε, |f s| ≤ C) :
    ∃ ℓ, Tendsto f (𝓝[>] 0) (𝓝 ℓ) := by
  have hne : (Ioo (0 : ℝ) ε).Nonempty := nonempty_Ioo.mpr hε
  rcases hm with hm | hm
  · refine ⟨_, hm.tendsto_nhdsWithin_Ioo_right hne ⟨-C, ?_⟩⟩
    rintro _ ⟨s, hs, rfl⟩
    exact (abs_le.mp (hC s hs)).1
  · have hm' : MonotoneOn (fun s ↦ -f s) (Ioo 0 ε) := fun a ha b hb hab ↦ neg_le_neg (hm ha hb hab)
    refine ⟨-sInf ((fun s ↦ -f s) '' Ioo 0 ε), ?_⟩
    have := (hm'.tendsto_nhdsWithin_Ioo_right hne ⟨-C, ?_⟩).neg
    · simpa using this
    rintro _ ⟨s, hs, rfl⟩
    exact neg_le_neg (abs_le.mp (hC s hs)).2

/-- Splitting `|f u - ℓ|` at `v` for a monotone or antitone function with limit `ℓ` at `0⁺`. -/
private lemma abs_sub_lim_eq {f : ℝ → ℝ} {ε ℓ u v : ℝ}
    (hm : MonotoneOn f (Ioo 0 ε) ∨ AntitoneOn f (Ioo 0 ε)) (hℓ : Tendsto f (𝓝[>] 0) (𝓝 ℓ))
    (hv : 0 < v) (hvu : v ≤ u) (hu : u < ε) :
    |f u - ℓ| = |f u - f v| + |f v - ℓ| := by
  have hvI : v ∈ Ioo 0 ε := ⟨hv, hvu.trans_lt hu⟩
  have huI : u ∈ Ioo 0 ε := ⟨hv.trans_le hvu, hu⟩
  rcases hm with hm | hm
  · have hℓv : ℓ ≤ f v := by
      refine le_of_tendsto hℓ ?_
      filter_upwards [Ioo_mem_nhdsGT hv] with w hw
      exact hm ⟨hw.1, hw.2.trans hvI.2⟩ hvI hw.2.le
    have hvu' : f v ≤ f u := hm hvI huI hvu
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    ring
  · have hℓv : f v ≤ ℓ := by
      refine ge_of_tendsto hℓ ?_
      filter_upwards [Ioo_mem_nhdsGT hv] with w hw
      exact hm ⟨hw.1, hw.2.trans hvI.2⟩ hvI hw.2.le
    have hvu' : f u ≤ f v := hm hvI huI hvu
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    ring

/-- `√(∑ dᵢ²) ≤ ∑ |dᵢ|`. -/
private lemma sqrt_sum_sq_le_sum_abs {ι : Type*} (s : Finset ι) (d : ι → ℝ) :
    √(∑ i ∈ s, d i ^ 2) ≤ ∑ i ∈ s, |d i| := by
  rw [Real.sqrt_le_left (Finset.sum_nonneg fun i _ ↦ abs_nonneg _)]
  calc ∑ i ∈ s, d i ^ 2 = ∑ i ∈ s, |d i| ^ 2 := by simp
    _ ≤ (∑ i ∈ s, |d i|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun i _ ↦ abs_nonneg _

end KurdykaLojasiewiczAux

open KurdykaLojasiewiczAux IsSemialgebraic in
/-- **Kurdyka–Łojasiewicz inequality** for a nonnegative real polynomial `f` near a zero `p`: for
every `R > 0` there are `ε > 0` and a nondecreasing `φ` on `[0, ε)`, continuous at `0` with
`φ 0 = 0`, such that `f x - v ≤ |∇f(x)| (φ (f x) - φ v)` whenever `‖x - p‖ ≤ R` and
`0 ≤ v ≤ f x < ε`. This is a difference-quotient variant of the usual inequality
`φ'(f x) |∇f(x)| ≥ 1` (with `φ` of class `C¹` and concave): here `φ` is only monotone and
continuous at `0`, which is what the gradient-descent retraction
(`exists_retraction_of_kurdykaLojasiewicz`) uses. -/
theorem exists_kurdykaLojasiewicz {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (hf : ∀ x, 0 ≤ eval x f) (p : Fin n → ℝ) (hp : eval p f = 0) (R : ℝ) (hR : 0 < R) :
    ∃ ε > 0, ∃ φ : ℝ → ℝ, φ 0 = 0 ∧ MonotoneOn φ (Ico 0 ε) ∧ ContinuousWithinAt φ (Ici 0) 0 ∧
      ∀ x ∈ closedBall p R, eval x f < ε → ∀ v ∈ Icc 0 (eval x f),
        eval x f - v ≤ √(∑ i, eval x (pderiv i f) ^ 2) * (φ (eval x f) - φ v) := by
  set F : (Fin n → ℝ) → ℝ := fun x ↦ eval x f with hF_def
  set G : (Fin n → ℝ) → ℝ := fun x ↦ ∑ i, eval x (pderiv i f) ^ 2 with hG_def
  set B := closedBall p R
  have hBc : IsCompact B := isCompact_closedBall p R
  have hBconv : Convex ℝ B := convex_closedBall p R
  have hFc : Continuous F := f.continuous_eval
  have hGc : Continuous G := continuous_finsetSum _ fun i _ ↦ ((pderiv i f).continuous_eval).pow 2
  have hG0 (x) : 0 ≤ G x := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  obtain ⟨L, hL, htay⟩ := exists_taylor_bound f hBc hBconv
  have hmemB (x : Fin n → ℝ) : x ∈ B ↔ ∀ i, (x i - p i) ^ 2 ≤ R ^ 2 := by
    simp only [B, mem_closedBall, dist_pi_le_iff hR.le, Real.dist_eq]
    refine forall_congr' fun i ↦ ?_
    rw [← sq_abs (x i - p i), sq_le_sq₀ (abs_nonneg _) hR.le]
  -- the trivial case
  by_cases hzeroB : ∀ x ∈ B, F x = 0
  · refine ⟨1, one_pos, fun _ ↦ 0, rfl, monotoneOn_const, continuousWithinAt_const, ?_⟩
    intro x hx _ v hv
    have h0 : F x = 0 := hzeroB x hx
    simp only [hF_def] at h0
    rw [h0] at hv ⊢
    obtain rfl : v = 0 := le_antisymm hv.2 hv.1
    simp
  push Not at hzeroB
  obtain ⟨x₁, hx₁B, hx₁⟩ := hzeroB
  set M := F x₁
  have hM : 0 < M := lt_of_le_of_ne (hf x₁) (Ne.symm hx₁)
  -- all the levels `s ∈ [0, M]` are met in `B`
  have hlvl (s : ℝ) (hs : s ∈ Icc 0 M) : ∃ x ∈ B, F x = s := by
    have hcont : ContinuousOn (fun t : ℝ ↦ F (p + t • (x₁ - p))) (Icc 0 1) :=
      (hFc.comp (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
    obtain ⟨t, ht, hts⟩ := intermediate_value_Icc zero_le_one hcont (by simpa [hF_def, hp] using hs)
    refine ⟨p + t • (x₁ - p), ?_, hts⟩
    have := hBconv.add_smul_sub_mem (mem_closedBall_self hR.le) hx₁B ht
    exact this
  -- the family of points of `B ∩ {f = s}` where `|∇f|²` is minimal
  set S : Set (Option (Fin n) → ℝ) := {w | (∀ i, (w (some i) - p i) ^ 2 ≤ R ^ 2) ∧
    eval (fun i ↦ w (some i)) f = w none ∧ ∀ y : Fin n → ℝ, (∀ i, (y i - p i) ^ 2 ≤ R ^ 2) →
      eval y f = w none →
        ∑ i, eval (fun j ↦ w (some j)) (pderiv i f) ^ 2 ≤ ∑ i, eval y (pderiv i f) ^ 2}
    with hS_def
  have hGpoly {ι : Type} (e : Fin n → ι) : IsPolynomialFun fun w : ι → ℝ ↦
      ∑ i, eval (fun j ↦ w (e j)) (pderiv i f) ^ 2 :=
    IsPolynomialFun.sum _ fun i ↦
      (IsPolynomialFun.eval_comp (fun j ↦ IsPolynomialFun.apply (e j)) _).pow 2
  have hS : IsSemialgebraic S := by
    refine ofPred_and (ofPred_forall_finite fun i ↦ ofPred_le (by fun_prop) (by fun_prop))
      (ofPred_and (ofPred_eq (IsPolynomialFun.eval_comp (fun j ↦ IsPolynomialFun.apply _) _)
        (by fun_prop)) (ofPred_forall_pi (ofPred_imp (ofPred_forall_finite fun i ↦
        ofPred_le (by fun_prop) (by fun_prop)) (ofPred_imp (ofPred_eq
        (IsPolynomialFun.eval_comp (fun j ↦ IsPolynomialFun.apply _) _) (by fun_prop))
        (ofPred_le (hGpoly _) (hGpoly _))))))
  have hSfib (s : ℝ) : IsCompact {x : Fin n → ℝ | (fun o ↦ Option.elim o s x) ∈ S} := by
    have heq : {x : Fin n → ℝ | (fun o ↦ Option.elim o s x) ∈ S} =
        B ∩ F ⁻¹' {s} ∩ ⋂ y : Fin n → ℝ, {x | y ∈ B → F y = s → G x ≤ G y} := by
      ext x
      simp only [hS_def, mem_ofPred_eq, Option.elim_some, Option.elim_none, mem_inter_iff,
        mem_preimage, mem_singleton_iff, mem_iInter, hmemB, hF_def, hG_def]
      exact and_assoc.symm
    rw [heq]
    refine (hBc.inter_right (isClosed_singleton.preimage hFc)).inter_right
      (isClosed_iInter fun y ↦ ?_)
    by_cases hy : y ∈ B ∧ F y = s
    · simpa [hy.1, hy.2] using isClosed_le hGc continuous_const
    · have : {x : Fin n → ℝ | y ∈ B → F y = s → G x ≤ G y} = univ := by
        ext x
        simp only [mem_ofPred_eq, mem_univ, iff_true]
        exact fun h1 h2 ↦ absurd ⟨h1, h2⟩ hy
      rw [this]
      exact isClosed_univ
  obtain ⟨γ, hγS, hγ⟩ := exists_section_of_isCompact hS hSfib
  have hγ' (s : ℝ) (hs : s ∈ Icc 0 M) :
      γ s ∈ B ∧ F (γ s) = s ∧ ∀ y ∈ B, F y = s → G (γ s) ≤ G y := by
    obtain ⟨x, hxB, hxs⟩ := hlvl s hs
    obtain ⟨y, hyL, hymin⟩ := (hBc.inter_right (isClosed_singleton.preimage hFc)).exists_isMinOn
      ⟨x, hxB, hxs⟩ hGc.continuousOn
    have hyS : (fun o ↦ Option.elim o s y) ∈ S := by
      refine ⟨(hmemB y).mp hyL.1, hyL.2, fun z hz hzs ↦ ?_⟩
      exact hymin ⟨(hmemB z).mpr hz, hzs⟩
    obtain ⟨h1, h2, h3⟩ := hγS s y hyS
    exact ⟨(hmemB _).mpr h1, h2, fun z hz hzs ↦ h3 z ((hmemB z).mp hz) hzs⟩
  -- the least value of `|∇f|²` on the level `s`
  set Ψ : ℝ → ℝ := fun s ↦ G (γ s) with hΨ_def
  have hΨ : Real.IsSemialgebraicFun Ψ := by
    have key : {v : Fin 2 → ℝ | Ψ (v 0) = v 1} = {v | ∃ x : Fin n → ℝ,
        (∀ i, γ (v 0) i = x i) ∧ ∑ i, eval (fun j ↦ x j) (pderiv i f) ^ 2 = v 1} := by
      ext v
      simp only [mem_ofPred_eq, hΨ_def, hG_def]
      constructor
      · intro h
        exact ⟨γ (v 0), fun i ↦ rfl, h⟩
      · rintro ⟨x, hx, h⟩
        rwa [show γ (v 0) = x from _root_.funext hx]
    unfold Real.IsSemialgebraicFun
    rw [key]
    exact ofPred_exists_pi (ofPred_and (ofPred_forall_finite fun i ↦ (hγ i).graph _ _)
      (ofPred_eq (hGpoly _) (by fun_prop)))
  -- monotonicity near `0`
  have hev := ((Filter.eventually_all.mpr fun i ↦
    (hγ i).eventually_continuousOn_monotoneOn_or_antitoneOn 0).and
    (hΨ.eventually_continuousOn_monotoneOn_or_antitoneOn 0)).and (Ioo_mem_nhdsGT hM)
  obtain ⟨ε, ⟨⟨hγε, hΨε⟩, hεM⟩, hε⟩ := (hev.and self_mem_nhdsWithin).exists
  simp only [zero_add] at hγε hΨε
  have hε0 : 0 < ε := hε
  have hIM (s : ℝ) (hs : s ∈ Ioo 0 ε) : s ∈ Icc 0 M := ⟨hs.1.le, (hs.2.trans hεM.2).le⟩
  have hγcont : ContinuousOn γ (Ioo 0 ε) := continuousOn_pi.mpr fun i ↦ (hγε i).1
  have hγmono (i : Fin n) (a b : ℝ) (ha : 0 < a) (hb : b < ε) :
      MonotoneOn (fun s ↦ γ s i) (Icc a b) ∨ AntitoneOn (fun s ↦ γ s i) (Icc a b) :=
    (hγε i).2.imp (fun h ↦ h.mono (Icc_subset_Ioo ha hb)) fun h ↦ h.mono (Icc_subset_Ioo ha hb)
  -- the inequality along the curve `γ`
  have hcurve (s s' : ℝ) (hs : s ∈ Ioo 0 ε) (hs' : s' ∈ Ioo 0 ε) :
      s' - s ≤ √(Ψ s) * ∑ i, |γ s' i - γ s i| + L * ‖γ s' - γ s‖ ^ 2 := by
    obtain ⟨hB, hF, -⟩ := hγ' s (hIM s hs)
    obtain ⟨hB', hF', -⟩ := hγ' s' (hIM s' hs')
    have ht := (abs_le.mp (htay (γ s) hB (γ s') hB')).2
    have hcs : ∑ i, eval (γ s) (pderiv i f) * (γ s' i - γ s i) ≤
        √(Ψ s) * ∑ i, |γ s' i - γ s i| :=
      (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans
        (mul_le_mul_of_nonneg_left (sqrt_sum_sq_le_sum_abs _ _) (Real.sqrt_nonneg _))
    simp only [hF_def] at hF hF'
    rw [hF, hF'] at ht
    linarith
  obtain ⟨-, hΨm | hΨa⟩ := hΨε
  · -- `ψ` nondecreasing: `φ (u) = ∑ᵢ |γᵢ u - γᵢ (0⁺)|`
    have hbound (i : Fin n) (s : ℝ) (hs : s ∈ Ioo 0 ε) : |γ s i| ≤ |p i| + R := by
      have h := (hγ' s (hIM s hs)).1
      rw [mem_closedBall, dist_pi_le_iff hR.le] at h
      have := h i
      rw [Real.dist_eq] at this
      calc |γ s i| = |(γ s i - p i) + p i| := by ring_nf
        _ ≤ |γ s i - p i| + |p i| := abs_add_le _ _
        _ ≤ |p i| + R := by linarith
    choose ℓ hℓ using fun i ↦ exists_tendsto_nhdsGT hε0 (hγε i).2 (hbound i)
    set φ : ℝ → ℝ := fun u ↦ if 0 < u then ∑ i, |γ u i - ℓ i| else 0 with hφ_def
    have hφ0 : φ 0 = 0 := by simp [hφ_def]
    have hφnn (u : ℝ) : 0 ≤ φ u := by
      simp only [hφ_def]
      split_ifs
      · exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      · exact le_rfl
    have hsplit (v u : ℝ) (hv : 0 < v) (hvu : v ≤ u) (hu : u < ε) :
        φ u - φ v = ∑ i, |γ u i - γ v i| := by
      simp only [hφ_def, hv, hv.trans_le hvu, ↓reduceIte, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [abs_sub_lim_eq (hγε i).2 (hℓ i) hv hvu hu]
      ring
    have hpart (v u : ℝ) (hv : 0 < v) (hvu : v ≤ u) (hu : u < ε) :
        u - v ≤ √(Ψ u) * (φ u - φ v) := by
      rw [hsplit v u hv hvu hu]
      refine KurdykaLojasiewiczAux.sub_le_of_forall_sub_le hvu hL
        (hγcont.mono (Icc_subset_Ioo hv hu)) (fun i ↦ hγmono i v u hv hu)
        fun s hs s' hs' _ ↦ (hcurve s s' ⟨hv.trans_le hs.1, hs.2.trans_lt hu⟩
          ⟨hv.trans_le hs'.1, hs'.2.trans_lt hu⟩).trans ?_
      have hΨsu : Ψ s ≤ Ψ u :=
        hΨm ⟨hv.trans_le hs.1, hs.2.trans_lt hu⟩ ⟨hv.trans_le hvu, hu⟩ hs.2
      have := Real.sqrt_le_sqrt hΨsu
      have hD : 0 ≤ ∑ i, |γ s' i - γ s i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      nlinarith
    refine ⟨ε, hε0, φ, hφ0, ?_, ?_, ?_⟩
    · intro a ha b hb hab
      rcases ha.1.eq_or_lt with rfl | ha0
      · rw [hφ0]
        exact hφnn b
      · have := hsplit a b ha0 hab hb.2
        have hD : 0 ≤ ∑ i, |γ b i - γ a i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
        linarith
    · rw [← continuousWithinAt_Ioi_iff_Ici, ContinuousWithinAt, hφ0]
      have h : Tendsto (fun u ↦ ∑ i, |γ u i - ℓ i|) (𝓝[>] 0) (𝓝 0) := by
        have := tendsto_finsetSum Finset.univ fun i _ ↦ ((hℓ i).sub_const (ℓ i)).abs
        simpa using this
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with u (hu : 0 < u)
      simp [hφ_def, hu]
    · intro x hx hFx v hv
      rcases (hf x).eq_or_lt with hu0 | hupos
      · have hv0 : v = 0 := le_antisymm (hu0 ▸ hv.2) hv.1
        rw [← hu0, hv0]
        simp
      have hxu : eval x f ∈ Icc 0 M := hIM _ ⟨hupos, hFx⟩
      have hΨG : √(Ψ (eval x f)) ≤ √(∑ i, eval x (pderiv i f) ^ 2) :=
        Real.sqrt_le_sqrt ((hγ' _ hxu).2.2 x hx rfl)
      have hD (w : ℝ) (hw : 0 < w) (hwu : w ≤ eval x f) :
          eval x f - w ≤ √(∑ i, eval x (pderiv i f) ^ 2) * (φ (eval x f) - φ w) := by
        refine (hpart w _ hw hwu hFx).trans (mul_le_mul_of_nonneg_right hΨG ?_)
        rw [hsplit w _ hw hwu hFx]
        exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
      rcases hv.1.eq_or_lt with rfl | hv0
      · rw [hφ0, sub_zero, sub_zero]
        refine le_of_forall_pos_le_add fun e he ↦ ?_
        set w := min e (eval x f / 2)
        have hw : 0 < w := lt_min he (by linarith)
        have h1 := hD w hw ((min_le_right _ _).trans (by linarith))
        have h2 := mul_le_mul_of_nonneg_left (by linarith [hφnn w] :
          φ (eval x f) - φ w ≤ φ (eval x f)) (Real.sqrt_nonneg (∑ i, eval x (pderiv i f) ^ 2))
        linarith [min_le_left e (eval x f / 2)]
      · exact hD v hv0 hv.2
  · -- `ψ` nonincreasing: it is bounded below by `c² > 0` near `0`, and `φ (u) = u / c`
    set c := √(Ψ (ε / 2))
    have hhalf : ε / 2 ∈ Ioo 0 ε := ⟨by linarith, by linarith⟩
    have hc : 0 < c := by
      refine lt_of_le_of_ne (Real.sqrt_nonneg _) fun hc0 ↦ ?_
      have := KurdykaLojasiewiczAux.sub_le_of_forall_sub_le (a := ε / 2) (b := 3 * ε / 4) (A := c)
        (by linarith) hL (hγcont.mono (Icc_subset_Ioo (by linarith) (by linarith)))
        (fun i ↦ hγmono i _ _ (by linarith) (by linarith)) fun s hs s' hs' _ ↦ ?_
      · rw [← hc0, zero_mul] at this
        linarith
      · have hsI : s ∈ Ioo 0 ε := ⟨by linarith [hs.1], by linarith [hs.2]⟩
        refine (hcurve s s' hsI ⟨by linarith [hs'.1], by linarith [hs'.2]⟩).trans ?_
        have := Real.sqrt_le_sqrt (hΨa hhalf hsI hs.1)
        have hD : 0 ≤ ∑ i, |γ s' i - γ s i| := Finset.sum_nonneg fun i _ ↦ abs_nonneg _
        nlinarith
    refine ⟨ε / 2, by linarith, fun u ↦ u / c, by simp, fun a _ b _ hab ↦
      div_le_div_of_nonneg_right hab hc.le, (continuous_id.div_const c).continuousWithinAt, ?_⟩
    intro x hx hFx v hv
    rcases (hf x).eq_or_lt with hu0 | hupos
    · have hv0 : v = 0 := le_antisymm (hu0 ▸ hv.2) hv.1
      rw [← hu0, hv0]
      simp
    have huI : eval x f ∈ Ioo 0 ε := ⟨hupos, by linarith⟩
    have hcG : c ≤ √(∑ i, eval x (pderiv i f) ^ 2) :=
      Real.sqrt_le_sqrt ((hΨa huI hhalf hFx.le).trans ((hγ' _ (hIM _ huI)).2.2 x hx rfl))
    have hvu : 0 ≤ eval x f - v := by linarith [hv.2]
    calc eval x f - v = c * ((eval x f - v) / c) := by field_simp
      _ ≤ √(∑ i, eval x (pderiv i f) ^ 2) * ((eval x f - v) / c) :=
        mul_le_mul_of_nonneg_right hcG (div_nonneg hvu hc.le)
      _ = √(∑ i, eval x (pderiv i f) ^ 2) * (eval x f / c - v / c) := by ring

/-- The partial derivatives of a nonnegative real polynomial vanish on its zero set. -/
theorem eval_pderiv_eq_zero_of_nonneg {σ : Type*} [Finite σ] (f : MvPolynomial σ ℝ)
    (hf : ∀ x, 0 ≤ eval x f) {x : σ → ℝ} (hx : eval x f = 0) (i : σ) :
    eval x (pderiv i f) = 0 := by
  classical
  have := Fintype.ofFinite σ
  have hmin : IsLocalMin (fun y ↦ eval y f) x :=
    Filter.Eventually.of_forall fun y ↦ by simp only [hx]; exact hf y
  have h := hmin.hasFDerivAt_eq_zero (hasFDerivAt_eval f x)
  have := congrArg (fun D ↦ D (Pi.single i 1)) h
  simpa [Finset.sum_apply, Pi.single_apply] using this

/-- **Real algebraic sets are locally contractible** (in the classical, weak sense): the zero set
of a nonnegative real polynomial. -/
theorem locallyContractibleSpace_setOf_eval_eq_zero_of_nonneg {n : ℕ} (f : MvPolynomial (Fin n) ℝ)
    (hf : ∀ x, 0 ≤ eval x f) : LocallyContractibleSpace {x : Fin n → ℝ | eval x f = 0} := by
  refine locallyContractibleSpace_of_kurdykaLojasiewicz (g := fun x i ↦ eval x (pderiv i f))
    f.continuous_eval (continuous_pi fun i ↦ (pderiv i f).continuous_eval) hf
    (fun x hx ↦ _root_.funext fun i ↦ eval_pderiv_eq_zero_of_nonneg f hf hx i) fun p hp ↦ ?_
  obtain ⟨ε, hε, φ, hφ0, hφm, hφc, hkl⟩ := exists_kurdykaLojasiewicz f hf p hp 1 one_pos
  obtain ⟨L, hL, htay⟩ := exists_taylor_bound f (isCompact_closedBall p (2 * 1))
    (convex_closedBall p (2 * 1))
  exact ⟨1, one_pos, ε, hε, L, hL, φ, fun x hx y hy ↦ by linarith [(abs_le.mp (htay x hx y hy)).2],
    hφ0, hφm, hφc, hkl⟩

/-- **Real algebraic sets are locally contractible** (in the classical, weak sense): the zero set
of a real polynomial. -/
theorem locallyContractibleSpace_setOf_eval_eq_zero {n : ℕ} (f : MvPolynomial (Fin n) ℝ) :
    LocallyContractibleSpace {x : Fin n → ℝ | eval x f = 0} := by
  have h := locallyContractibleSpace_setOf_eval_eq_zero_of_nonneg (f ^ 2) fun x ↦ by
    simpa using sq_nonneg (eval x f)
  have heq : {x : Fin n → ℝ | eval x (f ^ 2) = 0} = {x | eval x f = 0} := by
    ext x
    simp
  rwa [heq] at h

end MvPolynomial
