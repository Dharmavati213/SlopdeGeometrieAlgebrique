/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Gradient descent retracts a neighbourhood onto the zero set of a Kurdyka–Łojasiewicz function

Let `F : ℝ^σ → ℝ` be nonnegative with "gradient" `g`, in the weak sense of a one-sided Taylor
bound `F y ≤ F x + ⟨g x, y - x⟩ + L ‖y - x‖²` near a zero `p` of `F`, and assume the
**Kurdyka–Łojasiewicz inequality** near `p`: there is a nondecreasing `φ` on `[0, ε)`, continuous
at `0` with `φ 0 = 0`, such that
`F x - v ≤ |g x| (φ (F x) - φ v)` for `0 ≤ v ≤ F x < ε` (`|·|` the euclidean norm).

Then the iterates of the gradient step `T x = x - α g x` (`α` small) converge, uniformly on a
neighbourhood of `p`, to a continuous retraction `r` onto `F⁻¹(0)` with `‖r x - x‖ ≤ 2 φ (F x)`
(`exists_retraction_of_kurdykaLojasiewicz`): each step decreases `F` by `α/2 |g|²`, and the
inequality turns this into `‖T x - x‖ ≤ 2 (φ (F x) - φ (F (T x)))`, a telescoping bound on the
length of the whole trajectory. Consequently the zero set of `F` is locally contractible at `p` in
the weak (classical) sense: small neighbourhoods contract inside larger ones, by
`(y, t) ↦ r ((1 - t) y + t p)` (`exists_nullhomotopic_inclusion_of_retraction`; for the whole
zero set, `locallyContractibleSpace_of_kurdykaLojasiewicz`).

This is the discrete version of Łojasiewicz's gradient-flow argument; no differential equation is
solved.

## References

* [S. Łojasiewicz, *Ensembles semi-analytiques*, IHES notes, 1965][Lojasiewicz1965]
* [P.-A. Absil, R. Mahony, B. Andrews, *Convergence of the iterates of descent methods for analytic
  cost functions*, SIAM J. Optim. 16 (2005)][AbsilMahonyAndrews2005]
* [J. Bolte, A. Daniilidis, A. Lewis, *The Łojasiewicz inequality for nonsmooth subanalytic
  functions*, SIAM J. Optim. 17 (2007)][BolteDaniilidisLewis2007]
-/

open Set Filter Topology Metric

variable {σ : Type*} [Fintype σ]

namespace KurdykaLojasiewicz

/-- The euclidean norm squared of `v : ℝ^σ`. -/
private def sqNorm (v : σ → ℝ) : ℝ := ∑ i, v i ^ 2

private lemma sqNorm_nonneg (v : σ → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

private lemma norm_le_sqrt_sqNorm (v : σ → ℝ) : ‖v‖ ≤ √(sqNorm v) := by
  refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i ↦ ?_
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ ↦ sq_nonneg (v j)) (Finset.mem_univ i))

end KurdykaLojasiewicz

open KurdykaLojasiewicz

/-- **Gradient descent retraction.** Let `F ≥ 0` vanish at `p`, with "gradient" `g` (a one-sided
Taylor bound on `closedBall p (2 * R)`, `g = 0` on `F⁻¹(0)`), and satisfy the
Kurdyka–Łojasiewicz inequality with desingularizing function `φ` on `closedBall p R`. Then a
neighbourhood `ball p δ` retracts continuously onto `F⁻¹(0)`, by a retraction `r` moving each
point `x` by at most `2 φ (F x)`. -/
theorem exists_retraction_of_kurdykaLojasiewicz {F : (σ → ℝ) → ℝ} {g : (σ → ℝ) → σ → ℝ}
    {p : σ → ℝ} {R ε L : ℝ} {φ : ℝ → ℝ} (hR : 0 < R) (hε : 0 < ε) (hL : 0 ≤ L)
    (hF : Continuous F) (hg : Continuous g) (hF0 : ∀ x, 0 ≤ F x) (hFp : F p = 0)
    (hzero : ∀ x, F x = 0 → g x = 0)
    (htaylor : ∀ x ∈ closedBall p (2 * R), ∀ y ∈ closedBall p (2 * R),
      F y ≤ F x + ∑ i, g x i * (y i - x i) + L * ‖y - x‖ ^ 2)
    (hφ0 : φ 0 = 0) (hφm : MonotoneOn φ (Ico 0 ε)) (hφc : ContinuousWithinAt φ (Ici 0) 0)
    (hkl : ∀ x ∈ closedBall p R, F x < ε → ∀ v ∈ Icc 0 (F x),
      F x - v ≤ √(∑ i, g x i ^ 2) * (φ (F x) - φ v)) :
    ∃ δ > 0, ∃ r : (σ → ℝ) → σ → ℝ, ContinuousOn r (ball p δ) ∧
      (∀ x ∈ ball p δ, F (r x) = 0) ∧ (∀ x ∈ ball p δ, F x = 0 → r x = x) ∧
      ∀ x ∈ ball p δ, ‖r x - x‖ ≤ 2 * φ (F x) := by
  set G : (σ → ℝ) → ℝ := fun x ↦ sqNorm (g x) with hG_def
  have hG0 (x) : 0 ≤ G x := sqNorm_nonneg _
  have hgG (x) : ‖g x‖ ≤ √(G x) := norm_le_sqrt_sqNorm _
  have hφ_nonneg : ∀ t ∈ Ico 0 ε, 0 ≤ φ t := fun t ht ↦
    hφ0 ▸ hφm ⟨le_rfl, hε⟩ ht ht.1
  -- the step size
  obtain ⟨M, hM⟩ := (isCompact_closedBall p R).exists_bound_of_continuousOn hg.continuousOn
  set M' := max M 0
  set α := min (1 / (2 * (L + 1))) (R / (M' + 1)) with hα_def
  have hM' : 0 ≤ M' := le_max_right _ _
  have hα : 0 < α := lt_min (by positivity) (by positivity)
  have hαL : α * L ≤ 1 / 2 := by
    calc α * L ≤ 1 / (2 * (L + 1)) * L := mul_le_mul_of_nonneg_right (min_le_left _ _) hL
      _ ≤ 1 / 2 := by
        rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hαM : α * M' ≤ R := by
    calc α * M' ≤ R / (M' + 1) * M' := mul_le_mul_of_nonneg_right (min_le_right _ _) hM'
      _ ≤ R := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith
  set T : (σ → ℝ) → σ → ℝ := fun x ↦ x - α • g x with hT_def
  have hT : Continuous T := continuous_id.sub (hg.const_smul α)
  -- one step
  have step (x : σ → ℝ) (hx : x ∈ closedBall p R) (hFx : F x < ε) :
      F (T x) ≤ F x - α / 2 * G x ∧ ‖T x - x‖ ≤ 2 * (φ (F x) - φ (F (T x))) := by
    have hTx : T x - x = -(α • g x) := by simp [hT_def]
    have hnorm : ‖T x - x‖ ≤ α * √(G x) := by
      rw [hTx, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
      exact mul_le_mul_of_nonneg_left (hgG x) hα.le
    have hx2 : x ∈ closedBall p (2 * R) := closedBall_subset_closedBall (by linarith) hx
    have hTx2 : T x ∈ closedBall p (2 * R) := by
      rw [mem_closedBall] at hx ⊢
      calc dist (T x) p ≤ dist (T x) x + dist x p := dist_triangle _ _ _
        _ ≤ α * M' + R := by
          refine add_le_add ?_ hx
          rw [dist_eq_norm, hTx, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hα]
          exact mul_le_mul_of_nonneg_left ((hM x hx).trans (le_max_left _ _)) hα.le
        _ ≤ 2 * R := by linarith
    have hdec : F (T x) ≤ F x - α / 2 * G x := by
      have h := htaylor x hx2 (T x) hTx2
      have hsum : ∑ i, g x i * (T x i - x i) = -(α * G x) := by
        simp only [hT_def, hG_def, sqNorm, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
          Finset.mul_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        ring
      have hsq : ‖T x - x‖ ^ 2 ≤ α ^ 2 * G x := by
        calc ‖T x - x‖ ^ 2 ≤ (α * √(G x)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
          _ = α ^ 2 * G x := by rw [mul_pow, Real.sq_sqrt (hG0 x)]
      rw [hsum] at h
      have : L * ‖T x - x‖ ^ 2 ≤ α / 2 * G x := by
        calc L * ‖T x - x‖ ^ 2 ≤ L * (α ^ 2 * G x) := mul_le_mul_of_nonneg_left hsq hL
          _ = (α * L) * α * G x := by ring
          _ ≤ 1 / 2 * α * G x := by gcongr; exact hG0 x
          _ = α / 2 * G x := by ring
      linarith
    refine ⟨hdec, ?_⟩
    have hFT0 := hF0 (T x)
    have hFTle : F (T x) ≤ F x :=
      hdec.trans (by linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ α / 2) (hG0 x)])
    have hkl' := hkl x hx hFx (F (T x)) ⟨hFT0, hFTle⟩
    have hD : 0 ≤ φ (F x) - φ (F (T x)) :=
      sub_nonneg.mpr (hφm ⟨hFT0, hFTle.trans_lt hFx⟩ ⟨hF0 x, hFx⟩ hFTle)
    refine hnorm.trans ?_
    rcases (Real.sqrt_nonneg (G x)).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]
      linarith
    · have : α / 2 * √(G x) * √(G x) ≤ √(G x) * (φ (F x) - φ (F (T x))) := by
        calc α / 2 * √(G x) * √(G x) = α / 2 * G x := by
              rw [mul_assoc, Real.mul_self_sqrt (hG0 x)]
          _ ≤ F x - F (T x) := by linarith
          _ ≤ _ := hkl'
      have := le_of_mul_le_mul_right (by linarith : α / 2 * √(G x) * √(G x) ≤
        (φ (F x) - φ (F (T x))) * √(G x)) hpos
      linarith
  -- the orbit of a point near `p`
  have orbit (x₀ : σ → ℝ) (hF₀ : F x₀ < ε) (hd : dist x₀ p + 2 * φ (F x₀) ≤ R) (k : ℕ) :
      (T^[k] x₀ ∈ closedBall p R ∧ F (T^[k] x₀) ≤ F x₀) ∧ ∀ m ≤ k,
        F (T^[k] x₀) ≤ F (T^[m] x₀) ∧
        ‖T^[k] x₀ - T^[m] x₀‖ ≤ 2 * (φ (F (T^[m] x₀)) - φ (F (T^[k] x₀))) := by
    induction k with
    | zero =>
      refine ⟨⟨?_, le_rfl⟩, fun m hm ↦ ?_⟩
      · rw [Function.iterate_zero_apply, mem_closedBall]
        linarith [hφ_nonneg _ ⟨hF0 x₀, hF₀⟩]
      · obtain rfl : m = 0 := Nat.le_zero.mp hm
        simp
    | succ k ih =>
      obtain ⟨⟨hk, hFk⟩, hkm⟩ := ih
      have hFk' : F (T^[k] x₀) < ε := hFk.trans_lt hF₀
      obtain ⟨hdec, hstep⟩ := step _ hk hFk'
      have hle : F (T (T^[k] x₀)) ≤ F (T^[k] x₀) :=
        hdec.trans (by linarith [mul_nonneg (by linarith : (0 : ℝ) ≤ α / 2) (hG0 (T^[k] x₀))])
      have hdist : ‖T (T^[k] x₀) - x₀‖ ≤ 2 * (φ (F x₀) - φ (F (T (T^[k] x₀)))) := by
        have h0 := (hkm 0 (Nat.zero_le _)).2
        simp only [Function.iterate_zero_apply] at h0
        calc ‖T (T^[k] x₀) - x₀‖ ≤ ‖T (T^[k] x₀) - T^[k] x₀‖ + ‖T^[k] x₀ - x₀‖ :=
              norm_sub_le_norm_sub_add_norm_sub _ _ _
          _ ≤ _ := by linarith
      rw [Function.iterate_succ_apply']
      refine ⟨⟨?_, hle.trans hFk⟩, fun m hm ↦ ?_⟩
      · rw [mem_closedBall]
        calc dist (T (T^[k] x₀)) p ≤ dist (T (T^[k] x₀)) x₀ + dist x₀ p := dist_triangle _ _ _
          _ ≤ R := by
            rw [dist_eq_norm]
            linarith [hφ_nonneg (F (T (T^[k] x₀))) ⟨hF0 _, (hle.trans hFk).trans_lt hF₀⟩]
      · rcases Nat.lt_or_eq_of_le hm with hm | rfl
        · obtain ⟨hFm, hm'⟩ := hkm m (Nat.lt_succ_iff.mp hm)
          refine ⟨hle.trans hFm, ?_⟩
          calc _ ≤ ‖T (T^[k] x₀) - T^[k] x₀‖ + ‖T^[k] x₀ - T^[m] x₀‖ :=
                norm_sub_le_norm_sub_add_norm_sub _ _ _
            _ ≤ _ := by linarith
        · rw [Function.iterate_succ_apply']
          simp
  -- uniform decay of `F` along orbits
  set Φ := φ (ε / 2)
  have hdecay (x₀ : σ → ℝ) (hF₀ : F x₀ ≤ ε / 2) (hd : dist x₀ p + 2 * φ (F x₀) ≤ R) (η : ℝ)
      (hη : 0 < η) (k : ℕ) (hk : Φ ^ 2 * ε / (α * η ^ 2) < k) : F (T^[k] x₀) < η := by
    have hF₀' : F x₀ < ε := by linarith
    by_contra hcon
    rw [not_lt] at hcon
    have hall : ∀ j ≤ k, η ≤ F (T^[j] x₀) := fun j hj ↦ hcon.trans ((orbit x₀ hF₀' hd k).2 j hj).1
    have hG (j : ℕ) (hj : j ≤ k) : η ^ 2 ≤ Φ ^ 2 * G (T^[j] x₀) := by
      have hxj := (orbit x₀ hF₀' hd j).1
      have hFj : F (T^[j] x₀) ≤ ε / 2 := hxj.2.trans hF₀
      have h := hkl _ hxj.1 (by linarith) 0 ⟨le_rfl, hF0 _⟩
      rw [hφ0, sub_zero, sub_zero] at h
      have hφle : φ (F (T^[j] x₀)) ≤ Φ :=
        hφm ⟨hF0 _, by linarith⟩ ⟨by linarith, by linarith⟩ hFj
      have h2 : η ≤ √(G (T^[j] x₀)) * Φ :=
        (hall j hj).trans (h.trans (mul_le_mul_of_nonneg_left hφle (Real.sqrt_nonneg _)))
      have := pow_le_pow_left₀ hη.le h2 2
      rwa [mul_pow, Real.sq_sqrt (hG0 _), mul_comm] at this
    have hsum : ∀ j ≤ k, Φ ^ 2 * F (T^[j] x₀) ≤ Φ ^ 2 * F x₀ - j * (α / 2 * η ^ 2) := by
      intro j hj
      induction j with
      | zero => simp
      | succ j ihj =>
        have hj' : j ≤ k := Nat.le_of_succ_le hj
        have hxj := (orbit x₀ hF₀' hd j).1
        have hdec := (step _ hxj.1 (hxj.2.trans_lt hF₀')).1
        rw [Function.iterate_succ_apply']
        have h1 := ihj hj'
        have h2 := hG j hj'
        have h3 := mul_le_mul_of_nonneg_left hdec (sq_nonneg Φ)
        push_cast
        nlinarith
    have h1 := hsum k le_rfl
    have hΦF : Φ ^ 2 * F x₀ ≤ Φ ^ 2 * (ε / 2) := mul_le_mul_of_nonneg_left hF₀ (sq_nonneg _)
    have h2 : Φ ^ 2 * ε < k * (α * η ^ 2) := by rwa [div_lt_iff₀ (by positivity)] at hk
    nlinarith [mul_nonneg (sq_nonneg Φ) (hF0 (T^[k] x₀))]
  -- `φ η` is small for small `η`
  have hφsmall (e : ℝ) (he : 0 < e) : ∃ η > 0, η < ε / 2 ∧ 2 * φ η < e := by
    have h1 : Tendsto φ (𝓝[>] 0) (𝓝 0) := by
      have := hφc.tendsto.mono_left (nhdsWithin_mono (0 : ℝ) Ioi_subset_Ici_self)
      rwa [hφ0] at this
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ), 2 * φ η < e ∧ η < ε / 2 :=
      ((h1.const_mul 2).eventually (gt_mem_nhds (by simpa using he))).and
        (nhdsWithin_le_nhds (gt_mem_nhds (by linarith)))
    obtain ⟨η, ⟨h1, h2⟩, hη⟩ := (hev.and self_mem_nhdsWithin).exists
    exact ⟨η, hη, h2, h1⟩
  -- the neighbourhood
  have hnear : ∀ᶠ x in 𝓝 p, F x < ε / 2 ∧ dist x p + 2 * φ (F x) < R := by
    have hF' : Tendsto F (𝓝 p) (𝓝 0) := hFp ▸ hF.tendsto p
    have hFt : Tendsto F (𝓝 p) (𝓝[Ici 0] 0) :=
      tendsto_nhdsWithin_iff.mpr ⟨hF', Eventually.of_forall fun x ↦ hF0 x⟩
    have hφF : Tendsto (fun x ↦ φ (F x)) (𝓝 p) (𝓝 0) := hφ0 ▸ hφc.tendsto.comp hFt
    have hd : Tendsto (fun x ↦ dist x p + 2 * φ (F x)) (𝓝 p) (𝓝 0) := by
      have := (tendsto_id.dist (tendsto_const_nhds (x := p))).add (hφF.const_mul 2)
      simpa using this
    exact (hF'.eventually (gt_mem_nhds (by linarith))).and (hd.eventually (gt_mem_nhds hR))
  obtain ⟨δ, hδ, hδball⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  -- Cauchy bound
  have hcauchy (x : σ → ℝ) (hx : x ∈ ball p δ) (η : ℝ) (hη : 0 < η) (hηε : η < ε / 2) (m k : ℕ)
      (hm : Φ ^ 2 * ε / (α * η ^ 2) < m) (hmk : m ≤ k) : ‖T^[k] x - T^[m] x‖ ≤ 2 * φ η := by
    obtain ⟨hx1, hx2⟩ := hδball x hx
    have ho := (orbit x (by linarith) hx2.le k).2 m hmk
    have hFk := (orbit x (by linarith) hx2.le k).1.2
    have hFm := hdecay x hx1.le hx2.le η hη m hm
    have hφk : 0 ≤ φ (F (T^[k] x)) := hφ_nonneg _ ⟨hF0 _, by linarith⟩
    have hφm' : φ (F (T^[m] x)) ≤ φ η := hφm ⟨hF0 _, by linarith⟩ ⟨hη.le, by linarith⟩ hFm.le
    linarith [ho.2]
  -- the limit
  set r : (σ → ℝ) → σ → ℝ := fun x ↦ limUnder atTop fun k ↦ T^[k] x
  have hlim (x : σ → ℝ) (hx : x ∈ ball p δ) : Tendsto (fun k ↦ T^[k] x) atTop (𝓝 (r x)) := by
    refine tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete ?_)
    refine Metric.cauchySeq_iff'.mpr fun e he ↦ ?_
    obtain ⟨η, hη, hηε, hφη⟩ := hφsmall e he
    obtain ⟨N, hN⟩ := exists_nat_gt (Φ ^ 2 * ε / (α * η ^ 2))
    exact ⟨N, fun k hk ↦ by
      rw [dist_eq_norm]
      exact (hcauchy x hx η hη hηε N k hN hk).trans_lt hφη⟩
  have hunif (x : σ → ℝ) (hx : x ∈ ball p δ) (η : ℝ) (hη : 0 < η) (hηε : η < ε / 2) (k : ℕ)
      (hk : Φ ^ 2 * ε / (α * η ^ 2) < k) : ‖T^[k] x - r x‖ ≤ 2 * φ η := by
    refine le_of_tendsto ((tendsto_const_nhds (x := T^[k] x)).sub (hlim x hx)).norm ?_
    filter_upwards [eventually_ge_atTop k] with j hj
    rw [norm_sub_rev]
    exact hcauchy x hx η hη hηε k j hk hj
  have hTU : TendstoUniformlyOn (fun k ↦ T^[k]) r atTop (ball p δ) := by
    refine Metric.tendstoUniformlyOn_iff.mpr fun e he ↦ ?_
    obtain ⟨η, hη, hηε, hφη⟩ := hφsmall e he
    obtain ⟨N, hN⟩ := exists_nat_gt (Φ ^ 2 * ε / (α * η ^ 2))
    filter_upwards [eventually_ge_atTop N] with k hk x hx
    rw [dist_eq_norm, norm_sub_rev]
    exact (hunif x hx η hη hηε k (hN.trans_le (by exact_mod_cast hk))).trans_lt hφη
  refine ⟨δ, hδ, r, hTU.continuousOn (Frequently.of_forall fun k ↦ (hT.iterate k).continuousOn),
    fun x hx ↦ ?_, fun x hx hFx ↦ ?_, fun x hx ↦ ?_⟩
  · -- `F (r x) = 0`
    obtain ⟨hx1, hx2⟩ := hδball x hx
    refine le_antisymm (not_lt.mp fun hpos ↦ ?_) (hF0 _)
    set η := min (F (r x) / 2) (ε / 4)
    have hη : 0 < η := lt_min (by linarith) (by linarith)
    obtain ⟨N, hN⟩ := exists_nat_gt (Φ ^ 2 * ε / (α * η ^ 2))
    have hle : F (r x) ≤ η := by
      refine le_of_tendsto ((hF.tendsto _).comp (hlim x hx)) ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      exact (hdecay x hx1.le hx2.le η hη k (hN.trans_le (by exact_mod_cast hk))).le
    linarith [min_le_left (F (r x) / 2) (ε / 4)]
  · -- `r` fixes the zeros of `F`
    have hTx : T x = x := by simp [hT_def, hzero x hFx]
    have hconst : (fun k ↦ T^[k] x) = fun _ ↦ x := funext fun k ↦ Function.iterate_fixed hTx k
    exact tendsto_nhds_unique (hlim x hx) (hconst ▸ tendsto_const_nhds)
  · -- the displacement
    obtain ⟨hx1, hx2⟩ := hδball x hx
    refine le_of_tendsto ((hlim x hx).sub (tendsto_const_nhds (x := x))).norm ?_
    refine Eventually.of_forall fun k ↦ ?_
    have ho := ((orbit x (by linarith) hx2.le k).2 0 (Nat.zero_le _)).2
    have hFk := (orbit x (by linarith) hx2.le k).1.2
    simp only [Function.iterate_zero_apply] at ho
    linarith [hφ_nonneg (F (T^[k] x)) ⟨hF0 _, by linarith⟩]

/-- If a neighbourhood `ball p δ` of a point `p` of `Z ⊆ ℝ^σ` retracts continuously onto `Z`
(near `p`), then `Z` is locally contractible at `p` in the classical sense: every neighbourhood
`U` of `p` in `Z` contains a neighbourhood `V` whose inclusion into `U` is null-homotopic. -/
theorem exists_nullhomotopic_inclusion_of_retraction {Z : Set (σ → ℝ)} {p : σ → ℝ} (hp : p ∈ Z)
    {δ : ℝ} (hδ : 0 < δ) {r : (σ → ℝ) → σ → ℝ} (hr : ContinuousOn r (ball p δ))
    (hrZ : ∀ x ∈ ball p δ, r x ∈ Z) (hrid : ∀ x ∈ ball p δ, x ∈ Z → r x = x)
    (U : Set Z) (hU : U ∈ 𝓝 (⟨p, hp⟩ : Z)) :
    ∃ (V : Set Z) (hVU : V ⊆ U), V ∈ 𝓝 (⟨p, hp⟩ : Z) ∧
      ContinuousMap.Nullhomotopic (ContinuousMap.inclusion hVU) := by
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.mp hU
  have hrp : r p = p := hrid p (mem_ball_self hδ) hp
  have hrc : ContinuousAt r p := hr.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ))
  obtain ⟨δ₁, hδ₁, hδ₁r⟩ := Metric.continuousAt_iff.mp hrc ρ hρ
  set δ' := min δ δ₁
  have hδ' : 0 < δ' := lt_min hδ hδ₁
  have hball : ball p δ' ⊆ ball p δ := ball_subset_ball (min_le_left _ _)
  have hmemU (z : σ → ℝ) (hz : z ∈ ball p δ') : (⟨r z, hrZ z (hball hz)⟩ : Z) ∈ U := by
    refine hρU ?_
    rw [mem_ball, Subtype.dist_eq]
    have := hδ₁r (lt_of_lt_of_le (mem_ball.mp hz) (min_le_right _ _))
    rwa [hrp] at this
  set V : Set Z := {z | dist (z : σ → ℝ) p < δ'}
  have hVU : V ⊆ U := fun z hz ↦ by
    have h := hmemU z hz
    rwa [show (⟨r z, _⟩ : Z) = z from Subtype.ext (hrid z (hball hz) z.2)] at h
  refine ⟨V, hVU, ?_, ⟨⟨⟨p, hp⟩, hVU (show dist p p < δ' by simpa using hδ')⟩, ⟨?_⟩⟩⟩
  · refine Metric.mem_nhds_iff.mpr ⟨δ', hδ', fun z hz ↦ ?_⟩
    rw [mem_ball, Subtype.dist_eq] at hz
    exact hz
  -- the straight-line homotopy, pushed into `Z` by `r`
  have hseg (t : unitInterval) (z : V) :
      (1 - (t : ℝ)) • ((z : Z) : σ → ℝ) + (t : ℝ) • p ∈ ball p δ' := by
    rw [mem_ball, dist_eq_norm]
    have : (1 - (t : ℝ)) • ((z : Z) : σ → ℝ) + (t : ℝ) • p - p =
        (1 - (t : ℝ)) • (((z : Z) : σ → ℝ) - p) := by module
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [t.2.2])]
    have hz : ‖((z : Z) : σ → ℝ) - p‖ < δ' := by
      have := z.2
      simpa [V, dist_eq_norm] using this
    calc (1 - (t : ℝ)) * ‖((z : Z) : σ → ℝ) - p‖ ≤ 1 * ‖((z : Z) : σ → ℝ) - p‖ := by
          gcongr; linarith [t.2.1]
      _ < δ' := by rwa [one_mul]
  have hcont : Continuous fun q : unitInterval × V ↦
      r ((1 - (q.1 : ℝ)) • ((q.2 : Z) : σ → ℝ) + (q.1 : ℝ) • p) := by
    refine (hr.mono hball).comp_continuous (by fun_prop) fun q ↦ hseg q.1 q.2
  exact
    { toFun := fun q ↦ ⟨⟨r ((1 - (q.1 : ℝ)) • ((q.2 : Z) : σ → ℝ) + (q.1 : ℝ) • p),
        hrZ _ (hball (hseg q.1 q.2))⟩, hmemU _ (hseg q.1 q.2)⟩
      continuous_toFun := (hcont.subtype_mk _).subtype_mk _
      map_zero_left := fun z ↦ by
        refine Subtype.ext (Subtype.ext ?_)
        simp only [Set.Icc.coe_zero, sub_zero, one_smul, zero_smul, add_zero,
          ContinuousMap.inclusion_apply_coe]
        exact hrid _ (hball (by simpa using hseg 0 z)) (z : Z).2
      map_one_left := fun z ↦ by
        refine Subtype.ext (Subtype.ext ?_)
        simp [hrp] }

/-- **Gradient descent and local contractibility.** Let `F ≥ 0` be continuous on `ℝ^σ`, with a
continuous "gradient" `g` vanishing on `F⁻¹(0)`, and assume that at each zero `p` of `F` the
one-sided Taylor bound and the Kurdyka–Łojasiewicz inequality hold near `p`. Then the zero set
`{x | F x = 0}` is locally contractible in the classical sense. -/
theorem locallyContractibleSpace_of_kurdykaLojasiewicz {F : (σ → ℝ) → ℝ} {g : (σ → ℝ) → σ → ℝ}
    (hF : Continuous F) (hg : Continuous g) (hF0 : ∀ x, 0 ≤ F x)
    (hzero : ∀ x, F x = 0 → g x = 0)
    (hloc : ∀ p, F p = 0 → ∃ R > 0, ∃ ε > 0, ∃ L ≥ 0, ∃ φ : ℝ → ℝ,
      (∀ x ∈ closedBall p (2 * R), ∀ y ∈ closedBall p (2 * R),
        F y ≤ F x + ∑ i, g x i * (y i - x i) + L * ‖y - x‖ ^ 2) ∧
      φ 0 = 0 ∧ MonotoneOn φ (Ico 0 ε) ∧ ContinuousWithinAt φ (Ici 0) 0 ∧
      ∀ x ∈ closedBall p R, F x < ε → ∀ v ∈ Icc 0 (F x),
        F x - v ≤ √(∑ i, g x i ^ 2) * (φ (F x) - φ v)) :
    LocallyContractibleSpace {x | F x = 0} := by
  rintro ⟨p, hp⟩ U hU
  obtain ⟨R, hR, ε, hε, L, hL, φ, htaylor, hφ0, hφm, hφc, hkl⟩ := hloc p hp
  obtain ⟨δ, hδ, r, hr, hrZ, hrid, -⟩ := exists_retraction_of_kurdykaLojasiewicz hR hε hL hF hg
    hF0 hp hzero htaylor hφ0 hφm hφc hkl
  exact exists_nullhomotopic_inclusion_of_retraction (Z := {x | F x = 0}) hp hδ hr hrZ
    (fun x hx _ ↦ hrid x hx ‹_›) U hU
