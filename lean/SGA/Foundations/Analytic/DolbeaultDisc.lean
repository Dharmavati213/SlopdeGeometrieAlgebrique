/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Dolbeault
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# The `∂̄`-equation on a disc

**Dolbeault's lemma on a disc** (Forster, *Lectures on Riemann surfaces*, 13.2; Hörmander,
*An introduction to complex analysis in several variables*, 1.4.4 for discs): for every smooth
`w` on an open disc `B(c, R)` there is a smooth `u` on `B(c, R)` with `∂u/∂z̄ = w`
(`AnalyticGeometry.exists_contDiffOn_dbar_eq_ball`). Only finite radii are formalized; the case
`R = ∞` of Forster 13.2 (the whole plane) needs Runge approximation by polynomials on growing
discs and is not done.

`Dolbeault.lean` solves the equation on a smaller disc (`exists_contDiff_dbar_eq_on_ball`). Here
the solutions on an exhaustion `B(c, rₙ)`, `rₙ ↑ R`, are corrected by Taylor polynomials of the
holomorphic differences (`exists_differentiable_approx`, Runge's theorem for discs), so that they
converge, locally uniformly up to a holomorphic function, to a global solution (Weierstrass
M-test, `differentiableOn_tsum_of_summable_norm`).

This is the one-variable case of the Dolbeault–Grothendieck lemma on discs, a first step towards
Theorem B on polydiscs (`AnalyticGeometry.PolydiscProductVanishingStatement`; the factors `ℂ` and
`ℂ*` there also need `∂̄` on the plane and on annuli).
-/

noncomputable section

open Set Filter Topology Metric
open scoped ContDiff NNReal ENNReal

namespace AnalyticGeometry

lemma dbar_add {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) : dbar (f + g) z = dbar f z + dbar g z := by
  simp only [dbar, fderiv_add hf hg, add_apply]
  ring

lemma dbar_eq_zero_of_differentiableAt {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    dbar f z = 0 :=
  (dbar_eq_zero_iff (hf.restrictScalars ℝ)).mpr hf

/-- **Runge's theorem for discs**: a function holomorphic on `B(c, ρ)` is approximated, uniformly
on the closed disc `B̄(c, r)`, `r < ρ`, by entire functions (its Taylor polynomials). -/
theorem exists_differentiable_approx {h : ℂ → ℂ} {c : ℂ} {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ)
    (hh : DifferentiableOn ℂ h (ball c ρ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧ ∀ z ∈ closedBall c r, ‖h z - P z‖ < ε := by
  set ρ' : ℝ := (r + ρ) / 2
  set r' : ℝ := (r + ρ') / 2
  have hr' : r < r' := by simp only [r', ρ']; linarith
  have hr'ρ' : r' < ρ' := by simp only [r', ρ']; linarith
  have hρ'0 : 0 < ρ' := by simp only [ρ']; linarith
  set ρ'' : ℝ≥0 := ⟨ρ', hρ'0.le⟩
  set r'' : ℝ≥0 := ⟨r', by linarith⟩
  have hρ''0 : 0 < ρ'' := by
    change (0 : ℝ) < ρ'
    exact hρ'0
  have hp := (hh.mono (closedBall_subset_ball (by
    change ρ' < ρ
    simp only [ρ']; linarith))).hasFPowerSeriesOnBall (R := ρ'') hρ''0
  set p := cauchyPowerSeries h c ρ''
  have hU := hp.tendstoUniformlyOn' (r' := r'')
    (ENNReal.coe_lt_coe.mpr (show r'' < ρ'' from by
      change r' < ρ'
      exact hr'ρ'))
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.mp hU ε hε).exists
  refine ⟨fun z => p.partialSum N (z - c), ?_, fun z hz => ?_⟩
  · have : ContDiff ℂ ⊤ fun z => p.partialSum N (z - c) := by
      unfold FormalMultilinearSeries.partialSum
      exact ContDiff.sum fun k _ => (ContinuousMultilinearMap.contDiff _).comp
        (contDiff_pi.2 fun _ => contDiff_id.sub contDiff_const)
    exact this.differentiable (by simp)
  · rw [← dist_eq_norm]
    exact hN z (closedBall_subset_ball hr' hz)

variable {w : ℂ → ℂ} {c : ℂ} {R : ℝ}

/-- **Dolbeault's lemma on a disc** (Forster 13.2): for every smooth `w` on the open disc
`B(c, R)` there is a smooth `u` on `B(c, R)` with `∂u/∂z̄ = w` on `B(c, R)`. Only finite radii
`R : ℝ` are covered; Forster 13.2 also allows `R = ∞` (the whole plane), which is not formalized
here. -/
theorem exists_contDiffOn_dbar_eq_ball (hR : 0 < R) (hw : ContDiffOn ℝ ∞ w (ball c R)) :
    ∃ u : ℂ → ℂ, ContDiffOn ℝ ∞ u (ball c R) ∧ ∀ z ∈ ball c R, dbar u z = w z := by
  classical
  -- the exhaustion `rₙ = R - R / (n + 2)`
  set r : ℕ → ℝ := fun n => R - R / ((n : ℝ) + 2) with hrdef
  have hr_pos : ∀ n, 0 < r n := fun n => by
    simp only [hrdef, sub_pos]
    exact div_lt_self hR (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
  have hr_lt : ∀ n, r n < R := fun n => by
    simp only [hrdef]
    have : 0 < R / ((n : ℝ) + 2) := by positivity
    linarith
  have hr_lt_succ : ∀ n, r n < r (n + 1) := fun n => by
    simp only [hrdef]
    push_cast
    have : R / ((n : ℝ) + 1 + 2) < R / ((n : ℝ) + 2) :=
      div_lt_div_of_pos_left hR (by positivity) (by linarith)
    linarith
  have hr_mono : Monotone r := monotone_nat_of_le_succ fun n => (hr_lt_succ n).le
  -- solutions on the discs of the exhaustion
  have hsol : ∀ n, ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧ ∀ z ∈ ball c (r n), dbar u z = w z := fun n =>
    exists_contDiff_dbar_eq_on_ball (n := ⊤) le_top (hr_pos n) (hr_lt n) hw
  choose u hu hdu using hsol
  -- the correction step
  have step : ∀ n (v : ℂ → ℂ), ContDiff ℝ ∞ v → (∀ z ∈ ball c (r (n + 1)), dbar v z = w z) →
      ∃ v' : ℂ → ℂ, ContDiff ℝ ∞ v' ∧ (∀ z ∈ ball c (r (n + 2)), dbar v' z = w z) ∧
        DifferentiableOn ℂ (v' - v) (ball c (r (n + 1))) ∧
        ∀ z ∈ closedBall c (r n), ‖v' z - v z‖ ≤ (1 / 2) ^ n := by
    intro n v hv hdv
    have hhol : DifferentiableOn ℂ (u (n + 2) - v) (ball c (r (n + 1))) := fun z hz =>
      (differentiableAt_sub_of_dbar_eq ((hu _).differentiable (by simp) z)
        (hv.differentiable (by simp) z) (by
          rw [hdu _ z (ball_subset_ball (hr_mono (by omega)) hz), hdv z hz])).differentiableWithinAt
    obtain ⟨P, hP, hPa⟩ := exists_differentiable_approx (hr_pos n).le (hr_lt_succ n) hhol
      (by positivity : (0 : ℝ) < (1 / 2) ^ n)
    refine ⟨u (n + 2) - P, (hu _).sub (hP.contDiff.restrict_scalars ℝ), fun z hz => ?_, ?_,
      fun z hz => ?_⟩
    · rw [dbar_sub ((hu _).differentiable (by simp) z) ((hP z).restrictScalars ℝ),
        hdu _ z hz, dbar_eq_zero_of_differentiableAt (hP z), sub_zero]
    · have : u (n + 2) - P - v = (u (n + 2) - v) - P := by ring
      rw [this]
      exact hhol.sub hP.differentiableOn
    · have := hPa z hz
      simp only [Pi.sub_apply] at this ⊢
      rw [show u (n + 2) z - P z - v z = u (n + 2) z - v z - P z by ring]
      exact this.le
  -- the corrected sequence
  let V : (n : ℕ) → {v : ℂ → ℂ // ContDiff ℝ ∞ v ∧ ∀ z ∈ ball c (r (n + 1)), dbar v z = w z} :=
    fun n => Nat.rec ⟨u 1, hu 1, hdu 1⟩
      (fun n v => ⟨(step n v.1 v.2.1 v.2.2).choose, (step n v.1 v.2.1 v.2.2).choose_spec.1,
        (step n v.1 v.2.1 v.2.2).choose_spec.2.1⟩) n
  have hV : ∀ n, (V (n + 1)).1 = (step n (V n).1 (V n).2.1 (V n).2.2).choose := fun n => rfl
  set d : ℕ → ℂ → ℂ := fun n => (V (n + 1)).1 - (V n).1 with hddef
  have hd_hol : ∀ n, DifferentiableOn ℂ (d n) (ball c (r (n + 1))) := fun n => by
    simp only [hddef, hV]
    exact (step n (V n).1 (V n).2.1 (V n).2.2).choose_spec.2.2.1
  have hd_bd : ∀ n, ∀ z ∈ closedBall c (r n), ‖d n z‖ ≤ (1 / 2) ^ n := fun n z hz => by
    simp only [hddef, hV, Pi.sub_apply]
    exact (step n (V n).1 (V n).2.1 (V n).2.2).choose_spec.2.2.2 z hz
  -- every point of the disc lies in some `B(c, rₘ)`
  have hexists : ∀ z ∈ ball c R, ∃ m, z ∈ ball c (r m) := by
    intro z hz
    have hlim : Tendsto r atTop (𝓝 R) := by
      have h2 : Tendsto (fun n : ℕ => R / ((n : ℝ) + 2)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2
          tendsto_natCast_atTop_atTop)
      simpa [hrdef] using tendsto_const_nhds.sub h2
    obtain ⟨m, hm⟩ := (hlim.eventually (lt_mem_nhds (mem_ball.mp hz))).exists
    exact ⟨m, mem_ball.mpr hm⟩
  -- the global solution
  have hsum : ∀ z ∈ ball c R, Summable fun n => d n z := by
    intro z hz
    obtain ⟨m, hm⟩ := hexists z hz
    refine Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (by norm_num)
      (by norm_num : (1 / 2 : ℝ) < 1)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop m] with n hn
    exact hd_bd n z (ball_subset_closedBall (ball_subset_ball (hr_mono hn) hm))
  set U : ℂ → ℂ := fun z => (V 0).1 z + ∑' n, d n z with hUdef
  -- on `B(c, rₘ)`, `U` is `Vₘ` plus a holomorphic function
  have hloc : ∀ m, ∃ T : ℂ → ℂ, DifferentiableOn ℂ T (ball c (r m)) ∧
      ∀ z ∈ ball c (r m), U z = (V m).1 z + T z := by
    intro m
    refine ⟨fun z => ∑' n, d (n + m) z, ?_, fun z hz => ?_⟩
    · refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n => (1 / 2 : ℝ) ^ (n + m))
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).comp_injective
          (add_left_injective m)) (fun n => (hd_hol (n + m)).mono
            (ball_subset_ball (hr_mono (by omega)))) isOpen_ball fun n z hz => ?_
      exact hd_bd (n + m) z (ball_subset_closedBall (ball_subset_ball (hr_mono (by omega)) hz))
    · have hzR : z ∈ ball c R := ball_subset_ball (hr_lt m).le hz
      rw [hUdef]
      simp only
      rw [← (hsum z hzR).sum_add_tsum_nat_add m, ← add_assoc]
      congr 1
      have htel := Finset.sum_range_sub (fun n => (V n).1 z) m
      simp only [hddef, Pi.sub_apply] at htel ⊢
      rw [htel]
      ring
  -- smoothness and the equation, pointwise
  have hpt : ∀ z ∈ ball c R, ContDiffAt ℝ ∞ U z ∧ dbar U z = w z := by
    intro z hz
    obtain ⟨m, hm⟩ := hexists z hz
    obtain ⟨T, hT, hUT⟩ := hloc m
    have hev : U =ᶠ[𝓝 z] (V m).1 + T := by
      filter_upwards [isOpen_ball.mem_nhds hm] with z' hz'
      exact hUT z' hz'
    have hTz : DifferentiableAt ℂ T z := hT.differentiableAt (isOpen_ball.mem_nhds hm)
    have hTsmooth : ContDiffAt ℝ ∞ T z :=
      ((hT.contDiffOn (n := ∞) isOpen_ball).restrict_scalars ℝ).contDiffAt
        (isOpen_ball.mem_nhds hm)
    refine ⟨((V m).2.1.contDiffAt.add hTsmooth).congr_of_eventuallyEq hev, ?_⟩
    rw [dbar_congr hev, dbar_add ((V m).2.1.differentiable (by simp) z)
      (hTz.restrictScalars ℝ), (V m).2.2 z (ball_subset_ball (hr_mono (by omega)) hm),
      dbar_eq_zero_of_differentiableAt hTz, add_zero]
  exact ⟨U, fun z hz => (hpt z hz).1.contDiffWithinAt, fun z hz => (hpt z hz).2⟩

end AnalyticGeometry
