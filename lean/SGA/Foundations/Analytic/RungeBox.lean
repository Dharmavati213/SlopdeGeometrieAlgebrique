/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeRect
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Polynomial approximation on compact boxes (Oka–Weil for boxes)

* **Taylor polynomials** (`AnalyticGeometry.exists_mvPolynomial_approx_closedBall`): a function
  analytic at every point of the closed polydisc `P̄(0, 2R)` (sup norm on `ℂ^σ`, `σ` finite) is,
  uniformly on `P̄(0, R)`, a limit of polynomials (`MvPolynomial σ ℂ`): truncate its power series
  (`AnalyticGeometry.hasSum_cauchyCoeff`), the tail being dominated by `M ∑ 2^{-|α|}` by the Cauchy
  estimates. Consequently every entire function is a uniform limit of polynomials on every compact
  set (`AnalyticGeometry.exists_mvPolynomial_approx_of_isCompact`).
* **Open boxes** (`AnalyticGeometry.openBox`) form a basis of neighbourhoods of every compact box
  `∏ᵢ [aᵢ, bᵢ]` (`AnalyticGeometry.exists_openBox_subset`).
* **Oka–Weil for compact boxes** (`AnalyticGeometry.exists_mvPolynomial_approx_closedBox`): let
  `Q = ∏ᵢ [aᵢ, bᵢ] ⊆ ℂ^σ` be a product of closed rectangles (possibly degenerate: segments or
  points) and `f` analytic at every point of `Q`. Then `f` is, uniformly on `Q`, a limit of
  polynomials. Proof: `f` is analytic on a slightly larger box `∏ Lᵢ`; Runge approximation on
  products with the rectangle schemes (`AnalyticGeometry.rectScheme`, Cauchy integrals over the
  sides of `Lᵢ` with the kernel expanded around far away centres) gives an entire approximant
  (`AnalyticGeometry.ProductRungeData.exists_approx`), and Taylor polynomials approximate it.

References: Hörmander, *An introduction to complex analysis in several variables*, 2.2 (power
series, Cauchy estimates) and 2.7 (Oka–Weil); Gunning–Rossi, *Analytic functions of several
complex variables*, I.D (polynomial approximation on boxes), III.A.
-/

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

/-! ### Taylor polynomials -/

section Taylor

/-- The monomial `∏ⱼ zⱼ^{αⱼ}` as an `MvPolynomial`, evaluated. -/
private lemma eval_monomial_equivFunOnFinite {τ : Type} [Fintype τ] (α : τ → ℕ) (c : ℂ)
    (z : τ → ℂ) :
    MvPolynomial.eval z (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) c) =
      c * ∏ j, z j ^ α j := by
  rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
  simp

/-- **Taylor polynomials, `Fin n` coordinates**: if `f` is analytic at every point of the closed
polydisc `P̄(0, 2R)`, then for every `ε > 0` some polynomial is `ε`-close to `f` on `P̄(0, R)`. -/
theorem exists_mvPolynomial_approx_closedBall_fin {n : ℕ} {f : (Fin n → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : ∀ z ∈ closedBall (0 : Fin n → ℂ) (2 * R), AnalyticAt ℂ f z) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ P : MvPolynomial (Fin n) ℂ, ∀ z ∈ closedBall (0 : Fin n → ℂ) R,
      ‖f z - MvPolynomial.eval z P‖ < ε := by
  set U : Set (Fin n → ℂ) := {z | AnalyticAt ℂ f z}
  have hU : IsOpen U := isOpen_analyticAt ℂ f
  have hcont : ContinuousOn f U := fun z hz ↦ hz.continuousAt.continuousWithinAt
  have hsep : SeparatelyHolomorphicOn f U := fun z hz j ↦ by
    have h' : AnalyticAt ℂ f (Function.update z j (z j)) := by
      rw [Function.update_eq_self]
      exact hz
    exact h'.differentiableAt.comp (z j) (hasFDerivAt_update z (z j)).differentiableAt
  have hR2 : 0 < 2 * R := by positivity
  have hcU : closedBall (0 : Fin n → ℂ) (2 * R) ⊆ U := hf
  -- a bound for `f` on the closed polydisc
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (2 * R)).exists_bound_of_continuousOn
    (hcont.mono hcU)
  have hMt : ∀ θ, ‖f (torusMap 0 (fun _ ↦ 2 * R) θ)‖ ≤ M := fun θ ↦ by
    refine hM _ (mem_closedBall.mpr ((dist_pi_le_iff hR2.le).mpr fun j ↦ ?_))
    have := torusMap_mem_sphere (0 : Fin n → ℂ) (fun _ ↦ 2 * R) θ j
    rw [mem_sphere, abs_of_pos hR2] at this
    exact this.le
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMt 0)
  -- the dominating series `M ∏ 2^{-αⱼ}`
  set b : (Fin n → ℕ) → ℝ := fun α ↦ M * ∏ j, (1 / 2 : ℝ) ^ α j
  have hb : Summable b := by
    have := (hasSum_prod_geometric (n := n) (x := fun _ ↦ (1 / 2 : ℂ))
      (fun _ ↦ by norm_num)).2
    refine (this.mul_left M).congr fun α ↦ ?_
    simp [b, norm_prod, norm_pow]
  -- a finite set of multi-indices with a small tail
  obtain ⟨F, hF⟩ := ((tendsto_order.1 (tendsto_tsum_compl_atTop_zero b)).2 ε hε).exists
  set a : (Fin n → ℕ) → ℂ := cauchyCoeff f 0 (2 * R)
  refine ⟨∑ α ∈ F, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (a α),
    fun z hz ↦ ?_⟩
  have hzR : ∀ j, ‖z j‖ ≤ R := fun j ↦ by
    simpa using (dist_pi_le_iff hR.le).mp (mem_closedBall.mp hz) j
  set t : (Fin n → ℕ) → ℂ := fun α ↦ a α * ∏ j, (z j - (0 : Fin n → ℂ) j) ^ α j
  have hsum : HasSum t (f z) := hasSum_cauchyCoeff hU hcont hsep hR2 hcU
    (closedBall_subset_ball (by linarith) hz)
  have hbound : ∀ α, ‖t α‖ ≤ b α := fun α ↦ by
    simp only [t, b, Pi.zero_apply, sub_zero, norm_mul, norm_prod, norm_pow]
    calc ‖a α‖ * ∏ j, ‖z j‖ ^ α j ≤ (M * ∏ j, (2 * R)⁻¹ ^ α j) * ∏ j, R ^ α j :=
          mul_le_mul (norm_cauchyCoeff_le hR2 hMt α)
            (Finset.prod_le_prod (fun _ _ ↦ by positivity)
              fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (hzR j) _)
            (by positivity) (by positivity)
      _ = M * ∏ j, (1 / 2 : ℝ) ^ α j := by
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          rw [← mul_pow]
          congr 1
          field_simp
  have heval : MvPolynomial.eval z
      (∑ α ∈ F, MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm α) (a α)) =
      ∑ α ∈ F, t α := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun α _ ↦ ?_
    rw [eval_monomial_equivFunOnFinite]
    simp [t]
  have hsplit : ∑ α ∈ F, t α + ∑' α : {x // x ∉ F}, t α = f z := by
    rw [← hsum.tsum_eq]
    exact hsum.summable.sum_add_tsum_compl
  rw [heval, ← hsplit, add_sub_cancel_left]
  calc ‖∑' α : {x // x ∉ F}, t α‖ ≤ ∑' α : {x // x ∉ F}, b α :=
        tsum_of_norm_bounded (hb.subtype _).hasSum fun α ↦ hbound α
    _ < ε := hF

/-- **Taylor polynomials**: if `f : ℂ^σ → ℂ` (`σ` finite) is analytic at every point of the
closed polydisc `P̄(0, 2R)` (sup norm), then for every `ε > 0` some polynomial is `ε`-close to
`f` on `P̄(0, R)`. -/
theorem exists_mvPolynomial_approx_closedBall {σ : Type} [Fintype σ] {f : (σ → ℂ) → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : ∀ z ∈ closedBall (0 : σ → ℂ) (2 * R), AnalyticAt ℂ f z) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ P : MvPolynomial σ ℂ, ∀ z ∈ closedBall (0 : σ → ℂ) R,
      ‖f z - MvPolynomial.eval z P‖ < ε := by
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  let Φ : (Fin n → ℂ) →L[ℂ] (σ → ℂ) :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (e i)
  have hΦ : ∀ w, Φ w = fun i ↦ w (e i) := fun _ ↦ rfl
  have hΦnorm : ∀ w, ‖Φ w‖ ≤ ‖w‖ := fun w ↦
    (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i ↦ norm_le_pi_norm w (e i)
  obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_closedBall_fin (f := f ∘ Φ) hR
    (fun w hw ↦ (hf (Φ w) (mem_closedBall_zero_iff.mpr ((hΦnorm w).trans
      (mem_closedBall_zero_iff.mp hw)))).comp (Φ.analyticAt w)) hε
  refine ⟨MvPolynomial.rename e.symm P, fun z hz ↦ ?_⟩
  rw [MvPolynomial.eval_rename]
  have hw : z ∘ e.symm ∈ closedBall (0 : Fin n → ℂ) R := by
    refine mem_closedBall_zero_iff.mpr ((pi_norm_le_iff_of_nonneg hR.le).mpr fun j ↦ ?_)
    exact (norm_le_pi_norm z (e.symm j)).trans (mem_closedBall_zero_iff.mp hz)
  have := hP _ hw
  rwa [Function.comp_apply, hΦ, show (fun i ↦ (z ∘ e.symm) (e i)) = z from
    funext fun i ↦ by simp] at this

/-- **Entire functions are uniform limits of polynomials on compact sets.** -/
theorem exists_mvPolynomial_approx_of_isCompact {σ : Type} [Fintype σ] {f : (σ → ℂ) → ℂ}
    (hf : ∀ z, AnalyticAt ℂ f z) {K : Set (σ → ℂ)} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial σ ℂ, ∀ z ∈ K, ‖f z - MvPolynomial.eval z P‖ < ε := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : σ → ℂ)
  obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_closedBall (R := max R 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) (fun z _ ↦ hf z) hε
  exact ⟨P, fun z hz ↦ hP z (closedBall_subset_closedBall (le_max_left _ _) (hR hz))⟩

end Taylor

/-! ### Open boxes around compact boxes -/

section Box

variable {σ : Type}

/-- The open box `∏ᵢ {(aᵢ).re < Re zᵢ < (bᵢ).re, (aᵢ).im < Im zᵢ < (bᵢ).im}` (empty unless all
the rectangles are nonempty). -/
def openBox (a b : σ → ℂ) : Set (σ → ℂ) :=
  univ.pi fun i ↦ Ioo (a i).re (b i).re ×ℂ Ioo (a i).im (b i).im

lemma isOpen_openBox [Finite σ] (a b : σ → ℂ) : IsOpen (openBox a b) :=
  isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo.reProdIm isOpen_Ioo

private lemma abs_sub_clampIcc_lt {a b t ε : ℝ} (hε : 0 < ε) (hab : a ≤ b) (h1 : a - ε < t)
    (h2 : t < b + ε) : |t - clampIcc a b t| < ε := by
  unfold clampIcc
  rcases le_total t a with h | h
  · rw [min_eq_right (h.trans hab), max_eq_left h, abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  · rcases le_total t b with h' | h'
    · rw [min_eq_right h', max_eq_right h, sub_self, abs_zero]
      exact hε
    · rw [min_eq_left h', max_eq_right hab, abs_of_nonneg (by linarith)]
      linarith

/-- The real and imaginary parts of `a ± ε(1 + i)`. -/
private lemma re_im_sub_add (a : ℂ) (ε : ℝ) :
    (a - (ε : ℂ) * (1 + I)).re = a.re - ε ∧ (a - (ε : ℂ) * (1 + I)).im = a.im - ε ∧
      (a + (ε : ℂ) * (1 + I)).re = a.re + ε ∧ (a + (ε : ℂ) * (1 + I)).im = a.im + ε := by
  simp

/-- The compact box `∏ᵢ [aᵢ, bᵢ]` lies in the open box with corners `aᵢ - ε(1 + i)`,
`bᵢ + ε(1 + i)` for every `ε > 0`. -/
lemma pi_closedRect_subset_openBox {a b : σ → ℂ} {ε : ℝ} (hε : 0 < ε) :
    univ.pi (fun i ↦ closedRect (a i) (b i)) ⊆
      openBox (fun i ↦ a i - (ε : ℂ) * (1 + I)) (fun i ↦ b i + (ε : ℂ) * (1 + I)) := by
  intro z hz i _
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz i (mem_univ i)
  obtain ⟨e1, e2, e3, e4⟩ := re_im_sub_add (a i) ε
  obtain ⟨-, -, f3, f4⟩ := re_im_sub_add (b i) ε
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [e1]; linarith
  · rw [f3]; linarith
  · rw [e2]; linarith
  · rw [f4]; linarith

/-- **Open boxes form a basis of neighbourhoods of compact boxes**: if `V` is an open
neighbourhood of the nonempty compact box `∏ᵢ [aᵢ, bᵢ]`, then for some `ε > 0` the open box with
corners `aᵢ - ε(1 + i)`, `bᵢ + ε(1 + i)` (which contains the compact box,
`pi_closedRect_subset_openBox`) lies in `V`. -/
theorem exists_openBox_subset [Finite σ] {a b : σ → ℂ}
    (hab : ∀ i, (a i).re ≤ (b i).re ∧ (a i).im ≤ (b i).im)
    {V : Set (σ → ℂ)} (hV : IsOpen V) (hQV : univ.pi (fun i ↦ closedRect (a i) (b i)) ⊆ V) :
    ∃ ε : ℝ, 0 < ε ∧
      openBox (fun i ↦ a i - (ε : ℂ) * (1 + I)) (fun i ↦ b i + (ε : ℂ) * (1 + I)) ⊆ V := by
  have := Fintype.ofFinite σ
  have hQ : IsCompact (univ.pi fun i ↦ closedRect (a i) (b i)) :=
    isCompact_univ_pi fun i ↦ isCompact_closedRect _ _
  obtain ⟨δ, hδ, hδV⟩ := hQ.exists_thickening_subset_open hV hQV
  refine ⟨δ / 4, by positivity, fun z hz ↦ hδV ?_⟩
  set w : σ → ℂ := fun i ↦ ⟨clampIcc (a i).re (b i).re (z i).re,
    clampIcc (a i).im (b i).im (z i).im⟩ with hwdef
  have hwQ : w ∈ univ.pi fun i ↦ closedRect (a i) (b i) := fun i _ ↦
    ⟨clampIcc_mem (hab i).1 _, clampIcc_mem (hab i).2 _⟩
  refine Metric.mem_thickening_iff.mpr ⟨w, hwQ, ?_⟩
  rw [dist_pi_lt_iff hδ]
  intro i
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz i (mem_univ i)
  obtain ⟨e1, e2, -, -⟩ := re_im_sub_add (a i) (δ / 4)
  obtain ⟨-, -, f3, f4⟩ := re_im_sub_add (b i) (δ / 4)
  rw [e1] at h1
  rw [f3] at h2
  rw [e2] at h3
  rw [f4] at h4
  have hre := abs_sub_clampIcc_lt (by positivity) (hab i).1 (ε := δ / 4) (t := (z i).re) h1 h2
  have him := abs_sub_clampIcc_lt (by positivity) (hab i).2 (ε := δ / 4) (t := (z i).im) h3 h4
  rw [dist_eq_norm]
  calc ‖z i - w i‖ ≤ |(z i - w i).re| + |(z i - w i).im| := norm_le_abs_re_add_abs_im _
    _ < δ / 4 + δ / 4 := by
        simp only [sub_re, sub_im, hwdef]
        exact add_lt_add hre him
    _ < δ := by linarith

end Box

/-! ### Oka–Weil for compact boxes -/

/-- **Polynomial approximation on compact boxes** (Oka–Weil for boxes): let
`Q = ∏ᵢ [aᵢ, bᵢ] ⊆ ℂ^σ` (`σ` finite) be a product of closed rectangles `[aᵢ, bᵢ]`
(`(aᵢ).re ≤ (bᵢ).re`, `(aᵢ).im ≤ (bᵢ).im`; degenerate rectangles, i.e. segments and points, are
allowed) and let `f` be analytic at every point of `Q`. Then for every `ε > 0` there is a
polynomial `P` with `|f - P| < ε` on `Q`. -/
theorem exists_mvPolynomial_approx_closedBox {σ : Type} [Fintype σ] {a b : σ → ℂ}
    (hab : ∀ i, (a i).re ≤ (b i).re ∧ (a i).im ≤ (b i).im) {f : (σ → ℂ) → ℂ}
    (hf : ∀ z ∈ univ.pi (fun i ↦ closedRect (a i) (b i)), AnalyticAt ℂ f z) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ P : MvPolynomial σ ℂ, ∀ z ∈ univ.pi (fun i ↦ closedRect (a i) (b i)),
      ‖f z - MvPolynomial.eval z P‖ < ε := by
  -- `f` is analytic on an open box around `Q`
  obtain ⟨δ, hδ, hδV⟩ := exists_openBox_subset hab (isOpen_analyticAt ℂ f) hf
  -- the slightly larger compact box `∏ Lᵢ`
  set a' : σ → ℂ := fun i ↦ a i - ((δ / 2 : ℝ) : ℂ) * (1 + I)
  set b' : σ → ℂ := fun i ↦ b i + ((δ / 2 : ℝ) : ℂ) * (1 + I)
  have ha' : ∀ i, (a' i).re = (a i).re - δ / 2 ∧ (a' i).im = (a i).im - δ / 2 := fun i ↦
    ⟨(re_im_sub_add (a i) (δ / 2)).1, (re_im_sub_add (a i) (δ / 2)).2.1⟩
  have hb' : ∀ i, (b' i).re = (b i).re + δ / 2 ∧ (b' i).im = (b i).im + δ / 2 := fun i ↦
    ⟨(re_im_sub_add (b i) (δ / 2)).2.2.1, (re_im_sub_add (b i) (δ / 2)).2.2.2⟩
  have hL : ∀ z ∈ univ.pi (fun i ↦ closedRect (a' i) (b' i)), AnalyticAt ℂ f z := by
    intro z hz
    refine hδV fun i _ ↦ ?_
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz i (mem_univ i)
    obtain ⟨e1, e2, -, -⟩ := re_im_sub_add (a i) δ
    obtain ⟨-, -, f3, f4⟩ := re_im_sub_add (b i) δ
    rw [(ha' i).1] at h1
    rw [(hb' i).1] at h2
    rw [(ha' i).2] at h3
    rw [(hb' i).2] at h4
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · change (a i - (δ : ℂ) * (1 + I)).re < (z i).re
      rw [e1]; linarith
    · change (z i).re < (b i + (δ : ℂ) * (1 + I)).re
      rw [f3]; linarith
    · change (a i - (δ : ℂ) * (1 + I)).im < (z i).im
      rw [e2]; linarith
    · change (z i).im < (b i + (δ : ℂ) * (1 + I)).im
      rw [f4]; linarith
  -- an entire approximant, by Runge approximation with the rectangle schemes
  let D : ProductRungeData σ :=
    { K := fun i ↦ closedRect (a i) (b i)
      L := fun i ↦ closedRect (a' i) (b' i)
      Ω := fun _ ↦ univ
      isCompact_K := fun i ↦ isCompact_closedRect _ _
      K_subset_L := fun i z hz ↦ by
        obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
        refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
        · rw [(ha' i).1]; linarith
        · rw [(hb' i).1]; linarith
        · rw [(ha' i).2]; linarith
        · rw [(hb' i).2]; linarith
      K_subset_Ω := fun _ ↦ subset_univ _
      scheme := fun i ↦ rectScheme univ (by rw [(ha' i).1]; linarith)
        (by rw [(hb' i).1]; linarith) (by rw [(ha' i).2]; linarith)
        (by rw [(hb' i).2]; linarith) (hab i).1 (hab i).2 }
  obtain ⟨g, hg, hfg⟩ := D.exists_approx hL (by positivity : 0 < ε / 2)
  have hg' : ∀ z, AnalyticAt ℂ g z := fun z ↦ hg z fun i _ ↦ mem_univ _
  -- Taylor polynomials of the entire approximant
  obtain ⟨P, hP⟩ := exists_mvPolynomial_approx_of_isCompact hg'
    (isCompact_univ_pi fun i ↦ isCompact_closedRect (a i) (b i)) (by positivity : 0 < ε / 2)
  refine ⟨P, fun z hz ↦ ?_⟩
  calc ‖f z - MvPolynomial.eval z P‖ ≤ ‖f z - g z‖ + ‖g z - MvPolynomial.eval z P‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hfg z hz) (hP z hz)
    _ = ε := add_halves ε

/-- **Oka–Weil for compact boxes**, in the form requested by `an-coh`: rectangles given as
`{t | t.re ∈ [aᵢ, bᵢ], t.im ∈ [cᵢ, dᵢ]}`. -/
theorem exists_mvPolynomial_approx_of_isBox {σ : Type} [Fintype σ] (Q : σ → Set ℂ)
    (hQ : ∀ i, ∃ a b c d : ℝ, a ≤ b ∧ c ≤ d ∧ Q i = {t | t.re ∈ Icc a b ∧ t.im ∈ Icc c d})
    {f : (σ → ℂ) → ℂ} (hf : ∀ z ∈ univ.pi Q, AnalyticAt ℂ f z) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : MvPolynomial σ ℂ, ∀ z ∈ univ.pi Q, ‖f z - MvPolynomial.eval z P‖ < ε := by
  choose a b c d hab hcd hQi using hQ
  have hQ' : univ.pi Q = univ.pi fun i ↦ closedRect ⟨a i, c i⟩ ⟨b i, d i⟩ := by
    refine congrArg _ (funext fun i ↦ ?_)
    rw [hQi i]
    rfl
  rw [hQ'] at hf ⊢
  exact exists_mvPolynomial_approx_closedBox (fun i ↦ ⟨hab i, hcd i⟩) hf hε

end AnalyticGeometry
