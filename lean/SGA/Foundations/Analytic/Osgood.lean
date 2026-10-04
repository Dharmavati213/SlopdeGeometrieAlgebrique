/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.PowerSeriesExpansion
import Mathlib.MeasureTheory.Integral.TorusIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.FDeriv.Pi

/-!
# Holomorphic functions of several variables: Cauchy's formula on polydiscs and Osgood's lemma

Let `U ⊆ ℂⁿ` be open and `f : ℂⁿ → ℂ` continuous on `U` and holomorphic in each variable
separately. Then:

* **Cauchy's integral formula on polydiscs** (`AnalyticGeometry.torusIntegral_cauchy`): for every
  closed polydisc `P̄(c, R) ⊆ U` with all radii equal to the scalar `R > 0` and `z` in the open
  polydisc, `(2πi)ⁿ f(z) = ∯_{T(c, R)} f(ζ) ∏ⱼ (ζⱼ - zⱼ)⁻¹ dζ`;
* **Osgood's lemma** (`AnalyticGeometry.analyticAt_of_continuousOn_of_separately`): `f` is
  analytic on `U`. Expanding the Cauchy kernel in a multiple geometric series gives the power
  series `∑ aₐ (z - c)ᵅ` on the open polydisc (`AnalyticGeometry.hasSum_cauchyCoeff`), with the
  Cauchy estimates `|aₐ| ≤ M R^{-|α|}` (`AnalyticGeometry.norm_cauchyCoeff_le`).

Consequences: `DifferentiableOn ℂ` on an open subset of `ℂⁿ` implies analytic
(`AnalyticGeometry.analyticAt_of_differentiableOn`).

References: Hörmander, *An introduction to complex analysis in several variables*, 2.2.1–2.2.3;
Gunning–Rossi, *Analytic functions of several complex variables*, I.A; Osgood (1899).
-/

noncomputable section

open Complex MeasureTheory Set Metric Filter Topology
open scoped Real NNReal ENNReal

namespace AnalyticGeometry

/-! ### Products of absolutely convergent series -/

/-- The product of finitely many absolutely convergent series is the sum, over all multi-indices,
of the products of terms. -/
theorem hasSum_prod_fin (n : ℕ) : ∀ (g : Fin n → ℕ → ℂ) (s : Fin n → ℂ),
    (∀ j, HasSum (g j) (s j)) → (∀ j, Summable fun k ↦ ‖g j k‖) →
    HasSum (fun α : Fin n → ℕ ↦ ∏ j, g j (α j)) (∏ j, s j) ∧
      Summable fun α : Fin n → ℕ ↦ ‖∏ j, g j (α j)‖ := by
  induction n with
  | zero =>
    intro g s _ _
    simp only [Finset.univ_eq_empty, Finset.prod_empty, norm_one]
    refine ⟨?_, Summable.of_finite⟩
    convert hasSum_fintype (fun _ : Fin 0 → ℕ ↦ (1 : ℂ))
    simp
  | succ n ihn' =>
    intro g s hg hn
    have ih2 := ihn' (fun j ↦ g j.succ) (fun j ↦ s j.succ) (fun j ↦ hg j.succ)
      (fun j ↦ hn j.succ)
    have ih : HasSum (fun β : Fin n → ℕ ↦ ∏ j : Fin n, g j.succ (β j)) (∏ j : Fin n, s j.succ) :=
      ih2.1
    have ihn : Summable fun β : Fin n → ℕ ↦ ‖∏ j : Fin n, g j.succ (β j)‖ := ih2.2
    let e := Fin.consEquiv (fun _ : Fin (n + 1) ↦ ℕ)
    have hcomp : (fun α : Fin (n + 1) → ℕ ↦ ∏ j, g j (α j)) ∘ e =
        fun p : ℕ × (Fin n → ℕ) ↦ g 0 p.1 * ∏ j : Fin n, g j.succ (p.2 j) := by
      funext p
      simp only [Function.comp_apply, Fin.prod_univ_succ]
      rfl
    have hsum : Summable fun p : ℕ × (Fin n → ℕ) ↦ g 0 p.1 * ∏ j : Fin n, g j.succ (p.2 j) :=
      summable_mul_of_summable_norm (f := g 0)
        (g := fun β : Fin n → ℕ ↦ ∏ j : Fin n, g j.succ (β j)) (hn 0) ihn
    have hmul : HasSum (fun p : ℕ × (Fin n → ℕ) ↦ g 0 p.1 * ∏ j : Fin n, g j.succ (p.2 j))
        (s 0 * ∏ j : Fin n, s j.succ) :=
      HasSum.mul (f := g 0) (g := fun β : Fin n → ℕ ↦ ∏ j : Fin n, g j.succ (β j)) (hg 0) ih hsum
    have hnorm : Summable fun p : ℕ × (Fin n → ℕ) ↦
        ‖g 0 p.1‖ * ‖∏ j : Fin n, g j.succ (p.2 j)‖ :=
      Summable.mul_of_nonneg (f := fun k : ℕ ↦ ‖g 0 k‖)
        (g := fun β : Fin n → ℕ ↦ ‖∏ j : Fin n, g j.succ (β j)‖)
        (hn 0) ihn (by intro k; exact norm_nonneg _) (by intro k; exact norm_nonneg _)
    refine ⟨?_, ?_⟩
    · rw [← e.hasSum_iff, hcomp, Fin.prod_univ_succ]
      exact hmul
    · rw [← e.summable_iff]
      have : (fun α : Fin (n + 1) → ℕ ↦ ‖∏ j, g j (α j)‖) ∘ e =
          fun p : ℕ × (Fin n → ℕ) ↦ ‖g 0 p.1‖ * ‖∏ j : Fin n, g j.succ (p.2 j)‖ := by
        funext p
        rw [← norm_mul]
        exact congrArg norm (congrFun hcomp p)
      rw [this]
      exact hnorm

/-- The multiple geometric series `∑ₐ ∏ⱼ xⱼ^{αⱼ} = ∏ⱼ (1 - xⱼ)⁻¹` for `‖xⱼ‖ < 1`. -/
theorem hasSum_prod_geometric {n : ℕ} {x : Fin n → ℂ} (hx : ∀ j, ‖x j‖ < 1) :
    HasSum (fun α : Fin n → ℕ ↦ ∏ j, x j ^ α j) (∏ j, (1 - x j)⁻¹) ∧
      Summable fun α : Fin n → ℕ ↦ ‖∏ j, x j ^ α j‖ :=
  hasSum_prod_fin n (fun j k ↦ x j ^ k) _ (fun j ↦ hasSum_geometric_of_norm_lt_one (hx j))
    fun j ↦ by simpa [norm_pow] using summable_geometric_of_lt_one (norm_nonneg _) (hx j)

/-! ### Torus integrals of continuous functions -/

section Torus

variable {n : ℕ}

lemma continuous_torusMap (c : Fin n → ℂ) (R : Fin n → ℝ) : Continuous (torusMap c R) := by
  unfold torusMap
  fun_prop

lemma torusMap_mem_sphere (c : Fin n → ℂ) (R : Fin n → ℝ) (θ : Fin n → ℝ) (j : Fin n) :
    torusMap c R θ j ∈ sphere (c j) |R j| := by
  rw [mem_sphere, dist_eq_norm]
  simp [torusMap, norm_exp_ofReal_mul_I]

/-- A function continuous on the torus `T(c, R)` is integrable on it. -/
lemma torusIntegrable_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : (Fin n → ℂ) → E}
    {c : Fin n → ℂ} {R : Fin n → ℝ} {S : Set (Fin n → ℂ)} (hf : ContinuousOn f S)
    (hS : ∀ θ, torusMap c R θ ∈ S) : TorusIntegrable f c R :=
  (hf.comp_continuous (continuous_torusMap c R) hS).integrableOn_Icc

end Torus

/-! ### Cauchy's integral formula on polydiscs -/

section Cauchy

/-- `f` is holomorphic in each variable separately at every point of `U`. -/
def SeparatelyHolomorphicOn {σ : Type*} [DecidableEq σ] (f : (σ → ℂ) → ℂ) (U : Set (σ → ℂ)) :
    Prop :=
  ∀ z ∈ U, ∀ j, DifferentiableAt ℂ (fun t ↦ f (Function.update z j t)) (z j)

lemma mem_closedBall_cons {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} {y : Fin n → ℂ}
    (hx : dist x (c 0) ≤ R) (hy : y ∈ closedBall (Fin.tail c) R) :
    (Fin.cons x y : Fin (n + 1) → ℂ) ∈ closedBall c R := by
  have hR : 0 ≤ R := dist_nonneg.trans hx
  have hy' : ∀ j, dist (y j) (Fin.tail c j) ≤ R := (dist_pi_le_iff hR).mp (mem_closedBall.mp hy)
  rw [mem_closedBall, dist_pi_le_iff hR, Fin.forall_fin_succ]
  exact ⟨by simpa using hx, fun j ↦ by simpa [Fin.tail] using hy' j⟩

lemma mem_ball_cons {n : ℕ} {c : Fin (n + 1) → ℂ} {R : ℝ} {x : ℂ} {y : Fin n → ℂ}
    (hx : dist x (c 0) < R) (hy : y ∈ ball (Fin.tail c) R) :
    (Fin.cons x y : Fin (n + 1) → ℂ) ∈ ball c R := by
  have hR : 0 < R := dist_nonneg.trans_lt hx
  have hy' : ∀ j, dist (y j) (Fin.tail c j) < R := (dist_pi_lt_iff hR).mp (mem_ball.mp hy)
  rw [mem_ball, dist_pi_lt_iff hR, Fin.forall_fin_succ]
  exact ⟨by simpa using hx, fun j ↦ by simpa [Fin.tail] using hy' j⟩

/-- **Cauchy's integral formula on polydiscs.** Let `f` be continuous and separately holomorphic on
an open set `U ⊆ ℂⁿ` containing the closed polydisc `P̄(c, R)` (all radii equal to the scalar
`R > 0`, i.e. the closed ball of radius `R` for the sup norm). Then for `z ∈ P(c, R)`,
`∯_{T(c, R)} (∏ⱼ (ζⱼ - zⱼ)⁻¹) f(ζ) dζ = (2πi)ⁿ f(z)`. -/
theorem torusIntegral_cauchy : ∀ (n : ℕ) {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ},
    IsOpen U → ContinuousOn f U → SeparatelyHolomorphicOn f U →
    ∀ {c : Fin n → ℂ} {R : ℝ}, 0 < R → closedBall c R ⊆ U → ∀ {z : Fin n → ℂ}, z ∈ ball c R →
    (∯ ζ in T(c, fun _ ↦ R), (∏ j, (ζ j - z j)⁻¹) • f ζ) = (2 * π * I) ^ n • f z
  | 0, U, f, _, _, _, c, R, _, _, z, _ => by
    rw [torusIntegral_dim0, Subsingleton.elim c z]
    simp
  | n + 1, U, f, hU, hf, hsep, c, R, hR, hcU, z, hz => by
    -- the torus lies in the closed polydisc, away from `z`
    have hzj : ∀ j, ‖z j - c j‖ < R := fun j ↦ by
      have := (dist_pi_lt_iff hR).mp (mem_ball.mp hz) j
      rwa [dist_eq_norm] at this
    have htorus : ∀ θ, torusMap c (fun _ ↦ R) θ ∈ closedBall c R := fun θ ↦ by
      rw [mem_closedBall, dist_pi_le_iff hR.le]
      intro j
      have := torusMap_mem_sphere c (fun _ ↦ R) θ j
      rw [mem_sphere, abs_of_pos hR] at this
      exact this.le
    have hne : ∀ θ j, torusMap c (fun _ ↦ R) θ j - z j ≠ 0 := fun θ j h ↦ by
      have h1 := torusMap_mem_sphere c (fun _ ↦ R) θ j
      rw [mem_sphere, abs_of_pos hR, sub_eq_zero.mp h, dist_eq_norm] at h1
      exact (hzj j).ne h1
    have hint : TorusIntegrable (fun ζ ↦ (∏ j, (ζ j - z j)⁻¹) • f ζ) c (fun _ ↦ R) := by
      set S : Set (Fin (n + 1) → ℂ) := {ζ | ζ ∈ closedBall c R ∧ ∀ j, ζ j - z j ≠ 0}
      refine torusIntegrable_of_continuousOn (S := S) ?_ fun θ ↦ ⟨htorus θ, hne θ⟩
      refine ContinuousOn.smul (f := fun ζ : Fin (n + 1) → ℂ ↦ ∏ j, (ζ j - z j)⁻¹) ?_
        (hf.mono fun ζ (hζ : ζ ∈ S) ↦ hcU hζ.1)
      exact continuousOn_finsetProd _ fun j _ ↦ ((continuous_apply j).sub
        continuous_const).continuousOn.inv₀ fun ζ (hζ : ζ ∈ S) ↦ hζ.2 j
    rw [torusIntegral_succ hint]
    -- the inner integral, by induction
    set z' : Fin n → ℂ := Fin.tail z
    have hz' : z' ∈ ball (Fin.tail c) R := by
      rw [mem_ball, dist_pi_lt_iff hR]
      intro j
      exact (dist_pi_lt_iff hR).mp (mem_ball.mp hz) j.succ
    have hinner : ∀ x ∈ sphere (c 0) R,
        (∯ y in T(c ∘ Fin.succ, (fun _ : Fin (n + 1) ↦ R) ∘ Fin.succ),
          (∏ j, ((Fin.cons x y : Fin (n + 1) → ℂ) j - z j)⁻¹) • f (Fin.cons x y)) =
        (x - z 0)⁻¹ • ((2 * π * I) ^ n • f (Fin.cons x z')) := by
      intro x hx
      have hsplit : ∀ y : Fin n → ℂ,
          (∏ j, ((Fin.cons x y : Fin (n + 1) → ℂ) j - z j)⁻¹) • f (Fin.cons x y) =
          (x - z 0)⁻¹ • ((∏ j : Fin n, (y j - z' j)⁻¹) • f (Fin.cons x y)) := fun y ↦ by
        rw [Fin.prod_univ_succ, smul_smul]
        rfl
      simp_rw [hsplit]
      rw [torusIntegral_smul]
      congr 1
      have hcx : Continuous fun y : Fin n → ℂ ↦ (Fin.cons x y : Fin (n + 1) → ℂ) :=
        continuous_const.finCons continuous_id
      have hUx : IsOpen {y : Fin n → ℂ | (Fin.cons x y : Fin (n + 1) → ℂ) ∈ U} :=
        hU.preimage hcx
      refine torusIntegral_cauchy n hUx (hf.comp hcx.continuousOn fun y hy ↦ hy)
        (fun y hy j ↦ ?_) hR (fun y hy ↦ ?_) hz'
      · have := hsep _ hy j.succ
        simpa [Fin.cons_update] using this
      · exact hcU (mem_closedBall_cons (le_of_eq (mem_sphere.mp hx)) hy)
    rw [circleIntegral.integral_congr hR.le hinner]
    simp_rw [smul_comm (_ : ℂ)⁻¹ ((2 * π * I) ^ n)]
    rw [circleIntegral.integral_smul]
    -- the outer integral, by the one-variable formula
    have hz0 : z 0 ∈ ball (c 0) R := by
      rw [mem_ball, dist_eq_norm]
      exact hzj 0
    have hdiff : DiffContOnCl ℂ (fun x ↦ f (Fin.cons x z')) (ball (c 0) R) := by
      refine ⟨fun x hx ↦ ?_, ?_⟩
      · have hmem : (Fin.cons x z' : Fin (n + 1) → ℂ) ∈ U :=
          hcU (ball_subset_closedBall (mem_ball_cons (mem_ball.mp hx) hz'))
        have := hsep _ hmem 0
        simp only [Fin.cons_zero, Fin.update_cons_zero] at this
        exact this.differentiableWithinAt
      · rw [closure_ball _ hR.ne']
        have hcz : Continuous fun x : ℂ ↦ (Fin.cons x z' : Fin (n + 1) → ℂ) := by
          fun_prop
        exact hf.comp hcz.continuousOn fun x hx ↦
          hcU (mem_closedBall_cons (mem_closedBall.mp hx) (ball_subset_closedBall hz'))
    rw [hdiff.circleIntegral_sub_inv_smul hz0, smul_smul, ← pow_succ, Fin.cons_self_tail]

end Cauchy

/-! ### The power series expansion -/

section Expansion

variable {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ} {c : Fin n → ℂ} {R : ℝ}

/-- The Cauchy coefficients `aₐ = (2πi)⁻ⁿ ∯_{T(c, R)} f(ζ) ∏ⱼ (ζⱼ - cⱼ)^{-(αⱼ + 1)} dζ`. -/
def cauchyCoeff (f : (Fin n → ℂ) → ℂ) (c : Fin n → ℂ) (R : ℝ) (α : Fin n → ℕ) : ℂ :=
  ((2 * π * I : ℂ) ^ n)⁻¹ * ∯ ζ in T(c, fun _ ↦ R), (∏ j, (ζ j - c j)⁻¹ ^ (α j + 1)) • f ζ

lemma norm_torusMap_sub (c : Fin n → ℂ) {R : ℝ} (hR : 0 < R) (θ : Fin n → ℝ) (j : Fin n) :
    ‖torusMap c (fun _ ↦ R) θ j - c j‖ = R := by
  have := torusMap_mem_sphere c (fun _ ↦ R) θ j
  rwa [mem_sphere, dist_eq_norm, abs_of_pos hR] at this

/-- **Cauchy estimates**: `|aₐ| ≤ M R^{-|α|}` if `|f| ≤ M` on the torus. -/
lemma norm_cauchyCoeff_le (hR : 0 < R) {M : ℝ}
    (hM : ∀ θ, ‖f (torusMap c (fun _ ↦ R) θ)‖ ≤ M) (α : Fin n → ℕ) :
    ‖cauchyCoeff f c R α‖ ≤ M * ∏ j, R⁻¹ ^ α j := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hb : ∀ θ, ‖(∏ j, (torusMap c (fun _ ↦ R) θ j - c j)⁻¹ ^ (α j + 1)) •
      f (torusMap c (fun _ ↦ R) θ)‖ ≤ (∏ j, R⁻¹ ^ (α j + 1)) * M := fun θ ↦ by
    rw [norm_smul, norm_prod]
    refine mul_le_mul (Finset.prod_le_prod (fun j _ ↦ norm_nonneg _) fun j _ ↦ le_of_eq ?_)
      (hM θ) (norm_nonneg _) (Finset.prod_nonneg fun j _ ↦ by positivity)
    rw [norm_pow, norm_inv, norm_torusMap_sub c hR θ]
  have h := norm_torusIntegral_le_of_norm_le_const
    (f := fun ζ ↦ (∏ j, (ζ j - c j)⁻¹ ^ (α j + 1)) • f ζ) hb
  rw [cauchyCoeff, norm_mul, norm_inv, norm_pow]
  have h2π : ‖(2 * π * I : ℂ)‖ = 2 * π := by
    simp [Real.pi_pos.le]
  rw [h2π]
  calc ((2 * π) ^ n)⁻¹ * ‖∯ ζ in T(c, fun _ ↦ R), (∏ j, (ζ j - c j)⁻¹ ^ (α j + 1)) • f ζ‖
      ≤ ((2 * π) ^ n)⁻¹ * (((2 * π) ^ n * ∏ _j : Fin n, |R|) * ((∏ j, R⁻¹ ^ (α j + 1)) * M)) := by
        gcongr
    _ = M * ∏ j, R⁻¹ ^ α j := by
        have h2 : (2 * π) ^ n ≠ 0 := pow_ne_zero _ (by positivity)
        have hpr : ∏ j : Fin n, R⁻¹ ^ (α j + 1) = (∏ j, R⁻¹ ^ α j) * R⁻¹ ^ n := by
          simp [pow_succ, Finset.prod_mul_distrib]
        have hRn : R ^ n * R⁻¹ ^ n = 1 := by rw [← mul_pow, mul_inv_cancel₀ hR.ne', one_pow]
        rw [hpr, abs_of_pos hR, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
        calc ((2 * π) ^ n)⁻¹ * ((2 * π) ^ n * R ^ n * ((∏ j, R⁻¹ ^ α j) * R⁻¹ ^ n * M))
            = (((2 * π) ^ n)⁻¹ * (2 * π) ^ n) * (R ^ n * R⁻¹ ^ n) * (M * ∏ j, R⁻¹ ^ α j) := by
              ring
          _ = M * ∏ j, R⁻¹ ^ α j := by rw [inv_mul_cancel₀ h2, hRn, one_mul, one_mul]

/-- The terms of the expanded Cauchy integrand. -/
private def cauchyTerm (f : (Fin n → ℂ) → ℂ) (c z : Fin n → ℂ) (α : Fin n → ℕ)
    (w : Fin n → ℂ) : ℂ :=
  (∏ j, (z j - c j) ^ α j * (w j - c j)⁻¹ ^ (α j + 1)) • f w

/-- The terms of the expanded Cauchy integrand, in the coordinates `θ` of the torus. -/
private def cauchyTermθ (f : (Fin n → ℂ) → ℂ) (c z : Fin n → ℂ) (R : ℝ) (α : Fin n → ℕ)
    (θ : Fin n → ℝ) : ℂ :=
  (∏ i, R * exp (θ i * I) * I : ℂ) • cauchyTerm f c z α (torusMap c (fun _ ↦ R) θ)

/-- **The power series expansion** of a continuous separately holomorphic function: on the open
polydisc `P(c, R)`, `f(z) = ∑ₐ aₐ (z - c)ᵅ` with the Cauchy coefficients `aₐ`. -/
theorem hasSum_cauchyCoeff (hU : IsOpen U) (hf : ContinuousOn f U)
    (hsep : SeparatelyHolomorphicOn f U) (hR : 0 < R) (hcU : closedBall c R ⊆ U)
    {z : Fin n → ℂ} (hz : z ∈ ball c R) :
    HasSum (fun α : Fin n → ℕ ↦ cauchyCoeff f c R α * ∏ j, (z j - c j) ^ α j) (f z) := by
  set ζ : (Fin n → ℝ) → Fin n → ℂ := torusMap c (fun _ ↦ R) with hζdef
  have hζR : ∀ θ j, ‖ζ θ j - c j‖ = R := norm_torusMap_sub c hR
  have hζne : ∀ θ j, ζ θ j - c j ≠ 0 := fun θ j h ↦ by
    have := hζR θ j
    rw [h, norm_zero] at this
    exact hR.ne this
  have hzj : ∀ j, ‖z j - c j‖ < R := fun j ↦ by
    have := (dist_pi_lt_iff hR).mp (mem_ball.mp hz) j
    rwa [dist_eq_norm] at this
  -- a bound for `f` on the closed polydisc
  obtain ⟨M, hM⟩ := (isCompact_closedBall c R).exists_bound_of_continuousOn (hf.mono hcU)
  have htorus : ∀ θ, ζ θ ∈ closedBall c R := fun θ ↦ by
    rw [mem_closedBall, dist_pi_le_iff hR.le]
    intro j
    rw [dist_eq_norm, hζR]
  have hMθ : ∀ θ, ‖f (ζ θ)‖ ≤ M := fun θ ↦ hM _ (htorus θ)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMθ 0)
  -- the expansion of the Cauchy kernel on the torus
  have hker : ∀ θ, HasSum (fun α : Fin n → ℕ ↦ ∏ j, (z j - c j) ^ α j * (ζ θ j - c j)⁻¹ ^ (α j + 1))
      (∏ j, (ζ θ j - z j)⁻¹) := fun θ ↦ by
    have hx : ∀ j, ‖(z j - c j) / (ζ θ j - c j)‖ < 1 := fun j ↦ by
      rw [norm_div, hζR, div_lt_one hR]
      exact hzj j
    refine (hasSum_prod_fin n (fun j k ↦ (z j - c j) ^ k * (ζ θ j - c j)⁻¹ ^ (k + 1)) _
      (fun j ↦ ?_) (fun j ↦ ?_)).1
    · have hg := (hasSum_geometric_of_norm_lt_one (hx j)).mul_left (ζ θ j - c j)⁻¹
      have hfun : (fun k ↦ (z j - c j) ^ k * (ζ θ j - c j)⁻¹ ^ (k + 1)) =
          fun i ↦ (ζ θ j - c j)⁻¹ * ((z j - c j) / (ζ θ j - c j)) ^ i := by
        funext k
        rw [div_pow, pow_succ, div_eq_mul_inv, inv_pow]
        ring
      have h1 : (1 : ℂ) - (z j - c j) / (ζ θ j - c j) = (ζ θ j - z j) / (ζ θ j - c j) := by
        field_simp [hζne θ j]
        ring
      have hval : (ζ θ j - c j)⁻¹ * (1 - (z j - c j) / (ζ θ j - c j))⁻¹ = (ζ θ j - z j)⁻¹ := by
        rw [h1, inv_div, mul_div, inv_mul_cancel₀ (hζne θ j), one_div]
      rw [hfun, ← hval]
      exact hg
    · have hs := (summable_geometric_of_lt_one (norm_nonneg _) (hx j)).mul_left R⁻¹
      have hfun : (fun k ↦ ‖(z j - c j) ^ k * (ζ θ j - c j)⁻¹ ^ (k + 1)‖) =
          fun i ↦ R⁻¹ * ‖(z j - c j) / (ζ θ j - c j)‖ ^ i := by
        funext k
        rw [norm_mul, norm_pow, norm_pow, norm_inv, hζR, norm_div, hζR, div_pow, pow_succ,
          div_eq_mul_inv, inv_pow]
        ring
      rw [hfun]
      exact hs
  -- the terms of the expanded integrand
  have hGcont : ∀ α, TorusIntegrable (cauchyTerm f c z α) c (fun _ ↦ R) := fun α ↦ by
    set S : Set (Fin n → ℂ) := {w | w ∈ closedBall c R ∧ ∀ j, w j - c j ≠ 0}
    refine torusIntegrable_of_continuousOn (S := S) ?_ fun θ ↦ ⟨htorus θ, hζne θ⟩
    refine ContinuousOn.smul (f := fun w : Fin n → ℂ ↦
      ∏ j, (z j - c j) ^ α j * (w j - c j)⁻¹ ^ (α j + 1)) ?_
      (hf.mono fun w (hw : w ∈ S) ↦ hcU hw.1)
    exact continuousOn_finsetProd _ fun j _ ↦ continuousOn_const.mul
      ((((continuous_apply j).sub continuous_const).continuousOn.inv₀
        fun w (hw : w ∈ S) ↦ hw.2 j).pow _)
  set V : ℝ := volume.real (Icc (0 : Fin n → ℝ) fun _ ↦ 2 * π)
  have hVfin : volume (Icc (0 : Fin n → ℝ) fun _ ↦ 2 * π) < ⊤ := measure_Icc_lt_top
  have hFbound : ∀ α θ, ‖cauchyTermθ f c z R α θ‖ ≤ M * ∏ j, (‖z j - c j‖ / R) ^ α j :=
      fun α θ ↦ by
    have hI : ∀ i : Fin n, ‖(R : ℂ) * exp (θ i * I) * I‖ = R := fun i ↦ by
      rw [norm_mul, norm_mul, norm_exp_ofReal_mul_I, norm_I, Complex.norm_real,
        Real.norm_of_nonneg hR.le, mul_one, mul_one]
    have hA : ‖(∏ i, (R : ℂ) * exp (θ i * I) * I)‖ = R ^ n := by
      rw [norm_prod, Finset.prod_congr rfl fun i _ ↦ hI i, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
    have hP : ‖∏ j, (z j - c j) ^ α j * (ζ θ j - c j)⁻¹ ^ (α j + 1)‖ =
        ∏ j, ‖z j - c j‖ ^ α j * R⁻¹ ^ (α j + 1) := by
      rw [norm_prod]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [norm_mul, norm_pow, norm_pow, norm_inv, hζR]
    rw [cauchyTermθ, cauchyTerm, norm_smul, norm_smul, hA, hP]
    have hprod : R ^ n * ∏ j, ‖z j - c j‖ ^ α j * R⁻¹ ^ (α j + 1) =
        ∏ j, (‖z j - c j‖ / R) ^ α j := by
      have hRn : R ^ n = ∏ _j : Fin n, R := by simp
      rw [hRn, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [div_pow, pow_succ, div_eq_mul_inv, inv_pow]
      have hRk : R ^ α j * (R ^ α j)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hR.ne')
      calc R * (‖z j - c j‖ ^ α j * ((R ^ α j)⁻¹ * R⁻¹))
          = (R * R⁻¹) * (‖z j - c j‖ ^ α j * (R ^ α j)⁻¹) := by ring
        _ = ‖z j - c j‖ ^ α j * (R ^ α j)⁻¹ := by rw [mul_inv_cancel₀ hR.ne', one_mul]
    calc R ^ n * ((∏ j, ‖z j - c j‖ ^ α j * R⁻¹ ^ (α j + 1)) * ‖f (ζ θ)‖)
        = (R ^ n * ∏ j, ‖z j - c j‖ ^ α j * R⁻¹ ^ (α j + 1)) * ‖f (ζ θ)‖ := by ring
      _ ≤ (∏ j, (‖z j - c j‖ / R) ^ α j) * M := by
        rw [hprod]
        exact mul_le_mul_of_nonneg_left (hMθ θ) (Finset.prod_nonneg fun j _ ↦ by positivity)
      _ = M * ∏ j, (‖z j - c j‖ / R) ^ α j := mul_comm _ _
  -- summability of the norms of the terms
  have hgeom := (hasSum_prod_geometric (n := n) (x := fun j ↦ ((‖z j - c j‖ / R : ℝ) : ℂ))
    fun j ↦ by
      rw [Complex.norm_real, Real.norm_of_nonneg (by positivity), div_lt_one hR]
      exact hzj j).2
  have hgeom' : Summable fun α : Fin n → ℕ ↦ ∏ j, (‖z j - c j‖ / R) ^ α j := by
    refine hgeom.congr fun α ↦ ?_
    rw [norm_prod]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hint : ∀ α, Integrable (cauchyTermθ f c z R α)
      (volume.restrict (Icc (0 : Fin n → ℝ) fun _ ↦ 2 * π)) :=
    fun α ↦ (hGcont α).function_integrable
  have hsumint : Summable fun α ↦ ∫ θ, ‖cauchyTermθ f c z R α θ‖
      ∂(volume.restrict (Icc (0 : Fin n → ℝ) fun _ ↦ 2 * π)) := by
    refine Summable.of_nonneg_of_le (fun α ↦ integral_nonneg fun θ ↦ norm_nonneg _)
      (fun α ↦ ?_) ((hgeom'.mul_left M).mul_right V)
    have := norm_setIntegral_le_of_norm_le_const (f := fun θ ↦ ‖cauchyTermθ f c z R α θ‖) hVfin
      (C := M * ∏ j, (‖z j - c j‖ / R) ^ α j) fun θ _ ↦ by
        rw [norm_norm]
        exact hFbound α θ
    rw [Real.norm_of_nonneg (integral_nonneg fun θ ↦ norm_nonneg _)] at this
    exact this
  have hmain := hasSum_integral_of_summable_integral_norm hint hsumint
  -- identify the sum of the integrals and the integrals of the terms
  have hsum_pt : ∀ θ, ∑' α, cauchyTermθ f c z R α θ =
      (∏ i, R * exp (θ i * I) * I : ℂ) • ((∏ j, (ζ θ j - z j)⁻¹) • f (ζ θ)) := fun θ ↦ by
    simp only [cauchyTermθ, cauchyTerm, smul_eq_mul]
    rw [tsum_mul_left, tsum_mul_right, (hker θ).tsum_eq]
  have hlhs : ∫ θ, (∑' α, cauchyTermθ f c z R α θ)
      ∂(volume.restrict (Icc (0 : Fin n → ℝ) fun _ ↦ 2 * π)) = (2 * π * I) ^ n • f z := by
    simp_rw [hsum_pt]
    exact torusIntegral_cauchy n hU hf hsep hR hcU hz
  have h2 : ((2 * π * I : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  have hterm : ∀ α, ∫ θ, cauchyTermθ f c z R α θ
      ∂(volume.restrict (Icc (0 : Fin n → ℝ) fun _ ↦ 2 * π)) =
      (2 * π * I) ^ n * (cauchyCoeff f c R α * ∏ j, (z j - c j) ^ α j) := fun α ↦ by
    have hG : cauchyTerm f c z α = fun w ↦ (∏ j, (z j - c j) ^ α j) *
        ((∏ j, (w j - c j)⁻¹ ^ (α j + 1)) • f w) := by
      funext w
      simp only [cauchyTerm, smul_eq_mul, Finset.prod_mul_distrib]
      ring
    change torusIntegral (cauchyTerm f c z α) c (fun _ ↦ R) = _
    rw [hG, torusIntegral_const_mul, cauchyCoeff, ← mul_assoc, ← mul_assoc,
      mul_inv_cancel₀ h2, one_mul, mul_comm]
  rw [hlhs] at hmain
  simp_rw [hterm] at hmain
  have := hmain.mul_left ((2 * π * I : ℂ) ^ n)⁻¹
  simpa only [← mul_assoc, inv_mul_cancel₀ h2, one_mul, smul_eq_mul] using this

end Expansion

/-! ### Osgood's lemma -/

section Osgood

open MvPowerSeries in
/-- **Osgood's lemma** on `ℂⁿ` (`Fin n` coordinates): a function which is continuous and
separately holomorphic on an open set `U ⊆ ℂⁿ` is analytic at every point of `U`. -/
theorem analyticAt_of_separately_fin {n : ℕ} {U : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hsep : SeparatelyHolomorphicOn f U)
    {x : Fin n → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  set R : ℝ := ε / 2 with hRdef
  have hR : 0 < R := half_pos hε
  have hcU : closedBall x R ⊆ U := (closedBall_subset_ball (half_lt_self hε)).trans hεU
  obtain ⟨M, hM⟩ := (isCompact_closedBall x R).exists_bound_of_continuousOn (hf.mono hcU)
  have hMθ : ∀ θ, ‖f (torusMap x (fun _ ↦ R) θ)‖ ≤ M := fun θ ↦ by
    refine hM _ ?_
    rw [mem_closedBall, dist_pi_le_iff hR.le]
    intro j
    rw [dist_eq_norm, norm_torusMap_sub x hR θ j]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hMθ 0)
  -- the power series of the Cauchy coefficients
  let a : MvPowerSeries (Fin n) ℂ := fun β ↦ cauchyCoeff f x R ⇑β
  have ha : ∀ β, coeff β a = cauchyCoeff f x R ⇑β := fun β ↦ rfl
  have hr : (0 : ℝ) < R / 2 := half_pos hR
  set r : ℝ≥0 := ⟨R / 2, hr.le⟩ with hrdef
  have hr0 : 0 < r := hr
  -- the multiple geometric series with ratio `1/2`, indexed by finsupps
  have hgeom : Summable fun β : Fin n →₀ ℕ ↦ ∏ j, ((1 : ℝ) / 2) ^ β j := by
    have h := (hasSum_prod_geometric (n := n) (x := fun _ ↦ ((1 / 2 : ℝ) : ℂ)) fun _ ↦ by
      rw [Complex.norm_real]
      norm_num).2
    have h' : Summable fun α : Fin n → ℕ ↦ ∏ j, ((1 : ℝ) / 2) ^ α j := by
      refine h.congr fun α ↦ ?_
      rw [norm_prod]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [norm_pow, Complex.norm_real]
      norm_num
    have h'' := (Finsupp.equivFunOnFinite.summable_iff
      (f := fun α : Fin n → ℕ ↦ ∏ j, ((1 : ℝ) / 2) ^ α j)).mpr h'
    exact h''
  have hconv : weightedNorm (fun _ ↦ r) a ≠ ⊤ := by
    rw [weightedNorm, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe]
    refine Summable.of_nonneg_of_le (fun β ↦ by positivity) (fun β ↦ ?_) (hgeom.mul_left M)
    rw [NNReal.coe_mul, coe_nnnorm, ha, monomialEval_eq_prod, NNReal.coe_prod]
    simp only [NNReal.coe_pow]
    calc ‖cauchyCoeff f x R ⇑β‖ * ∏ j, (R / 2) ^ β j
        ≤ (M * ∏ j, R⁻¹ ^ β j) * ∏ j, (R / 2) ^ β j :=
          mul_le_mul_of_nonneg_right (norm_cauchyCoeff_le hR hMθ ⇑β)
            (Finset.prod_nonneg fun j _ ↦ by positivity)
      _ = M * ∏ j, ((1 : ℝ) / 2) ^ β j := by
          rw [mul_assoc, ← Finset.prod_mul_distrib]
          congr 1
          refine Finset.prod_congr rfl fun j _ ↦ ?_
          rw [← mul_pow]
          congr 1
          field_simp
  have han : AnalyticAt ℂ (tsumEval a) 0 := analyticAt_tsumEval ⟨fun _ ↦ r, fun _ ↦ hr0, hconv⟩
  -- `f(x + w)` is the sum of the series
  have heq : ∀ w ∈ ball (0 : Fin n → ℂ) R, f (x + w) = tsumEval a w := by
    intro w hw
    have hxw : x + w ∈ ball x R := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]
      simpa using hw
    have hs := hasSum_cauchyCoeff hU hf hsep hR hcU hxw
    simp only [Pi.add_apply, add_sub_cancel_left] at hs
    have h1 := (Finsupp.equivFunOnFinite.hasSum_iff
      (f := fun α : Fin n → ℕ ↦ cauchyCoeff f x R α * ∏ j, w j ^ α j)).mpr hs
    have hfun : (fun β : Fin n →₀ ℕ ↦ coeff β a * monomialEval w β) =
        (fun α : Fin n → ℕ ↦ cauchyCoeff f x R α * ∏ j, w j ^ α j) ∘
          Finsupp.equivFunOnFinite := by
      funext β
      simp only [Function.comp_apply, ha, monomialEval_eq_prod]
      rfl
    have hs' : HasSum (fun β : Fin n →₀ ℕ ↦ coeff β a * monomialEval w β) (f (x + w)) := by
      rw [hfun]
      exact h1
    exact hs'.tsum_eq.symm
  have hev : (fun y ↦ tsumEval a (y - x)) =ᶠ[𝓝 x] f := by
    filter_upwards [ball_mem_nhds x hR] with y hy
    rw [← heq (y - x) (by rwa [mem_ball, dist_zero_right, ← dist_eq_norm]), add_sub_cancel]
  exact (han.comp_of_eq ((analyticAt_id).sub analyticAt_const) (sub_self x)).congr hev

end Osgood

/-! ### Arbitrary finite index types, and consequences -/

section General

variable {σ : Type*} [Fintype σ]

/-- **Osgood's lemma**: a function which is continuous and holomorphic in each variable separately
on an open set `U ⊆ ℂ^σ` is analytic at every point of `U`. -/
theorem analyticAt_of_continuousOn_of_separately [DecidableEq σ] {U : Set (σ → ℂ)}
    {f : (σ → ℂ) → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U) (hsep : SeparatelyHolomorphicOn f U)
    {x : σ → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  -- `Φ w = w ∘ e` identifies `ℂ^{Fin n}` with `ℂ^σ`
  let Φ : (Fin n → ℂ) →L[ℂ] (σ → ℂ) := ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (e i)
  let Ψ : (σ → ℂ) →L[ℂ] (Fin n → ℂ) :=
    ContinuousLinearMap.pi fun k ↦ ContinuousLinearMap.proj (e.symm k)
  have hΦΨ : ∀ y, Φ (Ψ y) = y := fun y ↦ funext fun i ↦ by simp [Φ, Ψ]
  have hΦupd : ∀ w k t, Φ (Function.update w k t) = Function.update (Φ w) (e.symm k) t :=
    fun w k t ↦ funext fun i ↦ by
      by_cases hi : i = e.symm k
      · subst hi
        simp [Φ]
      · have hk : e i ≠ k := fun h ↦ hi (by rw [← h, Equiv.symm_apply_apply])
        simp [Φ, Function.update_of_ne hi, Function.update_of_ne hk]
  have hg : AnalyticAt ℂ (f ∘ Φ) (Ψ x) := by
    refine analyticAt_of_separately_fin (U := Φ ⁻¹' U) (hU.preimage Φ.continuous)
      (hf.comp Φ.continuous.continuousOn fun w hw ↦ hw) (fun w hw k ↦ ?_) (by simpa [hΦΨ] using hx)
    have := hsep (Φ w) hw (e.symm k)
    simp only [Function.comp_apply, hΦupd]
    have hwk : Φ w (e.symm k) = w k := by simp [Φ]
    rw [hwk] at this
    exact this
  have : f = (f ∘ Φ) ∘ Ψ := funext fun y ↦ by simp [hΦΨ]
  rw [this]
  exact hg.comp (Ψ.analyticAt x)

/-- A function `ℂ`-differentiable on an open subset of `ℂ^σ` is analytic there. -/
theorem analyticAt_of_differentiableOn {U : Set (σ → ℂ)} {f : (σ → ℂ) → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {x : σ → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  classical
  exact analyticAt_of_continuousOn_of_separately hU hf.continuousOn
    (fun z hz j ↦ by
      have hd : DifferentiableAt ℂ f (Function.update z j (z j)) := by
        rw [Function.update_eq_self]
        exact hf.differentiableAt (hU.mem_nhds hz)
      exact hd.comp (z j) (hasFDerivAt_update z (z j)).differentiableAt) hx

/-- **Weierstrass's theorem for series**: a series of holomorphic functions on an open set
`U ⊆ ℂ^σ` which is normally convergent (`|fₖ| ≤ uₖ` on `U`, `∑ uₖ < ∞`) has an analytic sum. -/
theorem analyticAt_tsum_of_summable_norm {ι : Type*} {U : Set (σ → ℂ)} (hU : IsOpen U)
    {F : ι → (σ → ℂ) → ℂ} (hF : ∀ i, DifferentiableOn ℂ (F i) U) {u : ι → ℝ} (hu : Summable u)
    (hFu : ∀ i, ∀ z ∈ U, ‖F i z‖ ≤ u i) {x : σ → ℂ} (hx : x ∈ U) :
    AnalyticAt ℂ (fun z ↦ ∑' i, F i z) x := by
  classical
  refine analyticAt_of_continuousOn_of_separately hU
    (continuousOn_tsum (fun i ↦ (hF i).continuousOn) hu hFu) (fun z hz j ↦ ?_) hx
  -- the restriction to the `j`-th coordinate line near `z j`
  set L : Set ℂ := (fun t ↦ Function.update z j t) ⁻¹' U
  have hL : IsOpen L := hU.preimage (continuous_const.update j continuous_id)
  have hzL : z j ∈ L := by simpa [L] using hz
  have hdiff : DifferentiableOn ℂ (fun t ↦ ∑' i, F i (Function.update z j t)) L :=
    differentiableOn_tsum_of_summable_norm hu (fun i t ht ↦
      ((hF i).differentiableAt (hU.mem_nhds ht)).comp t
        (hasFDerivAt_update z t).differentiableAt |>.differentiableWithinAt) hL
      fun i t ht ↦ hFu i _ ht
  exact hdiff.differentiableAt (hL.mem_nhds hzL)

end General

end AnalyticGeometry
