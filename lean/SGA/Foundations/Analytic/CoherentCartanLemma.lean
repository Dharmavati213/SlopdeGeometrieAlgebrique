/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Osgood
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Cartan's matrix lemma near the identity

Let `W', W'' ⊆ ℂ^σ` be open and `W ⊆ W' ∩ W''`. Suppose that the *additive* Cousin problem for
`(W', W'')` is solvable with bounds: every function `h` holomorphic on `W` with `|h| ≤ M` there is
`h' - h''` on `W`, with `h'`, `h''` holomorphic on `W'`, `W''` and bounded there by `C M`
(`AnalyticGeometry.HasBoundedSplitting W W' W'' C`). Then the *multiplicative* problem is solvable
for invertible matrices close to the identity: if `g` is a `p × p` matrix of functions holomorphic
on `W` whose entries satisfy `|gᵢⱼ - δᵢⱼ| ≤ ε` on `W`, with `ε = 1 / (4 (p + 1) C)`, then
`g A'' = A'` on `W` for matrices `A'`, `A''` of functions holomorphic on `W'`, `W''` that are
invertible at every point of `W'`, `W''` (`AnalyticGeometry.exists_mul_eq_of_hasBoundedSplitting`).
This is the analytic heart of Cartan's lemma on the gluing of holomorphic matrices
(H. Cartan, *Sur les matrices holomorphes de n variables complexes*, J. Math. Pures Appl. 19
(1940); see also Gunning–Rossi, *Analytic functions of several complex variables*, Chapter VI,
and Grauert–Remmert, *Theory of Stein spaces*, the "Heftungslemma" for matrices close to the
identity).

The bounded splitting holds without shrinking for `W' = D' × N`, `W'' = D'' × N`, `W = W' ∩ W''`
with `D'`, `D''` adjacent rectangles of the plane (Cauchy transform in one variable, with the other
variables as holomorphic parameters); it is taken here as a hypothesis.

## Proof

Since the splitting does not shrink the domains, a geometric iteration converges (no Newton
iteration with shrinking domains is needed). Put `e₀ = g - 1` and, splitting
`eₖ = Sₖ' - Sₖ''` entrywise, `eₖ₊₁ = (g - 1) Sₖ''`. The entries of `eₖ` are at most `ε 4⁻ᵏ`, and
`A' = 1 + ∑ₖ Sₖ'`, `A'' = 1 + ∑ₖ Sₖ''` are normally convergent series of holomorphic functions
(`AnalyticGeometry.analyticAt_tsum_of_summable_norm`). On `W`,
`∑ Sₖ' = ∑ eₖ + ∑ Sₖ'' = (g - 1) + (g - 1) ∑ Sₖ'' + ∑ Sₖ''`, i.e. `A' = g A''`. The entries of
`A' - 1` and `A'' - 1` are smaller than `1 / (3 p)`, so `A'`, `A''` are invertible
(`AnalyticGeometry.isUnit_one_add_of_norm_entry_le`).
-/

noncomputable section

open Set Filter Topology Matrix

namespace AnalyticGeometry

variable {σ : Type*} [Finite σ]

/-- **Additive splitting with bounds** for the pair `(W', W'')` along `W`: every function `h`
holomorphic on `W` with `|h| ≤ M` on `W` is `h' - h''` on `W`, where `h'` is holomorphic on `W'`,
`h''` on `W''`, and both are bounded by `C M` there. -/
def HasBoundedSplitting (W W' W'' : Set (σ → ℂ)) (C : ℝ) : Prop :=
  ∀ (h : (σ → ℂ) → ℂ) (M : ℝ), DifferentiableOn ℂ h W → (∀ z ∈ W, ‖h z‖ ≤ M) →
    ∃ h' h'' : (σ → ℂ) → ℂ, DifferentiableOn ℂ h' W' ∧ DifferentiableOn ℂ h'' W'' ∧
      (∀ z ∈ W', ‖h' z‖ ≤ C * M) ∧ (∀ z ∈ W'', ‖h'' z‖ ≤ C * M) ∧
      ∀ z ∈ W, h z = h' z - h'' z

/-- **Additive splitting with bounds on adjacent boxes** (statement only). Let `m ∈ σ` be a
coordinate, `N ⊆ ℂ^σ` an open set stable under changing the `m`-th coordinate (for instance a
product of open rectangles in the other coordinates), and `D' = (a, c + δ) × (α, β)`,
`D'' = (c - δ, b) × (α, β)` two open rectangles of the `zₘ`-plane overlapping in the strip
`(c - δ, c + δ) × (α, β)`. With `W' = {z ∈ N | zₘ ∈ D'}`, `W'' = {z ∈ N | zₘ ∈ D''}` and
`W = W' ∩ W''`, there is `C > 0` with `HasBoundedSplitting W W' W'' C`.

Proof plan (Hörmander, *An introduction to complex analysis in several variables*, Theorem 1.2.2
in its local form, with holomorphic parameters; the Cauchy transform is
`AnalyticGeometry.cauchyTransform`): with a cutoff
`χ(Re zₘ)` equal to `1` left of `c - δ/2` and `0` right of `c + δ/2`, put
`v = Tₘ(h ∂χ/∂z̄ₘ · 1_{strip})`, `h' = (1 - χ) h + v` on `W'` and `h'' = v - χ h` on `W''`.
Then `∂̄ₘ v = h ∂χ/∂z̄ₘ` on `D' ∪ D''` (the integrand jumps only on the horizontal edges of the
strip, outside `D' ∪ D''`), `v` is holomorphic in the other variables, and
`|v| ≤ 2 diam(D' ∪ D'') sup |∂χ/∂z̄ₘ| sup |h|`. -/
def ProductBoundedSplittingStatement : Prop :=
  ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (m : σ) (N : Set (σ → ℂ)), IsOpen N →
    (∀ z ∈ N, ∀ t, Function.update z m t ∈ N) →
    ∀ (a b c δ α β : ℝ), 0 < δ → a < c - δ → c + δ < b → α < β →
      let D' : Set ℂ := {t | t.re ∈ Set.Ioo a (c + δ) ∧ t.im ∈ Set.Ioo α β}
      let D'' : Set ℂ := {t | t.re ∈ Set.Ioo (c - δ) b ∧ t.im ∈ Set.Ioo α β}
      let W' : Set (σ → ℂ) := {z | z ∈ N ∧ z m ∈ D'}
      let W'' : Set (σ → ℂ) := {z | z ∈ N ∧ z m ∈ D''}
      ∃ C > 0, HasBoundedSplitting (W' ∩ W'') W' W'' C

section Matrix

variable {ι : Type*} [Fintype ι]

/-- The size of the perturbation of the identity handled by Cartan's lemma for `p × p` matrices
and a splitting constant `C`: `ε = 1 / (4 (p + 1) C)`. -/
def cartanEps (ι : Type*) [Fintype ι] (C : ℝ) : ℝ :=
  1 / (4 * (Fintype.card ι + 1) * C)

lemma cartanEps_pos {C : ℝ} (hC : 0 < C) : 0 < cartanEps ι C := by
  unfold cartanEps
  positivity

lemma card_mul_cartanEps_mul_le {C : ℝ} (hC : 0 < C) :
    Fintype.card ι * cartanEps ι C * C ≤ 1 / 4 := by
  unfold cartanEps
  have h1 : (0 : ℝ) < Fintype.card ι + 1 := by positivity
  have hC' : C ≠ 0 := hC.ne'
  have h2 : ↑(Fintype.card ι) * (1 / (4 * (↑(Fintype.card ι) + 1) * C)) * C =
      ↑(Fintype.card ι) / (4 * (↑(Fintype.card ι) + 1)) := by
    field_simp
  rw [h2, div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

variable [DecidableEq ι]

/-- A square matrix whose entries are smaller than `δ`, with `#ι δ < 1`, is a small perturbation
of the identity: `1 + A` is invertible. -/
theorem isUnit_one_add_of_norm_entry_le {A : Matrix ι ι ℂ} {δ : ℝ} (hA : ∀ i j, ‖A i j‖ ≤ δ)
    (hδ : Fintype.card ι * δ < 1) : IsUnit (1 + A) := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro hdet
  obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  obtain ⟨j₀, -⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j ↦ ‖v j‖) ⟨j₀, Finset.mem_univ _⟩
  have hvi : 0 < ‖v i‖ := by
    by_contra h
    push Not at h
    exact hv (funext fun j ↦ norm_le_zero_iff.mp ((hi j (Finset.mem_univ j)).trans h))
  have h1 : v i = -∑ j, A i j * v j := by
    have := congrFun hAv i
    rw [Matrix.add_mulVec, Matrix.one_mulVec] at this
    simp only [Pi.add_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at this
    linear_combination this
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hA i i)
  have h2 : ‖v i‖ ≤ Fintype.card ι * δ * ‖v i‖ := by
    calc ‖v i‖ = ‖∑ j, A i j * v j‖ := by rw [h1, norm_neg]
      _ ≤ ∑ j, ‖A i j * v j‖ := norm_sum_le _ _
      _ ≤ ∑ _j : ι, δ * ‖v i‖ := Finset.sum_le_sum fun j _ ↦ by
          rw [norm_mul]
          exact mul_le_mul (hA i j) (hi j (Finset.mem_univ j)) (norm_nonneg _) hδ0
      _ = Fintype.card ι * δ * ‖v i‖ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc]
  nlinarith

end Matrix

section Main

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {W W' W'' : Set (σ → ℂ)} {C : ℝ}

/-- **Cartan's lemma near the identity**: if the additive Cousin problem for `(W', W'')` along
`W ⊆ W' ∩ W''` is solvable with bounds (`HasBoundedSplitting W W' W'' C`), then every matrix `g`
of functions holomorphic on `W` with `|gᵢⱼ - δᵢⱼ| ≤ cartanEps ι C` on `W` satisfies `g A'' = A'` on
`W` for matrices `A'`, `A''` of functions holomorphic on `W'`, `W''` and invertible at every point
of `W'`, `W''`. -/
theorem exists_mul_eq_of_hasBoundedSplitting (hs : HasBoundedSplitting W W' W'' C) (hC : 0 < C)
    (hW' : IsOpen W') (hW'' : IsOpen W'') (hWW' : W ⊆ W') (hWW'' : W ⊆ W'')
    {g : (σ → ℂ) → Matrix ι ι ℂ} (hg : ∀ i j, DifferentiableOn ℂ (fun z ↦ g z i j) W)
    (hgε : ∀ z ∈ W, ∀ i j, ‖g z i j - (1 : Matrix ι ι ℂ) i j‖ ≤ cartanEps ι C) :
    ∃ A' A'' : (σ → ℂ) → Matrix ι ι ℂ,
      (∀ i j, DifferentiableOn ℂ (fun z ↦ A' z i j) W') ∧
      (∀ i j, DifferentiableOn ℂ (fun z ↦ A'' z i j) W'') ∧
      (∀ z ∈ W', IsUnit (A' z)) ∧ (∀ z ∈ W'', IsUnit (A'' z)) ∧
      ∀ z ∈ W, g z * A'' z = A' z := by
  classical
  have := Fintype.ofFinite σ
  set ε := cartanEps ι C with hε
  have hε0 : 0 < ε := cartanEps_pos hC
  have hpε : Fintype.card ι * ε * C ≤ 1 / 4 := card_mul_cartanEps_mul_le hC
  -- a splitting defined for all functions
  have key : ∀ (h : (σ → ℂ) → ℂ) (M : ℝ), ∃ h' h'' : (σ → ℂ) → ℂ,
      DifferentiableOn ℂ h W → (∀ z ∈ W, ‖h z‖ ≤ M) →
      DifferentiableOn ℂ h' W' ∧ DifferentiableOn ℂ h'' W'' ∧
      (∀ z ∈ W', ‖h' z‖ ≤ C * M) ∧ (∀ z ∈ W'', ‖h'' z‖ ≤ C * M) ∧
      ∀ z ∈ W, h z = h' z - h'' z := by
    intro h M
    by_cases hyp : DifferentiableOn ℂ h W ∧ ∀ z ∈ W, ‖h z‖ ≤ M
    · obtain ⟨h', h'', H⟩ := hs h M hyp.1 hyp.2
      exact ⟨h', h'', fun _ _ ↦ H⟩
    · exact ⟨0, 0, fun h1 h2 ↦ absurd ⟨h1, h2⟩ hyp⟩
  choose s' s'' hss using key
  let S' : ((σ → ℂ) → Matrix ι ι ℂ) → ℝ → (σ → ℂ) → Matrix ι ι ℂ :=
    fun A M z ↦ Matrix.of fun i j ↦ s' (fun w ↦ A w i j) M z
  let S'' : ((σ → ℂ) → Matrix ι ι ℂ) → ℝ → (σ → ℂ) → Matrix ι ι ℂ :=
    fun A M z ↦ Matrix.of fun i j ↦ s'' (fun w ↦ A w i j) M z
  let m : ℕ → ℝ := fun k ↦ ε * (1 / 4) ^ k
  have hm0 : ∀ k, 0 ≤ m k := fun k ↦ by positivity
  let e : ℕ → (σ → ℂ) → Matrix ι ι ℂ := fun k ↦
    Nat.rec (motive := fun _ ↦ (σ → ℂ) → Matrix ι ι ℂ) (fun z ↦ g z - 1)
      (fun k ek z ↦ (g z - 1) * S'' ek (m k) z) k
  have he0 : e 0 = fun z ↦ g z - 1 := rfl
  have heS : ∀ k, e (k + 1) = fun z ↦ (g z - 1) * S'' (e k) (m k) z := fun k ↦ rfl
  -- the invariant: holomorphic on `W`, entries bounded by `m k`
  have hinv : ∀ k, (∀ i j, DifferentiableOn ℂ (fun z ↦ e k z i j) W) ∧
      ∀ z ∈ W, ∀ i j, ‖e k z i j‖ ≤ m k := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun i j ↦ ?_, fun z hz i j ↦ ?_⟩
      · simp only [he0, Matrix.sub_apply]
        exact (hg i j).sub (differentiableOn_const _)
      · simp only [he0, Matrix.sub_apply, m, pow_zero, mul_one]
        exact hgε z hz i j
    | succ k ih =>
      obtain ⟨hd, hb⟩ := ih
      have hspl := fun i j ↦ hss (fun w ↦ e k w i j) (m k) (hd i j) (fun z hz ↦ hb z hz i j)
      refine ⟨fun i j ↦ ?_, fun z hz i j ↦ ?_⟩
      · rw [heS]
        simp only [Matrix.mul_apply]
        refine DifferentiableOn.fun_sum fun l _ ↦ ?_
        exact ((hg i l).sub (differentiableOn_const _)).mul ((hspl l j).2.1.mono hWW'')
      · rw [heS]
        simp only [Matrix.mul_apply]
        calc ‖∑ l, (g z - 1) i l * S'' (e k) (m k) z l j‖
            ≤ ∑ l, ‖(g z - 1) i l * S'' (e k) (m k) z l j‖ := norm_sum_le _ _
          _ ≤ ∑ _l : ι, ε * (C * m k) := Finset.sum_le_sum fun l _ ↦ by
              rw [norm_mul]
              exact mul_le_mul (hgε z hz i l) ((hspl l j).2.2.2.1 z (hWW'' hz))
                (norm_nonneg _) hε0.le
          _ = Fintype.card ι * ε * C * m k := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
          _ ≤ 1 / 4 * m k := mul_le_mul_of_nonneg_right hpε (hm0 k)
          _ = m (k + 1) := by simp only [m, pow_succ]; ring
  have hspl : ∀ k i j, DifferentiableOn ℂ (fun z ↦ S' (e k) (m k) z i j) W' ∧
      DifferentiableOn ℂ (fun z ↦ S'' (e k) (m k) z i j) W'' ∧
      (∀ z ∈ W', ‖S' (e k) (m k) z i j‖ ≤ C * m k) ∧
      (∀ z ∈ W'', ‖S'' (e k) (m k) z i j‖ ≤ C * m k) ∧
      ∀ z ∈ W, e k z i j = S' (e k) (m k) z i j - S'' (e k) (m k) z i j := fun k i j ↦
    hss (fun w ↦ e k w i j) (m k) ((hinv k).1 i j) (fun z hz ↦ (hinv k).2 z hz i j)
  -- the series
  have hgeom : HasSum (fun k ↦ C * m k) (C * (ε * (4 / 3))) := by
    have h := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
      (by norm_num)).mul_left (C * ε)
    have h' : C * ε * (1 - 1 / 4 : ℝ)⁻¹ = C * (ε * (4 / 3)) := by norm_num; ring
    rw [h'] at h
    have hfun : (fun k ↦ C * m k) = fun k ↦ C * ε * (1 / 4 : ℝ) ^ k :=
      funext fun k ↦ by simp only [m]; ring
    rw [hfun]
    exact h
  have hsumm : Summable fun k ↦ C * m k := hgeom.summable
  let B' : (σ → ℂ) → Matrix ι ι ℂ := fun z ↦ Matrix.of fun i j ↦ ∑' k, S' (e k) (m k) z i j
  let B'' : (σ → ℂ) → Matrix ι ι ℂ := fun z ↦ Matrix.of fun i j ↦ ∑' k, S'' (e k) (m k) z i j
  have hB'd : ∀ i j, DifferentiableOn ℂ (fun z ↦ B' z i j) W' := fun i j z hz ↦
    (analyticAt_tsum_of_summable_norm hW' (F := fun k z ↦ S' (e k) (m k) z i j)
      (fun k ↦ (hspl k i j).1) hsumm (fun k ↦ (hspl k i j).2.2.1) hz).differentiableAt
      |>.differentiableWithinAt
  have hB''d : ∀ i j, DifferentiableOn ℂ (fun z ↦ B'' z i j) W'' := fun i j z hz ↦
    (analyticAt_tsum_of_summable_norm hW'' (F := fun k z ↦ S'' (e k) (m k) z i j)
      (fun k ↦ (hspl k i j).2.1) hsumm (fun k ↦ (hspl k i j).2.2.2.1) hz).differentiableAt
      |>.differentiableWithinAt
  have hB'b : ∀ z ∈ W', ∀ i j, ‖B' z i j‖ ≤ C * (ε * (4 / 3)) := fun z hz i j ↦
    tsum_of_norm_bounded hgeom fun k ↦ (hspl k i j).2.2.1 z hz
  have hB''b : ∀ z ∈ W'', ∀ i j, ‖B'' z i j‖ ≤ C * (ε * (4 / 3)) := fun z hz i j ↦
    tsum_of_norm_bounded hgeom fun k ↦ (hspl k i j).2.2.2.1 z hz
  have hsmall : Fintype.card ι * (C * (ε * (4 / 3))) < 1 := by nlinarith
  refine ⟨fun z ↦ 1 + B' z, fun z ↦ 1 + B'' z, fun i j ↦ ?_, fun i j ↦ ?_,
    fun z hz ↦ isUnit_one_add_of_norm_entry_le (hB'b z hz) hsmall,
    fun z hz ↦ isUnit_one_add_of_norm_entry_le (hB''b z hz) hsmall, fun z hz ↦ ?_⟩
  · simp only [Matrix.add_apply]
    exact (differentiableOn_const _).add (hB'd i j)
  · simp only [Matrix.add_apply]
    exact (differentiableOn_const _).add (hB''d i j)
  -- the identity `g (1 + B'') = 1 + B'` on `W`
  have hz' := hWW' hz
  have hz'' := hWW'' hz
  have hB' : B' z = (g z - 1) + (g z - 1) * B'' z + B'' z := by
    ext i j
    have h1 : HasSum (fun k ↦ S' (e k) (m k) z i j) (B' z i j) :=
      (Summable.of_norm_bounded hsumm fun k ↦ (hspl k i j).2.2.1 z hz').hasSum
    have h2 : ∀ l, HasSum (fun k ↦ S'' (e k) (m k) z l j) (B'' z l j) := fun l ↦
      (Summable.of_norm_bounded hsumm fun k ↦ (hspl k l j).2.2.2.1 z hz'').hasSum
    have h3 : HasSum (fun k ↦ e k z i j) (B' z i j - B'' z i j) := by
      have hfun : (fun k ↦ e k z i j) =
          fun k ↦ S' (e k) (m k) z i j - S'' (e k) (m k) z i j :=
        funext fun k ↦ (hspl k i j).2.2.2.2 z hz
      rw [hfun]
      exact h1.sub (h2 i)
    have h4 : HasSum (fun k ↦ e (k + 1) z i j) (((g z - 1) * B'' z) i j) := by
      simp only [heS, Matrix.mul_apply]
      exact hasSum_sum fun l _ ↦ (h2 l).mul_left _
    have h5 : HasSum (fun k ↦ e k z i j) ((g z - 1) i j + ((g z - 1) * B'' z) i j) := by
      refine (hasSum_nat_add_iff' 1).mp ?_
      rw [Finset.sum_range_one]
      have hv : (g z - 1) i j + ((g z - 1) * B'' z) i j - e 0 z i j =
          ((g z - 1) * B'' z) i j :=
        add_sub_cancel_left _ _
      rw [hv]
      exact h4
    have := h3.unique h5
    simp only [Matrix.add_apply]
    linear_combination this
  change g z * (1 + B'' z) = 1 + B' z
  rw [hB', mul_add, mul_one, sub_mul, one_mul]
  abel

end Main

end AnalyticGeometry
