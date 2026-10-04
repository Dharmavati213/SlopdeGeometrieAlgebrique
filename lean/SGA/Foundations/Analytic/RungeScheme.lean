/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeParam

/-!
# Runge approximation on products from one-variable approximation schemes

A **one-variable approximation scheme** on compact `K ⊆ ℂ`, for functions holomorphic on
`L ⊇ K`, with approximants holomorphic on `Ω` (`AnalyticGeometry.ApproxScheme K L Ω`), consists of
a compact "contour" `Γ ⊆ L` and, for every order `N`, finitely many functions `ψ_{N,k}` holomorphic
on `Ω` and coefficient functionals `c_{N,k}` such that

* `|g(w) - ∑ₖ c_{N,k}(g) ψ_{N,k}(w)| ≤ M ε_N` for `w ∈ K`, whenever `g` is holomorphic on `L` and
  `|g| ≤ M` on `Γ`, with `ε_N → 0`;
* the coefficients depend holomorphically on parameters: if `h : ℂ^σ → ℂ` is analytic along
  `{z₍ⱼ←ζ₎ : ζ ∈ Γ}`, then `z ↦ c_{N,k}(ζ ↦ h(z₍ⱼ←ζ₎))` is analytic at `z`.

Truncated Laurent expansions on annuli and Cauchy integrals over the sides of rectangles give such
schemes. Given a scheme for every coordinate, every function analytic on `∏ Lᵢ` is, uniformly on
`∏ Kᵢ`, a limit of functions analytic on `∏ Ωᵢ` (`AnalyticGeometry.ProductRungeData.exists_approx`):
expand in one coordinate at a time and approximate the coefficients, which are analytic in the
remaining coordinates, by induction.

Reference: Hörmander, *An introduction to complex analysis in several variables*, proof of
Theorem 2.3.3 and 2.7; Gunning–Rossi, *Analytic functions of several complex variables*, I.D.
-/

noncomputable section

open Complex Set Metric Filter Topology

namespace AnalyticGeometry

/-- A **one-variable approximation scheme** on `K` for functions holomorphic on `L`, with
approximants holomorphic on `Ω`: see the module docstring. -/
structure ApproxScheme (K L Ω : Set ℂ) where
  /-- The contour on which the functions are bounded. -/
  Γ : Set ℂ
  isCompact_Γ : IsCompact Γ
  Γ_subset : Γ ⊆ L
  /-- The number of terms of order `N`. -/
  card : ℕ → ℕ
  /-- The approximating functions. -/
  ψ : ℕ → ℕ → ℂ → ℂ
  analyticAt_ψ : ∀ N k, ∀ w ∈ Ω, AnalyticAt ℂ (ψ N k) w
  /-- The coefficient functionals. -/
  coeff : ℕ → ℕ → (ℂ → ℂ) → ℂ
  analyticAt_coeff : ∀ {σ : Type} [Fintype σ] [DecidableEq σ] (N k : ℕ) (j : σ)
    (h : (σ → ℂ) → ℂ) (z : σ → ℂ), (∀ ζ ∈ Γ, AnalyticAt ℂ h (Function.update z j ζ)) →
    AnalyticAt ℂ (fun z ↦ coeff N k fun ζ ↦ h (Function.update z j ζ)) z
  /-- The error bound of order `N`, per unit bound on `Γ`. -/
  err : ℕ → ℝ
  tendsto_err : Tendsto err atTop (𝓝 0)
  approx : ∀ (N : ℕ) (g : ℂ → ℂ) (M : ℝ), (∀ ζ ∈ L, DifferentiableAt ℂ g ζ) →
    (∀ ζ ∈ Γ, ‖g ζ‖ ≤ M) → ∀ w ∈ K,
      ‖g w - ∑ k ∈ Finset.range (card N), coeff N k g * ψ N k w‖ ≤ M * err N

/-- The trivial scheme on the empty set. -/
def ApproxScheme.ofEmpty (L Ω : Set ℂ) : ApproxScheme ∅ L Ω where
  Γ := ∅
  isCompact_Γ := isCompact_empty
  Γ_subset := empty_subset _
  card _ := 0
  ψ _ _ _ := 0
  analyticAt_ψ _ _ _ _ := analyticAt_const
  coeff _ _ _ := 0
  analyticAt_coeff _ _ _ _ _ _ := analyticAt_const
  err _ := 0
  tendsto_err := tendsto_const_nhds
  approx _ _ _ _ _ _ hw := hw.elim

/-- A scheme transported along an equality of the approximation sets. -/
def ApproxScheme.congrK {K K' L Ω : Set ℂ} (S : ApproxScheme K L Ω) (h : K' = K) :
    ApproxScheme K' L Ω :=
  h ▸ S

/-- The data of Runge approximation on a product: approximation sets `Kᵢ` (compact), sets `Lᵢ`
near which the functions are holomorphic, domains `Ωᵢ` of the approximants, and a one-variable
approximation scheme for every coordinate. -/
structure ProductRungeData (σ : Type) where
  /-- The approximation sets. -/
  K : σ → Set ℂ
  /-- The sets where the functions to be approximated are holomorphic. -/
  L : σ → Set ℂ
  /-- The domains of the approximants. -/
  Ω : σ → Set ℂ
  isCompact_K : ∀ i, IsCompact (K i)
  K_subset_L : ∀ i, K i ⊆ L i
  K_subset_Ω : ∀ i, K i ⊆ Ω i
  /-- The one-variable schemes. -/
  scheme : ∀ i, ApproxScheme (K i) (L i) (Ω i)

namespace ProductRungeData

variable {σ : Type} [Fintype σ] (D : ProductRungeData σ)

/-- The statement proved by induction on the set `S` of coordinates already treated. -/
private def Step (S : Finset σ) : Prop :=
  ∀ h : (σ → ℂ) → ℂ,
    (∀ z : σ → ℂ, (∀ i ∈ S, z i ∈ D.L i) → (∀ i ∉ S, z i ∈ D.Ω i) → AnalyticAt ℂ h z) →
    ∀ C : σ → Set ℂ, (∀ i, IsCompact (C i)) → (∀ i ∉ S, C i ⊆ D.Ω i) →
    ∀ ε > 0, ∃ g : (σ → ℂ) → ℂ, (∀ z ∈ univ.pi D.Ω, AnalyticAt ℂ g z) ∧
      ∀ z : σ → ℂ, (∀ i ∈ S, z i ∈ D.K i) → (∀ i ∉ S, z i ∈ C i) → ‖h z - g z‖ < ε

private lemma step_empty : D.Step ∅ := by
  intro h hh C _ _ ε hε
  refine ⟨h, fun z hz ↦ hh z (by simp) fun i _ ↦ hz i (mem_univ i), fun z _ _ ↦ ?_⟩
  simpa using hε

private lemma step_insert [DecidableEq σ] {S : Finset σ} {j : σ} (hj : j ∉ S) (ih : D.Step S) :
    D.Step (insert j S) := by
  intro h hh C hC hCΩ ε hε
  set Sc := D.scheme j with hScdef
  -- the approximation set
  set Y : Set (σ → ℂ) := univ.pi fun i ↦ if i ∈ insert j S then D.K i else C i with hYdef
  have hmemY : ∀ z : σ → ℂ, (∀ i ∈ insert j S, z i ∈ D.K i) → (∀ i ∉ insert j S, z i ∈ C i) →
      z ∈ Y := fun z h1 h2 i _ ↦ by
    by_cases hi : i ∈ insert j S
    · simp only [hi, ↓reduceIte]
      exact h1 i hi
    · simp only [hi, ↓reduceIte]
      exact h2 i hi
  have hYK : ∀ z ∈ Y, ∀ i ∈ insert j S, z i ∈ D.K i := fun z hz i hi ↦ by
    have := hz i (mem_univ i)
    simpa [hi] using this
  have hYC : ∀ z ∈ Y, ∀ i ∉ insert j S, z i ∈ C i := fun z hz i hi ↦ by
    have := hz i (mem_univ i)
    simpa [hi] using this
  have hYc : IsCompact Y := isCompact_univ_pi fun i ↦ by
    by_cases hi : i ∈ insert j S
    · simp only [hi, ↓reduceIte]
      exact D.isCompact_K i
    · simp only [hi, ↓reduceIte]
      exact hC i
  have hjT : j ∈ insert j S := Finset.mem_insert_self j S
  -- `h` is analytic at the points obtained by moving the `j`-th coordinate in `Lⱼ`
  have hX : ∀ z : σ → ℂ, (∀ i ∈ S, z i ∈ D.L i) → (∀ i ∉ insert j S, z i ∈ D.Ω i) →
      ∀ ζ ∈ D.L j, AnalyticAt ℂ h (Function.update z j ζ) := by
    intro z h1 h2 ζ hζ
    refine hh _ (fun i hi ↦ ?_) fun i hi ↦ ?_
    · by_cases hij : i = j
      · subst hij
        simpa using hζ
      · rw [Function.update_of_ne hij]
        exact h1 i ((Finset.mem_insert.mp hi).resolve_left hij)
    · have hij : i ≠ j := fun h ↦ hi (h ▸ hjT)
      rw [Function.update_of_ne hij]
      exact h2 i hi
  have hYX : ∀ z ∈ Y, ∀ ζ ∈ D.L j, AnalyticAt ℂ h (Function.update z j ζ) := fun z hz ↦
    hX z (fun i hi ↦ D.K_subset_L i (hYK z hz i (Finset.mem_insert_of_mem hi)))
      fun i hi ↦ hCΩ i hi (hYC z hz i hi)
  -- a bound for `h` on `Y × Γ`
  have hcont : ContinuousOn (fun p : (σ → ℂ) × ℂ ↦ h (Function.update p.1 j p.2)) (Y ×ˢ Sc.Γ) :=
    fun p hp ↦ (ContinuousAt.comp (g := h)
      (f := fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2)
      (hYX p.1 hp.1 p.2 (Sc.Γ_subset hp.2)).continuousAt
      (analyticAt_update_prod j p).continuousAt).continuousWithinAt
  obtain ⟨M₁, hM₁⟩ := (hYc.prod Sc.isCompact_Γ).exists_bound_of_continuousOn hcont
  set M : ℝ := max M₁ 0 with hMdef
  have hM : ∀ p ∈ Y ×ˢ Sc.Γ, ‖h (Function.update p.1 j p.2)‖ ≤ M :=
    fun p hp ↦ (hM₁ p hp).trans (le_max_left _ _)
  -- the truncation order
  obtain ⟨N, hN⟩ : ∃ N, M * Sc.err N < ε / 2 := by
    have ht : Tendsto (fun N ↦ M * Sc.err N) atTop (𝓝 0) := by
      simpa using Sc.tendsto_err.const_mul M
    exact (ht.eventually (gt_mem_nhds (half_pos hε))).exists
  -- the coefficients, as functions of the other variables
  set c : ℕ → (σ → ℂ) → ℂ := fun k z ↦ Sc.coeff N k fun ζ ↦ h (Function.update z j ζ)
    with hcdef
  have hc : ∀ k, ∀ z : σ → ℂ, (∀ i ∈ S, z i ∈ D.L i) → (∀ i ∉ S, z i ∈ D.Ω i) →
      AnalyticAt ℂ (c k) z := fun k z h1 h2 ↦
    Sc.analyticAt_coeff N k j h z fun ζ hζ ↦
      hX z h1 (fun i hi ↦ h2 i fun hiS ↦ hi (Finset.mem_insert_of_mem hiS)) ζ (Sc.Γ_subset hζ)
  -- the compact sets for the induction hypothesis
  set C' : σ → Set ℂ := fun i ↦ if i = j then D.K j else C i with hC'def
  have hC' : ∀ i, IsCompact (C' i) := fun i ↦ by
    by_cases hij : i = j
    · simp only [hC'def, hij, ↓reduceIte]
      exact D.isCompact_K j
    · simp only [hC'def, hij, ↓reduceIte]
      exact hC i
  have hC'Ω : ∀ i ∉ S, C' i ⊆ D.Ω i := fun i hi ↦ by
    by_cases hij : i = j
    · subst hij
      simp only [hC'def, ↓reduceIte]
      exact D.K_subset_Ω i
    · simp only [hC'def, hij, ↓reduceIte]
      exact hCΩ i fun h ↦ (Finset.mem_insert.mp h).elim hij hi
  -- a bound for the approximating functions on `Kⱼ`
  have hψc : ContinuousOn (fun w ↦ ∑ k ∈ Finset.range (Sc.card N), ‖Sc.ψ N k w‖) (D.K j) :=
    continuousOn_finsetSum _ fun k _ ↦ fun w hw ↦
      (Sc.analyticAt_ψ N k w (D.K_subset_Ω j hw)).continuousAt.norm.continuousWithinAt
  obtain ⟨B₁, hB₁⟩ := (D.isCompact_K j).exists_bound_of_continuousOn hψc
  set B : ℝ := max B₁ 1 with hBdef
  have hBpos : 0 < B := one_pos.trans_le (le_max_right _ _)
  have hψB : ∀ w ∈ D.K j, ∀ k ∈ Finset.range (Sc.card N), ‖Sc.ψ N k w‖ ≤ B := fun w hw k hk ↦ by
    have h1 := hB₁ w hw
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at h1
    exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg (Sc.ψ N i w)) hk).trans
      (h1.trans (le_max_left _ _))
  -- approximate the coefficients
  set δ : ℝ := ε / (4 * (Sc.card N + 1) * B) with hδdef
  have hδ : 0 < δ := by positivity
  choose g hg_an hg using fun k ↦ ih (c k) (hc k) C' hC' hC'Ω δ hδ
  refine ⟨fun z ↦ ∑ k ∈ Finset.range (Sc.card N), g k z * Sc.ψ N k (z j), ?_, ?_⟩
  · -- analyticity
    intro z hz
    refine Finset.analyticAt_fun_sum _ fun k _ ↦ (hg_an k z hz).mul ?_
    exact AnalyticAt.comp (g := Sc.ψ N k) (f := fun z : σ → ℂ ↦ z j)
      (Sc.analyticAt_ψ N k (z j) (hz j (mem_univ j)))
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) j).analyticAt z)
  · -- the estimate
    intro z h1 h2
    have hzY : z ∈ Y := hmemY z h1 h2
    have hzj : z j ∈ D.K j := h1 j hjT
    have hzS : ∀ i ∈ S, z i ∈ D.K i := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have hzC' : ∀ i ∉ S, z i ∈ C' i := fun i hi ↦ by
      by_cases hij : i = j
      · subst hij
        simpa [hC'def] using hzj
      · simp only [hC'def, hij, ↓reduceIte]
        exact h2 i fun h ↦ (Finset.mem_insert.mp h).elim hij hi
    -- the one-variable approximation at `z`
    set f : ℂ → ℂ := fun ζ ↦ h (Function.update z j ζ) with hfdef
    have hfL : ∀ ζ ∈ D.L j, DifferentiableAt ℂ f ζ := fun ζ hζ ↦
      ((hYX z hzY ζ hζ).comp (analyticAt_update_right z j ζ)).differentiableAt
    have hfM : ∀ ζ ∈ Sc.Γ, ‖f ζ‖ ≤ M := fun ζ hζ ↦ hM (z, ζ) ⟨hzY, hζ⟩
    have happrox := Sc.approx N f M hfL hfM (z j) hzj
    have hfz : f (z j) = h z := by simp [hfdef]
    rw [hfz] at happrox
    -- the coefficient errors
    have hsum : ‖∑ k ∈ Finset.range (Sc.card N), Sc.coeff N k f * Sc.ψ N k (z j) -
        ∑ k ∈ Finset.range (Sc.card N), g k z * Sc.ψ N k (z j)‖ ≤ Sc.card N * (δ * B) := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      have hle : ∀ k ∈ Finset.range (Sc.card N),
          ‖Sc.coeff N k f * Sc.ψ N k (z j) - g k z * Sc.ψ N k (z j)‖ ≤ δ * B := fun k hk ↦ by
        rw [← sub_mul, norm_mul]
        exact mul_le_mul (hg k z hzS hzC').le (hψB _ hzj k hk) (norm_nonneg _) hδ.le
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    have hsmall : (Sc.card N : ℝ) * (δ * B) < ε / 2 := by
      have hδB : δ * B = ε / (4 * (Sc.card N + 1)) := by
        rw [hδdef]
        field_simp
      rw [hδB]
      have hN1 : (0 : ℝ) < Sc.card N + 1 := by positivity
      rw [show (Sc.card N : ℝ) * (ε / (4 * (Sc.card N + 1))) =
        ε / 4 * (Sc.card N / (Sc.card N + 1)) by field_simp]
      have : (Sc.card N : ℝ) / (Sc.card N + 1) < 1 := (div_lt_one hN1).mpr (lt_add_one _)
      nlinarith
    calc ‖h z - ∑ k ∈ Finset.range (Sc.card N), g k z * Sc.ψ N k (z j)‖
        ≤ ‖h z - ∑ k ∈ Finset.range (Sc.card N), Sc.coeff N k f * Sc.ψ N k (z j)‖ +
          ‖∑ k ∈ Finset.range (Sc.card N), Sc.coeff N k f * Sc.ψ N k (z j) -
            ∑ k ∈ Finset.range (Sc.card N), g k z * Sc.ψ N k (z j)‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (happrox.trans hN.le) (hsum.trans_lt hsmall)
      _ = ε := add_halves ε

private lemma step (S : Finset σ) : D.Step S := by
  classical
  induction S using Finset.induction_on with
  | empty => exact D.step_empty
  | insert j S hj ih => exact D.step_insert hj ih

/-- **Runge approximation on products**: given one-variable approximation schemes, a function
analytic at every point of `∏ Lᵢ` is, uniformly on `∏ Kᵢ`, a limit of functions analytic on
`∏ Ωᵢ`. -/
theorem exists_approx {h : (σ → ℂ) → ℂ} (hh : ∀ z ∈ univ.pi D.L, AnalyticAt ℂ h z) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ g : (σ → ℂ) → ℂ, (∀ z ∈ univ.pi D.Ω, AnalyticAt ℂ g z) ∧
      ∀ z ∈ univ.pi D.K, ‖h z - g z‖ < ε := by
  classical
  obtain ⟨g, hg, hgh⟩ := D.step Finset.univ h (fun z h1 _ ↦ hh z fun i _ ↦ h1 i (by simp))
    (fun _ ↦ ∅) (fun _ ↦ isCompact_empty) (fun i hi ↦ (hi (Finset.mem_univ i)).elim) ε hε
  exact ⟨g, hg, fun z hz ↦ hgh z (fun i _ ↦ hz i (mem_univ i))
    fun i hi ↦ (hi (Finset.mem_univ i)).elim⟩

end ProductRungeData

end AnalyticGeometry
