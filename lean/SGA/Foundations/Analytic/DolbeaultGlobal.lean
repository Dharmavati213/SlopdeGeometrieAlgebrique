/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultHolomorphic

/-!
# The `∂̄`-equation on product domains

Let `Ω = ∏ᵢ Ωᵢ ⊆ ℂ^σ` be a product of open subsets of `ℂ` with an exhaustion by compact products
`Kᵛ = ∏ᵢ Kᵢᵛ`, `Kᵢᵛ ⊆ interior Kᵢᵛ⁺¹` (`AnalyticGeometry.ProductExhaustion`). We solve the
`∂̄`-equation globally on `Ω` (Hörmander, *An introduction to complex analysis in several
variables*, proof of Theorem 2.3.3, for products of planar open sets instead of polydiscs).

## Main results

* `AnalyticGeometry.exists_dbarForm_eq_global_succ`, `AnalyticGeometry.dbarExactOn_pi_succ`
  (positive degree, no further hypothesis): every smooth `∂̄`-closed `(0, q + 2)`-form on `Ω` is
  `∂̄` of a smooth `(0, q + 1)`-form on `Ω`. Solve the equation near each `Kᵛ`
  (`exists_dbarForm_eq_near_compact`) and correct the solution on `Kᵛ⁺¹` by `∂̄(ψ w)`, where `∂̄w`
  is the difference of two consecutive solutions near `Kᵛ` and `ψ` a cutoff, so that the
  solutions stabilize.
* `AnalyticGeometry.exists_dbarForm_eq_global_zero`, `AnalyticGeometry.dbarExactOn_pi_zero`
  (degree `0`, **assuming the exhaustion has the Runge property** `ProductExhaustion.IsRunge`):
  every smooth `∂̄`-closed `(0, 1)`-form on `Ω` is `∂̄` of a smooth function on `Ω`. The
  consecutive local solutions now differ by holomorphic functions, which are corrected by global
  holomorphic approximants; the corrections converge normally.
* `AnalyticGeometry.H'_holomorphicAbSheaf_two_le`: `Hⁿ(Ω, 𝒪) = 0` for all `n ≥ 2` (no Runge
  hypothesis).
* `AnalyticGeometry.H'_holomorphicAbSheaf_subsingleton_of_isRunge`: `Hⁿ(Ω, 𝒪) = 0` for all
  `n ≥ 1`, **assuming `ProductExhaustion.IsRunge`**. The Runge property of the standard
  exhaustions of discs, `ℂ` and `ℂ*` is proved in `SGA.Foundations.Analytic.RungeProduct`.
-/

noncomputable section

open Topology Filter Set Complex
open scoped ContDiff

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] [LinearOrder σ]

/-- An exhaustion of the product `∏ᵢ Ωᵢ` by compact products `∏ᵢ K ν i`, each contained in the
interior of the next. -/
structure ProductExhaustion (Ω : σ → Set ℂ) where
  /-- The compact sets. -/
  K : ℕ → σ → Set ℂ
  isCompact : ∀ ν i, IsCompact (K ν i)
  subset_interior : ∀ ν i, K ν i ⊆ interior (K (ν + 1) i)
  subset : ∀ ν i, K ν i ⊆ Ω i
  exhaust : ∀ z ∈ univ.pi Ω, ∃ ν, ∀ i, z i ∈ interior (K ν i)

namespace ProductExhaustion

variable {Ω : σ → Set ℂ} (E : ProductExhaustion Ω)

omit [Fintype σ] [LinearOrder σ] in
lemma mono {ν ν' : ℕ} (h : ν ≤ ν') (i : σ) : E.K ν i ⊆ E.K ν' i := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans ((E.subset_interior _ i).trans interior_subset)

end ProductExhaustion

omit [LinearOrder σ] in
/-- A smooth product cutoff: `ψ = 1` near `∏ Kᵢ`, `ψ = 0` outside a compact product inside
`∏ Wᵢ`. -/
lemma exists_productCutoff {K W : σ → Set ℂ} (hK : ∀ i, IsCompact (K i))
    (hW : ∀ i, IsOpen (W i)) (hKW : ∀ i, K i ⊆ W i) :
    ∃ ψ : (σ → ℂ) → ℂ, ContDiff ℝ ∞ ψ ∧
      ∃ N : σ → Set ℂ, (∀ i, IsOpen (N i)) ∧ (∀ i, K i ⊆ N i) ∧
        (∀ z ∈ univ.pi N, ψ z = 1) ∧
      ∃ k : σ → Set ℂ, (∀ i, IsCompact (k i)) ∧ (∀ i, k i ⊆ W i) ∧
        ∀ z, z ∉ univ.pi k → ψ =ᶠ[𝓝 z] 0 := by
  choose χ hχ N hN hKN _ hχ1 k hk hkW hχ0 using fun i ↦ exists_cutoff (hK i) (hW i) (hKW i)
  refine ⟨fun z ↦ ∏ i, (χ i (z i) : ℂ), ?_, N, hN, hKN, fun z hz ↦ ?_, k, hk, hkW, fun z hz ↦ ?_⟩
  · exact contDiff_prod fun i _ ↦ ofRealCLM.contDiff.comp ((hχ i).comp (contDiff_apply ℝ ℂ i))
  · exact Finset.prod_eq_one fun i _ ↦ by rw [hχ1 i _ (hz i (mem_univ i))]; simp
  · obtain ⟨i, hi⟩ : ∃ i, z i ∉ k i := by
      simpa only [Set.mem_pi, mem_univ, true_implies, not_forall] using hz
    have : ∀ᶠ y in 𝓝 z, y i ∉ k i :=
      (continuous_apply i).continuousAt.preimage_mem_nhds
        ((hk i).isClosed.isOpen_compl.mem_nhds hi)
    filter_upwards [this] with y hy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hχ0 i _ hy]; simp)

/-- A solution of `∂̄u = G` near `∏ᵢ Kᵢ`. -/
private structure LocalSol (Ω K : σ → Set ℂ) (q : ℕ) (G : Finset σ → (σ → ℂ) → ℂ) where
  W : σ → Set ℂ
  isOpen : ∀ i, IsOpen (W i)
  K_subset : ∀ i, K i ⊆ W i
  subset : ∀ i, W i ⊆ Ω i
  u : Finset σ → (σ → ℂ) → ℂ
  smooth : ∀ z ∈ univ.pi W, IsSmoothFormAt u z
  deg : ∀ I, I.card ≠ q → u I = 0
  eq : ∀ J, ∀ z ∈ univ.pi W, dbarForm u J z = G J z

variable {Ω : σ → Set ℂ} {q : ℕ} {G : Finset σ → (σ → ℂ) → ℂ}

/-- Existence of local solutions near compact products. -/
private lemma LocalSol.nonempty (hΩ : ∀ i, IsOpen (Ω i)) {K : σ → Set ℂ}
    (hK : ∀ i, IsCompact (K i)) (hKΩ : ∀ i, K i ⊆ Ω i)
    (hGs : ∀ z ∈ univ.pi Ω, IsSmoothFormAt G z)
    (hdeg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi Ω, G J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi Ω, dbarForm G J z = 0) : Nonempty (LocalSol Ω K q G) := by
  obtain ⟨W, hWo, hKW, hWΩ, u, hus, hudeg, hdu⟩ :=
    exists_dbarForm_eq_near_compact hΩ hK hKΩ hGs hdeg hcl
  exact ⟨⟨W, hWo, hKW, hWΩ, u, hus, hudeg, hdu⟩⟩

/-- **The correction step** (degree `q + 1 ≥ 1`): given a solution `S` near `K` and a solution `T`
near `K' ⊇ K`, there is a solution near `K'` which agrees with `S` on a neighbourhood of `∏ K`. -/
private lemma LocalSol.exists_agree {K K' : σ → Set ℂ} (hK : ∀ i, IsCompact (K i))
    (hKK' : ∀ i, K i ⊆ K' i) (S : LocalSol Ω K (q + 1) G) (T : LocalSol Ω K' (q + 1) G) :
    ∃ T' : LocalSol Ω K' (q + 1) G, ∃ N : Set (σ → ℂ), IsOpen N ∧ univ.pi K ⊆ N ∧
      ∀ I, ∀ z ∈ N, T'.u I z = S.u I z := by
  -- the difference of the two solutions is closed near `K`
  set W₀ : σ → Set ℂ := fun i ↦ S.W i ∩ T.W i
  have hW₀ : ∀ i, IsOpen (W₀ i) := fun i ↦ (S.isOpen i).inter (T.isOpen i)
  have hKW₀ : ∀ i, K i ⊆ W₀ i := fun i ↦ subset_inter (S.K_subset i)
    ((hKK' i).trans (T.K_subset i))
  have hW₀S : ∀ z ∈ univ.pi W₀, z ∈ univ.pi S.W := fun z hz i _ ↦ (hz i (mem_univ i)).1
  have hW₀T : ∀ z ∈ univ.pi W₀, z ∈ univ.pi T.W := fun z hz i _ ↦ (hz i (mem_univ i)).2
  set D : Finset σ → (σ → ℂ) → ℂ := fun I y ↦ T.u I y - S.u I y with hDdef
  have hDs : ∀ z ∈ univ.pi W₀, IsSmoothFormAt D z := fun z hz I ↦
    (T.smooth z (hW₀T z hz) I).sub (S.smooth z (hW₀S z hz) I)
  have hDdeg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi W₀, D J z = 0 := fun J hJ z _ ↦ by
    simp [hDdef, T.deg J hJ, S.deg J hJ]
  have hDcl : ∀ J, ∀ z ∈ univ.pi W₀, dbarForm D J z = 0 := fun J z hz ↦ by
    rw [hDdef, dbarForm_sub ((T.smooth z (hW₀T z hz)).differentiableAt)
      ((S.smooth z (hW₀S z hz)).differentiableAt), T.eq J z (hW₀T z hz),
      S.eq J z (hW₀S z hz), sub_self]
  -- solve `∂̄w = D` near `K`
  obtain ⟨W'', hW''o, hKW'', hW''W₀, w, hws, hwdeg, hdw⟩ :=
    exists_dbarForm_eq_near_compact hW₀ hK hKW₀ hDs hDdeg hDcl
  -- cut `w` off
  obtain ⟨ψ, hψ, Nc, hNco, hKNc, hψ1, k, hk, hkW'', hψ0⟩ := exists_productCutoff hK hW''o hKW''
  set ψw : Finset σ → (σ → ℂ) → ℂ := fun I y ↦ ψ y * w I y with hψwdef
  have hψws : ∀ z, IsSmoothFormAt ψw z := fun z I ↦ by
    by_cases hz : z ∈ univ.pi k
    · have hzW : z ∈ univ.pi W'' := fun i _ ↦ hkW'' i (hz i (mem_univ i))
      exact hψ.contDiffAt.mul (hws z hzW I)
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hψ0 z hz] with y hy
      simp [hψwdef, hy]
  have hψwdeg : ∀ I, I.card ≠ q → ∀ y ∈ (univ : Set (σ → ℂ)), ψw I y = 0 := fun I hI y _ ↦ by
    simp [hψwdef, hwdeg I hI]
  -- the corrected solution
  refine ⟨⟨T.W, T.isOpen, T.K_subset, T.subset, fun I y ↦ T.u I y - dbarForm ψw I y,
    fun z hz I ↦ (T.smooth z hz I).sub ((hψws z).dbarForm I), fun I hI ↦ ?_, fun J z hz ↦ ?_⟩,
    univ.pi Nc ∩ univ.pi W'', (isOpen_univ_pi hNco).inter (isOpen_univ_pi hW''o),
    fun z hz ↦ ⟨fun i _ ↦ hKNc i (hz i (mem_univ i)), fun i _ ↦ hKW'' i (hz i (mem_univ i))⟩,
    fun I z hz ↦ ?_⟩
  · funext y
    rw [T.deg I hI, dbarForm_eq_zero_of_card_ne isOpen_univ hψwdeg hI (mem_univ y)]
    simp
  · rw [dbarForm_sub ((T.smooth z hz).differentiableAt) ((hψws z).dbarForm.differentiableAt),
      T.eq J z hz, dbarForm_dbarForm (hψws z), sub_zero]
  · -- near `∏ K`, `ψ = 1`, so `∂̄(ψ w) = ∂̄w = T - S`
    have hev : ∀ I', ψw I' =ᶠ[𝓝 z] w I' := fun I' ↦ by
      filter_upwards [(isOpen_univ_pi hNco).mem_nhds hz.1] with y hy
      simp [hψwdef, hψ1 y hy]
    change T.u I z - dbarForm ψw I z = S.u I z
    have hzW₀ : z ∈ univ.pi W₀ := fun i _ ↦ hW''W₀ i (hz.2 i (mem_univ i))
    rw [dbarForm_congr hev, hdw I z hz.2, hDdef]
    ring

/-- **`∂̄` on product domains in positive degree** (Hörmander, proof of 2.3.3 for `q ≥ 1`): every
smooth `∂̄`-closed `(0, q + 2)`-form on a product `∏ Ωᵢ` with an exhaustion by compact products is
`∂̄` of a smooth `(0, q + 1)`-form on `∏ Ωᵢ` (coefficient form). -/
theorem exists_dbarForm_eq_global_succ (hΩ : ∀ i, IsOpen (Ω i)) (E : ProductExhaustion Ω)
    (hGs : ∀ z ∈ univ.pi Ω, IsSmoothFormAt G z)
    (hdeg : ∀ J, J.card ≠ q + 1 + 1 → ∀ z ∈ univ.pi Ω, G J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi Ω, dbarForm G J z = 0) :
    ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ univ.pi Ω, IsSmoothFormAt u z) ∧
      (∀ I, I.card ≠ q + 1 → ∀ z ∈ univ.pi Ω, u I z = 0) ∧
      ∀ J, ∀ z ∈ univ.pi Ω, dbarForm u J z = G J z := by
  classical
  have sol : ∀ ν, LocalSol Ω (E.K ν) (q + 1) G := fun ν ↦
    (LocalSol.nonempty hΩ (E.isCompact ν) (E.subset ν) hGs hdeg hcl).some
  have step : ∀ ν (S : LocalSol Ω (E.K ν) (q + 1) G),
      ∃ T' : LocalSol Ω (E.K (ν + 1)) (q + 1) G, ∃ N : Set (σ → ℂ), IsOpen N ∧
        univ.pi (E.K ν) ⊆ N ∧ ∀ I, ∀ z ∈ N, T'.u I z = S.u I z := fun ν S ↦
    LocalSol.exists_agree (E.isCompact ν) (fun i ↦ E.mono (Nat.le_succ ν) i) S (sol (ν + 1))
  let seq : (ν : ℕ) → LocalSol Ω (E.K ν) (q + 1) G := fun ν ↦
    Nat.rec (motive := fun ν ↦ LocalSol Ω (E.K ν) (q + 1) G) (sol 0)
      (fun ν S ↦ (step ν S).choose) ν
  have hseq : ∀ ν, seq (ν + 1) = (step ν (seq ν)).choose := fun ν ↦ rfl
  -- consecutive solutions agree near `Kᵛ`
  have hagree : ∀ ν, ∀ I, ∀ y ∈ univ.pi (E.K ν), (seq (ν + 1)).u I y = (seq ν).u I y := by
    intro ν I y hy
    obtain ⟨N, -, hKN, hN⟩ := (step ν (seq ν)).choose_spec
    rw [hseq]
    exact hN I y (hKN hy)
  have hchain : ∀ m k, m ≤ k → ∀ I, ∀ y ∈ univ.pi (E.K m), (seq k).u I y = (seq m).u I y := by
    intro m k hmk I y hy
    induction k, hmk using Nat.le_induction with
    | base => rfl
    | succ k hmk ih =>
      rw [hagree k I y fun i _ ↦ E.mono hmk i (hy i (mem_univ i)), ih]
  -- the global solution
  let mz : ∀ z ∈ univ.pi Ω, ℕ := fun z hz ↦ Nat.find (E.exhaust z hz)
  let u : Finset σ → (σ → ℂ) → ℂ := fun I z ↦
    if hz : z ∈ univ.pi Ω then (seq (mz z hz)).u I z else 0
  have hint : ∀ ν, ∀ y, (∀ i, y i ∈ interior (E.K ν i)) → y ∈ univ.pi (E.K ν) :=
    fun ν y hy i _ ↦ interior_subset (hy i)
  have hΩK : ∀ ν, ∀ y, (∀ i, y i ∈ interior (E.K ν i)) → y ∈ univ.pi Ω :=
    fun ν y hy i _ ↦ E.subset ν i (interior_subset (hy i))
  have hloc : ∀ z (hz : z ∈ univ.pi Ω), ∀ I, u I =ᶠ[𝓝 z] (seq (mz z hz)).u I := by
    intro z hz I
    set m := mz z hz
    have hO : IsOpen {y : σ → ℂ | ∀ i, y i ∈ interior (E.K m i)} := by
      have : {y : σ → ℂ | ∀ i, y i ∈ interior (E.K m i)} =
          univ.pi fun i ↦ interior (E.K m i) := by
        ext y
        simp
      rw [this]
      exact isOpen_univ_pi fun i ↦ isOpen_interior
    have hzO : ∀ i, z i ∈ interior (E.K m i) := Nat.find_spec (E.exhaust z hz)
    filter_upwards [hO.mem_nhds hzO] with y hy
    have hyΩ := hΩK m y hy
    simp only [u, hyΩ, ↓reduceDIte]
    have hle : mz y hyΩ ≤ m := Nat.find_min' _ hy
    have hy' : y ∈ univ.pi (E.K (mz y hyΩ)) := hint _ y (Nat.find_spec (E.exhaust y hyΩ))
    exact (hchain _ m hle I y hy').symm
  have hzK : ∀ z (hz : z ∈ univ.pi Ω), z ∈ univ.pi (seq (mz z hz)).W := fun z hz ↦
    fun i _ ↦ (seq (mz z hz)).K_subset i (interior_subset (Nat.find_spec (E.exhaust z hz) i))
  refine ⟨u, fun z hz I ↦ ?_, fun I hI z hz ↦ ?_, fun J z hz ↦ ?_⟩
  · exact ((seq (mz z hz)).smooth z (hzK z hz) I).congr_of_eventuallyEq (hloc z hz I)
  · simp only [u, hz, ↓reduceDIte, (seq (mz z hz)).deg I hI, Pi.zero_apply]
  · rw [dbarForm_congr (hloc z hz), (seq (mz z hz)).eq J z (hzK z hz)]

/-- Global `∂̄`-exactness on an open set `V` from its coefficient form. -/
lemma dbarExactOn_of_exists {V : Set (σ → ℂ)} (hV : IsOpen V) (q : ℕ)
    (h : ∀ G : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ V, IsSmoothFormAt G z) →
      (∀ J, J.card ≠ q + 1 → ∀ z ∈ V, G J z = 0) → (∀ J, ∀ z ∈ V, dbarForm G J z = 0) →
      ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ V, IsSmoothFormAt u z) ∧
        (∀ I, I.card ≠ q → ∀ z ∈ V, u I z = 0) ∧ ∀ J, ∀ z ∈ V, dbarForm u J z = G J z) :
    DbarExactOn V q := by
  intro g hg
  have hcl : ∀ J, ∀ z ∈ V, dbarForm (formCoeffs g) J z = 0 := by
    intro J z hz
    by_cases hJ : J.card = q + 1 + 1
    · exact congrFun (congrFun hg.2 ⟨z, hz⟩) ⟨J, hJ⟩
    · exact dbarForm_eq_zero_of_card_ne isOpen_univ
        (fun I hI y _ ↦ by rw [formCoeffs_of_card_ne _ hI]; rfl) hJ (mem_univ z)
  obtain ⟨u, hus, hudeg, hdu⟩ := h (formCoeffs g) (fun z hz ↦ hg.1.isSmoothFormAt hz)
    (fun J hJ z _ ↦ by rw [formCoeffs_of_card_ne _ hJ]; rfl) hcl
  let s : V → FormCoeff σ q := fun y I ↦ u I.1 y
  have hs : IsSmoothOn s := isSmoothOn_restrict
    (g := fun y (I : {I : Finset σ // I.card = q}) ↦ u I.1 y) hV
    fun y hy ↦ contDiffAt_pi.mpr fun I ↦ hus y hy I.1
  refine ⟨s, hs, funext fun y ↦ funext fun J ↦ ?_⟩
  have hcoeff : ∀ I, formCoeffs s I =ᶠ[𝓝 (y : σ → ℂ)] u I := fun I ↦ by
    filter_upwards [hV.mem_nhds y.2] with z hz
    by_cases hI : I.card = q
    · rw [formCoeffs_of_card _ hI, extendByZero_of_mem _ hz]
    · rw [formCoeffs_of_card_ne _ hI, hudeg I hI z hz]
      rfl
  change dbarForm (formCoeffs s) J.1 y = g y J
  rw [dbarForm_congr hcoeff, hdu J.1 y y.2, formCoeffs_of_card _ J.2, extendByZero_of_mem _ y.2]

/-- **`∂̄`-exactness in positive degree on product domains**: on `∏ Ωᵢ` with an exhaustion by
compact products, every smooth `∂̄`-closed `(0, q + 2)`-form is `∂̄`-exact. -/
theorem dbarExactOn_pi_succ (hΩ : ∀ i, IsOpen (Ω i)) (E : ProductExhaustion Ω) (q : ℕ) :
    DbarExactOn (univ.pi Ω) (q + 1) :=
  dbarExactOn_of_exists (isOpen_univ_pi hΩ) (q + 1) fun _ hGs hdeg hcl ↦
    exists_dbarForm_eq_global_succ hΩ E hGs hdeg hcl

/-! ### Degree zero: Runge approximation -/

/-- The **Runge property** of an exhaustion: every function analytic near `K^{ν+1}` is, uniformly
on `Kᵛ`, a limit of functions analytic on `∏ Ωᵢ`. -/
def ProductExhaustion.IsRunge (E : ProductExhaustion Ω) : Prop :=
  ∀ ν (h : (σ → ℂ) → ℂ), (∀ z ∈ univ.pi (E.K (ν + 1)), AnalyticAt ℂ h z) →
    ∀ ε > 0, ∃ g : (σ → ℂ) → ℂ, (∀ z ∈ univ.pi Ω, AnalyticAt ℂ g z) ∧
      ∀ z ∈ univ.pi (E.K ν), ‖h z - g z‖ < ε

omit [Fintype σ] in
/-- `dbarForm` of a degree-zero form is `±∂/∂z̄ⱼ` of its coefficient. -/
lemma dbarForm_singleton (u : Finset σ → (σ → ℂ) → ℂ) (j : σ) (z : σ → ℂ) :
    dbarForm u {j} z = koszulSign j {j} * dbarPartial j (u ∅) z := by
  rw [dbarForm, Finset.sum_singleton, Finset.erase_singleton]

/-- The degree-zero form with coefficient `g`. -/
private def zeroForm (g : (σ → ℂ) → ℂ) : Finset σ → (σ → ℂ) → ℂ :=
  fun I y ↦ if I = ∅ then g y else 0

/-- A holomorphic function, as a form, is `∂̄`-closed. -/
private lemma dbarForm_zeroForm {g : (σ → ℂ) → ℂ} {z : σ → ℂ} (hg : AnalyticAt ℂ g z)
    (J : Finset σ) : dbarForm (zeroForm g) J z = 0 := by
  refine Finset.sum_eq_zero fun j _ ↦ ?_
  by_cases hJ : J.erase j = ∅
  · have : zeroForm g (J.erase j) = g := funext fun y ↦ by simp [zeroForm, hJ]
    rw [this, dbarPartial_eq_zero_of_differentiableAt j hg.differentiableAt, mul_zero]
  · have : zeroForm g (J.erase j) = 0 := funext fun y ↦ by simp [zeroForm, hJ]
    rw [this, dbarPartial_zero, mul_zero]

private lemma isSmoothFormAt_zeroForm {g : (σ → ℂ) → ℂ} {z : σ → ℂ} (hg : AnalyticAt ℂ g z) :
    IsSmoothFormAt (zeroForm g) z := fun I ↦ by
  by_cases hI : I = ∅
  · have : zeroForm g I = g := funext fun y ↦ by simp [zeroForm, hI]
    rw [this]
    exact (hg.contDiffAt (n := ∞)).restrict_scalars ℝ
  · have : zeroForm g I = 0 := funext fun y ↦ by simp [zeroForm, hI]
    rw [this]
    exact contDiffAt_const

/-- **The Runge step** (degree `0`): given a solution `S` near `K^{ν+1}`, there is a solution near
`K^{ν+2}` whose difference with `S` is analytic near `K^{ν+1}` and smaller than `2^{-ν}` on
`Kᵛ`. -/
private lemma LocalSol.exists_runge (hΩ : ∀ i, IsOpen (Ω i)) (E : ProductExhaustion Ω)
    (hR : E.IsRunge) (hGs : ∀ z ∈ univ.pi Ω, IsSmoothFormAt G z)
    (hdeg : ∀ J, J.card ≠ 0 + 1 → ∀ z ∈ univ.pi Ω, G J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi Ω, dbarForm G J z = 0) (ν : ℕ)
    (S : LocalSol Ω (E.K (ν + 1)) 0 G) :
    ∃ T' : LocalSol Ω (E.K (ν + 2)) 0 G,
      (∀ z ∈ univ.pi (E.K (ν + 1)), AnalyticAt ℂ (fun y ↦ T'.u ∅ y - S.u ∅ y) z) ∧
      ∀ z ∈ univ.pi (E.K ν), ‖T'.u ∅ z - S.u ∅ z‖ < (1 / 2) ^ ν := by
  obtain ⟨T⟩ := LocalSol.nonempty (K := E.K (ν + 2)) hΩ (E.isCompact _) (E.subset _) hGs hdeg hcl
  set W₀ : σ → Set ℂ := fun i ↦ S.W i ∩ T.W i
  have hW₀ : IsOpen (univ.pi W₀) := isOpen_univ_pi fun i ↦ (S.isOpen i).inter (T.isOpen i)
  have hKW₀ : ∀ z ∈ univ.pi (E.K (ν + 1)), z ∈ univ.pi W₀ := fun z hz i _ ↦
    ⟨S.K_subset i (hz i (mem_univ i)),
      T.K_subset i (E.mono (Nat.le_succ _) i (hz i (mem_univ i)))⟩
  have hW₀S : ∀ z ∈ univ.pi W₀, z ∈ univ.pi S.W := fun z hz i _ ↦ (hz i (mem_univ i)).1
  have hW₀T : ∀ z ∈ univ.pi W₀, z ∈ univ.pi T.W := fun z hz i _ ↦ (hz i (mem_univ i)).2
  set D : (σ → ℂ) → ℂ := fun y ↦ T.u ∅ y - S.u ∅ y with hDdef
  have hDan : ∀ z ∈ univ.pi W₀, AnalyticAt ℂ D z := by
    refine fun z hz ↦ analyticAt_of_dbarPartial_eq_zero' hW₀
      (fun y hy ↦ ((T.smooth y (hW₀T y hy)).differentiableAt ∅).sub
        ((S.smooth y (hW₀S y hy)).differentiableAt ∅)) (fun y hy j ↦ ?_) hz
    have h1 := T.eq {j} y (hW₀T y hy)
    have h2 := S.eq {j} y (hW₀S y hy)
    rw [dbarForm_singleton] at h1 h2
    have h3 : koszulSign j {j} * (dbarPartial j (T.u ∅) y - dbarPartial j (S.u ∅) y) = 0 := by
      rw [mul_sub, h1, h2, sub_self]
    rw [dbarPartial_sub ((T.smooth y (hW₀T y hy)).differentiableAt ∅)
      ((S.smooth y (hW₀S y hy)).differentiableAt ∅)]
    exact (mul_eq_zero.mp h3).resolve_left (koszulSign_ne_zero _ _)
  obtain ⟨g, hg, hgD⟩ := hR ν D (fun z hz ↦ hDan z (hKW₀ z hz)) ((1 / 2) ^ ν) (by positivity)
  have hgT : ∀ z ∈ univ.pi T.W, AnalyticAt ℂ g z := fun z hz ↦
    hg z fun i _ ↦ T.subset i (hz i (mem_univ i))
  refine ⟨⟨T.W, T.isOpen, T.K_subset, T.subset, fun I y ↦ T.u I y - zeroForm g I y,
    fun z hz I ↦ (T.smooth z hz I).sub (isSmoothFormAt_zeroForm (hgT z hz) I),
    fun I hI ↦ ?_, fun J z hz ↦ ?_⟩, fun z hz ↦ ?_, fun z hz ↦ ?_⟩
  · have hI' : I ≠ ∅ := fun h ↦ hI (by rw [h]; rfl)
    funext y
    simp [T.deg I hI, zeroForm, hI']
  · rw [dbarForm_sub ((T.smooth z hz).differentiableAt)
      (isSmoothFormAt_zeroForm (hgT z hz)).differentiableAt, T.eq J z hz,
      dbarForm_zeroForm (hgT z hz), sub_zero]
  · have : (fun y ↦ T.u ∅ y - zeroForm g ∅ y - S.u ∅ y) = fun y ↦ D y - g y := by
      funext y
      simp [hDdef, zeroForm]
      ring
    simp only
    rw [this]
    exact (hDan z (hKW₀ z hz)).sub (hg z fun i _ ↦
      E.subset _ i (hz i (mem_univ i)))
  · have : T.u ∅ z - zeroForm g ∅ z - S.u ∅ z = D z - g z := by
      simp [hDdef, zeroForm]
      ring
    simp only
    rw [this]
    exact hgD z hz

/-- **`∂̄` on product domains in degree zero** (Hörmander, proof of 2.3.3 for `q = 0`): on `∏ Ωᵢ`
with an exhaustion by compact products having the Runge property, every smooth `∂̄`-closed
`(0, 1)`-form is `∂̄` of a smooth function (coefficient form). -/
theorem exists_dbarForm_eq_global_zero (hΩ : ∀ i, IsOpen (Ω i)) (E : ProductExhaustion Ω)
    (hR : E.IsRunge) (hGs : ∀ z ∈ univ.pi Ω, IsSmoothFormAt G z)
    (hdeg : ∀ J, J.card ≠ 0 + 1 → ∀ z ∈ univ.pi Ω, G J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi Ω, dbarForm G J z = 0) :
    ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ univ.pi Ω, IsSmoothFormAt u z) ∧
      (∀ I, I.card ≠ 0 → ∀ z ∈ univ.pi Ω, u I z = 0) ∧
      ∀ J, ∀ z ∈ univ.pi Ω, dbarForm u J z = G J z := by
  classical
  have step := LocalSol.exists_runge hΩ E hR hGs hdeg hcl
  have sol0 : LocalSol Ω (E.K (0 + 1)) 0 G :=
    (LocalSol.nonempty hΩ (E.isCompact _) (E.subset _) hGs hdeg hcl).some
  let seq : (ν : ℕ) → LocalSol Ω (E.K (ν + 1)) 0 G := fun ν ↦
    Nat.rec (motive := fun ν ↦ LocalSol Ω (E.K (ν + 1)) 0 G) sol0
      (fun ν S ↦ (step ν S).choose) ν
  have hseq : ∀ ν, seq (ν + 1) = (step ν (seq ν)).choose := fun ν ↦ rfl
  set d : ℕ → (σ → ℂ) → ℂ := fun ν y ↦ (seq (ν + 1)).u ∅ y - (seq ν).u ∅ y with hddef
  have hdan : ∀ ν, ∀ z ∈ univ.pi (E.K (ν + 1)), AnalyticAt ℂ (d ν) z := fun ν z hz ↦ by
    have := (step ν (seq ν)).choose_spec.1 z hz
    rw [← hseq] at this
    exact this
  have hdbd : ∀ ν, ∀ z ∈ univ.pi (E.K ν), ‖d ν z‖ < (1 / 2) ^ ν := fun ν z hz ↦ by
    have := (step ν (seq ν)).choose_spec.2 z hz
    rw [← hseq] at this
    exact this
  have hint : ∀ ν, ∀ y, (∀ i, y i ∈ interior (E.K ν i)) → y ∈ univ.pi (E.K ν) :=
    fun ν y hy i _ ↦ interior_subset (hy i)
  have hmono : ∀ {m k}, m ≤ k → ∀ y ∈ univ.pi (E.K m), y ∈ univ.pi (E.K k) :=
    fun hmk y hy i _ ↦ E.mono hmk i (hy i (mem_univ i))
  -- summability
  have hsum : ∀ y ∈ univ.pi Ω, Summable fun ν ↦ d ν y := by
    intro y hy
    obtain ⟨m, hm⟩ := E.exhaust y hy
    refine Summable.of_norm_bounded_eventually (summable_geometric_of_lt_one (by norm_num)
      (by norm_num : (1 / 2 : ℝ) < 1)) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop m] with ν hν
    exact (hdbd ν y (hmono hν y (hint m y hm))).le
  -- the global solution
  set U : (σ → ℂ) → ℂ := fun y ↦ (seq 0).u ∅ y + ∑' ν, d ν y with hUdef
  let u : Finset σ → (σ → ℂ) → ℂ := zeroForm U
  -- near a point of `int Kᵐ`, `U` is `(seq m).u ∅` plus an analytic function
  have hloc : ∀ z ∈ univ.pi Ω, ∃ m, z ∈ univ.pi (E.K (m + 1)) ∧
      ∃ T : (σ → ℂ) → ℂ, AnalyticAt ℂ T z ∧ U =ᶠ[𝓝 z] fun y ↦ (seq m).u ∅ y + T y := by
    intro z hz
    obtain ⟨m, hm⟩ := E.exhaust z hz
    have hO : IsOpen {y : σ → ℂ | ∀ i, y i ∈ interior (E.K m i)} := by
      have : {y : σ → ℂ | ∀ i, y i ∈ interior (E.K m i)} =
          univ.pi fun i ↦ interior (E.K m i) := by
        ext y
        simp
      rw [this]
      exact isOpen_univ_pi fun i ↦ isOpen_interior
    refine ⟨m, hmono (Nat.le_succ m) z (hint m z hm), fun y ↦ ∑' k, d (k + m) y, ?_, ?_⟩
    · refine analyticAt_tsum_of_summable_norm hO (fun k y hy ↦ ?_)
        ((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 2 : ℝ) < 1)).comp_injective
          (add_left_injective m)) (fun k y hy ↦ ?_) hm
      · exact (hdan (k + m) y (hmono (by omega) y
          (hint m y hy))).differentiableAt.differentiableWithinAt
      · exact (hdbd (k + m) y (hmono (by omega) y (hint m y hy))).le
    · filter_upwards [hO.mem_nhds hm] with y hy
      have hyΩ : y ∈ univ.pi Ω := fun i _ ↦ E.subset m i (interior_subset (hy i))
      rw [hUdef]
      simp only
      rw [← (hsum y hyΩ).sum_add_tsum_nat_add m, ← add_assoc]
      congr 1
      have htel := Finset.sum_range_sub (fun ν ↦ (seq ν).u ∅ y) m
      simp only [hddef] at htel ⊢
      rw [htel]
      ring
  have hzW : ∀ m, ∀ z ∈ univ.pi (E.K (m + 1)), z ∈ univ.pi (seq m).W := fun m z hz i _ ↦
    (seq m).K_subset i (hz i (mem_univ i))
  -- the form `u` near `z`
  have hform : ∀ z ∈ univ.pi Ω, ∃ m, z ∈ univ.pi (E.K (m + 1)) ∧ ∃ T : (σ → ℂ) → ℂ,
      AnalyticAt ℂ T z ∧ ∀ I, u I =ᶠ[𝓝 z] fun y ↦ (seq m).u I y + zeroForm T I y := by
    intro z hz
    obtain ⟨m, hmK, T, hT, hev⟩ := hloc z hz
    refine ⟨m, hmK, T, hT, fun I ↦ ?_⟩
    by_cases hI : I = ∅
    · subst hI
      filter_upwards [hev] with y hy
      simp [u, zeroForm, hy]
    · have h0 : (seq m).u I = 0 := (seq m).deg I fun h ↦ hI (Finset.card_eq_zero.mp h)
      refine Eventually.of_forall fun y ↦ ?_
      simp [u, zeroForm, hI, h0]
  refine ⟨u, fun z hz I ↦ ?_, fun I hI z _ ↦ ?_, fun J z hz ↦ ?_⟩
  · obtain ⟨m, hmK, T, hT, hev⟩ := hform z hz
    exact (((seq m).smooth z (hzW m z hmK) I).add
      (isSmoothFormAt_zeroForm hT I)).congr_of_eventuallyEq (hev I)
  · have hI' : I ≠ ∅ := fun h ↦ hI (by rw [h]; rfl)
    simp [u, zeroForm, hI']
  · obtain ⟨m, hmK, T, hT, hev⟩ := hform z hz
    rw [dbarForm_congr hev, dbarForm_add ((seq m).smooth z (hzW m z hmK)).differentiableAt
      (isSmoothFormAt_zeroForm hT).differentiableAt, (seq m).eq J z (hzW m z hmK),
      dbarForm_zeroForm hT, add_zero]

/-- **`∂̄`-exactness in degree zero on product domains with the Runge property.** -/
theorem dbarExactOn_pi_zero (hΩ : ∀ i, IsOpen (Ω i)) (E : ProductExhaustion Ω)
    (hR : E.IsRunge) : DbarExactOn (univ.pi Ω) 0 :=
  dbarExactOn_of_exists (isOpen_univ_pi hΩ) 0 fun _ hGs hdeg hcl ↦
    exists_dbarForm_eq_global_zero hΩ E hR hGs hdeg hcl

variable [CategoryTheory.HasExt.{0}
  (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of (σ → ℂ))) AddCommGrpCat.{0})]

omit [LinearOrder σ] in
/-- **Vanishing of `Hⁿ(Ω, 𝒪)` for `n ≥ 2` on product domains**: for a product `Ω = ∏ Ωᵢ` of open
subsets of `ℂ` with an exhaustion by compact products, `H^{n+2}(Ω, 𝒪) = 0`. (`H¹` needs the Runge
property of the exhaustion: `H'_holomorphicAbSheaf_subsingleton_of_isRunge`.) -/
theorem H'_holomorphicAbSheaf_two_le (hΩ : ∀ i, IsOpen (Ω i)) (E : ProductExhaustion Ω)
    (n : ℕ) :
    Subsingleton ((holomorphicAbSheaf σ).H' (n + 2)
      (⟨univ.pi Ω, isOpen_univ_pi hΩ⟩ : TopologicalSpace.Opens (TopCat.of (σ → ℂ)))) := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact TopCat.Sheaf.subsingleton_H'_succ_succ_of_shortExact holomorphicSeq_shortExact _ n
    (H'_closedFormSheaf_subsingleton_of_le _ n 1 fun q' hq' ↦ by
      obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le hq'
      rw [add_comm]
      exact dbarExactOn_pi_succ hΩ E q)
    (H'_smoothSheaf_subsingleton (n + 1) _)

omit [LinearOrder σ] in
/-- **Theorem B for `𝒪` on product domains, from the Runge property**: for a product `Ω = ∏ Ωᵢ`
of open subsets of `ℂ` with an exhaustion by compact products which has the Runge property,
`Hⁿ(Ω, 𝒪) = 0` for all `n > 0`. -/
theorem H'_holomorphicAbSheaf_subsingleton_of_isRunge (hΩ : ∀ i, IsOpen (Ω i))
    (E : ProductExhaustion Ω) (hR : E.IsRunge) (n : ℕ) :
    Subsingleton ((holomorphicAbSheaf σ).H' (n + 1)
      (⟨univ.pi Ω, isOpen_univ_pi hΩ⟩ : TopologicalSpace.Opens (TopCat.of (σ → ℂ)))) := by
  let : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  exact H'_holomorphicAbSheaf_subsingleton_of_dbarExact _ (fun q ↦ by
    cases q with
    | zero => exact dbarExactOn_pi_zero hΩ E hR
    | succ q => exact dbarExactOn_pi_succ hΩ E q) n

end AnalyticGeometry
