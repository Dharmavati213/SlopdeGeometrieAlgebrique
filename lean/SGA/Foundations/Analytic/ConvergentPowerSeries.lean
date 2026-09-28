/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Finsupp.Antidiagonal

/-!
# Convergent power series

Let `𝕜` be a normed field. For a polyradius `ρ : σ → ℝ≥0` the *weighted norm* of a power series
`f = ∑ aₐ Xᵅ` is `‖f‖_ρ = ∑ |aₐ| ρᵅ ∈ [0, ∞]`. It is subadditive and submultiplicative, so the
series with finite weighted norm for some polyradius with positive entries form a subalgebra
of `MvPowerSeries σ 𝕜`: the algebra `𝕜{X}` of *convergent power series* (for `σ = Fin n` and
`𝕜 = ℂ`, the ring `ℂ{z₁, …, zₙ}` of germs of holomorphic functions at the origin,
[Grauert–Remmert, *Analytische Stellenalgebren*, I §1]).

## Main definitions

* `MvPowerSeries.monomialEval z α = ∏ zᵢ ^ αᵢ`.
* `MvPowerSeries.weightedNorm ρ f = ∑ ‖aₐ‖ ρᵅ` (in `ℝ≥0∞`).
* `MvPowerSeries.convergent σ 𝕜`: the subalgebra of convergent power series.
-/

open scoped NNReal ENNReal
open Finset

noncomputable section

namespace MvPowerSeries

variable {σ : Type*}

section MonomialEval

variable {M : Type*} [CommMonoid M]

/-- The value `∏ zᵢ ^ αᵢ` of the monomial `Xᵅ` at `z`. -/
def monomialEval (z : σ → M) (α : σ →₀ ℕ) : M :=
  α.prod fun i k ↦ z i ^ k

@[simp] lemma monomialEval_zero (z : σ → M) : monomialEval z 0 = 1 := by
  simp [monomialEval]

lemma monomialEval_add (z : σ → M) (α β : σ →₀ ℕ) :
    monomialEval z (α + β) = monomialEval z α * monomialEval z β := by
  classical
  exact Finsupp.prod_add_index' (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)

@[simp] lemma monomialEval_single (z : σ → M) (i : σ) (k : ℕ) :
    monomialEval z (Finsupp.single i k) = z i ^ k := by
  simp [monomialEval]

lemma monomialEval_eq_prod [Fintype σ] (z : σ → M) (α : σ →₀ ℕ) :
    monomialEval z α = ∏ i, z i ^ α i :=
  Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _

lemma map_monomialEval {N : Type*} [CommMonoid N] {F : Type*} [FunLike F M N]
    [MonoidHomClass F M N] (φ : F) (z : σ → M) (α : σ →₀ ℕ) :
    φ (monomialEval z α) = monomialEval (φ ∘ z) α := by
  simp [monomialEval, Finsupp.prod, map_prod, map_pow]

lemma monomialEval_mul (z w : σ → M) (α : σ →₀ ℕ) :
    monomialEval (z * w) α = monomialEval z α * monomialEval w α := by
  simp [monomialEval, Finsupp.prod, mul_pow, prod_mul_distrib]

lemma monomialEval_const_mul {R : Type*} [CommSemiring R] (c : R) (z : σ → R) (α : σ →₀ ℕ) :
    monomialEval (fun i ↦ c * z i) α = c ^ α.degree * monomialEval z α := by
  simp only [monomialEval, Finsupp.prod, mul_pow, prod_mul_distrib, Finsupp.degree_apply,
    prod_pow_eq_pow_sum]

@[simp] lemma monomialEval_one (α : σ →₀ ℕ) : monomialEval (fun _ ↦ (1 : M)) α = 1 := by
  simp [monomialEval]

lemma monomialEval_const {R : Type*} [CommSemiring R] (c : R) (α : σ →₀ ℕ) :
    monomialEval (fun _ ↦ c) α = c ^ α.degree := by
  simpa using monomialEval_const_mul c (fun _ ↦ 1) α

lemma monomialEval_le_monomialEval {z w : σ → ℝ≥0} (h : z ≤ w) (α : σ →₀ ℕ) :
    monomialEval z α ≤ monomialEval w α :=
  Finset.prod_le_prod' fun i _ ↦ pow_le_pow_left₀ (by positivity) (h i) _

lemma monomialEval_pos {z : σ → ℝ≥0} (h : ∀ i, 0 < z i) (α : σ →₀ ℕ) :
    0 < monomialEval z α :=
  Finset.prod_pos fun i _ ↦ pow_pos (h i) _

lemma norm_monomialEval {𝕜 : Type*} [NormedField 𝕜] (z : σ → 𝕜) (α : σ →₀ ℕ) :
    ‖monomialEval z α‖₊ = monomialEval (fun i ↦ ‖z i‖₊) α :=
  map_monomialEval (nnnormHom : 𝕜 →*₀ ℝ≥0) z α

end MonomialEval

section WeightedNorm

/-- Cauchy product formula in `ℝ≥0∞`. -/
lemma _root_.ENNReal.tsum_mul_tsum_eq_tsum_sum_antidiagonal {A : Type*} [AddCommMonoid A]
    [HasAntidiagonal A] (f g : A → ℝ≥0∞) :
    (∑' a, f a) * (∑' b, g b) = ∑' n, ∑ p ∈ antidiagonal n, f p.1 * g p.2 := by
  simp_rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
  rw [← ENNReal.tsum_prod (f := fun a b ↦ f a * g b),
    ← HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (fun p : A × A ↦ f p.1 * g p.2),
    ENNReal.tsum_sigma']
  refine tsum_congr fun n ↦ ?_
  exact Finset.tsum_subtype (antidiagonal n) (fun p : A × A ↦ f p.1 * g p.2)

variable {𝕜 : Type*} [NormedField 𝕜]

/-- The weighted norm `‖f‖_ρ = ∑ ‖aₐ‖ ρᵅ ∈ [0, ∞]` of a power series `f = ∑ aₐ Xᵅ` for a
polyradius `ρ`. -/
def weightedNorm (ρ : σ → ℝ≥0) (f : MvPowerSeries σ 𝕜) : ℝ≥0∞ :=
  ∑' α, ((‖coeff α f‖₊ * monomialEval ρ α : ℝ≥0) : ℝ≥0∞)

variable (ρ : σ → ℝ≥0) (f g : MvPowerSeries σ 𝕜)

lemma coe_nnnorm_coeff_mul_le_weightedNorm (α : σ →₀ ℕ) :
    ((‖coeff α f‖₊ * monomialEval ρ α : ℝ≥0) : ℝ≥0∞) ≤ weightedNorm ρ f :=
  ENNReal.le_tsum α

@[simp] lemma weightedNorm_zero : weightedNorm ρ (0 : MvPowerSeries σ 𝕜) = 0 := by
  simp [weightedNorm]

lemma weightedNorm_add_le : weightedNorm ρ (f + g) ≤ weightedNorm ρ f + weightedNorm ρ g := by
  rw [weightedNorm, weightedNorm, weightedNorm, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun α ↦ ?_
  rw [← ENNReal.coe_add, ENNReal.coe_le_coe, ← add_mul, map_add]
  gcongr
  exact nnnorm_add_le _ _

@[simp] lemma weightedNorm_neg : weightedNorm ρ (-f) = weightedNorm ρ f := by
  simp [weightedNorm]

lemma weightedNorm_sub_le : weightedNorm ρ (f - g) ≤ weightedNorm ρ f + weightedNorm ρ g := by
  simpa [sub_eq_add_neg] using weightedNorm_add_le ρ f (-g)

lemma weightedNorm_smul (c : 𝕜) : weightedNorm ρ (c • f) = ‖c‖₊ * weightedNorm ρ f := by
  rw [weightedNorm, weightedNorm, ← ENNReal.tsum_mul_left]
  congr 1
  funext α
  rw [coeff_smul, nnnorm_mul, mul_assoc, ENNReal.coe_mul]

lemma weightedNorm_mono {ρ ρ' : σ → ℝ≥0} (h : ρ ≤ ρ') (f : MvPowerSeries σ 𝕜) :
    weightedNorm ρ f ≤ weightedNorm ρ' f :=
  ENNReal.tsum_le_tsum fun α ↦ ENNReal.coe_le_coe.mpr (by
    gcongr
    exact monomialEval_le_monomialEval h α)

lemma weightedNorm_mul_le :
    weightedNorm ρ (f * g) ≤ weightedNorm ρ f * weightedNorm ρ g := by
  classical
  rw [weightedNorm, weightedNorm, weightedNorm, ENNReal.tsum_mul_tsum_eq_tsum_sum_antidiagonal]
  refine ENNReal.tsum_le_tsum fun γ ↦ ?_
  rw [coeff_mul]
  calc ((‖∑ p ∈ antidiagonal γ, coeff p.1 f * coeff p.2 g‖₊ * monomialEval ρ γ : ℝ≥0) : ℝ≥0∞)
      ≤ ((∑ p ∈ antidiagonal γ, ‖coeff p.1 f‖₊ * ‖coeff p.2 g‖₊) * monomialEval ρ γ : ℝ≥0) := by
        rw [ENNReal.coe_le_coe]
        gcongr
        refine (nnnorm_sum_le _ _).trans (le_of_eq ?_)
        simp [nnnorm_mul]
    _ = ∑ p ∈ antidiagonal γ, ((‖coeff p.1 f‖₊ * monomialEval ρ p.1 : ℝ≥0) : ℝ≥0∞) *
          ((‖coeff p.2 g‖₊ * monomialEval ρ p.2 : ℝ≥0) : ℝ≥0∞) := by
        rw [sum_mul, ENNReal.ofNNReal_finsetSum]
        refine sum_congr rfl fun p hp ↦ ?_
        rw [← ENNReal.coe_mul, ENNReal.coe_inj, ← mem_antidiagonal.mp hp, monomialEval_add]
        ring

@[simp] lemma weightedNorm_C (c : 𝕜) :
    weightedNorm ρ (C (σ := σ) c) = ‖c‖₊ := by
  classical
  rw [weightedNorm, tsum_eq_single 0]
  · simp
  · intro α hα
    simp [coeff_C, hα]

@[simp] lemma weightedNorm_one :
    weightedNorm ρ (1 : MvPowerSeries σ 𝕜) = 1 := by
  simpa using weightedNorm_C (𝕜 := 𝕜) ρ 1

lemma weightedNorm_monomial (α : σ →₀ ℕ) (c : 𝕜) :
    weightedNorm ρ (monomial α c) = ‖c‖₊ * monomialEval ρ α := by
  classical
  rw [weightedNorm, tsum_eq_single α]
  · simp
  · intro β hβ
    simp [coeff_monomial, hβ]

@[simp] lemma weightedNorm_X (i : σ) :
    weightedNorm ρ (X i : MvPowerSeries σ 𝕜) = ρ i := by
  change weightedNorm ρ (monomial (Finsupp.single i 1) (1 : 𝕜)) = ρ i
  rw [weightedNorm_monomial]
  simp

lemma weightedNorm_pow_le (n : ℕ) :
    weightedNorm ρ (f ^ n) ≤ weightedNorm ρ f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (weightedNorm_mul_le ρ _ _).trans (by gcongr)

lemma weightedNorm_eq_zero_iff {ρ : σ → ℝ≥0} (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ 𝕜} :
    weightedNorm ρ f = 0 ↔ f = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ weightedNorm_zero ρ⟩
  ext α
  have := (coe_nnnorm_coeff_mul_le_weightedNorm ρ f α).trans h.le
  rw [nonpos_iff_eq_zero, ENNReal.coe_eq_zero, mul_eq_zero] at this
  rcases this with h | h
  · simpa using h
  · exact absurd h (monomialEval_pos hρ α).ne'

lemma nnnorm_coeff_le {ρ : σ → ℝ≥0} (hρ : ∀ i, 0 < ρ i) {f : MvPowerSeries σ 𝕜}
    (hf : weightedNorm ρ f ≠ ⊤) (α : σ →₀ ℕ) :
    ‖coeff α f‖₊ ≤ (weightedNorm ρ f).toNNReal / monomialEval ρ α := by
  rw [le_div_iff₀ (monomialEval_pos hρ α), ← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hf]
  exact coe_nnnorm_coeff_mul_le_weightedNorm ρ f α

/-- Summability of the weighted coefficients, when the weighted norm is finite. -/
lemma summable_of_weightedNorm_ne_top {f : MvPowerSeries σ 𝕜} (hf : weightedNorm ρ f ≠ ⊤) :
    Summable fun α ↦ ‖coeff α f‖₊ * monomialEval ρ α :=
  ENNReal.tsum_coe_ne_top_iff_summable.mp hf

lemma weightedNorm_eq_tsum {f : MvPowerSeries σ 𝕜} (hf : weightedNorm ρ f ≠ ⊤) :
    weightedNorm ρ f = ((∑' α, ‖coeff α f‖₊ * monomialEval ρ α : ℝ≥0) : ℝ≥0∞) :=
  (ENNReal.coe_tsum (summable_of_weightedNorm_ne_top ρ hf)).symm

end WeightedNorm

/-! ### Convergent power series -/

section Convergent

variable (σ) (𝕜 : Type*) [NormedField 𝕜]

/-- The convergent power series: those with finite weighted norm for some polyradius with
positive entries. -/
def convergent : Subalgebra 𝕜 (MvPowerSeries σ 𝕜) where
  carrier := {f | ∃ ρ : σ → ℝ≥0, (∀ i, 0 < ρ i) ∧ weightedNorm ρ f ≠ ⊤}
  mul_mem' := by
    rintro f g ⟨ρ, hρ, hf⟩ ⟨ρ', hρ', hg⟩
    refine ⟨ρ ⊓ ρ', fun i ↦ lt_min (hρ i) (hρ' i), ?_⟩
    refine ne_top_of_le_ne_top ?_ (weightedNorm_mul_le _ f g)
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top hf (weightedNorm_mono inf_le_left f))
      (ne_top_of_le_ne_top hg (weightedNorm_mono inf_le_right g))
  add_mem' := by
    rintro f g ⟨ρ, hρ, hf⟩ ⟨ρ', hρ', hg⟩
    refine ⟨ρ ⊓ ρ', fun i ↦ lt_min (hρ i) (hρ' i), ?_⟩
    refine ne_top_of_le_ne_top ?_ (weightedNorm_add_le _ f g)
    exact ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top hf (weightedNorm_mono inf_le_left f),
      ne_top_of_le_ne_top hg (weightedNorm_mono inf_le_right g)⟩
  algebraMap_mem' c := by
    classical
    exact ⟨fun _ ↦ 1, fun _ ↦ one_pos, by
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
        weightedNorm_C]
      exact ENNReal.coe_ne_top⟩

variable {σ 𝕜}

lemma mem_convergent {f : MvPowerSeries σ 𝕜} :
    f ∈ convergent σ 𝕜 ↔ ∃ ρ : σ → ℝ≥0, (∀ i, 0 < ρ i) ∧ weightedNorm ρ f ≠ ⊤ := Iff.rfl

lemma X_mem_convergent (i : σ) : X i ∈ convergent σ 𝕜 := by
  classical
  exact ⟨fun _ ↦ 1, fun _ ↦ one_pos, by simp⟩

lemma monomial_mem_convergent (α : σ →₀ ℕ) (c : 𝕜) : monomial α c ∈ convergent σ 𝕜 := by
  classical
  exact ⟨fun _ ↦ 1, fun _ ↦ one_pos, by
    rw [weightedNorm_monomial, monomialEval_one]; exact ENNReal.coe_ne_top⟩

/-- A convergent power series has finite weighted norm for all small constant polyradii. -/
lemma exists_weightedNorm_const_ne_top [Finite σ] {f : MvPowerSeries σ 𝕜}
    (hf : f ∈ convergent σ 𝕜) : ∃ r : ℝ≥0, 0 < r ∧ weightedNorm (fun _ ↦ r) f ≠ ⊤ := by
  obtain ⟨ρ, hρ, hf⟩ := hf
  cases isEmpty_or_nonempty σ
  · exact ⟨1, one_pos, by
      rw [show (fun _ : σ ↦ (1 : ℝ≥0)) = ρ from funext fun i ↦ isEmptyElim i]; exact hf⟩
  · have := Fintype.ofFinite σ
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min ρ
    exact ⟨ρ i₀, hρ i₀, ne_top_of_le_ne_top hf (weightedNorm_mono (fun i ↦ hi₀ i) f)⟩

end Convergent

end MvPowerSeries
