/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ConvergentPowerSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.RingTheory.MvPowerSeries.Rename

/-!
# The Weierstrass division theorem for convergent power series

We consider power series in the variables `Option τ`: the variable `none` plays the role of the
distinguished variable `y`, the variables `some i` are the parameters `z = (zᵢ)`. A power series
`g` is *regular of order `b` in `y`* if `g(0, y) = c y^b + (higher order terms)` with `c ≠ 0`.

**Weierstrass division theorem** ([Grauert–Remmert, *Coherent analytic sheaves*, §2.1];
[Grauert–Remmert, *Analytische Stellenalgebren*, I §3]): if `g ∈ 𝕜{z, y}` is regular of order
`b` in `y`, every `f ∈ 𝕜{z, y}` can be written uniquely as `f = g q + r` with `q, r ∈ 𝕜{z, y}` and
`r` a polynomial in `y` of degree `< b` (`exists_weierstrassDiv`, `weierstrassDiv_unique`).

The proof is the one of Grauert–Remmert via the weighted norms `‖·‖_ρ`: division by `y^b` is
trivial (`f = y^b · highQuot b f + lowPart b f`), and if `‖y^b - g‖_ρ ≤ ε ρ_y^b` with `ε < 1`
then division by `g` is obtained by a Neumann series. Any `g` regular of order `b` can be brought
into this situation after multiplication by a constant, by shrinking the polyradius.
-/

open scoped NNReal ENNReal
open Finset

noncomputable section

namespace MvPowerSeries

variable {τ : Type*}

/-! ### Division by `y^b` -/

section Formal

variable {R : Type*} [CommRing R] (b : ℕ)

/-- The part of degree `< b` in the variable `none` of a power series. -/
def lowPart : MvPowerSeries (Option τ) R →ₗ[R] MvPowerSeries (Option τ) R where
  toFun f α := if α none < b then coeff α f else 0
  map_add' f g := by
    ext α
    change (if α none < b then coeff α (f + g) else 0) =
      (if α none < b then coeff α f else 0) + (if α none < b then coeff α g else 0)
    split_ifs <;> simp
  map_smul' c f := by
    ext α
    change (if α none < b then coeff α (c • f) else 0) = c * (if α none < b then coeff α f else 0)
    split_ifs <;> simp

/-- The quotient of the division of a power series by `y^b` (`y` the variable `none`). -/
def highQuot : MvPowerSeries (Option τ) R →ₗ[R] MvPowerSeries (Option τ) R where
  toFun f α := coeff (α + Finsupp.single none b) f
  map_add' f g := by
    ext α
    exact map_add (coeff (α + Finsupp.single none b)) f g
  map_smul' c f := by
    ext α
    exact (coeff (α + Finsupp.single none b)).map_smul c f

variable {b}

lemma coeff_lowPart (f : MvPowerSeries (Option τ) R) (α : Option τ →₀ ℕ) :
    coeff α (lowPart b f) = if α none < b then coeff α f else 0 := rfl

lemma coeff_highQuot (f : MvPowerSeries (Option τ) R) (α : Option τ →₀ ℕ) :
    coeff α (highQuot b f) = coeff (α + Finsupp.single none b) f := rfl

lemma coeff_X_none_pow_mul (f : MvPowerSeries (Option τ) R) (α : Option τ →₀ ℕ) :
    coeff α (X none ^ b * f) =
      if b ≤ α none then coeff (α - Finsupp.single none b) f else 0 := by
  rw [X_pow_eq, coeff_monomial_mul, one_mul]
  congr 1
  exact propext Finsupp.single_le_iff

/-- A power series `r` is *low* (of degree `< b` in `y`) if its coefficients of `y`-degree
`≥ b` vanish. -/
def IsLow (b : ℕ) (r : MvPowerSeries (Option τ) R) : Prop :=
  ∀ α : Option τ →₀ ℕ, b ≤ α none → coeff α r = 0

/-- `g` is *regular of order `b` in `y`*: `g(0, y) = c y^b + O(y^(b+1))` with `c ≠ 0`. -/
def IsRegularOfOrder (b : ℕ) (g : MvPowerSeries (Option τ) R) : Prop :=
  (∀ j < b, coeff (Finsupp.single none j) g = 0) ∧ coeff (Finsupp.single none b) g ≠ 0

lemma isLow_lowPart (f : MvPowerSeries (Option τ) R) : IsLow b (lowPart b f) := by
  intro α hα
  rw [coeff_lowPart, ite_eq_right (not_lt.mpr hα)]

lemma IsLow.lowPart_eq {r : MvPowerSeries (Option τ) R} (hr : IsLow b r) : lowPart b r = r := by
  ext α
  rw [coeff_lowPart]
  split_ifs with h
  · rfl
  · exact (hr α (not_lt.mp h)).symm

lemma IsLow.highQuot_eq {r : MvPowerSeries (Option τ) R} (hr : IsLow b r) :
    highQuot b r = 0 := by
  ext α
  rw [coeff_highQuot, map_zero]
  exact hr _ (by simp)

lemma IsLow.add {r s : MvPowerSeries (Option τ) R} (hr : IsLow b r) (hs : IsLow b s) :
    IsLow b (r + s) := fun α h ↦ by rw [map_add, hr α h, hs α h, add_zero]

lemma IsLow.smul {r : MvPowerSeries (Option τ) R} (hr : IsLow b r) (c : R) :
    IsLow b (c • r) := fun α h ↦ by rw [coeff_smul, hr α h, mul_zero]

lemma IsLow.neg {r : MvPowerSeries (Option τ) R} (hr : IsLow b r) : IsLow b (-r) :=
  fun α h ↦ by rw [map_neg, hr α h, neg_zero]

lemma isLow_zero : IsLow b (0 : MvPowerSeries (Option τ) R) := fun _ _ ↦ map_zero _

/-- Division by `y^b`: `f = y^b · highQuot b f + lowPart b f`. -/
lemma X_none_pow_mul_highQuot_add_lowPart (f : MvPowerSeries (Option τ) R) :
    X none ^ b * highQuot b f + lowPart b f = f := by
  ext α
  rw [map_add, coeff_X_none_pow_mul, coeff_lowPart]
  by_cases h : b ≤ α none
  · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h), add_zero, coeff_highQuot,
      tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h)]
  · rw [ite_eq_right h, ite_eq_left (not_le.mp h), zero_add]

lemma highQuot_X_none_pow_mul (f : MvPowerSeries (Option τ) R) :
    highQuot b (X none ^ b * f) = f := by
  ext α
  rw [coeff_highQuot, coeff_X_none_pow_mul, ite_eq_left (by simp), add_tsub_cancel_right]

/-- The restriction `h ↦ h(0, y)` of a power series to the `y`-axis. -/
def restrictY : MvPowerSeries (Option τ) R →ₐ[R] MvPowerSeries Unit R :=
  killCompl ⟨fun _ ↦ none, fun _ _ _ ↦ rfl⟩

lemma coeff_restrictY (h : MvPowerSeries (Option τ) R) (j : ℕ) :
    coeff (Finsupp.single () j) (restrictY h) = coeff (Finsupp.single none j) h := by
  rw [restrictY, coeff_killCompl, Finsupp.embDomain_single]
  rfl

lemma eq_single_unit (x : Unit →₀ ℕ) : x = Finsupp.single () (x ()) := by
  ext
  simp

lemma restrictY_eq_zero_iff {h : MvPowerSeries (Option τ) R} :
    restrictY h = 0 ↔ ∀ j, coeff (Finsupp.single none j) h = 0 := by
  constructor
  · intro H j
    rw [← coeff_restrictY, H, map_zero]
  · intro H
    ext x
    rw [eq_single_unit x, coeff_restrictY, H, map_zero]

lemma restrictY_X_none : restrictY (X none : MvPowerSeries (Option τ) R) = X () :=
  killCompl_X (e := ⟨fun _ ↦ none, fun _ _ _ ↦ rfl⟩) ()

lemma constantCoeff_restrictY (h : MvPowerSeries (Option τ) R) :
    constantCoeff (restrictY h) = constantCoeff h := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← Finsupp.single_zero (),
    coeff_restrictY, Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply]

lemma restrictY_lowPart_of_isRegularOfOrder {g : MvPowerSeries (Option τ) R}
    (hg : ∀ j < b, coeff (Finsupp.single none j) g = 0) : restrictY (lowPart b g) = 0 := by
  rw [restrictY_eq_zero_iff]
  intro j
  rw [coeff_lowPart]
  split_ifs with h
  · simpa using hg j (by simpa using h)
  · rfl

end Formal

/-! ### Norm estimates -/

section Norm

variable {𝕜 : Type*} [NormedField 𝕜] {b : ℕ}

lemma weightedNorm_lowPart_le (ρ : Option τ → ℝ≥0) (f : MvPowerSeries (Option τ) 𝕜) :
    weightedNorm ρ (lowPart b f) ≤ weightedNorm ρ f := by
  refine ENNReal.tsum_le_tsum fun α ↦ ENNReal.coe_le_coe.mpr ?_
  rw [coeff_lowPart]
  split_ifs
  · rfl
  · simp

lemma monomialEval_add_single_none (ρ : Option τ → ℝ≥0) (α : Option τ →₀ ℕ) :
    monomialEval ρ (α + Finsupp.single none b) = monomialEval ρ α * ρ none ^ b := by
  rw [monomialEval_add, monomialEval_single]

lemma weightedNorm_highQuot_le (ρ : Option τ → ℝ≥0) (f : MvPowerSeries (Option τ) 𝕜) :
    (ρ none : ℝ≥0∞) ^ b * weightedNorm ρ (highQuot b f) ≤ weightedNorm ρ f := by
  rw [weightedNorm, ← ENNReal.tsum_mul_left]
  refine le_trans (le_of_eq (tsum_congr fun α ↦ ?_)) (ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun α : Option τ →₀ ℕ ↦ α + Finsupp.single none b) (add_left_injective _)
    fun β ↦ ((‖coeff β f‖₊ * monomialEval ρ β : ℝ≥0) : ℝ≥0∞))
  rw [coeff_highQuot, monomialEval_add_single_none, ← ENNReal.coe_pow, ← ENNReal.coe_mul]
  congr 1
  ring

lemma weightedNorm_highQuot_le' {ρ : Option τ → ℝ≥0} (hρ : 0 < ρ none)
    (f : MvPowerSeries (Option τ) 𝕜) :
    weightedNorm ρ (highQuot b f) ≤ weightedNorm ρ f / (ρ none : ℝ≥0∞) ^ b := by
  rw [ENNReal.le_div_iff_mul_le (by simp [hρ.ne']) (by simp), mul_comm]
  exact weightedNorm_highQuot_le ρ f

end Norm

/-! ### Division at a fixed polyradius -/

section FixedRadius

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {b : ℕ}
  {ρ : Option τ → ℝ≥0} {g : MvPowerSeries (Option τ) 𝕜} {ε : ℝ≥0}

/-- The operator `u ↦ (y^b - g) · highQuot b u` of the Neumann series. -/
def divOp (b : ℕ) (g : MvPowerSeries (Option τ) 𝕜) (u : MvPowerSeries (Option τ) 𝕜) :
    MvPowerSeries (Option τ) 𝕜 :=
  (X none ^ b - g) * highQuot b u

lemma weightedNorm_divOp_le
    (hg : weightedNorm ρ (X none ^ b - g) ≤ ε * (ρ none : ℝ≥0∞) ^ b)
    (u : MvPowerSeries (Option τ) 𝕜) :
    weightedNorm ρ (divOp b g u) ≤ ε * weightedNorm ρ u := by
  refine (weightedNorm_mul_le ρ _ _).trans ?_
  calc weightedNorm ρ (X none ^ b - g) * weightedNorm ρ (highQuot b u)
      ≤ ε * (ρ none : ℝ≥0∞) ^ b * weightedNorm ρ (highQuot b u) := by gcongr
    _ ≤ ε * weightedNorm ρ u := by
      rw [mul_assoc]
      gcongr
      exact weightedNorm_highQuot_le ρ u

lemma weightedNorm_divOp_iterate_le
    (hg : weightedNorm ρ (X none ^ b - g) ≤ ε * (ρ none : ℝ≥0∞) ^ b)
    (u : MvPowerSeries (Option τ) 𝕜) (k : ℕ) :
    weightedNorm ρ ((divOp b g)^[k] u) ≤ (ε : ℝ≥0∞) ^ k * weightedNorm ρ u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', pow_succ, mul_comm ((ε : ℝ≥0∞) ^ k), mul_assoc]
    exact (weightedNorm_divOp_le hg _).trans (by gcongr)

private lemma eq_zero_of_le_mul {x : ℝ≥0∞} (hx : x ≠ ⊤) (h : x ≤ ε * x) (hε : ε < 1) :
    x = 0 := by
  lift x to ℝ≥0 using hx
  rw [← ENNReal.coe_mul, ENNReal.coe_le_coe] at h
  rw [ENNReal.coe_eq_zero]
  by_contra hne
  exact (not_lt.mpr h) (mul_lt_of_lt_one_left (pos_iff_ne_zero.mpr hne) hε)

variable [CompleteSpace 𝕜] (hρ : ∀ i, 0 < ρ i) (hε : ε < 1)
  (hg : weightedNorm ρ (X none ^ b - g) ≤ ε * (ρ none : ℝ≥0∞) ^ b)
include hρ hε hg

omit [CompleteSpace 𝕜] in
/-- The coefficients of the iterates of `divOp` decay geometrically. -/
lemma summable_coeff_divOp_iterate {u : MvPowerSeries (Option τ) 𝕜}
    (hu : weightedNorm ρ u ≠ ⊤) (α : Option τ →₀ ℕ) :
    Summable fun k ↦ ‖coeff α ((divOp b g)^[k] u)‖₊ := by
  refine NNReal.summable_of_le (fun k ↦ ?_) ((NNReal.summable_geometric hε).mul_right
    ((weightedNorm ρ u).toNNReal / monomialEval ρ α))
  have hk := weightedNorm_divOp_iterate_le hg u k
  have hk' : weightedNorm ρ ((divOp b g)^[k] u) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.coe_ne_top hu) hk
  refine (nnnorm_coeff_le hρ hk' α).trans ?_
  rw [mul_div_assoc']
  gcongr
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hk', ENNReal.coe_mul, ENNReal.coe_toNNReal hu]
  simpa using hk

/-- The Neumann series `∑ₖ Tᵏ u` for the operator `T = divOp b g`, computed coefficientwise. -/
def neumannSeries (b : ℕ) (g u : MvPowerSeries (Option τ) 𝕜) : MvPowerSeries (Option τ) 𝕜 :=
  fun α ↦ ∑' k, coeff α ((divOp b g)^[k] u)

omit [CompleteSpace 𝕜] hρ hε hg in
lemma coeff_neumannSeries (u : MvPowerSeries (Option τ) 𝕜) (α : Option τ →₀ ℕ) :
    coeff α (neumannSeries b g u) = ∑' k, coeff α ((divOp b g)^[k] u) := rfl

omit [CompleteSpace 𝕜] in
lemma weightedNorm_neumannSeries_ne_top {u : MvPowerSeries (Option τ) 𝕜}
    (hu : weightedNorm ρ u ≠ ⊤) : weightedNorm ρ (neumannSeries b g u) ≠ ⊤ := by
  have key : weightedNorm ρ (neumannSeries b g u) ≤
      ∑' k, (ε : ℝ≥0∞) ^ k * weightedNorm ρ u := by
    calc weightedNorm ρ (neumannSeries b g u)
        ≤ ∑' α, ∑' k, ((‖coeff α ((divOp b g)^[k] u)‖₊ * monomialEval ρ α : ℝ≥0) : ℝ≥0∞) := by
          refine ENNReal.tsum_le_tsum fun α ↦ ?_
          have hs := summable_coeff_divOp_iterate hρ hε hg hu α
          rw [coeff_neumannSeries, ← ENNReal.coe_tsum (hs.mul_right _), ENNReal.coe_le_coe,
            NNReal.tsum_mul_right]
          gcongr
          exact nnnorm_tsum_le hs
      _ = ∑' k, weightedNorm ρ ((divOp b g)^[k] u) := ENNReal.tsum_comm
      _ ≤ ∑' k, (ε : ℝ≥0∞) ^ k * weightedNorm ρ u :=
          ENNReal.tsum_le_tsum fun k ↦ weightedNorm_divOp_iterate_le hg u k
  refine ne_top_of_le_ne_top ?_ key
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  refine ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr ?_) hu
  rw [ne_eq, tsub_eq_zero_iff_le, not_le]
  exact_mod_cast hε

/-- The Neumann series `w = ∑ₖ Tᵏ u` solves `w - T w = u`. -/
lemma neumannSeries_sub_divOp {u : MvPowerSeries (Option τ) 𝕜} (hu : weightedNorm ρ u ≠ ⊤) :
    neumannSeries b g u - divOp b g (neumannSeries b g u) = u := by
  classical
  have hs : ∀ β, Summable fun k ↦ coeff β ((divOp b g)^[k] u) := fun β ↦
    (summable_coeff_divOp_iterate hρ hε hg hu β).of_nnnorm
  ext α
  have hT : coeff α (divOp b g (neumannSeries b g u)) =
      ∑' k, coeff α (divOp b g ((divOp b g)^[k] u)) := by
    simp only [divOp, coeff_mul, coeff_highQuot, coeff_neumannSeries]
    rw [Summable.tsum_finsetSum (fun p _ ↦ (hs _).mul_left _)]
    exact sum_congr rfl fun p _ ↦ tsum_mul_left.symm
  rw [map_sub, hT, coeff_neumannSeries, (hs α).tsum_eq_zero_add]
  simp only [Function.iterate_succ_apply', Function.iterate_zero, id]
  ring

/-- **Weierstrass division at a fixed polyradius**: if `‖y^b - g‖_ρ ≤ ε ρ_y^b` with `ε < 1`,
every `f` with `‖f‖_ρ < ∞` is `g q + r` with `‖q‖_ρ, ‖r‖_ρ < ∞` and `r` of degree `< b` in
`y`. -/
theorem exists_weierstrassDiv_of_weightedNorm {f : MvPowerSeries (Option τ) 𝕜}
    (hf : weightedNorm ρ f ≠ ⊤) :
    ∃ q r, weightedNorm ρ q ≠ ⊤ ∧ weightedNorm ρ r ≠ ⊤ ∧ IsLow b r ∧ f = g * q + r := by
  set w := neumannSeries b g f
  have hw : weightedNorm ρ w ≠ ⊤ := weightedNorm_neumannSeries_ne_top hρ hε hg hf
  refine ⟨highQuot b w, lowPart b w, ?_, ?_, isLow_lowPart w, ?_⟩
  · refine ne_top_of_le_ne_top (ENNReal.div_ne_top hw ?_) (weightedNorm_highQuot_le' (hρ none) w)
    exact pow_ne_zero _ (by simp [(hρ none).ne'])
  · exact ne_top_of_le_ne_top hw (weightedNorm_lowPart_le ρ w)
  · calc f = w - divOp b g w := (neumannSeries_sub_divOp hρ hε hg hf).symm
      _ = (X none ^ b * highQuot b w + lowPart b w) - (X none ^ b - g) * highQuot b w := by
          rw [X_none_pow_mul_highQuot_add_lowPart]; rfl
      _ = g * highQuot b w + lowPart b w := by ring

omit [CompleteSpace 𝕜] in
/-- Uniqueness in the Weierstrass division at a fixed polyradius. -/
theorem weierstrassDiv_eq_zero_of_weightedNorm {q r : MvPowerSeries (Option τ) 𝕜}
    (hq : weightedNorm ρ q ≠ ⊤) (hr : IsLow b r) (h : g * q + r = 0) : q = 0 ∧ r = 0 := by
  have hq' : q = highQuot b ((X none ^ b - g) * q) := by
    have : (X none ^ b - g) * q = X none ^ b * q + r := by
      rw [sub_mul, eq_neg_of_add_eq_zero_left h, sub_neg_eq_add]
    rw [this, map_add, highQuot_X_none_pow_mul, hr.highQuot_eq, add_zero]
  have hρb : ((ρ none : ℝ≥0∞) ^ b) ≠ 0 := pow_ne_zero _ (by simp [(hρ none).ne'])
  have hle : (ρ none : ℝ≥0∞) ^ b * weightedNorm ρ q ≤ ε * ((ρ none : ℝ≥0∞) ^ b *
      weightedNorm ρ q) := by
    calc (ρ none : ℝ≥0∞) ^ b * weightedNorm ρ q
        ≤ weightedNorm ρ ((X none ^ b - g) * q) := by
          conv_lhs => rw [hq']
          exact weightedNorm_highQuot_le ρ _
      _ ≤ weightedNorm ρ (X none ^ b - g) * weightedNorm ρ q := weightedNorm_mul_le ρ _ _
      _ ≤ ε * (ρ none : ℝ≥0∞) ^ b * weightedNorm ρ q := by gcongr
      _ = ε * ((ρ none : ℝ≥0∞) ^ b * weightedNorm ρ q) := mul_assoc _ _ _
  have h0 := eq_zero_of_le_mul (ENNReal.mul_ne_top (by simp) hq) hle hε
  rw [mul_eq_zero, or_iff_right hρb, weightedNorm_eq_zero_iff hρ] at h0
  subst h0
  simpa using h

end FixedRadius

/-! ### Normalization of a divisor regular in `y` -/

section Normalize

variable {𝕜 : Type*} [NormedField 𝕜] {b : ℕ}

lemma monomialEval_option {M : Type*} [CommMonoid M] (z : Option τ → M) (α : Option τ →₀ ℕ) :
    monomialEval z α = z none ^ α none * monomialEval (fun i ↦ z (some i)) α.some :=
  Finsupp.prod_option_index _ _ (fun _ ↦ pow_zero _) (fun _ _ _ ↦ pow_add _ _ _)

lemma eq_single_none_of_some_eq_zero {α : Option τ →₀ ℕ} (h : α.some = 0) :
    α = Finsupp.single none (α none) := by
  ext o
  cases o with
  | none => simp
  | some i =>
    have := congr_arg (· i) h
    simp only [Finsupp.some_apply, Finsupp.coe_zero, Pi.zero_apply] at this
    simp [this]

private lemma nnreal_ineq {a s t M : ℝ≥0} (ha : 0 < a) (hs : s ≤ a ^ (b + 1) / (4 * (M + 1)))
    (ht : t ≤ s ^ b / (4 * (M + 1))) : ((s / a) ^ (b + 1) + t) * M ≤ 2⁻¹ * s ^ b := by
  have h4 : (0 : ℝ≥0) < 4 * (M + 1) := by positivity
  rw [le_div_iff₀ h4] at hs ht
  rw [← NNReal.coe_le_coe] at hs ht ⊢
  push_cast at hs ht ⊢
  have ha' : (0 : ℝ) < a := ha
  have hM : (0 : ℝ) ≤ M := M.2
  have hsb : (0 : ℝ) ≤ (s : ℝ) ^ b := pow_nonneg s.2 b
  have hab : (0 : ℝ) < (a : ℝ) ^ (b + 1) := pow_pos ha' _
  have e1 : ((s : ℝ) / a) ^ (b + 1) * M ≤ (s : ℝ) ^ b / 4 := by
    rw [div_pow, pow_succ (s : ℝ) b, div_mul_eq_mul_div, div_le_iff₀ hab]
    nlinarith [mul_le_mul_of_nonneg_left hs hsb, s.2]
  have e2 : (t : ℝ) * M ≤ (s : ℝ) ^ b / 4 := by
    nlinarith [mul_le_mul_of_nonneg_right ht hM, t.2]
  nlinarith

/-- The key estimate on monomials: with `ρ = (t ρ₀(z), s)` and `s ≤ ρ₀(y)`, `t ≤ 1`, a monomial
`zᵅ' yʲ` with `α' ≠ 0` or `j > b` gets multiplied by at most `(s/ρ₀(y))^(b+1) + t`. -/
private lemma monomialEval_le_of_rescale {ρ₀ : Option τ → ℝ≥0} {s t : ℝ≥0}
    (ha : 0 < ρ₀ none) (hsa : s ≤ ρ₀ none) (ht1 : t ≤ 1) {α : Option τ →₀ ℕ}
    (hα : α.some = 0 → b < α none) :
    monomialEval (fun o ↦ o.elim s fun i ↦ t * ρ₀ (some i)) α ≤
      ((s / ρ₀ none) ^ (b + 1) + t) * monomialEval ρ₀ α := by
  rw [monomialEval_option, monomialEval_option ρ₀]
  simp only [Option.elim_none, Option.elim_some]
  rw [monomialEval_const_mul]
  have hsa' : s / ρ₀ none ≤ 1 := (div_le_one ha).mpr hsa
  by_cases h : α.some = 0
  · have hb := hα h
    rw [h]
    simp only [map_zero, pow_zero, monomialEval_zero, mul_one]
    calc s ^ α none = (s / ρ₀ none) ^ α none * ρ₀ none ^ α none := by
          rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ha.ne')]
      _ ≤ (s / ρ₀ none) ^ (b + 1) * ρ₀ none ^ α none :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one zero_le hsa' hb) zero_le
      _ ≤ ((s / ρ₀ none) ^ (b + 1) + t) * ρ₀ none ^ α none := by
          gcongr
          exact le_self_add
  · have hdeg : α.some.degree ≠ 0 := by
      rwa [ne_eq, Finsupp.degree_eq_zero_iff]
    calc s ^ α none * (t ^ α.some.degree * monomialEval (fun i ↦ ρ₀ (some i)) α.some)
        ≤ ρ₀ none ^ α none * (t * monomialEval (fun i ↦ ρ₀ (some i)) α.some) := by
          gcongr
          exact pow_le_of_le_one zero_le ht1 hdeg
      _ ≤ ((s / ρ₀ none) ^ (b + 1) + t) *
          (ρ₀ none ^ α none * monomialEval (fun i ↦ ρ₀ (some i)) α.some) := by
          rw [mul_left_comm]
          gcongr
          exact le_add_self

/-- After shrinking the polyradius, a series `g` regular of order `b` with leading coefficient
`1` satisfies `‖y^b - g‖_ρ ≤ ρ_y^b / 2`. -/
theorem exists_weightedNorm_X_pow_sub_le {g : MvPowerSeries (Option τ) 𝕜}
    (hg₀ : ∀ j < b, coeff (Finsupp.single none j) g = 0)
    (hg₁ : coeff (Finsupp.single none b) g = 1)
    {ρ₀ : Option τ → ℝ≥0} (hρ₀ : ∀ i, 0 < ρ₀ i) (hfin : weightedNorm ρ₀ (X none ^ b - g) ≠ ⊤) :
    ∃ ρ ≤ ρ₀, (∀ i, 0 < ρ i) ∧
      weightedNorm ρ (X none ^ b - g) ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (ρ none : ℝ≥0∞) ^ b := by
  classical
  set c := X none ^ b - g with hc_def
  set M : ℝ≥0 := (weightedNorm ρ₀ c).toNNReal
  have ha : 0 < ρ₀ none := hρ₀ none
  set s : ℝ≥0 := min (ρ₀ none) (ρ₀ none ^ (b + 1) / (4 * (M + 1)))
  have hs : 0 < s := lt_min ha (div_pos (pow_pos ha _) (by positivity))
  set t : ℝ≥0 := min 1 (s ^ b / (4 * (M + 1)))
  have ht : 0 < t := lt_min one_pos (div_pos (pow_pos hs _) (by positivity))
  refine ⟨fun o ↦ o.elim s fun i ↦ t * ρ₀ (some i), fun o ↦ ?_, fun o ↦ ?_, ?_⟩
  · cases o with
    | none => exact min_le_left _ _
    | some i => exact mul_le_of_le_one_left zero_le (min_le_left _ _)
  · cases o with
    | none => exact hs
    | some i => exact mul_pos ht (hρ₀ _)
  have hterm : ∀ α, ‖coeff α c‖₊ * monomialEval (fun o ↦ o.elim s fun i ↦ t * ρ₀ (some i)) α ≤
      ((s / ρ₀ none) ^ (b + 1) + t) * (‖coeff α c‖₊ * monomialEval ρ₀ α) := by
    intro α
    by_cases hcα : coeff α c = 0
    · simp [hcα]
    rw [mul_left_comm]
    gcongr
    refine monomialEval_le_of_rescale ha (min_le_left _ _) (min_le_left _ _) fun h ↦ ?_
    by_contra! hle
    apply hcα
    rw [eq_single_none_of_some_eq_zero h, hc_def, map_sub, coeff_X_pow]
    rcases hle.lt_or_eq with hlt | heq
    · rw [ite_eq_right (fun e ↦ hlt.ne (by simpa using congr_arg (· none) e)), hg₀ _ hlt, sub_zero]
    · rw [heq, ite_eq_left rfl, hg₁, sub_self]
  calc weightedNorm (fun o ↦ o.elim s fun i ↦ t * ρ₀ (some i)) c
      ≤ ∑' α, ((((s / ρ₀ none) ^ (b + 1) + t) * (‖coeff α c‖₊ * monomialEval ρ₀ α) : ℝ≥0) :
          ℝ≥0∞) := ENNReal.tsum_le_tsum fun α ↦ ENNReal.coe_le_coe.mpr (hterm α)
    _ = (((s / ρ₀ none) ^ (b + 1) + t : ℝ≥0) : ℝ≥0∞) * M := by
        simp_rw [ENNReal.coe_mul]
        rw [ENNReal.tsum_mul_left, ENNReal.coe_toNNReal hfin]
        rfl
    _ ≤ ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (s : ℝ≥0∞) ^ b := by
        rw [← ENNReal.coe_mul, ← ENNReal.coe_pow, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
        exact nnreal_ineq ha (min_le_right _ _) (min_le_right _ _)

end Normalize

/-! ### Weierstrass division for convergent power series -/

section Convergent

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {b : ℕ} {g : MvPowerSeries (Option τ) 𝕜}

lemma weightedNorm_X_pow_ne_top (ρ : Option τ → ℝ≥0) (o : Option τ) (n : ℕ) :
    weightedNorm ρ (X o ^ n : MvPowerSeries (Option τ) 𝕜) ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) (weightedNorm_pow_le ρ _ n)

/-- A convergent series regular of order `b` in `y` becomes, after normalization of its leading
coefficient, a small perturbation of `y^b` on small polydiscs. -/
lemma exists_radius_of_isRegularOfOrder (hg : g ∈ convergent (Option τ) 𝕜)
    (hreg : IsRegularOfOrder b g) {ρ₁ : Option τ → ℝ≥0} (hρ₁ : ∀ i, 0 < ρ₁ i) :
    ∃ ρ ≤ ρ₁, (∀ i, 0 < ρ i) ∧
      weightedNorm ρ (X none ^ b - (coeff (Finsupp.single none b) g)⁻¹ • g) ≤
        ((2⁻¹ : ℝ≥0) : ℝ≥0∞) * (ρ none : ℝ≥0∞) ^ b := by
  obtain ⟨ρg, hρg, hgfin⟩ := hg
  set c := coeff (Finsupp.single none b) g
  have hc : c ≠ 0 := hreg.2
  have hρ₀ : ∀ i, 0 < (ρ₁ ⊓ ρg) i := fun i ↦ lt_min (hρ₁ i) (hρg i)
  have hfin : weightedNorm (ρ₁ ⊓ ρg) (X none ^ b - c⁻¹ • g) ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨weightedNorm_X_pow_ne_top _ _ _, ?_⟩)
      (weightedNorm_sub_le _ _ _)
    rw [weightedNorm_smul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top hgfin (weightedNorm_mono inf_le_right g))
  obtain ⟨ρ, hρle, hρ, hnorm⟩ := exists_weightedNorm_X_pow_sub_le (g := c⁻¹ • g)
    (fun j hj ↦ by rw [coeff_smul, hreg.1 j hj, mul_zero])
    (by rw [coeff_smul, inv_mul_cancel₀ hc]) hρ₀ hfin
  exact ⟨ρ, hρle.trans inf_le_left, hρ, hnorm⟩

variable [CompleteSpace 𝕜]

/-- **Weierstrass division theorem** (existence): if `g ∈ 𝕜{z, y}` is regular of order `b` in
`y`, every `f ∈ 𝕜{z, y}` is `g q + r` with `q, r ∈ 𝕜{z, y}` and `r` of degree `< b` in `y`. -/
theorem exists_weierstrassDiv (hg : g ∈ convergent (Option τ) 𝕜) (hreg : IsRegularOfOrder b g)
    {f : MvPowerSeries (Option τ) 𝕜} (hf : f ∈ convergent (Option τ) 𝕜) :
    ∃ q ∈ convergent (Option τ) 𝕜, ∃ r ∈ convergent (Option τ) 𝕜, IsLow b r ∧
      f = g * q + r := by
  obtain ⟨ρf, hρf, hffin⟩ := hf
  obtain ⟨ρ, hρle, hρ, hnorm⟩ := exists_radius_of_isRegularOfOrder hg hreg hρf
  obtain ⟨q, r, hq, hr, hlow, heq⟩ := exists_weierstrassDiv_of_weightedNorm hρ
    (by norm_num : (2⁻¹ : ℝ≥0) < 1) hnorm (ne_top_of_le_ne_top hffin (weightedNorm_mono hρle f))
  set c := coeff (Finsupp.single none b) g
  refine ⟨c⁻¹ • q, ⟨ρ, hρ, ?_⟩, r, ⟨ρ, hρ, hr⟩, hlow, ?_⟩
  · rw [weightedNorm_smul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top hq
  · rw [heq, smul_mul_assoc, mul_smul_comm]

omit [CompleteSpace 𝕜] in
/-- **Weierstrass division theorem** (uniqueness). -/
theorem weierstrassDiv_unique (hg : g ∈ convergent (Option τ) 𝕜) (hreg : IsRegularOfOrder b g)
    {q r : MvPowerSeries (Option τ) 𝕜} (hq : q ∈ convergent (Option τ) 𝕜) (hr : IsLow b r)
    (h : g * q + r = 0) : q = 0 ∧ r = 0 := by
  obtain ⟨ρq, hρq, hqfin⟩ := hq
  obtain ⟨ρ, hρle, hρ, hnorm⟩ := exists_radius_of_isRegularOfOrder hg hreg hρq
  set c := coeff (Finsupp.single none b) g
  have hc : c ≠ 0 := hreg.2
  have h' : (c⁻¹ • g) * (c • q) + r = 0 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, one_smul, h]
  have hcq : weightedNorm ρ (c • q) ≠ ⊤ := by
    rw [weightedNorm_smul]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      (ne_top_of_le_ne_top hqfin (weightedNorm_mono hρle q))
  obtain ⟨h1, h2⟩ := weierstrassDiv_eq_zero_of_weightedNorm hρ (by norm_num : (2⁻¹ : ℝ≥0) < 1)
    hnorm hcq hr h'
  exact ⟨(smul_eq_zero.mp h1).resolve_left hc, h2⟩

omit [CompleteSpace 𝕜] in
theorem weierstrassDiv_eq (hg : g ∈ convergent (Option τ) 𝕜) (hreg : IsRegularOfOrder b g)
    {f q₁ r₁ q₂ r₂ : MvPowerSeries (Option τ) 𝕜} (hq₁ : q₁ ∈ convergent (Option τ) 𝕜)
    (hq₂ : q₂ ∈ convergent (Option τ) 𝕜) (hr₁ : IsLow b r₁) (hr₂ : IsLow b r₂)
    (h₁ : f = g * q₁ + r₁) (h₂ : f = g * q₂ + r₂) : q₁ = q₂ ∧ r₁ = r₂ := by
  have h : g * (q₁ - q₂) + (r₁ + -r₂) = 0 := by
    rw [show g * (q₁ - q₂) + (r₁ + -r₂) = (g * q₁ + r₁) - (g * q₂ + r₂) by ring, ← h₁, ← h₂,
      sub_self]
  obtain ⟨e₁, e₂⟩ := weierstrassDiv_unique hg hreg (sub_mem hq₁ hq₂) (hr₁.add hr₂.neg) h
  exact ⟨sub_eq_zero.mp e₁, by rwa [← sub_eq_add_neg, sub_eq_zero] at e₂⟩

/-- **Weierstrass preparation theorem**: if `g ∈ 𝕜{z, y}` is regular of order `b` in `y`, there
is a unit `q` of `𝕜{z, y}` such that `g q = y^b - r` with `r` of degree `< b` in `y` and
`r(0, y) = 0`; that is, `g` is a unit times the *Weierstrass polynomial* `y^b - r`. -/
theorem exists_weierstrassPreparation (hg : g ∈ convergent (Option τ) 𝕜)
    (hreg : IsRegularOfOrder b g) :
    ∃ q ∈ convergent (Option τ) 𝕜, constantCoeff q ≠ 0 ∧ ∃ r ∈ convergent (Option τ) 𝕜,
      IsLow b r ∧ (∀ j, coeff (Finsupp.single none j) r = 0) ∧ g * q = X none ^ b - r := by
  obtain ⟨q, hq, r, hr, hlow, heq⟩ :=
    exists_weierstrassDiv hg hreg (pow_mem (X_mem_convergent (none : Option τ)) b)
  set c := coeff (Finsupp.single none b) g
  have hmain : X () ^ b * (1 - restrictY (highQuot b g) * restrictY q) = restrictY r := by
    have h := congr_arg restrictY heq
    rw [← X_none_pow_mul_highQuot_add_lowPart (b := b) g] at h
    simp only [map_add, map_mul, map_pow, restrictY_X_none,
      restrictY_lowPart_of_isRegularOfOrder hreg.1, add_zero] at h
    rw [mul_sub, mul_one, ← mul_assoc]
    exact sub_eq_of_eq_add' h
  have hr0 : ∀ j, coeff (Finsupp.single none j) r = 0 := by
    intro j
    rcases lt_or_ge j b with hj | hj
    · rw [← coeff_restrictY, ← hmain, X_pow_eq, coeff_monomial_mul, ite_eq_right]
      simpa [Finsupp.single_le_iff] using hj
    · exact hlow _ (by simpa using hj)
  have hr0' : restrictY r = 0 := restrictY_eq_zero_iff.mpr hr0
  have hc : c * constantCoeff q = 1 := by
    have h := congr_arg (coeff (Finsupp.single () b)) hmain
    rw [hr0', map_zero, X_pow_eq, coeff_monomial_mul, ite_eq_left le_rfl, one_mul, tsub_self,
      coeff_zero_eq_constantCoeff_apply, map_sub, map_one, map_mul, constantCoeff_restrictY,
      constantCoeff_restrictY, sub_eq_zero] at h
    rw [h, ← coeff_zero_eq_constantCoeff_apply (highQuot b g), coeff_highQuot, zero_add]
  refine ⟨q, hq, right_ne_zero_of_mul_eq_one hc, r, hr, hlow, hr0, ?_⟩
  rw [heq, add_sub_cancel_right]

end Convergent

end MvPowerSeries
