/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Order
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# The completion of the ring of convergent power series

Let `A = 𝕜{X}` be the ring of convergent power series in finitely many variables and `m` its
maximal ideal. The powers of `m` are the convergent series of order `≥ n`
(`mem_maximalIdeal_pow_convergent_iff`). Hence `A/m^n` is the ring of polynomials of degree
`< n`, and the `m`-adic completion of `A` is the ring of formal power series:
`convergentCompletionEquiv : 𝕜⟦X⟧ ≃ₐ[A] Â`. Since `A` is noetherian, `𝕜⟦X⟧` is flat over `A`,
and even faithfully flat as `A → 𝕜⟦X⟧` is a local homomorphism
([Grauert–Remmert, *Analytische Stellenalgebren*, II §1]; [Stacks, Tag 00MB]).
-/

open scoped NNReal ENNReal
open Finset IsLocalRing AdicCompletion

noncomputable section

namespace MvPowerSeries

variable {σ : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-! ### Polynomials are convergent -/

section Polynomial

/-- Polynomials, as convergent power series. -/
def polynomialToConvergent : MvPolynomial σ 𝕜 →ₐ[𝕜] convergent σ 𝕜 :=
  MvPolynomial.aeval fun i ↦ ⟨X i, X_mem_convergent i⟩

@[simp] lemma coe_polynomialToConvergent (p : MvPolynomial σ 𝕜) :
    (polynomialToConvergent p : MvPowerSeries σ 𝕜) = p := by
  have : (convergent σ 𝕜).val.comp polynomialToConvergent =
      MvPolynomial.coeToMvPowerSeries.algHom 𝕜 := MvPolynomial.algHom_ext fun i ↦ by
    simp [polynomialToConvergent]
  exact congr($this p)

end Polynomial

/-! ### Division by the variables -/

section DivX

variable [LinearOrder σ]

/-- The part of a series whose first variable is `i`, divided by `Xᵢ`: its coefficient of `Xᵅ`
is the coefficient of `Xᵅ⁺ᵉⁱ` in `f` if `α` involves no variable `< i`, and `0` otherwise. -/
def divX (i : σ) (f : MvPowerSeries σ 𝕜) : MvPowerSeries σ 𝕜 :=
  fun α ↦ if ∀ j ∈ α.support, i ≤ j then coeff (α + Finsupp.single i 1) f else 0

lemma coeff_divX (i : σ) (f : MvPowerSeries σ 𝕜) (α : σ →₀ ℕ) :
    coeff α (divX i f) = if ∀ j ∈ α.support, i ≤ j then coeff (α + Finsupp.single i 1) f
      else 0 :=
  rfl

lemma forall_support_le_iff (i : σ) (α : σ →₀ ℕ) :
    (∀ j ∈ α.support, i ≤ j) ↔ ∀ j < i, α j = 0 := by
  constructor
  · intro h j hj
    by_contra hne
    exact absurd (h j (Finsupp.mem_support_iff.mpr hne)) (not_le.mpr hj)
  · intro h j hj
    by_contra hlt
    exact Finsupp.mem_support_iff.mp hj (h j (not_le.mp hlt))

omit [LinearOrder σ] in
lemma coeff_X_mul (i : σ) (h : MvPowerSeries σ 𝕜) (α : σ →₀ ℕ) :
    coeff α (X i * h) = if 1 ≤ α i then coeff (α - Finsupp.single i 1) h else 0 := by
  classical
  rw [X, coeff_monomial_mul, one_mul]
  congr 1
  exact propext Finsupp.single_le_iff

/-- A series without constant term is `∑ᵢ Xᵢ · divX i f`. -/
lemma sum_X_mul_divX [Fintype σ] {f : MvPowerSeries σ 𝕜} (hf : constantCoeff f = 0) :
    ∑ i, X i * divX i f = f := by
  classical
  ext α
  rw [map_sum]
  simp_rw [coeff_X_mul, coeff_divX, forall_support_le_iff]
  -- the condition holds for at most one `i`, namely the smallest variable occurring in `α`
  have key : ∀ i, (if 1 ≤ α i then
      (if ∀ j < i, (α - Finsupp.single i 1 : σ →₀ ℕ) j = 0 then
        coeff (α - Finsupp.single i 1 + Finsupp.single i 1) f else 0) else 0) =
      if 1 ≤ α i ∧ ∀ j < i, α j = 0 then coeff α f else 0 := by
    intro i
    by_cases h₁ : 1 ≤ α i
    · have hsub : α - Finsupp.single i 1 + Finsupp.single i 1 = α :=
        tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr h₁)
      have hj : (∀ j < i, (α - Finsupp.single i 1 : σ →₀ ℕ) j = 0) ↔ ∀ j < i, α j = 0 := by
        refine forall₂_congr fun j hj ↦ ?_
        rw [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hj.ne, tsub_zero]
      simp only [h₁, hj, hsub, true_and, ite_true]
    · simp [h₁]
  simp_rw [key]
  by_cases hα : α = 0
  · subst hα
    simp [coeff_zero_eq_constantCoeff_apply, hf]
  · have hne : α.support.Nonempty := Finsupp.support_nonempty_iff.mpr hα
    set i₀ := α.support.min' hne
    rw [sum_eq_single i₀]
    · rw [ite_eq_left_iff.mpr]
      refine fun h ↦ absurd ⟨?_, fun j hj ↦ ?_⟩ h
      · exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (α.support.min'_mem hne))
      · by_contra hj'
        exact absurd (α.support.min'_le j (Finsupp.mem_support_iff.mpr hj')) (not_le.mpr hj)
    · intro i _ hi
      rw [ite_eq_right_iff]
      rintro ⟨h₁, h₂⟩
      exfalso
      rcases lt_or_gt_of_ne hi with h | h
      · exact (Nat.one_le_iff_ne_zero.mp h₁) (by
          by_contra h'
          exact absurd (α.support.min'_le i (Finsupp.mem_support_iff.mpr h')) (not_le.mpr h))
      · exact (Finsupp.mem_support_iff.mp (α.support.min'_mem hne)) (h₂ _ h)
    · simp

lemma order_le_order_divX_add_one (i : σ) (f : MvPowerSeries σ 𝕜) :
    f.order ≤ (divX i f).order + 1 := by
  by_cases h : divX i f = 0
  · simp [h]
  obtain ⟨α, hα, hord⟩ := exists_coeff_ne_zero_and_order (f := divX i f)
    (ne_zero_iff_order_finite.mp h)
  rw [← hord]
  have h' : coeff (α + Finsupp.single i 1) f ≠ 0 := by
    rw [coeff_divX] at hα
    split_ifs at hα
    · exact hα
    · exact absurd rfl hα
  refine (order_le h').trans ?_
  simp [map_add, Finsupp.degree_single]

lemma weightedNorm_divX_le (ρ : σ → ℝ≥0) (i : σ) (f : MvPowerSeries σ 𝕜) :
    (ρ i : ℝ≥0∞) * weightedNorm ρ (divX i f) ≤ weightedNorm ρ f := by
  rw [weightedNorm, ← ENNReal.tsum_mul_left]
  refine le_trans (ENNReal.tsum_le_tsum fun α ↦ ?_) (ENNReal.tsum_comp_le_tsum_of_injective
    (f := fun α : σ →₀ ℕ ↦ α + Finsupp.single i 1) (add_left_injective _)
    fun β ↦ ((‖coeff β f‖₊ * monomialEval ρ β : ℝ≥0) : ℝ≥0∞))
  rw [coeff_divX, ← ENNReal.coe_mul, ENNReal.coe_le_coe, monomialEval_add, monomialEval_single,
    pow_one]
  split_ifs
  · exact le_of_eq (by ring)
  · simp

lemma divX_mem_convergent (i : σ) {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) :
    divX i f ∈ convergent σ 𝕜 := by
  obtain ⟨ρ, hρ, hfin⟩ := hf
  refine ⟨ρ, hρ, fun htop ↦ hfin ?_⟩
  have h := weightedNorm_divX_le ρ i f
  rw [htop, ENNReal.mul_top (by simp [(hρ i).ne'])] at h
  exact top_le_iff.mp h

end DivX

/-! ### Powers of the maximal ideal -/

section MaximalIdeal

variable [Finite σ] [CompleteSpace 𝕜]

lemma X_mem_maximalIdeal_convergent (i : σ) :
    (⟨X i, X_mem_convergent i⟩ : convergent σ 𝕜) ∈ maximalIdeal (convergent σ 𝕜) := by
  classical
  rw [mem_maximalIdeal_convergent_iff]
  simp

lemma order_ge_of_mem_maximalIdeal_pow {n : ℕ} {f : convergent σ 𝕜}
    (hf : f ∈ maximalIdeal (convergent σ 𝕜) ^ n) : (n : ℕ∞) ≤ f.1.order := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on hf (fun a ha b hb ↦ ?_) (fun a b ha hb ↦ ?_)
    · have h₁ := ih ha
      have h₂ : (1 : ℕ∞) ≤ b.1.order := by
        rw [one_le_order_iff_constCoeff_eq_zero]
        exact mem_maximalIdeal_convergent_iff.mp hb
      calc ((n + 1 : ℕ) : ℕ∞) = n + 1 := by push_cast; rfl
        _ ≤ a.1.order + b.1.order := add_le_add h₁ h₂
        _ ≤ (a * b).1.order := le_order_mul
    · exact (le_min ha hb).trans min_order_le_add

lemma mem_maximalIdeal_pow_of_order_ge {n : ℕ} {f : convergent σ 𝕜}
    (hf : (n : ℕ∞) ≤ f.1.order) : f ∈ maximalIdeal (convergent σ 𝕜) ^ n := by
  classical
  have := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' (Fintype.equivFin σ) (Fintype.equivFin σ).injective
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have hc : constantCoeff f.1 = 0 := by
      rw [← one_le_order_iff_constCoeff_eq_zero]
      exact le_trans (by norm_cast; omega) hf
    have hsum : f = ∑ i, (⟨X i, X_mem_convergent i⟩ : convergent σ 𝕜) *
        ⟨divX i f.1, divX_mem_convergent i f.2⟩ := by
      apply Subtype.ext
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
      exact (sum_X_mul_divX hc).symm
    rw [hsum, pow_succ']
    refine Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_mul (X_mem_maximalIdeal_convergent i) (ih ?_)
    have h := order_le_order_divX_add_one i f.1
    have h' : ((n + 1 : ℕ) : ℕ∞) ≤ (divX i f.1).order + 1 := hf.trans h
    rw [Nat.cast_add, Nat.cast_one] at h'
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

/-- The `n`-th power of the maximal ideal of `𝕜{X}` consists of the series of order `≥ n`. -/
theorem mem_maximalIdeal_pow_convergent_iff {n : ℕ} {f : convergent σ 𝕜} :
    f ∈ maximalIdeal (convergent σ 𝕜) ^ n ↔ (n : ℕ∞) ≤ f.1.order :=
  ⟨order_ge_of_mem_maximalIdeal_pow, mem_maximalIdeal_pow_of_order_ge⟩

lemma smodEq_maximalIdeal_pow_iff {n : ℕ} {a b : convergent σ 𝕜} :
    a ≡ b [SMOD (maximalIdeal (convergent σ 𝕜) ^ n • ⊤ : Submodule (convergent σ 𝕜)
      (convergent σ 𝕜))] ↔ (n : ℕ∞) ≤ (a.1 - b.1).order := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_convergent_iff]
  rfl

end MaximalIdeal

/-! ### The completion -/

section Completion

variable [Finite σ] [CompleteSpace 𝕜]

omit [Finite σ] [CompleteSpace 𝕜] in
lemma le_order_of_eq_add {n : ℕ∞} {x y z : MvPowerSeries σ 𝕜} (h : x = y + z)
    (hy : n ≤ y.order) (hz : n ≤ z.order) : n ≤ x.order :=
  h ▸ (le_min hy hz).trans min_order_le_add

omit [CompleteSpace 𝕜] in
lemma le_order_truncTotal_sub (F : MvPowerSeries σ 𝕜) {m n : ℕ} (h : m ≤ n) :
    (m : ℕ∞) ≤ ((truncTotal n F : MvPowerSeries σ 𝕜) - F).order :=
  nat_le_order fun d hd ↦ by
    rw [map_sub, MvPolynomial.coeff_coe, coeff_truncTotal _ (hd.trans_le h), sub_self]

omit [CompleteSpace 𝕜] in
lemma le_order_truncTotal_sub_truncTotal (F : MvPowerSeries σ 𝕜) {l m n : ℕ} (hm : l ≤ m)
    (hn : l ≤ n) :
    (l : ℕ∞) ≤ ((truncTotal m F : MvPowerSeries σ 𝕜) - truncTotal n F).order :=
  nat_le_order fun d hd ↦ by
    rw [map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, coeff_truncTotal _
      (hd.trans_le hm), coeff_truncTotal _ (hd.trans_le hn), sub_self]

/-- The truncations of a power series, as an adic Cauchy sequence of convergent series. -/
def truncSeq (F : MvPowerSeries σ 𝕜) :
    AdicCauchySequence (maximalIdeal (convergent σ 𝕜)) (convergent σ 𝕜) :=
  AdicCauchySequence.mk _ _ (fun n ↦ polynomialToConvergent (truncTotal n F)) fun n ↦ by
    rw [smodEq_maximalIdeal_pow_iff]
    simpa using le_order_truncTotal_sub_truncTotal F le_rfl (Nat.le_succ n)

@[simp] lemma truncSeq_apply (F : MvPowerSeries σ 𝕜) (n : ℕ) :
    truncSeq F n = polynomialToConvergent (truncTotal n F) := rfl

lemma truncSeq_add (F G : MvPowerSeries σ 𝕜) : truncSeq (F + G) = truncSeq F + truncSeq G :=
  AdicCauchySequence.ext fun n ↦ by
    rw [AdicCauchySequence.add_apply, truncSeq_apply, truncSeq_apply, truncSeq_apply, map_add,
      map_add]

lemma mk_eq_mk_of_le_order
    {f g : AdicCauchySequence (maximalIdeal (convergent σ 𝕜)) (convergent σ 𝕜)}
    (h : ∀ n : ℕ, (n : ℕ∞) ≤ ((f n).1 - (g n).1).order) :
    AdicCompletion.mk _ _ f = AdicCompletion.mk _ _ g := by
  ext n
  rw [mk_apply_coe, mk_apply_coe, Submodule.mkQ_apply, Submodule.mkQ_apply, ← SModEq.def,
    smodEq_maximalIdeal_pow_iff]
  exact h n

variable (σ 𝕜) in
/-- The map `𝕜⟦X⟧ → Â` sending a power series to the sequence of its truncations. -/
def toCompletion : MvPowerSeries σ 𝕜 →ₗ[convergent σ 𝕜]
    AdicCompletion (maximalIdeal (convergent σ 𝕜)) (convergent σ 𝕜) where
  toFun F := AdicCompletion.mk _ _ (truncSeq F)
  map_add' F G := by
    rw [truncSeq_add, map_add]
  map_smul' a F := by
    rw [RingHom.id_apply, ← map_smul]
    refine mk_eq_mk_of_le_order fun n ↦ ?_
    rw [AdicCauchySequence.smul_apply, truncSeq_apply, truncSeq_apply]
    change (n : ℕ∞) ≤ ((polynomialToConvergent (truncTotal n (a • F))).1 -
      a.1 * (polynomialToConvergent (truncTotal n F)).1).order
    rw [coe_polynomialToConvergent, coe_polynomialToConvergent]
    have hsmul : a • F = a.1 * F := rfl
    rw [hsmul]
    refine le_order_of_eq_add (y := (truncTotal n (a.1 * F) : MvPowerSeries σ 𝕜) - a.1 * F)
      (z := a.1 * (F - truncTotal n F)) (by ring) (le_order_truncTotal_sub _ le_rfl) ?_
    refine le_trans ?_ le_order_mul
    have h := le_order_truncTotal_sub F (le_refl n)
    rw [← order_neg, neg_sub] at h
    exact le_add_left h

lemma toCompletion_apply (F : MvPowerSeries σ 𝕜) :
    toCompletion σ 𝕜 F = AdicCompletion.mk _ _ (truncSeq F) := rfl

lemma toCompletion_injective : Function.Injective (toCompletion σ 𝕜) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro F hF
  ext α
  rw [toCompletion_apply] at hF
  have h : (Submodule.Quotient.mk (polynomialToConvergent (truncTotal (α.degree + 1) F)) :
      convergent σ 𝕜 ⧸ (maximalIdeal (convergent σ 𝕜) ^ (α.degree + 1) • ⊤ :
        Submodule (convergent σ 𝕜) (convergent σ 𝕜))) = 0 :=
    congr_arg (fun x ↦ x.val (α.degree + 1)) hF
  rw [Submodule.Quotient.mk_eq_zero, smul_eq_mul, Ideal.mul_top,
    mem_maximalIdeal_pow_convergent_iff, coe_polynomialToConvergent] at h
  have h' := coeff_of_lt_order (d := α) (lt_of_lt_of_le (by exact_mod_cast lt_add_one _) h)
  rwa [MvPolynomial.coeff_coe, coeff_truncTotal _ (lt_add_one _)] at h'

lemma toCompletion_surjective : Function.Surjective (toCompletion σ 𝕜) := by
  intro x
  obtain ⟨⟨g, hg⟩, rfl⟩ := AdicCompletion.mk_surjective _ _ x
  let F : MvPowerSeries σ 𝕜 := fun α ↦ coeff α (g (α.degree + 1)).1
  have hF : ∀ d, coeff d F = coeff d (g (d.degree + 1)).1 := fun _ ↦ rfl
  refine ⟨F, ?_⟩
  refine mk_eq_mk_of_le_order fun n ↦ ?_
  change (n : ℕ∞) ≤ ((polynomialToConvergent (truncTotal n F)).1 - (g n).1).order
  rw [coe_polynomialToConvergent]
  refine nat_le_order fun d hd ↦ ?_
  rw [map_sub, sub_eq_zero, MvPolynomial.coeff_coe, coeff_truncTotal _ hd, hF]
  have hc := hg (show d.degree + 1 ≤ n by omega)
  rw [smodEq_maximalIdeal_pow_iff] at hc
  have := coeff_of_lt_order (d := d) (lt_of_lt_of_le (by exact_mod_cast lt_add_one _) hc)
  rw [map_sub, sub_eq_zero] at this
  exact this

lemma toCompletion_mul (F G : MvPowerSeries σ 𝕜) :
    toCompletion σ 𝕜 (F * G) = toCompletion σ 𝕜 F * toCompletion σ 𝕜 G := by
  have := Fintype.ofFinite σ
  ext n
  change (toCompletion σ 𝕜 (F * G)).val n =
    ((toCompletion σ 𝕜 F) * (toCompletion σ 𝕜 G)).val n
  rw [val_mul]
  change Ideal.Quotient.mk _ (polynomialToConvergent (truncTotal n (F * G))) =
    Ideal.Quotient.mk _ (polynomialToConvergent (truncTotal n F)) *
      Ideal.Quotient.mk _ (polynomialToConvergent (truncTotal n G))
  rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_mul]
  change _ ∈ (maximalIdeal (convergent σ 𝕜) ^ n • ⊤ : Submodule _ _)
  rw [smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_convergent_iff]
  change (n : ℕ∞) ≤ order ((polynomialToConvergent (truncTotal n (F * G))).1 -
    (polynomialToConvergent (truncTotal n F * truncTotal n G)).1 : MvPowerSeries σ 𝕜)
  rw [coe_polynomialToConvergent, coe_polynomialToConvergent]
  have h := (MvPolynomial.mem_pow_idealOfVars_iff' n _).mp
    (truncTotal_mul_sub_mul_truncTotal_mem_pow_idealOfVars (n := n) F G)
  exact nat_le_order fun d hd ↦ by
    rw [map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, ← MvPolynomial.coeff_sub,
      h d hd]

lemma toCompletion_one : toCompletion σ 𝕜 1 = 1 := by
  ext n
  change (toCompletion σ 𝕜 1).val n = (1 : AdicCompletion _ _).val n
  rw [val_one]
  change Ideal.Quotient.mk _ (polynomialToConvergent (truncTotal n 1)) = Ideal.Quotient.mk _ 1
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  change _ ∈ (maximalIdeal (convergent σ 𝕜) ^ n • ⊤ : Submodule _ _)
  rw [smul_eq_mul, Ideal.mul_top, mem_maximalIdeal_pow_convergent_iff]
  change (n : ℕ∞) ≤ order ((polynomialToConvergent (truncTotal n 1)).1 - 1 : MvPowerSeries σ 𝕜)
  rw [coe_polynomialToConvergent]
  exact le_order_truncTotal_sub _ le_rfl

/-- **The completion of `𝕜{X}` is `𝕜⟦X⟧`**: the formal power series ring is the adic completion
of the ring of convergent power series with respect to its maximal ideal. -/
def completionEquiv : MvPowerSeries σ 𝕜 ≃ₐ[convergent σ 𝕜]
    AdicCompletion (maximalIdeal (convergent σ 𝕜)) (convergent σ 𝕜) :=
  AlgEquiv.ofLinearEquiv
    (LinearEquiv.ofBijective (toCompletion σ 𝕜) ⟨toCompletion_injective, toCompletion_surjective⟩)
    toCompletion_one toCompletion_mul

/-- `𝕜⟦X⟧` is flat over `𝕜{X}`. -/
instance flat_convergent : Module.Flat (convergent σ 𝕜) (MvPowerSeries σ 𝕜) :=
  Module.Flat.of_linearEquiv completionEquiv.toLinearEquiv

instance isLocalHom_algebraMap_convergent :
    IsLocalHom (algebraMap (convergent σ 𝕜) (MvPowerSeries σ 𝕜)) := by
  refine ⟨fun a ha ↦ ?_⟩
  rw [isUnit_convergent_iff]
  exact (isUnit_iff_constantCoeff.mp ha).ne_zero

/-- `𝕜⟦X⟧` is faithfully flat over `𝕜{X}`. -/
instance faithfullyFlat_convergent : Module.FaithfullyFlat (convergent σ 𝕜) (MvPowerSeries σ 𝕜) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

end Completion

end MvPowerSeries
