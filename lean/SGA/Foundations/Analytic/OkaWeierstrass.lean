/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaRelations
import SGA.Foundations.Analytic.Henselian
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Polynomial and analytic division in the coherence argument

We compare a polynomial in the last variable with its convergent power series and show
that division by a monic Weierstrass polynomial agrees with polynomial division whenever
the dividend is polynomial. In particular an analytic quotient of two such polynomials
is polynomial. This is the algebraic input to the bounded-degree reduction of relations
in Oka's coherence proof; see Demailly, *Complex Analytic and Differential Geometry*,
Chapter II, Lemma 3.20. No uniform neighborhood-generation conclusion is asserted here.
-/

noncomputable section

open Finset
open scoped Polynomial

namespace MvPowerSeries

variable {τ : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]

@[simp] lemma polyY_sub (P Q : (convergent τ 𝕜)[X]) :
    polyY (P - Q) = polyY P - polyY Q := map_sub _ _ _

@[simp] lemma polyY_mul (P Q : (convergent τ 𝕜)[X]) :
    polyY (P * Q) = polyY P * polyY Q := map_mul _ _ _

@[simp] lemma polyY_X_pow (b : ℕ) :
    polyY (Polynomial.X ^ b : (convergent τ 𝕜)[X]) =
      (⟨X none, X_mem_convergent none⟩ : convergent (Option τ) 𝕜) ^ b := by
  exact (map_pow _ _ _).trans (congrArg (· ^ b) (Polynomial.aeval_X _))

/-- Every coefficient of a polynomial in the last variable can be read from its
associated convergent power series. -/
lemma coeff_polyY (P : (convergent τ 𝕜)[X]) (α : Option τ →₀ ℕ) :
    coeff α (polyY P).1 = coeff α.some (P.coeff (α none)).1 := by
  classical
  rw [polyY, Polynomial.aeval_eq_sum_range' (n := max (P.natDegree + 1) (α none + 1))
    (by omega)]
  simp only [AddSubmonoidClass.coe_finsetSum, Algebra.smul_def, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, algebraMap_convergent_option, coe_renameSomeHom, map_sum]
  simp_rw [mul_comm (rename someEmb _), coeff_X_none_pow_mul_rename_some]
  rw [sum_ite_eq]
  exact ite_eq_left (by simp only [mem_range]; omega)

/-- A polynomial in the last variable is determined by its analytic germ. -/
theorem polyY_injective : Function.Injective (polyY : (convergent τ 𝕜)[X] → _) := by
  intro P Q h
  ext j : 1
  apply Subtype.ext
  ext β
  have he := congrArg (fun f : convergent (Option τ) 𝕜 ↦ coeff (β.optionElim j) f.1) h
  simpa only [coeff_polyY, Finsupp.optionElim_apply_none, Finsupp.some_optionElim] using he

/-- A polynomial of degree below `b` is a Weierstrass remainder of order `b`. -/
lemma isLow_polyY {P : (convergent τ 𝕜)[X]} {b : ℕ} (hP : P.degree < b) :
    IsLow b (polyY P).1 := by
  intro α hα
  rw [coeff_polyY, Polynomial.coeff_eq_zero_of_degree_lt (hP.trans_le (by exact_mod_cast hα))]
  exact map_zero _

/-- A convergent Weierstrass remainder is a polynomial in the last variable whose
coefficients remain convergent in the other variables. -/
theorem exists_polyY_of_isLow {f : convergent (Option τ) 𝕜} {b : ℕ} (hf : IsLow b f.1) :
    ∃ P : (convergent τ 𝕜)[X], P.degree < b ∧ polyY P = f := by
  classical
  let v : Fin b → convergent τ 𝕜 := fun j ↦ ⟨yCoeff j f.1, yCoeff_mem_convergent j f.2⟩
  refine ⟨Polynomial.ofFn b v, Polynomial.ofFn_degree_lt v, ?_⟩
  apply Subtype.ext
  ext α
  rw [coeff_polyY]
  by_cases hα : α none < b
  · rw [Polynomial.ofFn_coeff_eq_val_of_lt v hα]
    exact (coeff_yCoeff (α none) f.1 α.some).trans (congrArg (coeff · f.1)
      (Finsupp.optionElim_some α))
  · rw [Polynomial.ofFn_coeff_eq_zero_of_ge v (Nat.le_of_not_gt hα)]
    exact (map_zero _).trans (hf α (Nat.le_of_not_gt hα)).symm

/-- Polynomial division by a monic polynomial gives an analytic Weierstrass division. -/
lemma polyY_division (P Q : (convergent τ 𝕜)[X]) :
    polyY Q = polyY P * polyY (Q /ₘ P) + polyY (Q %ₘ P) := by
  rw [polyY, polyY, polyY, polyY, ← map_mul, ← map_add, add_comm,
    Polynomial.modByMonic_add_div]

/-- The analytic quotient and remainder of a polynomial by a monic Weierstrass polynomial
agree with polynomial division. -/
theorem weierstrassDivision_polyY (P Q : (convergent τ 𝕜)[X]) (hP : P.Monic)
    (hreg : IsRegularOfOrder P.natDegree (polyY P).1)
    (q r : convergent (Option τ) 𝕜) (hr : IsLow P.natDegree r.1)
    (h : polyY Q = polyY P * q + r) :
    q = polyY (Q /ₘ P) ∧ r = polyY (Q %ₘ P) := by
  have hlow : IsLow P.natDegree (polyY (Q %ₘ P)).1 := by
    apply isLow_polyY
    simpa only [Polynomial.degree_eq_natDegree hP.ne_zero] using
      Polynomial.degree_modByMonic_lt Q hP
  have hdiv := weierstrassDiv_eq (polyY P).2 hreg q.2 (polyY (Q /ₘ P)).2 hr hlow
    (congrArg Subtype.val h) (congrArg Subtype.val (polyY_division P Q))
  exact ⟨Subtype.ext hdiv.1, Subtype.ext hdiv.2⟩

/-- If a monic Weierstrass polynomial analytically divides a polynomial, the quotient is
itself a polynomial and the polynomial remainder vanishes. -/
theorem eq_polyY_divByMonic_of_mul_eq (P Q : (convergent τ 𝕜)[X]) (hP : P.Monic)
    (hreg : IsRegularOfOrder P.natDegree (polyY P).1)
    (q : convergent (Option τ) 𝕜) (hq : polyY P * q = polyY Q) :
    q = polyY (Q /ₘ P) ∧ Q %ₘ P = 0 := by
  obtain ⟨heq, hr⟩ := weierstrassDivision_polyY P Q hP hreg q 0 isLow_zero (by
    simpa only [add_zero] using hq.symm)
  refine ⟨heq, polyY_injective ?_⟩
  rw [← hr]
  exact (map_zero _).symm

open AnalyticGeometry

variable [CompleteSpace 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weierstrass division reduces every analytic relation among polynomial coefficients
of degree at most `μ` to elementary relations and a polynomial relation of degree at most
`μ + degree(Pⱼ)`. All coordinates other than the distinguished one have degree below that
of the distinguished polynomial. This is the bounded-degree relation reduction at the
center of a Weierstrass coordinate neighborhood. -/
theorem exists_polynomial_relation_reduction (P : ι → (convergent τ 𝕜)[X]) (j : ι)
    (μ : ℕ) (hdeg : ∀ i, (P i).natDegree ≤ μ)
    (hP : (P j).Monic) (hreg : IsRegularOfOrder (P j).natDegree (polyY (P j)).1)
    (a : ι → convergent (Option τ) 𝕜) (ha : a ∈ relationModule (fun i ↦ polyY (P i))) :
    ∃ (q : ι → convergent (Option τ) 𝕜) (R : ι → (convergent τ 𝕜)[X]),
      (∀ i, i ≠ j → (R i).degree < (P j).natDegree) ∧
      (∀ i, (R i).natDegree ≤ μ + (P j).natDegree) ∧
      (fun i ↦ polyY (R i)) ∈ relationModule (fun i ↦ polyY (P i)) ∧
      a = (∑ i, q i • elementaryRelation (fun l ↦ polyY (P l)) j i) +
        (fun i ↦ polyY (R i)) := by
  classical
  choose q hq r hr hlow hdiv using fun i ↦
    exists_weierstrassDiv (polyY (P j)).2 hreg (a i).2
  let q' : ι → convergent (Option τ) 𝕜 := fun i ↦ ⟨q i, hq i⟩
  let r' : ι → convergent (Option τ) 𝕜 := fun i ↦ ⟨r i, hr i⟩
  let f : ι → convergent (Option τ) 𝕜 := fun i ↦ polyY (P i)
  let c := a - ∑ i, q' i • elementaryRelation f j i
  have hc : c ∈ relationModule f := sub_sum_elementaryRelation_mem f j a q' ha
  have hc_eq (i : ι) (hi : i ≠ j) : c i = r' i := by
    change (a - ∑ l, q' l • elementaryRelation f j l) i = r' i
    rw [sub_sum_elementaryRelation_apply f j a q' i hi]
    have hd : a i = f j * q' i + r' i := Subtype.ext (hdiv i)
    rw [hd]
    ring
  choose T hT hTr using fun i ↦ exists_polyY_of_isLow (f := r' i) (hlow i)
  have hTdeg (i : ι) : (T i).natDegree ≤ (P j).natDegree :=
    Polynomial.natDegree_le_of_degree_le (hT i).le
  let Q : (convergent τ 𝕜)[X] := -∑ i ∈ univ.erase j, T i * P i
  have hQdeg : Q.natDegree ≤ μ + (P j).natDegree := by
    simp only [Q, Polynomial.natDegree_neg]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i hi
    have h := Polynomial.natDegree_mul_le (p := T i) (q := P i)
    have h₁ := hTdeg i
    have h₂ := hdeg i
    omega
  have hQc : polyY (P j) * c j = polyY Q := by
    have hsum : (∑ i ∈ univ.erase j, c i * f i) + c j * f j = 0 := by
      rw [sum_erase_add _ _ (mem_univ j)]
      exact (mem_relationModule f c).mp hc
    have hQ : polyY Q = -∑ i ∈ univ.erase j, c i * f i := by
      let Φ : (convergent τ 𝕜)[X] →ₐ[convergent τ 𝕜] convergent (Option τ) 𝕜 :=
        Polynomial.aeval ⟨X none, X_mem_convergent none⟩
      change Φ (-∑ i ∈ univ.erase j, T i * P i) = _
      calc
        Φ (-∑ i ∈ univ.erase j, T i * P i) = -Φ (∑ i ∈ univ.erase j, T i * P i) :=
          _root_.map_neg Φ _
        _ = -∑ i ∈ univ.erase j, Φ (T i * P i) := congrArg Neg.neg (_root_.map_sum Φ _ _)
        _ = -∑ i ∈ univ.erase j, c i * f i := by
          congr 1
          apply sum_congr rfl
          intro i hi
          rw [_root_.map_mul]
          have hij : i ≠ j := (mem_erase.mp hi).1
          rw [hc_eq i hij, ← hTr i]
    rw [hQ]
    change f j * c j = -∑ i ∈ univ.erase j, c i * f i
    linear_combination hsum
  have hcj : c j = polyY (Q /ₘ P j) :=
    (eq_polyY_divByMonic_of_mul_eq (P j) Q hP hreg (c j) hQc).1
  let R : ι → (convergent τ 𝕜)[X] := Function.update T j (Q /ₘ P j)
  have hR : (fun i ↦ polyY (R i)) = c := by
    funext i
    by_cases hi : i = j
    · subst i
      simpa [R] using hcj.symm
    · simpa [R, hi] using (hTr i).trans (hc_eq i hi).symm
  refine ⟨q', R, ?_, ?_, hR.symm ▸ hc, ?_⟩
  · intro i hi
    simpa [R, hi] using hT i
  · intro i
    by_cases hi : i = j
    · subst i
      simpa only [R, Function.update_self] using
        (Polynomial.natDegree_le_natDegree (Polynomial.degree_divByMonic_le Q (P j))).trans hQdeg
    · simp only [R, Function.update_of_ne hi]
      exact (hTdeg i).trans (Nat.le_add_left _ _)
  · rw [hR]
    change a = _ + (a - _)
    abel

end MvPowerSeries
