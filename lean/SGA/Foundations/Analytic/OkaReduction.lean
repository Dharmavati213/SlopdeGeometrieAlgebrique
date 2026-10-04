/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaFactorization
import SGA.Foundations.Analytic.OkaPolynomial

/-!
# Bounded-degree reduction of analytic relations

For polynomial coefficients of degree at most `μ`, with one coefficient monic, every
analytic relation is a combination of elementary relations and an analytic scalar times
a polynomial relation of degree at most `2 * μ`. The monic coefficient need not have all
its roots at the origin: it is first split into its distinguished factor and its unit
factor. This is the algebraic reduction used at every point in Oka's induction
(Demailly, *Complex Analytic and Differential Geometry*, II.3.20).
-/

noncomputable section

open Finset AnalyticGeometry
open scoped Polynomial

namespace MvPowerSeries

variable {τ : Type*} [Finite τ] {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The bounded-degree relation reduction for an arbitrary monic distinguished
coefficient, including points at which only some of its roots meet the origin. -/
theorem exists_bounded_polynomial_relation_reduction
    (P : ι → (convergent τ 𝕜)[X]) (j : ι) (hP : (P j).Monic)
    (μ : ℕ) (hdeg : ∀ i, (P i).natDegree ≤ μ)
    (a : ι → convergent (Option τ) 𝕜) (ha : a ∈ relationModule (fun i ↦ polyY (P i))) :
    ∃ (q : ι → convergent (Option τ) 𝕜) (s : convergent (Option τ) 𝕜)
      (R : ι → (convergent τ 𝕜)[X]),
      (∀ i, (R i).natDegree ≤ 2 * μ) ∧
      (fun i ↦ polyY (R i)) ∈ relationModule (fun i ↦ polyY (P i)) ∧
      a = (∑ i, q i • elementaryRelation (fun l ↦ polyY (P l)) j i) +
        s • (fun i ↦ polyY (R i)) := by
  classical
  obtain ⟨b, W, V, hb, hW, hWdeg, hfac, hWcoeff, hV0⟩ :=
    exists_polynomial_weierstrass_factorization (P j) hP
  have hWreg : IsRegularOfOrder W.natDegree (polyY W).1 := by
    rw [hWdeg]
    refine ⟨fun l hl ↦ ?_, ?_⟩
    · rw [coeff_single_none_polyY, hWcoeff, ite_eq_right (by omega)]
    · rw [coeff_single_none_polyY, hWcoeff, ite_eq_left rfl]
      exact one_ne_zero
  have hVunit : IsUnit (polyY V) := by
    rw [isUnit_convergent_iff, constantCoeff_polyY]
    exact hV0
  obtain ⟨v, hv⟩ := hVunit
  have hVdeg : V.natDegree ≤ μ := by
    have hVm : V.Monic := hW.of_mul_monic_left (hfac ▸ hP)
    exact (hVm.natDegree_le_of_dvd hP.ne_zero
      ⟨W, hfac.trans (mul_comm W V)⟩).trans (hdeg j)
  choose q hq r hr hlow hdiv using fun i ↦
    exists_weierstrassDiv (polyY W).2 hWreg (a i).2
  let q' : ι → convergent (Option τ) 𝕜 := fun i ↦ (⟨q i, hq i⟩ : convergent _ _) * ↑v⁻¹
  let r' : ι → convergent (Option τ) 𝕜 := fun i ↦ ⟨r i, hr i⟩
  let f : ι → convergent (Option τ) 𝕜 := fun i ↦ polyY (P i)
  let c := a - ∑ i, q' i • elementaryRelation f j i
  have hc : c ∈ relationModule f := sub_sum_elementaryRelation_mem f j a q' ha
  have hc_eq (i : ι) (hi : i ≠ j) : c i = r' i := by
    change (a - ∑ l, q' l • elementaryRelation f j l) i = r' i
    rw [sub_sum_elementaryRelation_apply f j a q' i hi]
    have hd : a i = polyY W * ⟨q i, hq i⟩ + r' i := Subtype.ext (hdiv i)
    have hcancel : q' i * f j = polyY W * ⟨q i, hq i⟩ := by
      change (⟨q i, hq i⟩ : convergent _ _) * ↑v⁻¹ * polyY (P j) = _
      rw [hfac, polyY_mul, ← hv]
      calc
        (⟨q i, hq i⟩ : convergent _ _) * ↑v⁻¹ * (polyY W * ↑v) =
            polyY W * ⟨q i, hq i⟩ * (↑v⁻¹ * ↑v) := by ring
        _ = polyY W * ⟨q i, hq i⟩ := by rw [Units.inv_mul, mul_one]
    rw [hcancel, hd, add_sub_cancel_left]
  choose T hT hTr using fun i ↦ exists_polyY_of_isLow (f := r' i) (hlow i)
  have hTdeg (i : ι) : (T i).natDegree ≤ μ :=
    (Polynomial.natDegree_le_of_degree_le (hT i).le).trans
      (hWdeg ▸ hb.trans (hdeg j))
  let Q : (convergent τ 𝕜)[X] := -∑ i ∈ univ.erase j, T i * P i
  have hQdeg : Q.natDegree ≤ 2 * μ := by
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
  have hWc : polyY W * ((↑v : convergent (Option τ) 𝕜) * c j) = polyY Q := by
    rw [← mul_assoc, hv, ← polyY_mul, ← hfac]
    exact hQc
  have hcj : (↑v : convergent (Option τ) 𝕜) * c j = polyY (Q /ₘ W) :=
    (eq_polyY_divByMonic_of_mul_eq W Q hW hWreg _ hWc).1
  let R : ι → (convergent τ 𝕜)[X] := Function.update (fun i ↦ V * T i) j (Q /ₘ W)
  have hR : (fun i ↦ polyY (R i)) = (↑v : convergent (Option τ) 𝕜) • c := by
    funext i
    by_cases hi : i = j
    · subst i
      simpa [R] using hcj.symm
    · simp only [R, Function.update_of_ne hi, polyY_mul, hTr]
      rw [Pi.smul_apply, smul_eq_mul, hv, hc_eq i hi]
  refine ⟨q', ↑v⁻¹, R, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = j
    · subst i
      simpa only [R, Function.update_self] using
        (Polynomial.natDegree_le_natDegree (Polynomial.degree_divByMonic_le Q W)).trans hQdeg
    · simp only [R, Function.update_of_ne hi]
      have h := Polynomial.natDegree_mul_le (p := V) (q := T i)
      have h₁ := hTdeg i
      omega
  · rw [hR]
    exact (relationModule f).smul_mem _ hc
  · rw [hR, smul_smul, Units.inv_mul, one_smul]
    change a = _ + (a - _)
    abel

end MvPowerSeries
