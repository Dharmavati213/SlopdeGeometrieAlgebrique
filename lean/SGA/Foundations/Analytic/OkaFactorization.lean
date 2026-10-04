/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaWeierstrass
import Mathlib.Algebra.Polynomial.Taylor

/-!
# The polynomial factor in Weierstrass preparation

A monic polynomial over the ring of convergent series in the base variables factors as
a monic distinguished polynomial times a polynomial which is an analytic unit at the
origin. Weierstrass preparation initially supplies an analytic unit; uniqueness of
division shows that its inverse is polynomial. This factorization is the local algebra
needed at varying points in the Oka coherence argument (Demailly, *Complex Analytic and
Differential Geometry*, II.3.20).
-/

noncomputable section

open scoped Polynomial

namespace MvPowerSeries

variable {τ : Type*} [Finite τ] {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

omit [Finite τ] [CompleteSpace 𝕜] in
lemma constantCoeff_polyY (P : (convergent τ 𝕜)[X]) :
    constantCoeff (polyY P).1 = constantCoeff (P.coeff 0).1 := by
  simpa only [Finsupp.single_zero, coeff_zero_eq_constantCoeff_apply] using
    coeff_single_none_polyY P 0

omit [Finite τ] [CompleteSpace 𝕜] in
/-- A monic polynomial is regular of some finite order in its last variable. -/
theorem exists_isRegularOfOrder_polyY (P : (convergent τ 𝕜)[X]) (hP : P.Monic) :
    ∃ b ≤ P.natDegree, IsRegularOfOrder b (polyY P).1 := by
  classical
  have hlead : coeff (Finsupp.single none P.natDegree) (polyY P).1 ≠ 0 := by
    rw [coeff_single_none_polyY, hP.coeff_natDegree]
    exact one_ne_zero
  have hex : ∃ b, coeff (Finsupp.single none b) (polyY P).1 ≠ 0 := ⟨_, hlead⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hlead, ?_, Nat.find_spec hex⟩
  intro j hj
  exact not_not.mp (Nat.find_min hex hj)

/-- A monic polynomial splits into the factor meeting the origin and a polynomial
factor invertible there. The first factor specializes exactly to a power of the variable. -/
theorem exists_polynomial_weierstrass_factorization
    (P : (convergent τ 𝕜)[X]) (hP : P.Monic) :
    ∃ (b : ℕ) (W Q : (convergent τ 𝕜)[X]), b ≤ P.natDegree ∧ W.Monic ∧
      W.natDegree = b ∧ P = W * Q ∧
      (∀ j, constantCoeff (W.coeff j).1 = if j = b then 1 else 0) ∧
      constantCoeff (Q.coeff 0).1 ≠ 0 := by
  classical
  obtain ⟨b, hb, hreg⟩ := exists_isRegularOfOrder_polyY P hP
  obtain ⟨u, hu, hu0, r, hr, hrlow, hr0, hprep⟩ :=
    exists_weierstrassPreparation (polyY P).2 hreg
  obtain ⟨R, hRdeg, hR⟩ := exists_polyY_of_isLow (f := ⟨r, hr⟩) hrlow
  let W : (convergent τ 𝕜)[X] := Polynomial.X ^ b - R
  have hW : W.Monic := Polynomial.monic_X_pow_sub hRdeg
  have hWdeg : W.natDegree = b := by
    apply Polynomial.natDegree_eq_of_degree_eq_some
    change (Polynomial.X ^ b - R).degree = (b : WithBot ℕ)
    rw [Polynomial.degree_sub_eq_left_of_degree_lt (by simpa using hRdeg), Polynomial.degree_X_pow]
  have hRzero (j : ℕ) : constantCoeff (R.coeff j).1 = 0 := by
    rw [← coeff_single_none_polyY, hR]
    exact hr0 j
  have hWcoeff (j : ℕ) : constantCoeff (W.coeff j).1 = if j = b then 1 else 0 := by
    simp only [W, Polynomial.coeff_sub, AddSubgroupClass.coe_sub, map_sub, hRzero, sub_zero]
    by_cases hj : j = b <;> simp [Polynomial.coeff_X_pow, hj]
  have hWreg : IsRegularOfOrder W.natDegree (polyY W).1 := by
    rw [hWdeg]
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · rw [coeff_single_none_polyY, hWcoeff, ite_eq_right (by omega)]
    · rw [coeff_single_none_polyY, hWcoeff, ite_eq_left rfl]
      exact one_ne_zero
  have hunit : IsUnit (⟨u, hu⟩ : convergent (Option τ) 𝕜) :=
    isUnit_convergent_iff.mpr hu0
  obtain ⟨v, hv⟩ := hunit
  have hPu : polyY P * (v : convergent (Option τ) 𝕜) = polyY W := by
    rw [hv]
    apply Subtype.ext
    change (polyY P).1 * u = (polyY W).1
    rw [hprep]
    have hWpoly : polyY W =
        (⟨X none, X_mem_convergent none⟩ : convergent (Option τ) 𝕜) ^ b - ⟨r, hr⟩ := by
      change polyY (Polynomial.X ^ b - R) = _
      rw [polyY_sub, polyY_X_pow, hR]
    exact (congrArg Subtype.val hWpoly).symm
  have hquot : polyY W * (↑v⁻¹ : convergent (Option τ) 𝕜) = polyY P := by
    rw [← hPu, mul_assoc, Units.mul_inv, mul_one]
  obtain ⟨hQ, -⟩ := eq_polyY_divByMonic_of_mul_eq W P hW hWreg (↑v⁻¹) hquot
  refine ⟨b, W, P /ₘ W, hb, hW, hWdeg, ?_, hWcoeff, ?_⟩
  · apply polyY_injective
    rw [polyY_mul, ← hQ]
    exact hquot.symm
  · rw [← constantCoeff_polyY, ← hQ]
    exact isUnit_convergent_iff.mp (Units.isUnit v⁻¹)

omit [Finite τ] [CompleteSpace 𝕜] in
/-- Specialization of a convergent power series at the origin. -/
def convergentConstantCoeff : convergent τ 𝕜 →+* 𝕜 :=
  constantCoeff.comp (convergent τ 𝕜).val.toRingHom

omit [Finite τ] [CompleteSpace 𝕜] in
@[simp] lemma convergentConstantCoeff_apply (f : convergent τ 𝕜) :
    convergentConstantCoeff f = constantCoeff f.1 := rfl

omit [Finite τ] [CompleteSpace 𝕜] in
@[simp] lemma convergentConstantCoeff_algebraMap (a : 𝕜) :
    convergentConstantCoeff (algebraMap 𝕜 (convergent τ 𝕜) a) = a := by
  change constantCoeff (C a : MvPowerSeries τ 𝕜) = a
  exact constantCoeff_C a

/-- At an arbitrary point of the last variable, a monic analytic polynomial splits
into the monic factor specializing to a power of that point and a polynomial factor
invertible at that point. Both factors have convergent coefficients in the base variables. -/
theorem exists_polynomial_weierstrass_factorization_at
    (P : (convergent τ 𝕜)[X]) (hP : P.Monic) (a : 𝕜) :
    ∃ (b : ℕ) (W Q : (convergent τ 𝕜)[X]), b ≤ P.natDegree ∧ W.Monic ∧ Q.Monic ∧
      W.natDegree = b ∧ P = W * Q ∧
      W.map convergentConstantCoeff = (Polynomial.X - Polynomial.C a) ^ b ∧
      convergentConstantCoeff (Q.eval (algebraMap 𝕜 (convergent τ 𝕜) a)) ≠ 0 := by
  let a₀ : convergent τ 𝕜 := algebraMap 𝕜 _ a
  have hPa : (P.taylor a₀).Monic := by simpa [Polynomial.Monic] using hP
  obtain ⟨b, W, Q, hb, hW, hWdeg, hPfac, hWcoeff, hQ⟩ :=
    exists_polynomial_weierstrass_factorization (P.taylor a₀) hPa
  have hQmonic : Q.Monic := hW.of_mul_monic_left (hPfac ▸ hPa)
  have hWmap : W.map convergentConstantCoeff = Polynomial.X ^ b := by
    ext j
    rw [Polynomial.coeff_map]
    change constantCoeff (W.coeff j).1 = _
    rw [hWcoeff]
    simp [Polynomial.coeff_X_pow, eq_comm]
  refine ⟨b, W.taylor (-a₀), Q.taylor (-a₀), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Polynomial.natDegree_taylor] using hb
  · simpa only [Polynomial.Monic, Polynomial.leadingCoeff_taylor] using hW
  · simpa only [Polynomial.Monic, Polynomial.leadingCoeff_taylor] using hQmonic
  · simpa only [Polynomial.natDegree_taylor] using hWdeg
  · have h := congrArg (Polynomial.taylor (-a₀)) hPfac
    simpa only [Polynomial.taylor_taylor, neg_add_cancel, Polynomial.taylor_zero,
      Polynomial.taylor_mul] using h
  · rw [Polynomial.map_taylor, hWmap, Polynomial.taylor_X_pow, map_neg,
      convergentConstantCoeff_algebraMap]
    simp only [Polynomial.C_neg, sub_eq_add_neg]
  · simpa only [Polynomial.taylor_eval, a₀, add_neg_cancel, ← Polynomial.coeff_zero_eq_eval_zero,
      convergentConstantCoeff_apply] using hQ

end MvPowerSeries

namespace AnalyticGeometry

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {σ : Type u} [Fintype σ]

@[simp]
lemma convergentStalkEquiv_algebraMap (x : σ → 𝕜) (a : 𝕜) :
    convergentStalkEquiv x (algebraMap 𝕜 (MvPowerSeries.convergent σ 𝕜) a) =
      germOf (fun _ : (σ → 𝕜) ↦ a) analyticAt_const := by
  rw [convergentStalkEquiv_apply, convergentToStalk_apply]
  apply germOf_congr
  exact Filter.Eventually.of_forall fun _ ↦ MvPowerSeries.tsumEval_C _

/-- The separated-root factorization at any base point and any value of the last
coordinate. This statement is over the actual stalk of holomorphic functions at the
base point, so it can be applied separately at every point of a coordinate neighborhood. -/
theorem exists_stalkPolynomial_weierstrass_factorization
    (x : σ → 𝕜) (P : ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x)[X]) (hP : P.Monic) (a : 𝕜) :
    ∃ (b : ℕ) (W Q : ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x)[X]),
      b ≤ P.natDegree ∧ W.Monic ∧ Q.Monic ∧ W.natDegree = b ∧ P = W * Q ∧
      W.map (evalStalk x) = (Polynomial.X - Polynomial.C a) ^ b ∧
      evalStalk x (Q.eval (germOf (fun _ : (σ → 𝕜) ↦ a) analyticAt_const)) ≠ 0 := by
  let e := convergentStalkEquiv x
  let E := Polynomial.mapEquiv e
  have hpre : (E.symm P).Monic := hP.map e.symm.toRingHom
  obtain ⟨b, W, Q, hb, hW, hQ, hWdeg, hfac, hWmap, hQval⟩ :=
    MvPowerSeries.exists_polynomial_weierstrass_factorization_at (E.symm P) hpre a
  have hEval : (evalStalk x).comp e.toRingHom = MvPowerSeries.convergentConstantCoeff := by
    ext f
    exact evalStalk_convergentToStalk x f
  refine ⟨b, E W, E Q, ?_, hW.map e.toRingHom, hQ.map e.toRingHom, ?_, ?_, ?_, ?_⟩
  · change b ≤ (P.map e.symm.toRingHom).natDegree at hb
    rwa [Polynomial.natDegree_map_eq_of_injective (f := e.symm.toRingHom) e.symm.injective] at hb
  · change (W.map e.toRingHom).natDegree = b
    rwa [Polynomial.natDegree_map_eq_of_injective (f := e.toRingHom) e.injective]
  · simpa only [map_mul, RingEquiv.apply_symm_apply] using congrArg E hfac
  · change (W.map e.toRingHom).map (evalStalk x) = _
    rw [Polynomial.map_map, hEval, hWmap]
  · rw [← convergentStalkEquiv_algebraMap x a]
    change evalStalk x ((Q.map e.toRingHom).eval
      (e.toRingHom (algebraMap 𝕜 (MvPowerSeries.convergent σ 𝕜) a))) ≠ 0
    rw [Polynomial.eval_map_apply]
    change ((evalStalk x).comp e.toRingHom) _ ≠ 0
    rw [hEval]
    exact hQval

end AnalyticGeometry
