/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Noetherian
import Mathlib.RingTheory.Henselian

/-!
# The ring of convergent power series is henselian

Let `P ∈ 𝕜{z}[T]` and `a₀ ∈ 𝕜{z}` with `P(a₀)(0) = 0` and `P'(a₀)(0) ≠ 0`. After translation,
`P(a₀ + y)` is a convergent series in `(z, y)` regular of order `1` in `y`; by the Weierstrass
preparation theorem it is a unit times `y - a(z)`, and substituting `y = a(z)` gives
`P(a₀ + a) = 0`. Hence `𝕜{z}` is a henselian local ring ([Grauert–Remmert, *Analytische
Stellenalgebren*, I §4]; [Stacks, Tag 04GE] for the notion).
-/

open scoped NNReal ENNReal Topology Polynomial
open Finset Filter

noncomputable section

namespace MvPowerSeries

variable {τ : Type*} {𝕜 : Type*} [NontriviallyNormedField 𝕜]

lemma tsumEval_rename_some (h : MvPowerSeries τ 𝕜) (w : Option τ → 𝕜) :
    tsumEval (rename someEmb h) w = tsumEval h fun i ↦ w (some i) := by
  rw [tsumEval, tsumEval, ← (Finsupp.embDomain_injective someEmb).tsum_eq]
  · refine tsum_congr fun x ↦ ?_
    rw [coeff_embDomain_rename, monomialEval, Finsupp.prod_embDomain]
    rfl
  · intro β hβ
    by_contra h'
    apply hβ
    dsimp only
    rw [coeff_rename_eq_zero, zero_mul]
    rintro ⟨x, rfl⟩
    exact h' ⟨x, Finsupp.embDomain_eq_mapDomain _ _⟩

/-- The graph `z ↦ (z, a(z))` of a power series `a`. -/
def graphMap (a : MvPowerSeries τ 𝕜) (z : τ → 𝕜) : Option τ → 𝕜 :=
  fun o ↦ o.elim (tsumEval a z) z

variable [Fintype τ] [CompleteSpace 𝕜] {a : MvPowerSeries τ 𝕜}

lemma analyticAt_graphMap (ha : a ∈ convergent τ 𝕜) : AnalyticAt 𝕜 (graphMap a) 0 := by
  refine AnalyticAt.pi (f := fun o z ↦ graphMap a z o) fun o ↦ ?_
  cases o with
  | none => exact analyticAt_tsumEval ha
  | some i => exact analyticAt_apply i 0

omit [Fintype τ] [CompleteSpace 𝕜] in
lemma graphMap_zero (ha0 : constantCoeff a = 0) : graphMap a 0 = 0 := by
  funext o
  cases o with
  | none => simp [graphMap, tsumEval_zero_eq_constantCoeff, ha0]
  | some i => rfl

/-- Substitution of `a(z)` for the variable `y`: `f(z, y) ↦ f(z, a(z))`. -/
def evalY (ha : a ∈ convergent τ 𝕜) (ha0 : constantCoeff a = 0) :
    convergent (Option τ) 𝕜 →ₐ[𝕜] convergent τ 𝕜 :=
  substAnalyticHom (analyticAt_graphMap ha) (graphMap_zero ha0)

lemma evalY_algebraMap (ha : a ∈ convergent τ 𝕜) (ha0 : constantCoeff a = 0)
    (h : convergent τ 𝕜) :
    evalY ha ha0 (algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜) h) = h := by
  apply Subtype.ext
  change taylorSeries (fun z ↦ tsumEval (rename someEmb h.1) (graphMap a z)) = h.1
  simp_rw [tsumEval_rename_some]
  exact taylorSeries_tsumEval h.2

lemma evalY_comp_algebraMap (ha : a ∈ convergent τ 𝕜) (ha0 : constantCoeff a = 0) :
    (evalY ha ha0 : convergent (Option τ) 𝕜 →+* convergent τ 𝕜).comp
      (algebraMap (convergent τ 𝕜) (convergent (Option τ) 𝕜)) = RingHom.id _ :=
  RingHom.ext (evalY_algebraMap ha ha0)

lemma evalY_X (ha : a ∈ convergent τ 𝕜) (ha0 : constantCoeff a = 0) :
    evalY ha ha0 ⟨X none, X_mem_convergent none⟩ = ⟨a, ha⟩ := by
  apply Subtype.ext
  change substAnalytic (graphMap a) (X none) = a
  rw [substAnalytic_X]
  exact taylorSeries_tsumEval ha

/-- The polynomial `P(y)` with coefficients in `𝕜{z}`, as a convergent series in `(z, y)`. -/
abbrev polyY (P : (convergent τ 𝕜)[X]) : convergent (Option τ) 𝕜 :=
  Polynomial.aeval (⟨X none, X_mem_convergent none⟩ : convergent (Option τ) 𝕜) P

lemma evalY_polyY (ha : a ∈ convergent τ 𝕜) (ha0 : constantCoeff a = 0)
    (P : (convergent τ 𝕜)[X]) : evalY ha ha0 (polyY P) = P.eval ⟨a, ha⟩ := by
  rw [polyY, Polynomial.aeval_def, ← AlgHom.coe_toRingHom, Polynomial.hom_eval₂,
    evalY_comp_algebraMap, AlgHom.coe_toRingHom, evalY_X]
  rfl

omit [Fintype τ] [CompleteSpace 𝕜] in
lemma coeff_single_none_polyY (P : (convergent τ 𝕜)[X]) (j : ℕ) :
    coeff (Finsupp.single none j) (polyY P).1 = constantCoeff (P.coeff j).1 := by
  classical
  rw [polyY, Polynomial.aeval_eq_sum_range' (n := max (P.natDegree + 1) (j + 1))
    (by omega)]
  simp only [AddSubmonoidClass.coe_finsetSum, Algebra.smul_def, MulMemClass.coe_mul,
    SubmonoidClass.coe_pow, algebraMap_convergent_option, coe_renameSomeHom, map_sum]
  simp_rw [mul_comm (rename someEmb _), coeff_X_none_pow_mul_rename_some]
  rw [sum_ite_eq]
  simp only [Finsupp.single_eq_same, Finsupp.some_single_none, coeff_zero_eq_constantCoeff_apply,
    mem_range]
  rw [ite_eq_left (by omega)]

/-- **Hensel's lemma for convergent power series**: `𝕜{z}` is a henselian local ring. -/
instance henselianLocalRing_convergent {σ : Type*} [Finite σ] :
    HenselianLocalRing (convergent σ 𝕜) := by
  have := Fintype.ofFinite σ
  refine ⟨fun P _ a₀ hP hP' ↦ ?_⟩
  -- translate the root to `0`
  set Q := P.comp (Polynomial.X + Polynomial.C a₀)
  have hQ0 : constantCoeff (Q.coeff 0).1 = 0 := by
    rw [← mem_maximalIdeal_convergent_iff, Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.eval_comp]
    simpa using hP
  have hQ1 : constantCoeff (Q.coeff 1).1 ≠ 0 := by
    rw [← isUnit_convergent_iff]
    have : Q.derivative.eval 0 = P.derivative.eval a₀ := by
      simp [Q, Polynomial.derivative_comp]
    rw [← this, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] at hP'
    simpa using hP'
  have hreg : IsRegularOfOrder 1 (polyY Q).1 := by
    refine ⟨fun j hj ↦ ?_, ?_⟩
    · obtain rfl : j = 0 := by omega
      rw [coeff_single_none_polyY, hQ0]
    · rw [coeff_single_none_polyY]
      exact hQ1
  obtain ⟨q, hq, hq0, r, hr, hlow, hr0, heq⟩ := exists_weierstrassPreparation (polyY Q).2 hreg
  -- the root `a := r(z, ·)`
  set a := yCoeff 0 r with ha_def
  have ha : a ∈ convergent σ 𝕜 := yCoeff_mem_convergent 0 hr
  have ha0 : constantCoeff a = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, ha_def, coeff_yCoeff]
    simpa using hr0 0
  have hra : r = rename someEmb a := by
    conv_lhs => rw [hlow.eq_sum]
    simp [ha_def]
  have key : evalY ha ha0 (polyY Q) * evalY ha ha0 ⟨q, hq⟩ = 0 := by
    rw [← map_mul]
    have : polyY Q * ⟨q, hq⟩ = ⟨X none, X_mem_convergent none⟩ -
        algebraMap (convergent σ 𝕜) (convergent (Option σ) 𝕜) ⟨a, ha⟩ :=
      Subtype.ext (by simpa [hra, algebraMap_convergent_option, coe_renameSomeHom] using heq)
    rw [this, map_sub, evalY_X, evalY_algebraMap, sub_self]
  have hunit : IsUnit (evalY ha ha0 ⟨q, hq⟩) :=
    (isUnit_convergent_iff.mpr hq0).map _
  rw [hunit.mul_left_eq_zero, evalY_polyY] at key
  refine ⟨⟨a, ha⟩ + a₀, ?_, ?_⟩
  · rw [Polynomial.IsRoot, ← key, Polynomial.eval_comp]
    simp
  · rw [add_sub_cancel_right, mem_maximalIdeal_convergent_iff]
    exact ha0

end MvPowerSeries
