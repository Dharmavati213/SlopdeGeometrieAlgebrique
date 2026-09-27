/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.MvPowerSeries.Trunc
import SGA.Foundations.Formal.FormalScheme
import SGA.Foundations.Formal.SpfCompletion

/-!
# The completion of a noetherian ring is noetherian

Let `A` be a noetherian ring and `I = (a₁, …, aᵣ)` an ideal. The `I`-adic completion `Â` is a
quotient of the power series ring `A⟦X₁, …, Xᵣ⟧` via `Xᵢ ↦ aᵢ`, hence is noetherian
(`AdicCompletion.isNoetherianRing`; Atiyah–Macdonald, Thm. 10.26; EGA 0_I, §7.2).
The map `A⟦X⟧ → Â` is the limit of the maps
`f ↦ f(a) mod Iⁿ` evaluating the truncation of `f` in total degree `< n`; it is surjective by the
Nakayama lemma for complete rings.
-/

universe u

open MvPowerSeries

namespace MvPolynomial

variable {σ A : Type*} [CommRing A] {I : Ideal A}

/-- If every monomial of `P` has degree `≥ n` and the `aᵢ` lie in `I`, then `P(a) ∈ Iⁿ`. -/
lemma aeval_mem_pow_of_le_degree {a : σ → A} (ha : ∀ i, a i ∈ I) {n : ℕ} (P : MvPolynomial σ A)
    (hP : ∀ x ∈ P.support, n ≤ x.degree) : aeval a P ∈ I ^ n := by
  classical
  rw [P.as_sum, map_sum]
  refine Ideal.sum_mem _ fun x hx ↦ ?_
  rw [aeval_monomial]
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (hP x hx) ?_)
  rw [Finsupp.prod, Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ ↦ Ideal.pow_mem_pow (ha i) _

end MvPolynomial

namespace AdicCompletion

variable {A : Type u} [CommRing A] (I : Ideal A) {r : ℕ} (a : Fin r → A)

/-- `f ↦ f(a) mod Iⁿ`, evaluating the truncation of `f` in total degree `< n`. -/
noncomputable def truncEval (ha : ∀ i, a i ∈ I) (n : ℕ) :
    MvPowerSeries (Fin r) A →+* A ⧸ I ^ n where
  toFun f := Ideal.Quotient.mk _ (MvPolynomial.aeval a (truncTotal n f))
  map_zero' := by simp
  map_add' f g := by simp
  map_one' := by
    rcases n with _ | n
    · exact Subsingleton.elim (h := by rw [pow_zero, Ideal.one_eq_top]; infer_instance) _ _
    · rw [truncTotal_one n.succ_ne_zero, map_one, map_one]
  map_mul' f g := by
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, ← map_sub]
    refine MvPolynomial.aeval_mem_pow_of_le_degree ha _ fun x hx ↦ ?_
    by_contra h
    rw [not_le] at h
    apply MvPolynomial.mem_support_iff.mp hx
    rw [MvPolynomial.coeff_sub, coeff_truncTotal _ h, coeff_truncTotal_mul_truncTotal_eq_coeff_mul
      _ _ h, sub_self]

variable {I a}

lemma factorPow_comp_truncEval (ha : ∀ i, a i ∈ I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (truncEval I a ha n) = truncEval I a ha m := by
  ext f
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, ← map_sub]
  refine MvPolynomial.aeval_mem_pow_of_le_degree ha _ fun x hx ↦ ?_
  by_contra h
  rw [not_le] at h
  apply MvPolynomial.mem_support_iff.mp hx
  rw [MvPolynomial.coeff_sub, coeff_truncTotal _ h, coeff_truncTotal _ (h.trans_le hle), sub_self]

/-- The map `A⟦X₁, …, Xᵣ⟧ → Â`, `Xᵢ ↦ aᵢ`. -/
noncomputable def powerSeriesEval (ha : ∀ i, a i ∈ I) :
    MvPowerSeries (Fin r) A →+* AdicCompletion I A :=
  liftRingHom I (truncEval I a ha) (factorPow_comp_truncEval ha)

lemma powerSeriesEval_C (ha : ∀ i, a i ∈ I) (b : A) :
    powerSeriesEval ha (MvPowerSeries.C b) = algebraMap A _ b := by
  refine ext_evalₐ fun n ↦ ?_
  rw [powerSeriesEval, evalₐ_liftRingHom, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, evalₐ_of]
  rcases n with _ | n
  · exact Subsingleton.elim (h := by rw [pow_zero, Ideal.one_eq_top]; infer_instance) _ _
  · change Ideal.Quotient.mk _ (MvPolynomial.aeval a (truncTotal (n + 1) (MvPowerSeries.C b))) = _
    congr 1
    have : truncTotal (n + 1) (MvPowerSeries.C b : MvPowerSeries (Fin r) A) = MvPolynomial.C b := by
      rw [← MvPolynomial.coe_C, truncTotal_coe_eq_self_iff _ n.succ_ne_zero,
        MvPolynomial.totalDegree_C]
      exact n.succ_pos
    rw [this, MvPolynomial.aeval_C, Algebra.algebraMap_self, RingHom.id_apply]

lemma powerSeriesEval_X (ha : ∀ i, a i ∈ I) (i : Fin r) :
    powerSeriesEval ha (MvPowerSeries.X i) = algebraMap A _ (a i) := by
  refine ext_evalₐ fun n ↦ ?_
  rw [powerSeriesEval, evalₐ_liftRingHom, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, evalₐ_of]
  change Ideal.Quotient.mk _ (MvPolynomial.aeval a (truncTotal n (MvPowerSeries.X i))) = _
  rcases Nat.lt_or_ge 1 n with hn | hn
  · have : truncTotal n (MvPowerSeries.X i : MvPowerSeries (Fin r) A) = MvPolynomial.X i := by
      nontriviality A
      rw [← MvPolynomial.coe_X, truncTotal_coe_eq_self_iff _ (by lia), MvPolynomial.totalDegree_X]
      exact hn
    rw [this, MvPolynomial.aeval_X]
  · rw [Ideal.Quotient.eq]
    refine Ideal.pow_le_pow_right hn ?_
    rw [pow_one]
    refine sub_mem ?_ (ha i)
    have := MvPolynomial.aeval_mem_pow_of_le_degree (n := 1) ha (truncTotal n (X i)) fun x hx ↦ by
      by_contra h
      rw [not_le, Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at h
      subst h
      apply MvPolynomial.mem_support_iff.mp hx
      simp [coeff_truncTotal_eq_ite]
    simpa using this

lemma map_span_X_eq (ha : ∀ i, a i ∈ I) (hspan : Ideal.span (Set.range a) = I) :
    (Ideal.span (Set.range (MvPowerSeries.X : Fin r → MvPowerSeries (Fin r) A))).map
      (powerSeriesEval ha) = completionIdeal I := by
  have h : completionIdeal I = (Ideal.span (Set.range a)).map (algebraMap A _) := by rw [hspan]
  rw [h, Ideal.map_span, Ideal.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 2
  ext i
  simp [powerSeriesEval_X]

/-- `A⟦X₁, …, Xᵣ⟧ → Â`, `Xᵢ ↦ aᵢ`, is surjective when the `aᵢ` generate `I`. -/
theorem powerSeriesEval_surjective (ha : ∀ i, a i ∈ I) (hspan : Ideal.span (Set.range a) = I) :
    Function.Surjective (powerSeriesEval ha) := by
  have hI : I.FG := hspan ▸ Submodule.fg_span (Set.finite_range a)
  have : IsAdicComplete (completionIdeal I) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hI)
  have : IsHausdorff ((Ideal.span (Set.range (MvPowerSeries.X : Fin r → _))).map
      (powerSeriesEval ha)) (AdicCompletion I A) := by
    rw [map_span_X_eq ha hspan]
    infer_instance
  refine surjective_of_mk_map_comp_surjective (I := Ideal.span (Set.range MvPowerSeries.X))
    (powerSeriesEval ha) fun y ↦ ?_
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 z)
  refine ⟨MvPowerSeries.C b, ?_⟩
  rw [RingHom.comp_apply, powerSeriesEval_C, Ideal.Quotient.eq, map_span_X_eq ha hspan]
  have := mem_pow_of_evalₐ_eq_zero I hI (n := 1) (x := algebraMap A _ b - z) (by
    rw [_root_.map_sub, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, evalₐ_of, hb, sub_self])
  simpa using this

/-- The completion of a noetherian ring is noetherian (Atiyah–Macdonald, Thm. 10.26). -/
instance isNoetherianRing [IsNoetherianRing A] : IsNoetherianRing (AdicCompletion I A) := by
  obtain ⟨r, a, hspan⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  have ha (i : Fin r) : a i ∈ I := hspan ▸ Ideal.subset_span ⟨i, rfl⟩
  exact isNoetherianRing_of_surjective _ _ (powerSeriesEval ha)
    (powerSeriesEval_surjective ha hspan)

end AdicCompletion

namespace AlgebraicGeometry.Spf

variable (A : Type u) [CommRing A] (I : Ideal A)

/-- For `A` noetherian (not necessarily complete), `Spf A = Spf Â` is a locally noetherian formal
scheme. -/
theorem isLocallyNoetherianFormalScheme_of_isNoetherianRing [IsNoetherianRing A] :
    LocallyRingedSpace.IsLocallyNoetherianFormalScheme (Spf A I) := by
  have hI : I.FG := IsNoetherian.noetherian I
  have : IsAdicComplete (AdicCompletion.completionIdeal I) (AdicCompletion I A) :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr (AdicCompletion.isAdicComplete hI)
  exact LocallyRingedSpace.IsLocallyNoetherianFormalScheme.prop_of_iso
    (isoCompletion A I hI).symm (isLocallyNoetherianFormalScheme _ _)

end AlgebraicGeometry.Spf
