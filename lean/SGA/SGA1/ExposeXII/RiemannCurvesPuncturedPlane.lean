/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannCurvesSymmetric
import SGA.SGA1.ExposeXII.RiemannExistence

/-!
# SGA 1, Exposé XII, 5.1 for curves: the punctured plane `ℂ ∖ S`

For `S ⊂ ℂ` finite, the affine curve `ℂ ∖ S` is `Spec ℂ[t][1/f_S]`, `f_S = ∏_{a ∈ S} (t - a)`
(`PuncturedPlane.coordRing`), and its `ℂ`-points are `ℂ ∖ S` (`PuncturedPlane.homeomorph`): a point
is determined by the image of `t`, which avoids `S` because `f_S` is invertible. An element
`q / f_Sᵐ` of the coordinate ring is the function `z ↦ q(z) / f_S(z)ᵐ` (`evalAt_mk'`).

With `PuncturedPlane.exists_coeff_fiberCharpoly_mul_eq_eval`, the coefficients of the fibrewise
characteristic polynomial of a holomorphic function of moderate growth on a finite covering of
`ℂ ∖ S` are elements of the coordinate ring (`exists_coordRing_eq_coeff_fiberCharpoly`): the
starting point of the algebraic half of XII.5.1 for `ℂ ∖ S`.
-/

noncomputable section

open Polynomial Topology Set

namespace SGA.SGA1.ExposeXII

namespace PuncturedPlane

variable (S : Finset ℂ)

/-- `f_S = ∏_{a ∈ S} (t - a)`, the polynomial vanishing exactly on `S`. -/
abbrev punctures : ℂ[X] := ∏ a ∈ S, (X - C a)

/-- The coordinate ring `ℂ[t][1/f_S]` of `ℂ ∖ S`. -/
abbrev coordRing : Type := Localization.Away (punctures S)

variable {S}

lemma eval_punctures_ne_zero {z : ℂ} (hz : z ∉ S) : (punctures S).eval z ≠ 0 := by
  rw [eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun a ha ↦ by
    rw [eval_sub, eval_X, eval_C]
    exact sub_ne_zero.mpr fun h ↦ hz (by rwa [h])

lemma notMem_of_eval_punctures_ne_zero {z : ℂ} (hz : (punctures S).eval z ≠ 0) : z ∉ S := by
  intro hzS
  rw [eval_prod] at hz
  exact hz (Finset.prod_eq_zero hzS (by simp))

/-- Evaluation at a point `z ∉ S`, as a `ℂ`-point of `ℂ[t][1/f_S]`. -/
def evalAt (z : {z : ℂ // z ∉ S}) : Points ℂ (coordRing S) :=
  Points.ofAlgHom (IsLocalization.Away.liftAlgHom (punctures S) (f := Polynomial.aeval z.1)
    (Ne.isUnit (by rw [Polynomial.coe_aeval_eq_eval]; exact eval_punctures_ne_zero z.2)))

lemma evalAt_algebraMap (z : {z : ℂ // z ∉ S}) (q : ℂ[X]) :
    evalAt z (algebraMap ℂ[X] (coordRing S) q) = q.eval z.1 := by
  change IsLocalization.Away.liftAlgHom _ _ (algebraMap ℂ[X] (coordRing S) q) = _
  rw [IsLocalization.Away.liftAlgHom_apply, IsLocalization.Away.lift_eq]
  simp

lemma evalAt_mk' (z : {z : ℂ // z ∉ S}) (q : ℂ[X]) (m : ℕ) :
    evalAt z (IsLocalization.mk' (coordRing S) q (⟨punctures S ^ m, m, rfl⟩ :
      Submonoid.powers (punctures S))) = q.eval z.1 / (punctures S).eval z.1 ^ m := by
  have h := congrArg (evalAt z) (IsLocalization.mk'_spec (coordRing S) q
    (⟨punctures S ^ m, m, rfl⟩ : Submonoid.powers (punctures S)))
  rw [map_mul, evalAt_algebraMap, evalAt_algebraMap, eval_pow] at h
  rw [eq_div_iff (pow_ne_zero m (eval_punctures_ne_zero z.2)), ← h]

lemma apply_algebraMap (φ : Points ℂ (coordRing S)) (q : ℂ[X]) :
    φ (algebraMap ℂ[X] (coordRing S) q) = q.eval (φ (algebraMap ℂ[X] (coordRing S) X)) := by
  let ψ : ℂ[X] →ₐ[ℂ] ℂ := φ.toAlgHom.comp (IsScalarTower.toAlgHom ℂ ℂ[X] (coordRing S))
  change ψ q = q.eval (ψ X)
  rw [← Polynomial.coe_aeval_eq_eval, Polynomial.aeval_algHom_apply, Polynomial.aeval_X_left,
    AlgHom.id_apply]

lemma apply_X_notMem (φ : Points ℂ (coordRing S)) :
    φ (algebraMap ℂ[X] (coordRing S) X) ∉ S := by
  refine notMem_of_eval_punctures_ne_zero ?_
  rw [← apply_algebraMap]
  exact ((IsLocalization.Away.algebraMap_isUnit (punctures S)).map φ).ne_zero

lemma continuous_evalAt_apply (a : coordRing S) :
    Continuous fun z : {z : ℂ // z ∉ S} ↦ evalAt z a := by
  obtain ⟨⟨q, ⟨_, m, rfl⟩⟩, rfl⟩ :=
    IsLocalization.mk'_surjective (Submonoid.powers (punctures S)) a
  simp_rw [evalAt_mk']
  exact ((q.continuous.comp continuous_subtype_val).div
    (((punctures S).continuous.comp continuous_subtype_val).pow m)
    fun z ↦ pow_ne_zero m (eval_punctures_ne_zero z.2))

variable (S) in
/-- The `ℂ`-points of `Spec ℂ[t][1/f_S]` are `ℂ ∖ S`. -/
def homeomorph : Points ℂ (coordRing S) ≃ₜ {z : ℂ // z ∉ S} where
  toFun φ := ⟨φ (algebraMap ℂ[X] (coordRing S) X), apply_X_notMem φ⟩
  invFun := evalAt
  left_inv φ := by
    refine Points.ext fun a ↦ ?_
    obtain ⟨⟨q, ⟨_, m, rfl⟩⟩, rfl⟩ :=
      IsLocalization.mk'_surjective (Submonoid.powers (punctures S)) a
    dsimp only
    rw [evalAt_mk']
    have h := congrArg φ (IsLocalization.mk'_spec (coordRing S) q
      (⟨punctures S ^ m, m, rfl⟩ : Submonoid.powers (punctures S)))
    rw [map_mul, apply_algebraMap φ q, apply_algebraMap φ (punctures S ^ m), eval_pow] at h
    rw [div_eq_iff (pow_ne_zero m (eval_punctures_ne_zero (apply_X_notMem φ))), ← h]
  right_inv z := Subtype.ext (by
    change evalAt z (algebraMap ℂ[X] (coordRing S) X) = z.1
    rw [evalAt_algebraMap, eval_X])
  continuous_toFun := (Points.continuous_apply _).subtype_mk _
  continuous_invFun := Points.continuous_iff.mpr continuous_evalAt_apply

@[simp] lemma homeomorph_symm_apply (z : {z : ℂ // z ∉ S}) : (homeomorph S).symm z = evalAt z :=
  rfl

section Charpoly

variable {E : Type*} [TopologicalSpace E] {p : E → {z : ℂ // z ∉ S}}
  (hfin : ∀ z, (p ⁻¹' {z}).Finite) {F : E → ℂ}

/-- The coefficients of the fibrewise characteristic polynomial of a holomorphic `F` of moderate
growth are elements of the coordinate ring `ℂ[t][1/f_S]` of `ℂ ∖ S`. -/
theorem exists_coordRing_eq_coeff_fiberCharpoly (hp : IsCoveringMap p) (hF : IsHolomorphic p F)
    (hb : IsModerate p F) (k : ℕ) :
    ∃ c : coordRing S, ∀ z, evalAt z c = (fiberCharpoly hfin F z).coeff k := by
  obtain ⟨q, M, hqM⟩ := exists_coeff_fiberCharpoly_mul_eq_eval hfin hp hF hb k
  refine ⟨IsLocalization.mk' (coordRing S) q
    (⟨punctures S ^ M, M, rfl⟩ : Submonoid.powers (punctures S)), fun z ↦ ?_⟩
  rw [evalAt_mk', div_eq_iff (pow_ne_zero M (eval_punctures_ne_zero z.2)), ← hqM z, eval_prod,
    Finset.prod_pow]
  simp

omit [TopologicalSpace E] in
private lemma coeff_sum_range {R : Type*} [CommRing R] (c : ℕ → R) (d m : ℕ) :
    (∑ k ∈ Finset.range d, C (c k) * X ^ k).coeff m = if m < d then c m else 0 := by
  rw [finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  simp [Finset.mem_range]

/-- XII.5.1 for `ℂ ∖ S`, first step of this project's proof (not SGA's route; see
`SGA.SGA1.ExposeXII.RiemannCurves`): the fibrewise characteristic polynomial of a holomorphic `F`
of moderate growth is a monic polynomial over `ℂ[t][1/f_S]` (so `F` is integral over the
coordinate ring of `ℂ ∖ S`). -/
theorem exists_monic_map_evalAt_eq_fiberCharpoly (hp : IsCoveringMap p) (hF : IsHolomorphic p F)
    (hb : IsModerate p F) :
    ∃ P : (coordRing S)[X], P.Monic ∧
      ∀ z, P.map (evalAt z).toRingHom = fiberCharpoly hfin F z := by
  classical
  obtain ⟨z₁, hz₁⟩ := S.exists_notMem
  let d := (hfin ⟨z₁, hz₁⟩).toFinset.card
  have hd (z : {z : ℂ // z ∉ S}) : (fiberCharpoly hfin F z).natDegree = d := by
    rw [natDegree_fiberCharpoly, card_fiber_eq hfin hp z]
  choose c hc using exists_coordRing_eq_coeff_fiberCharpoly hfin hp hF hb
  let Q : (coordRing S)[X] := ∑ k ∈ Finset.range d, C (c k) * X ^ k
  have hQ : Q.degree < d := by
    rw [degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_sum_range, ite_eq_right (not_lt.mpr hm)]
  refine ⟨X ^ d + Q, monic_X_pow_add hQ, fun z ↦ Polynomial.ext fun m ↦ ?_⟩
  rw [coeff_map, coeff_add, coeff_X_pow, coeff_sum_range]
  have hmon := monic_fiberCharpoly hfin F z
  rcases lt_trichotomy m d with hm | rfl | hm
  · rw [ite_eq_right hm.ne, ite_eq_left hm, zero_add]
    exact hc m z
  · rw [ite_eq_left rfl, ite_eq_right (lt_irrefl _), add_zero, map_one, ← hd z]
    exact hmon.coeff_natDegree.symm
  · rw [ite_eq_right hm.ne', ite_eq_right (not_lt.mpr hm.le), add_zero, map_zero,
      coeff_eq_zero_of_natDegree_lt ((hd z).trans_lt hm)]

end Charpoly

end PuncturedPlane

end SGA.SGA1.ExposeXII
