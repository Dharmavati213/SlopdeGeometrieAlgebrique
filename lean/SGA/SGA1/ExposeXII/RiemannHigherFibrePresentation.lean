/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.GAGAFiberSeparating
import SGA.SGA1.ExposeXII.RiemannHigherPresentation
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Topology.Algebra.Polynomial

/-!
# Polynomial presentations of finite coverings of `ℂ ∖ S`

Every finite covering `p : E → ℂ ∖ S` (`S` finite, `E` not necessarily connected) has a continuous
function `F : E → ℂ`, injective on a given fibre, whose fibrewise characteristic polynomial
`∏_{p(e) = z} (Y - F(e))` is `P(z, Y)` for a polynomial `P ∈ ℂ[X][Y]` monic in `Y`
(`RiemannHigher.exists_fibrePoly_eq_fiberCharpoly`).

For connected `E` this is xii51's analytic input `fiberSeparatingFunction` (a holomorphic function
of moderate growth separating the fibre) with the polynomiality of its symmetric functions
(`PuncturedPlane.exists_coeff_fiberCharpoly_mul_eq_eval`), after multiplying `F` by a power of
`∏_{a ∈ S} (z - a)` to clear the denominators; in general by induction on the number of sheets,
splitting off a clopen piece and shifting the values of `F` on it by a constant.

This gives the presentation of every fibre of a family of punctured lines in the induction step of
XII.5.1 in higher dimension (`SGA.SGA1.ExposeXII.RiemannHigher`, step 1 (a)).
-/
noncomputable section

open Polynomial Topology Set

namespace SGA.SGA1.ExposeXII.RiemannHigher

lemma scaleRoots_prod_X_sub_C {R ι : Type*} [CommRing R] [NoZeroDivisors R] (s : Finset ι)
    (g : ι → R) (t : R) :
    (∏ i ∈ s, (X - C (g i))).scaleRoots t = ∏ i ∈ s, (X - C (g i * t)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, mul_scaleRoots_of_noZeroDivisors, ih,
      sub_eq_add_neg, ← C_neg, X_add_C_scaleRoots, sub_eq_add_neg, ← C_neg, neg_mul]

section Connected

variable {S : Finset ℂ} {E : Type} [TopologicalSpace E] {p : E → {z : ℂ // z ∉ S}}
  (hp : IsCoveringMap p) (hfin : ∀ z, (p ⁻¹' {z}).Finite)

open PuncturedPlane

include hp in
/-- A polynomial presentation of a connected finite covering of `ℂ ∖ S`, separating the fibre
over `z₀`. -/
theorem exists_fibrePoly_eq_fiberCharpoly_of_connected [ConnectedSpace E] (z₀ : {z : ℂ // z ∉ S}) :
    ∃ (F : E → ℂ) (P : ℂ[X][X]), Continuous F ∧ P.Monic ∧
      (∀ z : {z : ℂ // z ∉ S}, fibrePoly P z = fiberCharpoly hfin F z) ∧
        InjOn F (p ⁻¹' {z₀}) := by
  classical
  obtain ⟨F₀, hF₀, hhol, hmod, hinj⟩ := fiberSeparatingFunction S E p hp hfin z₀
  let n := (hfin z₀).toFinset.card
  have hcard (z : {z : ℂ // z ∉ S}) : (hfin z).toFinset.card = n := card_fiber_eq hfin hp z z₀
  choose q M hqM using exists_coeff_fiberCharpoly_mul_eq_eval hfin hp hhol hmod
  let M₀ := ∑ k ∈ Finset.range n, M k
  have hM (k : ℕ) (hk : k < n) : M k ≤ M₀ :=
    Finset.single_le_sum (f := M) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_range.mpr hk)
  let f : ℂ[X] := punctures S
  let lam : {z : ℂ // z ∉ S} → ℂ := fun z ↦ f.eval (z : ℂ) ^ M₀
  let F : E → ℂ := fun e ↦ F₀ e * lam (p e)
  have hfz (z : {z : ℂ // z ∉ S}) : ∏ a ∈ S, ((z : ℂ) - a) = f.eval (z : ℂ) := by
    simp [f, punctures, eval_prod]
  have hcp (z : {z : ℂ // z ∉ S}) :
      fiberCharpoly hfin F z = (fiberCharpoly hfin F₀ z).scaleRoots (lam z) := by
    rw [fiberCharpoly, fiberCharpoly, scaleRoots_prod_X_sub_C]
    refine Finset.prod_congr rfl fun e he ↦ ?_
    rw [(hfin z).mem_toFinset, mem_preimage, mem_singleton_iff] at he
    simp only [F, he]
  let P : ℂ[X][X] := X ^ n + ∑ k ∈ Finset.range n,
    C (q k * f ^ (M₀ - M k) * f ^ (M₀ * (n - k - 1))) * X ^ k
  have hPmonic : P.Monic := by
    refine monic_X_pow_add ?_
    refine (degree_sum_le _ _).trans_lt ?_
    refine Finset.sup_lt_iff (WithBot.bot_lt_coe n) |>.mpr fun k hk ↦ ?_
    exact (degree_C_mul_X_pow_le _ _).trans_lt (WithBot.coe_lt_coe.mpr (Finset.mem_range.mp hk))
  refine ⟨F, P,
    hF₀.mul (((f.continuous.comp continuous_subtype_val).pow M₀).comp hp.continuous), hPmonic,
    fun z ↦ ?_, fun e he e' he' h ↦ ?_⟩
  · rw [hcp]
    ext k
    rw [coeff_scaleRoots, natDegree_fiberCharpoly, hcard]
    simp only [P, fibrePoly, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X,
      Polynomial.map_sum, Polynomial.map_mul, Polynomial.map_C, coe_evalRingHom, coeff_add,
      coeff_X_pow, finset_sum_coeff, coeff_C_mul_X_pow, eval_mul, eval_pow]
    rcases lt_trichotomy k n with hk | rfl | hk
    · rw [if_neg hk.ne, zero_add, Finset.sum_eq_single k (fun j _ hj ↦ if_neg (Ne.symm hj))
        (fun h ↦ (h (Finset.mem_range.mpr hk)).elim), if_pos rfl]
      rw [← hqM k z]
      have hp : (∏ a ∈ S, ((z : ℂ) - a) ^ M k) = (f.eval (z : ℂ)) ^ M k := by
        rw [← hfz, Finset.prod_pow]
      rw [hp, mul_assoc, mul_assoc, ← pow_add]
      simp only [lam]
      -- `c * (e^{M k} * e^{M₀ - M k + M₀ * (n - k - 1)}) = c * (e^{M₀})^{(n - k)}`.
      rw [← pow_add, ← pow_mul]
      rw [show M k + (M₀ - M k + M₀ * (n - k - 1)) = M₀ * (n - k) by
        have hMk : M k ≤ M₀ := hM k hk
        have h1 : n - k = n - k - 1 + 1 := by omega
        calc
          M k + (M₀ - M k + M₀ * (n - k - 1))
              = M k + (M₀ - M k) + M₀ * (n - k - 1) := by rw [Nat.add_assoc]
          _ = M₀ + M₀ * (n - k - 1) := by rw [Nat.add_sub_cancel' hMk]
          _ = M₀ * (n - k - 1) + M₀ := by rw [Nat.add_comm]
          _ = M₀ * (n - k - 1) + M₀ * 1 := by rw [Nat.mul_one]
          _ = M₀ * (n - k - 1 + 1) := by rw [← Nat.mul_add]
          _ = M₀ * (n - k) := by rw [← h1]]
    · rw [if_pos rfl, Finset.sum_eq_zero fun j hj ↦ if_neg (Finset.mem_range.mp hj).ne', add_zero,
        Nat.sub_self, pow_zero, mul_one]
      exact ((monic_fiberCharpoly hfin F₀ z).coeff_natDegree.symm.trans (by
        rw [natDegree_fiberCharpoly, hcard]))
    · rw [if_neg hk.ne', Finset.sum_eq_zero fun j hj ↦ if_neg (by
        have := Finset.mem_range.mp hj; omega), add_zero]
      rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_fiberCharpoly, hcard]; exact hk),
        zero_mul]
  · have hpe : p e = z₀ := he
    have hpe' : p e' = z₀ := he'
    have hlam : lam z₀ ≠ 0 := pow_ne_zero _ (eval_punctures_ne_zero z₀.2)
    simp only [F, hpe, hpe'] at h
    exact hinj he he' (mul_right_cancel₀ hlam h)

end Connected

end SGA.SGA1.ExposeXII.RiemannHigher
