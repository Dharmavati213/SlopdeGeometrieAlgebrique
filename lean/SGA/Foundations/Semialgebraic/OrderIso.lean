/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Order.Group.OrderIso
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extending finite order isomorphisms of `ℝ`

A strictly monotone map from a finite subset of `ℝ` to `ℝ` extends to an order automorphism of
`ℝ` (`Real.exists_orderIso_eqOn`), built from piecewise affine automorphisms which are the
identity on a half-line (`Real.exists_orderIso_eq_self_of_le`).

This is used to compare the sign diagrams of two families of real polynomials: two families have
the same sign diagram when an order automorphism of `ℝ` matches their signs pointwise.

## References

* [L. Hörmander, *The analysis of linear partial differential operators II*, Appendix A.2]
-/

open Set

namespace Real

/-- The piecewise affine bump: identity on `(-∞, u]`, affine from `[u, p]` onto `[u, q]`, a
translation on `[p, ∞)`. -/
private noncomputable def bump (u p q : ℝ) (x : ℝ) : ℝ :=
  if x ≤ u then x else if x ≤ p then u + (x - u) * ((q - u) / (p - u)) else x - p + q

private lemma bump_strictMono {u p q : ℝ} (hp : u < p) (hq : u < q) : StrictMono (bump u p q) := by
  have hpu : 0 < p - u := sub_pos.mpr hp
  have hqu : 0 < q - u := sub_pos.mpr hq
  have hk : 0 < (q - u) / (p - u) := div_pos hqu hpu
  intro x y hxy
  unfold bump
  have hpk : (p - u) * ((q - u) / (p - u)) = q - u := by field_simp
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> try linarith
  · nlinarith [mul_pos (sub_pos.mpr (not_le.mp ‹¬y ≤ u›)) hk]
  · nlinarith [mul_lt_mul_of_pos_right (sub_lt_sub_right hxy u) hk]
  · nlinarith [mul_le_mul_of_nonneg_right (sub_le_sub_right ‹x ≤ p› u) hk.le]

private lemma bump_surjective {u p q : ℝ} (hp : u < p) (hq : u < q) :
    Function.Surjective (bump u p q) := by
  intro y
  have hpu : 0 < p - u := sub_pos.mpr hp
  have hqu : 0 < q - u := sub_pos.mpr hq
  by_cases h1 : y ≤ u
  · exact ⟨y, by simp [bump, h1]⟩
  by_cases h2 : y ≤ q
  · refine ⟨u + (y - u) * ((p - u) / (q - u)), ?_⟩
    have hx1 : ¬ u + (y - u) * ((p - u) / (q - u)) ≤ u := by
      have : 0 < (y - u) * ((p - u) / (q - u)) :=
        mul_pos (sub_pos.mpr (not_le.mp h1)) (div_pos hpu hqu)
      linarith
    have hx2 : u + (y - u) * ((p - u) / (q - u)) ≤ p := by
      have : (y - u) * ((p - u) / (q - u)) ≤ (q - u) * ((p - u) / (q - u)) :=
        mul_le_mul_of_nonneg_right (by linarith) (div_pos hpu hqu).le
      have h' : (q - u) * ((p - u) / (q - u)) = p - u := by field_simp
      linarith
    simp only [bump, hx1, hx2, ite_false, ite_true]
    field_simp
    ring
  · refine ⟨y - q + p, ?_⟩
    have hx1 : ¬ y - q + p ≤ u := by linarith
    have hx2 : ¬ y - q + p ≤ p := by linarith
    simp only [bump, hx1, hx2, ite_false]
    ring

/-- An order automorphism of `ℝ` which is the identity on `(-∞, u]` and sends `p` to `q`, for
`u < p` and `u < q`. -/
lemma exists_orderIso_eq_self_of_le {u p q : ℝ} (hp : u < p) (hq : u < q) :
    ∃ ψ : ℝ ≃o ℝ, (∀ x ≤ u, ψ x = x) ∧ ψ p = q := by
  refine ⟨StrictMono.orderIsoOfSurjective _ (bump_strictMono hp hq) (bump_surjective hp hq),
    fun x hx ↦ ?_, ?_⟩
  · simp [bump, hx]
  · have hpu : 0 < p - u := sub_pos.mpr hp
    simp only [StrictMono.coe_orderIsoOfSurjective, bump, not_le.mpr hp, le_refl, ite_true,
      ite_false]
    field_simp
    ring

/-- A strictly monotone map from a finite subset of `ℝ` to `ℝ` extends to an order automorphism
of `ℝ`. -/
theorem exists_orderIso_eqOn (C : Finset ℝ) {Φ : ℝ → ℝ} (hΦ : StrictMonoOn Φ C) :
    ∃ H : ℝ ≃o ℝ, EqOn H Φ C := by
  induction C using Finset.induction_on_max with
  | empty => exact ⟨OrderIso.refl ℝ, by simp⟩
  | insert c C₀ hc ih =>
    obtain ⟨H₀, hH₀⟩ := ih (hΦ.mono (by simp))
    rcases C₀.eq_empty_or_nonempty with rfl | hne
    · refine ⟨H₀.trans (OrderIso.addRight (Φ c - H₀ c)), ?_⟩
      intro x hx
      rw [Finset.coe_insert, Finset.coe_empty, insert_empty_eq, mem_singleton_iff] at hx
      subst hx
      simp
    · set m := C₀.max' hne
      have hm : m ∈ C₀ := C₀.max'_mem hne
      have hmc : m < c := hc m hm
      have hcC : c ∈ (insert c C₀ : Finset ℝ) := Finset.mem_insert_self c C₀
      have hmC : m ∈ (insert c C₀ : Finset ℝ) := Finset.mem_insert_of_mem hm
      have hq : Φ m < Φ c := hΦ hmC hcC hmc
      have hp : Φ m < H₀ c := by
        rw [← hH₀ hm]
        exact H₀.strictMono hmc
      obtain ⟨ψ, hψu, hψp⟩ := exists_orderIso_eq_self_of_le hp hq
      refine ⟨H₀.trans ψ, fun x hx ↦ ?_⟩
      rw [Finset.coe_insert, mem_insert_iff] at hx
      rcases hx with rfl | hx
      · exact hψp
      · have hxm : x ≤ m := C₀.le_max' x hx
        have hΦx : Φ x ≤ Φ m := hΦ.monotoneOn (Finset.mem_insert_of_mem hx) hmC hxm
        rw [OrderIso.trans_apply, hH₀ hx]
        exact hψu _ hΦx

end Real
