/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.RegularLocalParameterChoice
import SGA.SGA2.ExposeIII.RegularLocalDomainLift

/-!
# Actual regular local rings are domains

Dimension induction uses finite prime avoidance, a lifted cotangent basis,
the regularity and dimension of the actual principal quotient, and Krull
intersection. Thus the nonzerodivisor property is derived from mathlib's
original regular-local-ring class rather than supplied as a new hypothesis.
-/

noncomputable section
universe u
open IsLocalRing

namespace SGA.SGA2.ExposeIII

private theorem regularLocal_isDomain_induction (n : ℕ) :
    ∀ (S : Type u) [CommRing S] [IsRegularLocalRing S],
      ringKrullDim S = n → IsDomain S := by
  induction n with
  | zero =>
    intro S _ _ hd
    let := (regularLocal_isField_of_dimension_zero hd).toField
    infer_instance
  | succ n ih =>
    intro S _ _ hd
    have hpos : 0 < ringKrullDim S := by rw [hd]; exact_mod_cast Nat.succ_pos n
    obtain ⟨x, hx, hx2, hmin⟩ := local_exists_parameter_avoiding_minimalPrimes hpos
    obtain ⟨s, hxs, hs, hc⟩ := local_exists_minimal_generators_containing x hx hx2
    obtain ⟨hQreg, hQdim⟩ := regularLocal_quotient_minimal_generator s hs
      (by rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]) x hxs
    let := hQreg
    have hQn : ringKrullDim (S ⧸ Ideal.span ({x} : Set S)) = (n : WithBot ℕ∞) := by
      apply ENat.WithBot.add_one_cancel.mp
      rw [hQdim, hd, Nat.cast_add_one]
    let := ih (S ⧸ Ideal.span ({x} : Set S)) hQn
    exact (regular_and_isDomain_of_domain_quotient_of_avoids_minimalPrimes x hx hmin).2

/-- Every actual regular local ring is an integral domain. -/
theorem regularLocal_isDomain (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsDomain R := by
  obtain ⟨s, _, hc⟩ := regularLocal_exists_minimal_generators (R := R)
  exact regularLocal_isDomain_induction s.card R hc.symm

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- A nonzero cotangent class is represented by a genuine nonzerodivisor
in a regular local ring. -/
theorem regularLocal_isSMulRegular_of_not_mem_square (x : R)
    (hx2 : x ∉ maximalIdeal R ^ 2) : IsSMulRegular R x := by
  let := regularLocal_isDomain R
  have hx0 : x ≠ 0 := fun h ↦ hx2 (h ▸ (maximalIdeal R ^ 2).zero_mem)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  exact (mul_eq_zero.mp ha).resolve_left hx0

/-- The full first-parameter induction step, from genuine regularity:
multiplication is injective and the original quotient is regular of
dimension one less. -/
theorem regularLocal_parameter_quotient (x : R) (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) :
    IsSMulRegular R x ∧ IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  obtain ⟨s, hxs, hs, hc⟩ := local_exists_minimal_generators_containing x hx hx2
  exact ⟨regularLocal_isSMulRegular_of_not_mem_square x hx2,
    regularLocal_quotient_minimal_generator s hs
      (by rw [hc, IsRegularLocalRing.spanFinrank_maximalIdeal]) x hxs⟩

end SGA.SGA2.ExposeIII
