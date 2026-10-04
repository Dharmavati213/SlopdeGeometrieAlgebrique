/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Polynomial.CancelLeads
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Tactic.LinearCombination

/-!
# Pseudo-division of polynomials

Over a commutative ring `R`, the *pseudo-remainder* `prem P Q` of `P` by `Q` satisfies
`lc(Q)ᵐ • P = q * Q + prem P Q` for some `m` and `q` (`Polynomial.exists_prem_eq`), and has degree
less than `Q` when `Q` is not constant (`Polynomial.natDegree_prem_lt`). Unlike the remainder, it
is defined over any ring, and its formation commutes with ring homomorphisms in the sense that the
defining identity can be specialized: this is how remainders of polynomials whose coefficients
depend on parameters are handled in Hörmander's proof of the Tarski–Seidenberg theorem.

One step of the pseudo-division is mathlib's `Polynomial.cancelLeads`; this file iterates it.

## References

* [D. E. Knuth, *The Art of Computer Programming*, vol. 2, §4.6.1]
-/

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- Pseudo-division with fuel `n`: cancel the leading term of `P` by a multiple of `Q`
(`Q.cancelLeads P`) as long as `deg P ≥ deg Q`. -/
noncomputable def premAux (Q : R[X]) : ℕ → R[X] → R[X]
  | 0, P => P
  | n + 1, P => if P.natDegree < Q.natDegree then P else premAux Q n (Q.cancelLeads P)

/-- The *pseudo-remainder* of `P` by `Q`. -/
noncomputable def prem (P Q : R[X]) : R[X] := premAux Q (P.natDegree + 1) P

lemma exists_premAux_eq (Q : R[X]) (n : ℕ) (P : R[X]) :
    ∃ (m : ℕ) (q : R[X]), C Q.leadingCoeff ^ m * P = q * Q + premAux Q n P := by
  induction n generalizing P with
  | zero => exact ⟨0, 0, by simp [premAux]⟩
  | succ n ih =>
    by_cases hP : P.natDegree < Q.natDegree
    · exact ⟨0, 0, by simp [premAux, hP]⟩
    · obtain ⟨m, q, hq⟩ := ih (Q.cancelLeads P)
      refine ⟨m + 1, q + C Q.leadingCoeff ^ m * C P.leadingCoeff *
        X ^ (P.natDegree - Q.natDegree), ?_⟩
      simp only [premAux, hP, ite_false]
      have e : Q.cancelLeads P = C Q.leadingCoeff * P -
          C P.leadingCoeff * X ^ (P.natDegree - Q.natDegree) * Q := by
        simp [cancelLeads, Nat.sub_eq_zero_of_le (not_lt.mp hP)]
      linear_combination hq - C Q.leadingCoeff ^ m * e

/-- The defining identity of the pseudo-remainder: `lc(Q)ᵐ P = q Q + prem P Q`. -/
theorem exists_prem_eq (P Q : R[X]) :
    ∃ (m : ℕ) (q : R[X]), C Q.leadingCoeff ^ m * P = q * Q + prem P Q :=
  exists_premAux_eq Q _ P

lemma natDegree_premAux_lt {Q : R[X]} (hQ : 0 < Q.natDegree) (n : ℕ) (P : R[X])
    (hn : P.natDegree < n + Q.natDegree) : (premAux Q n P).natDegree < Q.natDegree := by
  induction n generalizing P with
  | zero => simpa [premAux] using hn
  | succ n ih =>
    by_cases hP : P.natDegree < Q.natDegree
    · simp [premAux, hP]
    · simp only [premAux, hP, ite_false]
      refine ih _ ?_
      have := natDegree_cancelLeads_lt_of_natDegree_le_natDegree (not_lt.mp hP)
        (hQ.trans_le (not_lt.mp hP))
      omega

/-- The pseudo-remainder by a nonconstant polynomial has smaller degree. -/
theorem natDegree_prem_lt (P : R[X]) {Q : R[X]} (hQ : 0 < Q.natDegree) :
    (prem P Q).natDegree < Q.natDegree :=
  natDegree_premAux_lt hQ _ P (by omega)

end Polynomial
