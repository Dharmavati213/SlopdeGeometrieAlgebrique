/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# A domain-lifting input for regular local parameters

Let `R` be a noetherian local ring and `x` an element of its maximal ideal.
If `x` avoids every minimal prime and `R/(x)` is a domain, then `x` is a
nonzerodivisor and `R` is a domain. The proof uses actual annihilators,
primality of the original principal ideal, and Krull's intersection theorem.

This is a general induction input, not a replacement definition of a regular
local ring or an assumed residue-field Ext computation for IV.5.4.
-/

noncomputable section

universe u

open IsLocalRing

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- Avoidance of the actual minimal primes puts each annihilator of a
power of `x` inside the nilradical. No noetherianity is needed here. -/
theorem annihilated_pow_mem_nilradical_of_avoids_minimalPrimes (x : R)
    (hx : ∀ p ∈ minimalPrimes R, x ∉ p) (n : ℕ) (a : R)
    (ha : x ^ n * a = 0) : a ∈ (⊥ : Ideal R).radical := by
  rw [← Ideal.sInf_minimalPrimes, Ideal.mem_sInf]
  intro p hp
  exact (hp.isPrime.mem_or_mem (ha ▸ p.zero_mem)).resolve_left
    (fun hxp ↦ hx p hp (hp.isPrime.mem_of_pow_mem n hxp))

variable [IsNoetherianRing R] [IsLocalRing R]

private theorem principal_pow_annihilator_eq_zero (x : R)
    (hx : x ∈ maximalIdeal R)
    (hdiv : ∀ (n : ℕ) (a : R), x ^ n * a = 0 → a ∈ Ideal.span {x})
    (n : ℕ) (a : R) (ha : x ^ n * a = 0) : a = 0 := by
  let P : Ideal R := Ideal.span {x}
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hpow : ∀ k : ℕ, ∀ (n : ℕ) (a : R), x ^ n * a = 0 → a ∈ P ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro n a ha
      obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp (hdiv n a ha)
      have hbzero : x ^ (n + 1) * b = 0 := by
        rw [pow_succ, mul_assoc, ← hb]
        exact ha
      rw [hb, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton x))
        (ih (n + 1) b hbzero)
  have hmem : a ∈ ⨅ k : ℕ, P ^ k := Ideal.mem_iInf.mpr (fun k ↦ hpow k n a ha)
  rwa [P.iInf_pow_eq_bot_of_isLocalRing hP, Ideal.mem_bot] at hmem

/-- A domain principal quotient and minimal-prime avoidance genuinely
imply injectivity of multiplication by the original element. -/
theorem isSMulRegular_of_domain_quotient_of_avoids_minimalPrimes (x : R)
    (hx : x ∈ maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, x ∉ p)
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))] : IsSMulRegular R x := by
  have hP : (Ideal.span ({x} : Set R)).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance
  have hdiv (n : ℕ) (a : R) (ha : x ^ n * a = 0) : a ∈ Ideal.span {x} :=
    (hP.radical_le_iff.mpr bot_le)
      (annihilated_pow_mem_nilradical_of_avoids_minimalPrimes x hmin n a ha)
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro a ha
  exact principal_pow_annihilator_eq_zero x hx hdiv 1 a (by simpa using ha)

private theorem right_eq_zero_of_mul_eq_zero_of_not_mem_principal
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    (hPprime : (Ideal.span ({x} : Set R)).IsPrime)
    (a b : R) (ha : a ∉ Ideal.span ({x} : Set R)) (hab : a * b = 0) : b = 0 := by
  let P : Ideal R := Ideal.span {x}
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hpow : ∀ k : ℕ, ∀ b : R, a * b = 0 → b ∈ P ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro b hab
      have hb : b ∈ P := (hPprime.mem_or_mem (hab ▸ P.zero_mem)).resolve_left ha
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      have hac : a * c = 0 := hreg.right_eq_zero_of_smul (by
        change x * (a * c) = 0
        rw [mul_left_comm, ← hc]
        exact hab)
      rw [hc, pow_succ']
      exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton x)) (ih c hac)
  have hmem : b ∈ ⨅ k : ℕ, P ^ k := Ideal.mem_iInf.mpr (fun k ↦ hpow k b hab)
  rwa [P.iInf_pow_eq_bot_of_isLocalRing hP, Ideal.mem_bot] at hmem

/-- Domain structure lifts through an actual principal quotient by a
regular element in the maximal ideal. Both Krull-intersection arguments
take place in the original ring. -/
theorem isDomain_of_regular_domain_quotient (x : R)
    (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular R x)
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))] : IsDomain R := by
  let P : Ideal R := Ideal.span {x}
  have hP : P ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
    ((Ideal.span_singleton_le_iff_mem _).mpr hx)
  have hPprime : P.IsPrime := (Ideal.Quotient.isDomain_iff_prime P).mp inferInstance
  have : NoZeroDivisors R := ⟨by
    intro a b hab
    by_cases hb : b = 0
    · exact Or.inr hb
    left
    have hpow : ∀ k : ℕ, ∀ a : R, a * b = 0 → a ∈ P ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro a hab
        have ha : a ∈ P := by
          by_contra ha
          exact hb (right_eq_zero_of_mul_eq_zero_of_not_mem_principal
            x hx hreg hPprime a b ha hab)
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp ha
        have hcb : c * b = 0 := hreg.right_eq_zero_of_smul (by
          change x * (c * b) = 0
          rw [← mul_assoc, ← hc]
          exact hab)
        rw [hc, pow_succ']
        exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton x)) (ih c hcb)
    have hmem : a ∈ ⨅ k : ℕ, P ^ k := Ideal.mem_iInf.mpr (fun k ↦ hpow k a hab)
    rwa [P.iInf_pow_eq_bot_of_isLocalRing hP, Ideal.mem_bot] at hmem⟩
  exact NoZeroDivisors.to_isDomain R

/-- The combined induction step: avoidance of all minimal primes and a
domain principal quotient imply both regularity of `x` and a domain `R`. -/
theorem regular_and_isDomain_of_domain_quotient_of_avoids_minimalPrimes (x : R)
    (hx : x ∈ maximalIdeal R) (hmin : ∀ p ∈ minimalPrimes R, x ∉ p)
    [IsDomain (R ⧸ Ideal.span ({x} : Set R))] : IsSMulRegular R x ∧ IsDomain R := by
  have hreg := isSMulRegular_of_domain_quotient_of_avoids_minimalPrimes x hx hmin
  exact ⟨hreg, isDomain_of_regular_domain_quotient x hx hreg⟩

end SGA.SGA2.ExposeIII
