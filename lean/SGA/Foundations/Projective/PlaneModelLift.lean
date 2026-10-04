/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraic elements over a complete ring with algebraically closed residue field

Let `R` be a domain, complete for the `π`-adic topology, whose residue ring `R ⧸ (π)` is an
algebraically closed field `k` (e.g. the Witt vectors `W(k)` with `π = p`). Let `O` be a domain
which is an `R`-algebra, separated for the `π`-adic topology, in which `π O` is prime. Then every
element `β ∈ O` which is a root of a polynomial over `R` with nonzero reduction modulo `π` lies in
(the image of) `R` (`IsAdicComplete.mem_range_algebraMap_of_aeval_eq_zero`).

Proof: the residue of such a `β` in the domain `O ⧸ π O` is a root of a nonzero polynomial over
`k`, hence lies in `k`; so `β = r₀ + π β₁` with `r₀ ∈ R`, `β₁ ∈ O`, and `β₁` is again a root of a
polynomial with nonzero reduction. Iterating, `β ≡ r₀ + r₁ π + ⋯ + r_{m-1} π^{m-1} (mod π^m O)`
for all `m`; the series converges in `R` to some `r`, and `β - r ∈ ⋂ π^m O = 0`.

This is the algebraic input for the geometric connectedness of the generic fibre of a lift of a
plane curve to `W(k)` (applied to the ring of a chart of the lifted curve, whose reduction modulo
`π` is the ring of a chart of the plane curve): it shows that the global sections of the lifted
curve are `R`, with no valuation theory (no uniqueness of extensions of valuations).

## References

* [EGA III₁, 4.3.12] (connectedness of fibres; the form used here is elementary)
-/

open Polynomial

namespace Polynomial

variable {R k : Type*} [CommRing R] [Field k]

/-- Over a ring `R` separated for the `π`-adic topology, a nonzero polynomial is `π^j` times a
polynomial whose reduction modulo `π` (through `φ : R → k` with kernel `(π)`) is nonzero. -/
theorem exists_eq_C_pow_mul_of_ne_zero {π : R}
    (hsep : ∀ r : R, (∀ n, r ∈ Ideal.span {π ^ n}) → r = 0) (φ : R →+* k)
    (hker : RingHom.ker φ = Ideal.span {π}) {Q : R[X]} (hQ : Q ≠ 0) :
    ∃ (j : ℕ) (Q' : R[X]), Q = C (π ^ j) * Q' ∧ Q'.map φ ≠ 0 := by
  classical
  -- some coefficient of `Q` is not divisible by a power of `π`
  obtain ⟨i, hi⟩ : ∃ i, Q.coeff i ≠ 0 := by
    by_contra h
    push Not at h
    exact hQ (Polynomial.ext fun i ↦ by simp [h i])
  have hex : ∃ n, ¬ ∃ Q' : R[X], Q = C (π ^ n) * Q' := by
    by_contra h
    push Not at h
    refine hi (hsep _ fun n ↦ ?_)
    obtain ⟨Q', hQ'⟩ := h n
    rw [hQ', coeff_C_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have h0 : Nat.find hex ≠ 0 := by
    intro h
    have := Nat.find_spec hex
    rw [h] at this
    exact this ⟨Q, by simp⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero h0
  obtain ⟨Q', hQ'⟩ : ∃ Q' : R[X], Q = C (π ^ j) * Q' := by
    have := Nat.find_min hex (show j < Nat.find hex by omega)
    push Not at this
    exact this
  refine ⟨j, Q', hQ', fun hmap ↦ ?_⟩
  -- all coefficients of `Q'` are divisible by `π`
  have hmem : Q' ∈ Ideal.map (C : R →+* R[X]) (Ideal.span {π}) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [← hker, RingHom.mem_ker, ← coeff_map, hmap, coeff_zero]
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hmem
  obtain ⟨Q'', rfl⟩ := hmem
  have := Nat.find_spec hex
  rw [hj] at this
  exact this ⟨Q'', by rw [hQ', ← mul_assoc, ← C_mul, ← pow_succ]⟩

end Polynomial

namespace IsAdicComplete

variable {R O k : Type*} [CommRing R] [IsDomain R] [CommRing O] [IsDomain O] [Algebra R O]
  [Field k] [IsAlgClosed k] {π : R} (φ : R →+* k) (hφ : Function.Surjective φ)
  (hker : RingHom.ker φ = Ideal.span {π}) (hprime : (Ideal.span {algebraMap R O π}).IsPrime)

omit [IsDomain R] [IsDomain O] in
include hφ hker hprime in
/-- The residue step: a root `γ ∈ O` of a polynomial over `R` with nonzero reduction is congruent
modulo `π O` to an element of `R`. -/
theorem exists_sub_mem_span_of_aeval_eq_zero {γ : O} {Q : R[X]} (hQ : Q.map φ ≠ 0)
    (hγ : aeval γ Q = 0) : ∃ r : R, γ - algebraMap R O r ∈ Ideal.span {algebraMap R O π} := by
  classical
  set I := Ideal.span {algebraMap R O π}
  set q := Ideal.Quotient.mk I
  -- a lift `ℓ : k → R` of `φ`
  set ℓ := Function.surjInv hφ
  have hℓ : ∀ a, φ (ℓ a) = a := Function.surjInv_eq hφ
  set P := Q.map φ
  -- `P = c ∏ (X - a)` over the roots `a` of `P`
  have hP : C P.leadingCoeff * (P.roots.map fun a ↦ X - C a).prod = P :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  set Q₀ : R[X] := C (ℓ P.leadingCoeff) * (P.roots.map fun a ↦ X - C (ℓ a)).prod
  have hQ₀ : Q₀.map φ = P := by
    rw [← hP, Polynomial.map_mul, map_C, hℓ, Polynomial.map_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun a _ ↦ ?_
    simp [hℓ]
  have hQ₀γ' : aeval γ Q₀ = algebraMap R O (ℓ P.leadingCoeff) *
      (P.roots.map fun a ↦ γ - algebraMap R O (ℓ a)).prod := by
    simp [Q₀, map_multiset_prod, Multiset.map_map]
  clear_value Q₀
  -- `Q - Q₀` is divisible by `π`
  have hdiff : Q - Q₀ ∈ Ideal.map (C : R →+* R[X]) (Ideal.span {π}) := by
    rw [Ideal.mem_map_C_iff]
    intro n
    rw [← hker, RingHom.mem_ker, ← coeff_map, Polynomial.map_sub, hQ₀, sub_self, coeff_zero]
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at hdiff
  obtain ⟨H, hH⟩ := hdiff
  have hQ₀γ : aeval γ Q₀ ∈ I := by
    have h := congrArg (aeval γ) hH
    rw [map_sub, hγ, zero_sub, map_mul, aeval_C] at h
    have : aeval γ Q₀ = -(algebraMap R O π * aeval γ H) := by rw [← h, neg_neg]
    rw [this]
    exact I.neg_mem (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  -- in the domain `O ⧸ π O`, one of the factors vanishes
  have hq : q (aeval γ Q₀) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hQ₀γ
  have hP0 : P ≠ 0 := hQ
  rw [hQ₀γ', map_mul, mul_eq_zero] at hq
  rcases hq with hc | hprod
  · -- the leading coefficient is not divisible by `π`
    exfalso
    have hlc : P.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hP0
    obtain ⟨s, hs⟩ : ∃ s : R, ℓ P.leadingCoeff * s - 1 ∈ Ideal.span {π} := by
      obtain ⟨s, hs⟩ := hφ (P.leadingCoeff)⁻¹
      refine ⟨s, ?_⟩
      rw [← hker, RingHom.mem_ker, map_sub, map_mul, hℓ, hs, map_one,
        mul_inv_cancel₀ hlc, sub_self]
    have h1 : algebraMap R O (ℓ P.leadingCoeff * s - 1) ∈ I := by
      rw [Ideal.mem_span_singleton] at hs ⊢
      obtain ⟨t, ht⟩ := hs
      exact ⟨algebraMap R O t, by rw [ht, map_mul]⟩
    have h2 : algebraMap R O (ℓ P.leadingCoeff) ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hc
    have h3 : (1 : O) ∈ I := by
      have : (1 : O) = algebraMap R O (ℓ P.leadingCoeff) * algebraMap R O s -
          algebraMap R O (ℓ P.leadingCoeff * s - 1) := by
        rw [map_sub, map_mul, map_one]; ring
      rw [this]
      exact I.sub_mem (Ideal.mul_mem_right _ _ h2) h1
    exact hprime.ne_top ((Ideal.eq_top_iff_one I).mpr h3)
  · simp only [map_multiset_prod, Multiset.map_map] at hprod
    obtain ⟨b, hb, hb0⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hprod)
    refine ⟨ℓ b, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
    rw [map_sub]
    exact hb0

include hφ hker hprime in
/-- **Roots over a complete ring with algebraically closed residue field.** Let `R` be a domain,
`π`-adically complete, with `R ⧸ (π) ≅ k` algebraically closed (through `φ`), and `O` a domain
and `R`-algebra, `π`-adically separated, with `π O` prime and `π ≠ 0` in `O`. Then every `β ∈ O`
which is a root of a polynomial `Q` over `R` with nonzero reduction modulo `π` lies in `R`. -/
theorem mem_range_algebraMap_of_aeval_eq_zero [IsAdicComplete (Ideal.span {π}) R]
    (hπ : algebraMap R O π ≠ 0)
    (hsep : ∀ x : O, (∀ n, x ∈ Ideal.span {algebraMap R O π ^ n}) → x = 0)
    {β : O} {Q : R[X]} (hQ : Q.map φ ≠ 0) (hβ : aeval β Q = 0) :
    β ∈ Set.range (algebraMap R O) := by
  classical
  set πO := algebraMap R O π
  have hπR : π ≠ 0 := fun h ↦ hπ (by rw [show πO = algebraMap R O π from rfl, h, map_zero])
  have hsepR : ∀ r : R, (∀ n, r ∈ Ideal.span {π ^ n}) → r = 0 := by
    intro r hr
    have := IsHausdorff.haus (IsAdicComplete.toIsHausdorff (I := Ideal.span {π}) (M := R)) r
    refine this fun n ↦ ?_
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    exact hr n
  -- the inductive step
  have key : ∀ (m : ℕ) (r : R), β - algebraMap R O r ∈ Ideal.span {πO ^ m} →
      ∃ r', r' - r ∈ Ideal.span {π ^ m} ∧ β - algebraMap R O r' ∈ Ideal.span {πO ^ (m + 1)} := by
    intro m r hr
    obtain ⟨γ, hγ⟩ := Ideal.mem_span_singleton'.mp hr
    -- `γ` is a root of `Q (r + π^m X)`
    set p : R[X] := C r + C (π ^ m) * X
    have hp : p ≠ C (p.coeff 0) := by
      intro h
      have := congrArg (coeff · 1) h
      simp only [p, coeff_add, coeff_C_mul_X, coeff_C, one_ne_zero, ite_false, zero_add,
        ite_true] at this
      exact pow_ne_zero m hπR this
    have hQ0 : Q ≠ 0 := by rintro rfl; exact hQ (Polynomial.map_zero φ)
    have hQ1 : Q.comp p ≠ 0 := by
      rw [Ne, comp_eq_zero_iff]
      push Not
      exact ⟨hQ0, fun _ ↦ hp⟩
    have hQ1γ : aeval γ (Q.comp p) = 0 := by
      rw [aeval_comp]
      have : aeval γ p = β := by
        simp only [p, map_add, aeval_C, map_mul, aeval_X, map_pow]
        rw [mul_comm, hγ]
        ring
      rw [this, hβ]
    obtain ⟨j, Q', hQ', hQ'0⟩ := exists_eq_C_pow_mul_of_ne_zero hsepR φ hker hQ1
    have hQ'γ : aeval γ Q' = 0 := by
      rw [hQ', map_mul, aeval_C, map_pow] at hQ1γ
      exact (mul_eq_zero.mp hQ1γ).resolve_left (pow_ne_zero j hπ)
    obtain ⟨r'', hr''⟩ := exists_sub_mem_span_of_aeval_eq_zero φ hφ hker hprime hQ'0 hQ'γ
    obtain ⟨δ, hδ⟩ := Ideal.mem_span_singleton'.mp hr''
    refine ⟨r + π ^ m * r'', ?_, ?_⟩
    · rw [add_sub_cancel_left, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    · rw [Ideal.mem_span_singleton]
      refine ⟨δ, ?_⟩
      rw [map_add, map_mul, map_pow]
      change β - (algebraMap R O r + πO ^ m * algebraMap R O r'') = πO ^ (m + 1) * δ
      linear_combination (-1 : O) * hγ - πO ^ m * hδ
  choose! next hnext₁ hnext₂ using key
  let seq : ℕ → R := fun m ↦ Nat.rec 0 (fun m r ↦ next m r) m
  have hseq_succ (m : ℕ) : seq (m + 1) = next m (seq m) := rfl
  have hseq : ∀ m, β - algebraMap R O (seq m) ∈ Ideal.span {πO ^ m} := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [hseq_succ]; exact hnext₂ m _ ih
  have hstep (m : ℕ) : seq (m + 1) - seq m ∈ Ideal.span {π ^ m} := by
    rw [hseq_succ]; exact hnext₁ m _ (hseq m)
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → seq n - seq m ∈ Ideal.span {π ^ m} := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have h1 : seq (n + 1) - seq n ∈ Ideal.span {π ^ m} :=
        Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow π hmn) (hstep n)
      have : seq (n + 1) - seq m = (seq (n + 1) - seq n) + (seq n - seq m) := by ring
      rw [this]
      exact add_mem h1 ih
  -- the limit
  have hpow (n : ℕ) : (Ideal.span {π} ^ n • ⊤ : Submodule R R) = Ideal.span {π ^ n} := by
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := Ideal.span {π}))
    (f := seq) fun {m n} hmn ↦ by
      rw [hpow, SModEq.sub_mem]
      have := (Ideal.span {π ^ m}).neg_mem (hcauchy hmn)
      rwa [neg_sub] at this
  refine ⟨L, (sub_eq_zero.mp (hsep _ fun n ↦ ?_)).symm⟩
  have h1 : seq n - L ∈ Ideal.span {π ^ n} := by
    have := hL n
    rwa [hpow, SModEq.sub_mem] at this
  have h2 : algebraMap R O (seq n - L) ∈ Ideal.span {πO ^ n} := by
    rw [Ideal.mem_span_singleton] at h1 ⊢
    obtain ⟨t, ht⟩ := h1
    exact ⟨algebraMap R O t, by rw [ht, map_mul, map_pow]⟩
  have : β - algebraMap R O L =
      (β - algebraMap R O (seq n)) + algebraMap R O (seq n - L) := by
    rw [map_sub]; ring
  rw [this]
  exact add_mem (hseq n) h2

end IsAdicComplete
