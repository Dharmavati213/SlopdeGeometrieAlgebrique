/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Minimal parameters in an actual regular local ring

These are dimension-theoretic inputs for the regular-local example IV.5.3–5.4.
They use mathlib's original `IsRegularLocalRing`, not a replacement definition
assuming a regular sequence or an Ext computation.

The maximal ideal has a minimal generating set of size equal to the dimension.
Quotienting by any subset of such a generating set gives a regular local ring,
and lowers the dimension by exactly the cardinality of that subset. This follows
from Krull's height inequality and the remaining generators of the quotient.

This file does not yet prove that the generators form a regular sequence:
nonzerodivisors and the resulting residue-field Ext computation remain separate
dependencies of IV.5.4.
-/

noncomputable section

universe u

open IsLocalRing

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The genuine regular-local-ring hypothesis supplies minimal generators
of the maximal ideal, with cardinality equal to its Krull dimension. -/
theorem regularLocal_exists_minimal_generators :
    ∃ s : Finset R, Ideal.span (s : Set R) = maximalIdeal R ∧
      (s.card : WithBot ℕ∞) = ringKrullDim R := by
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal R).fg_of_isNoetherianRing
  exact ⟨s, hspan, by rw [hcard, IsRegularLocalRing.spanFinrank_maximalIdeal]⟩

/-- The same actual generators with an explicitly specified finite dimension. -/
theorem regularLocal_exists_generators_of_dimension (n : ℕ)
    (hdim : ringKrullDim R = n) :
    ∃ s : Finset R, Ideal.span (s : Set R) = maximalIdeal R ∧ s.card = n := by
  obtain ⟨s, hs, hc⟩ := regularLocal_exists_minimal_generators (R := R)
  exact ⟨s, hs, by exact_mod_cast hc.trans hdim⟩

/-- Each member of the actual minimal generating set is outside the square
of the maximal ideal. The proof uses Nakayama, not a regularity assumption
on multiplication by that member. -/
theorem regularLocal_minimal_generator_not_mem_square (s : Finset R)
    (hs : Ideal.span (s : Set R) = maximalIdeal R)
    (hcard : (s.card : WithBot ℕ∞) = ringKrullDim R) (x : R) (hx : x ∈ s) :
    x ∉ maximalIdeal R ^ 2 := by
  classical
  intro hx2
  let J : Ideal R := Ideal.span ((s.erase x : Finset R) : Set R)
  have hm : maximalIdeal R ≤ J ⊔ maximalIdeal R • maximalIdeal R := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro y hy
    by_cases hyx : y = x
    · subst y
      apply Submodule.mem_sup_right
      simpa only [hs, Ideal.smul_eq_mul, ← pow_two] using hx2
    · exact Submodule.mem_sup_left (Ideal.subset_span (Finset.mem_erase.mpr ⟨hyx, hy⟩))
  have hmJ : maximalIdeal R ≤ J :=
    Submodule.le_of_le_smul_of_le_jacobson_bot
      (maximalIdeal R).fg_of_isNoetherianRing
      (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) hm
  have hJm : J ≤ maximalIdeal R := by
    rw [← hs]
    exact Ideal.span_mono (Finset.erase_subset x s)
  have hrank : (maximalIdeal R).spanFinrank ≤ (s.erase x).card := by
    rw [← le_antisymm hJm hmJ]
    simpa only [Set.ncard_coe_finset] using
      Submodule.spanFinrank_span_le_ncard_of_finite (s.erase x).finite_toSet
  have hmin : s.card = (maximalIdeal R).spanFinrank := by
    exact_mod_cast hcard.trans (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlt := Finset.card_erase_lt_of_mem hx
  omega

/-- The zero-dimensional base case of the regular-parameter induction:
regularity forces the maximal ideal itself to vanish. -/
theorem regularLocal_maximalIdeal_eq_bot_of_dimension_zero
    (hdim : ringKrullDim R = 0) : maximalIdeal R = ⊥ := by
  apply (Submodule.spanFinrank_eq_zero_iff_eq_bot
    (maximalIdeal R).fg_of_isNoetherianRing).mp
  have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
  rw [hdim] at h
  exact_mod_cast h

/-- The zero-dimensional base case is a field, derived from actual regularity. -/
theorem regularLocal_isField_of_dimension_zero (hdim : ringKrullDim R = 0) :
    IsField R :=
  isField_iff_maximalIdeal_eq.mpr
    (regularLocal_maximalIdeal_eq_bot_of_dimension_zero hdim)

/-- Quotienting by any subset of a minimal generating set of the maximal
ideal preserves genuine regularity and lowers dimension by exactly its size.
No regular-sequence or nonzerodivisor hypothesis is supplied. -/
theorem regularLocal_quotient_subset_generators (s t : Finset R)
    (hs : Ideal.span (s : Set R) = maximalIdeal R)
    (hcard : (s.card : WithBot ℕ∞) = ringKrullDim R) (ht : t ⊆ s) :
    IsRegularLocalRing (R ⧸ Ideal.span (t : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span (t : Set R)) + t.card = ringKrullDim R := by
  classical
  let J : Ideal R := Ideal.span (t : Set R)
  let Q := R ⧸ J
  let q : R →+* Q := Ideal.Quotient.mk J
  have hs_mem : (s : Set R) ⊆ maximalIdeal R := by
    rw [← hs]
    exact Ideal.subset_span
  have hJ : J ≤ maximalIdeal R :=
    Ideal.span_le.mpr (fun x hx ↦ hs_mem (ht hx))
  have hJ_ne : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hJ
  let : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJ_ne
  let : IsLocalRing Q := IsLocalRing.of_surjective' q Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal R).map q = maximalIdeal Q :=
    map_maximalIdeal_of_surjective q Ideal.Quotient.mk_surjective
  have hJmap : J.map q = ⊥ := by
    rw [Ideal.map_eq_bot_iff_le_ker]
    exact le_of_eq (Ideal.mk_ker (I := J)).symm
  have hspan : Ideal.span (q '' ((s \ t : Finset R) : Set R)) = maximalIdeal Q := by
    rw [← Ideal.map_span, ← hmap, ← hs]
    have hsplit : Ideal.span (s : Set R) =
        Ideal.span ((s \ t : Finset R) : Set R) ⊔ J := by
      rw [← Ideal.span_union]
      congr 1
      exact_mod_cast (Finset.sdiff_union_of_subset ht).symm
    rw [hsplit, Ideal.map_sup, hJmap, sup_bot_eq]
  have hrank : (maximalIdeal Q).spanFinrank ≤ (s \ t).card := by
    rw [← hspan]
    exact (Submodule.spanFinrank_span_le_ncard_of_finite
      ((s \ t).finite_toSet.image q)).trans
        (by simpa only [Set.ncard_coe_finset] using
          Set.ncard_image_le (f := q) (s \ t).finite_toSet)
  have hlower : ringKrullDim R ≤ ringKrullDim Q + t.card := by
    apply ringKrullDim_le_ringKrullDim_quotient_add_card
    rw [ringJacobson_eq_maximalIdeal]
    exact fun x hx ↦ hs_mem (ht hx)
  have hupper := ringKrullDim_le_spanFinrank_maximalIdeal Q
  let d : ℕ := (LTSeries.longestOf (PrimeSpectrum Q)).length
  have hd : ringKrullDim Q = (d : WithBot ℕ∞) :=
    Order.krullDim_eq_length_of_finiteDimensionalOrder
  have hlow_nat : s.card ≤ d + t.card := by
    rw [← hcard, hd, ← Nat.cast_add] at hlower
    exact_mod_cast hlower
  have hup_nat : d ≤ (maximalIdeal Q).spanFinrank := by
    rw [hd] at hupper
    exact_mod_cast hupper
  have hsum := Finset.card_sdiff_add_card_eq_card ht
  have hdim_nat : d + t.card = s.card := by omega
  have hrank_eq : (maximalIdeal Q).spanFinrank = d := by omega
  refine ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le Q ?_, ?_⟩
  · rw [hrank_eq, hd]
  · change ringKrullDim Q + t.card = ringKrullDim R
    rw [hd, ← Nat.cast_add, hdim_nat, hcard]

/-- In particular, killing one member of a minimal generating set gives
a regular local quotient of dimension one less. -/
theorem regularLocal_quotient_minimal_generator (s : Finset R)
    (hs : Ideal.span (s : Set R) = maximalIdeal R)
    (hcard : (s.card : WithBot ℕ∞) = ringKrullDim R) (x : R) (hx : x ∈ s) :
    IsRegularLocalRing (R ⧸ Ideal.span ({x} : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span ({x} : Set R)) + 1 = ringKrullDim R := by
  classical
  obtain ⟨hreg, hdim⟩ := regularLocal_quotient_subset_generators s {x} hs hcard
    (Finset.singleton_subset_iff.mpr hx)
  have he : Ideal.span (({x} : Finset R) : Set R) = Ideal.span ({x} : Set R) := by
    rw [Finset.coe_singleton]
  let e := (Ideal.quotientEquivAlgOfEq R he).toRingEquiv
  let := hreg
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv e]
  exact hdim

/-- For every `j ≤ n`, genuine regularity produces `j` actual parameters
whose quotient is again regular local of dimension `n - j`. -/
theorem regularLocal_exists_regular_quotient_of_dimension (n j : ℕ)
    (hdim : ringKrullDim R = n) (hj : j ≤ n) :
    ∃ t : Finset R, t.card = j ∧ (t : Set R) ⊆ maximalIdeal R ∧
      IsRegularLocalRing (R ⧸ Ideal.span (t : Set R)) ∧
      ringKrullDim (R ⧸ Ideal.span (t : Set R)) = ((n - j : ℕ) : WithBot ℕ∞) := by
  obtain ⟨s, hs, hc⟩ := regularLocal_exists_generators_of_dimension n hdim
  obtain ⟨t, ht, htc⟩ := Finset.exists_subset_card_eq (hj.trans_eq hc.symm)
  have hs_mem : (s : Set R) ⊆ maximalIdeal R := by
    rw [← hs]
    exact Ideal.subset_span
  obtain ⟨hreg, hq⟩ := regularLocal_quotient_subset_generators s t hs
    (by rw [hc, hdim]) ht
  refine ⟨t, htc, fun x hx ↦ hs_mem (ht hx), hreg, ?_⟩
  apply (ENat.WithBot.add_natCast_cancel (c := j)).mp
  rw [← htc, hq, hdim, htc, ← Nat.cast_add, Nat.sub_add_cancel hj]

end SGA.SGA2.ExposeIII
