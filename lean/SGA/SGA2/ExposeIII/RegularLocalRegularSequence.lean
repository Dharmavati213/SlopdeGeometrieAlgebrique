/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.RegularLocalDomain
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Genuine regular systems of parameters

An actual minimal generating list of the maximal ideal of a regular local
ring is a regular sequence. Every prefix quotient is an actual regular local
ring and hence a domain; minimality makes the next generator nonzero there.
This supplies the regular system of parameters used in IV.5.3–5.4 without
assuming its existence or its nonzerodivisor properties.
-/

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- No generator can be removed from an actual minimal generating set. -/
theorem regularLocal_minimal_generator_not_mem_span_erase [DecidableEq R] (s : Finset R)
    (hs : Ideal.span (s : Set R) = maximalIdeal R)
    (hcard : (s.card : WithBot ℕ∞) = ringKrullDim R) (x : R) (hx : x ∈ s) :
    x ∉ Ideal.span ((s.erase x : Finset R) : Set R) := by
  classical
  intro hxJ
  let J : Ideal R := Ideal.span ((s.erase x : Finset R) : Set R)
  have hmJ : maximalIdeal R ≤ J := by
    rw [← hs]
    apply Ideal.span_le.mpr
    intro y hy
    by_cases hyx : y = x
    · exact hyx ▸ hxJ
    · exact Ideal.subset_span (Finset.mem_erase.mpr ⟨hyx, hy⟩)
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

/-- Every minimal generating list of the maximal ideal is genuinely a
regular sequence, including nonvanishing of the final quotient. -/
theorem regularLocal_isRegular_of_minimal_generating_list (rs : List R)
    (hnodup : rs.Nodup) (hs : Ideal.ofList rs = maximalIdeal R)
    (hlen : (rs.length : WithBot ℕ∞) = ringKrullDim R) : IsRegular R rs := by
  classical
  let s := rs.toFinset
  have hs' : Ideal.span (s : Set R) = maximalIdeal R := by
    simpa only [s, List.coe_toFinset] using hs
  have hcard : (s.card : WithBot ℕ∞) = ringKrullDim R := by
    rw [List.toFinset_card_of_nodup hnodup]
    exact hlen
  refine ⟨⟨fun i hi ↦ ?_⟩, ?_⟩
  · let t := (rs.take i).toFinset
    have hxnot : rs[i] ∉ rs.take i := by
      intro hmem
      obtain ⟨j, hj, hji⟩ := List.mem_take_iff_getElem.mp hmem
      have hji' := hnodup.getElem_inj_iff.mp hji
      omega
    have hterase : t ⊆ s.erase rs[i] := by
      intro y hy
      have hy' : y ∈ rs.take i := List.mem_toFinset.mp hy
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro hyx
        exact hxnot (hyx ▸ hy')
      · exact List.mem_toFinset.mpr ((List.take_sublist i rs).subset hy')
    have ht : t ⊆ s := hterase.trans (Finset.erase_subset _ _)
    let P : Ideal R := Ideal.span (t : Set R)
    let Q := R ⧸ P
    have hQreg : IsRegularLocalRing Q :=
      (regularLocal_quotient_subset_generators s t hs' hcard ht).1
    let := hQreg
    let := regularLocal_isDomain Q
    have hxP : rs[i] ∉ P := fun h ↦
      regularLocal_minimal_generator_not_mem_span_erase s hs' hcard rs[i]
        (List.mem_toFinset.mpr (List.getElem_mem hi)) (Ideal.span_mono hterase h)
    have hP : Ideal.ofList (rs.take i) • (⊤ : Ideal R) = P := by
      simp only [Ideal.smul_eq_mul, Ideal.mul_top, P, t, List.coe_toFinset, Ideal.ofList]
    let e := Submodule.quotEquivOfEq _ P hP
    apply (e.isSMulRegular_congr rs[i]).mpr
    have hxQ : Ideal.Quotient.mk P rs[i] ≠ 0 := fun h ↦
      hxP (Ideal.Quotient.eq_zero_iff_mem.mp h)
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro y hy
    have hmul : Ideal.Quotient.mk P rs[i] * y = 0 := by
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hy
    exact (mul_eq_zero.mp hmul).resolve_left hxQ
  · simpa only [hs, Ideal.smul_eq_mul, Ideal.mul_top] using
      (maximalIdeal.isMaximal R).ne_top.symm

/-- **IV.5.3, regular parameters:** a regular local ring of dimension `n`
has an actual `R`-regular sequence of length `n` generating its maximal ideal. -/
theorem regularLocal_exists_regular_parameters (n : ℕ) (hdim : ringKrullDim R = n) :
    ∃ rs : List R, rs.length = n ∧ Ideal.ofList rs = maximalIdeal R ∧ IsRegular R rs := by
  classical
  obtain ⟨s, hs, hc⟩ := regularLocal_exists_generators_of_dimension n hdim
  have hspan : Ideal.ofList s.toList = maximalIdeal R := by
    convert hs using 2
    ext y
    exact Finset.mem_toList
  have hlen : (s.toList.length : WithBot ℕ∞) = ringKrullDim R := by
    rw [Finset.length_toList, hc, hdim]
  exact ⟨s.toList, by simpa using hc, hspan,
    regularLocal_isRegular_of_minimal_generating_list s.toList s.nodup_toList hspan hlen⟩

end SGA.SGA2.ExposeIII
