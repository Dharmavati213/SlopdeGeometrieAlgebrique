/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.Tactic.LinearCombination

/-!
# Regular pairs and their spreading out from a local ring

* `RingTheory.Sequence.isWeaklyRegular_pair_iff`: `a, b` is a regular sequence on a commutative
  ring `B` iff `a` is a nonzerodivisor and `a ∣ b z` implies `a ∣ z`.
* `exists_isWeaklyRegular_away_of_isWeaklyRegular_atPrime`: if `a, b` is a regular sequence in the
  localization `R_p` of a noetherian ring, it is a regular sequence in `R_g` for some `g ∉ p`
  (the non-regularity loci are closed; used to find affine neighbourhoods of a point on which a
  regular system of parameters is regular).
-/

open RingTheory.Sequence

namespace RingTheory.Sequence

/-- `a, b` is a regular sequence on the ring `B` iff `a` is a nonzerodivisor and `a ∣ b z`
implies `a ∣ z`. -/
theorem isWeaklyRegular_pair_iff {B : Type*} [CommRing B] (a b : B) :
    IsWeaklyRegular B [a, b] ↔ IsSMulRegular B a ∧ ∀ z : B, a ∣ b * z → a ∣ z := by
  constructor
  · intro h
    rw [isWeaklyRegular_cons_iff, isWeaklyRegular_singleton_iff] at h
    refine ⟨h.1, fun z ⟨w, hw⟩ ↦ ?_⟩
    have : b • (Submodule.Quotient.mk z : QuotSMulTop a B) = b • 0 := by
      rw [smul_zero, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
        Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨w, Submodule.mem_top, by rw [smul_eq_mul, smul_eq_mul, hw]⟩
    have := h.2 this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at this
    obtain ⟨e, -, he⟩ := this
    exact ⟨e, he.symm⟩
  · rintro ⟨ha, hb⟩
    refine IsWeaklyRegular.cons ha ((isWeaklyRegular_singleton_iff _ b).mpr ?_)
    intro u v huv
    rw [← sub_eq_zero, ← smul_sub] at huv
    rw [← sub_eq_zero]
    generalize u - v = w at huv ⊢
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists] at huv
    obtain ⟨d, -, hd⟩ := huv
    obtain ⟨e, rfl⟩ := hb c ⟨d, by rw [← smul_eq_mul, ← hd, smul_eq_mul]⟩
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨e, Submodule.mem_top, rfl⟩

/-- Multiplying the terms of a regular pair by units gives a regular pair. -/
theorem IsWeaklyRegular.pair_mul_isUnit {B : Type*} [CommRing B] {a b u v : B}
    (h : IsWeaklyRegular B [a, b]) (hu : IsUnit u) (hv : IsUnit v) :
    IsWeaklyRegular B [a * u, b * v] := by
  rw [isWeaklyRegular_pair_iff] at h ⊢
  obtain ⟨ha, hb⟩ := h
  refine ⟨fun z₁ z₂ hz ↦ hu.mul_right_injective (ha ?_), fun z hz ↦ ?_⟩
  · simp only [smul_eq_mul] at hz ⊢
    rw [← mul_assoc, ← mul_assoc]
    exact hz
  · have h1 : a ∣ b * (v * z) := by
      rw [← mul_assoc]
      exact (dvd_mul_right a u).trans hz
    obtain ⟨c, hc⟩ := hb _ h1
    refine ⟨↑hu.unit⁻¹ * ↑hv.unit⁻¹ * c, ?_⟩
    calc z = ↑hv.unit⁻¹ * (v * z) := by rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = a * u * (↑hu.unit⁻¹ * ↑hv.unit⁻¹ * c) := by
        rw [hc]
        calc ↑hv.unit⁻¹ * (a * c) = a * (u * ↑hu.unit⁻¹) * ↑hv.unit⁻¹ * c := by
              rw [IsUnit.mul_val_inv, mul_one]; ring
          _ = _ := by ring

end RingTheory.Sequence

section Spreading

variable {R : Type*} [CommRing R]

/-- If every element of a finite module is killed by an element outside the prime `p`, a single
element outside `p` kills the module. -/
theorem exists_notMem_forall_smul_eq_zero {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] (p : Ideal R) [p.IsPrime] (h : ∀ m : M, ∃ s ∉ p, s • m = 0) :
    ∃ g ∉ p, ∀ m : M, g • m = 0 := by
  have hsub : Subsingleton (LocalizedModule p.primeCompl M) :=
    LocalizedModule.subsingleton_iff.mpr fun m ↦ h m
  have hp : (⟨p, ‹_›⟩ : PrimeSpectrum R) ∉ Module.support R M :=
    Module.notMem_support_iff.mpr hsub
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hp
  obtain ⟨g, hg, hgp⟩ := hp
  exact ⟨g, hgp, fun m ↦ Module.mem_annihilator.mp hg m⟩

variable [IsNoetherianRing R]

/-- If `a, b` is a regular sequence in `R_p` (`R` noetherian), there is `g ∉ p` such that
`g` kills the obstructions to the regularity of `a, b` on `R`: `a r = 0 → g r = 0` and
`a ∣ b r → a ∣ g r`. -/
theorem exists_notMem_of_isWeaklyRegular_atPrime (p : Ideal R) [p.IsPrime] {a b : R}
    (h : IsWeaklyRegular (Localization.AtPrime p)
      [algebraMap R (Localization.AtPrime p) a, algebraMap R (Localization.AtPrime p) b]) :
    ∃ g ∉ p, (∀ r : R, a * r = 0 → g * r = 0) ∧ (∀ r : R, a ∣ b * r → a ∣ g * r) := by
  classical
  let Rp := Localization.AtPrime p
  rw [isWeaklyRegular_pair_iff] at h
  obtain ⟨ha, hb⟩ := h
  -- the kernel of `a`
  let K : Submodule R R := Submodule.torsionBy R R a
  have hK : ∀ m : K, ∃ s ∉ p, s • m = 0 := by
    intro ⟨r, hr⟩
    have hr' : a * r = 0 := hr
    have : algebraMap R Rp r = 0 := by
      apply ha
      change algebraMap R Rp a * algebraMap R Rp r = algebraMap R Rp a * 0
      rw [mul_zero, ← map_mul, hr', map_zero]
    obtain ⟨⟨s, hs⟩, hsr⟩ := (IsLocalization.map_eq_zero_iff p.primeCompl Rp r).mp this
    exact ⟨s, hs, Subtype.ext hsr⟩
  obtain ⟨g₁, hg₁p, hg₁⟩ := exists_notMem_forall_smul_eq_zero p hK
  -- the kernel of `b` on `R / a`
  let N : Submodule R (R ⧸ Ideal.span {a}) := Submodule.torsionBy R _ b
  have hN : ∀ m : N, ∃ s ∉ p, s • m = 0 := by
    intro ⟨x, hx⟩
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hbr : a ∣ b * r := by
      have : b • Ideal.Quotient.mk (Ideal.span {a}) r = 0 := hx
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
      exact this
    have : algebraMap R Rp a ∣ algebraMap R Rp r := by
      apply hb
      rw [← map_mul]
      exact map_dvd _ hbr
    obtain ⟨w, hw⟩ := this
    obtain ⟨⟨c, ⟨s, hs⟩⟩, hc⟩ := IsLocalization.surj p.primeCompl w
    -- `r s = a c` in `R_p`
    have : algebraMap R Rp (r * s) = algebraMap R Rp (a * c) := by
      rw [map_mul, hw, map_mul, ← hc, mul_assoc]
    obtain ⟨⟨t, ht⟩, hts⟩ := IsLocalization.exists_of_eq (M := p.primeCompl) this
    refine ⟨t * s, fun h ↦ (Ideal.primeCompl p).mul_mem ht hs h, Subtype.ext ?_⟩
    change (t * s) • Ideal.Quotient.mk (Ideal.span {a}) r = 0
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    exact ⟨t * c, by simp only at hts; linear_combination hts⟩
  have : Module.Finite R N := Module.IsNoetherian.finite R N
  obtain ⟨g₂, hg₂p, hg₂⟩ := exists_notMem_forall_smul_eq_zero (M := N) p hN
  refine ⟨g₁ * g₂, fun h ↦ (Ideal.primeCompl p).mul_mem hg₁p hg₂p h, fun r hr ↦ ?_, fun r hr ↦ ?_⟩
  · have := congrArg Subtype.val (hg₁ ⟨r, hr⟩)
    change g₁ * r = 0 at this
    rw [mul_right_comm, this, zero_mul]
  · have hmem : Ideal.Quotient.mk (Ideal.span {a}) r ∈ N := by
      change b • Ideal.Quotient.mk (Ideal.span {a}) r = 0
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hr
    have := congrArg Subtype.val (hg₂ ⟨_, hmem⟩)
    change g₂ • Ideal.Quotient.mk (Ideal.span {a}) r = 0 at this
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    rw [mul_assoc]
    exact dvd_mul_of_dvd_right this g₁

/-- Spreading out a regular pair: if `a, b` is a regular sequence in `R_p` (`R` noetherian), there
is `g ∉ p` such that `a, b` is a regular sequence in every localization of `R` in which `g` is
invertible. -/
theorem exists_isWeaklyRegular_of_isWeaklyRegular_atPrime (p : Ideal R) [p.IsPrime] {a b : R}
    (h : IsWeaklyRegular (Localization.AtPrime p)
      [algebraMap R (Localization.AtPrime p) a, algebraMap R (Localization.AtPrime p) b]) :
    ∃ g ∉ p, ∀ (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S],
      IsUnit (algebraMap R S g) → IsWeaklyRegular S [algebraMap R S a, algebraMap R S b] := by
  obtain ⟨g, hgp, h₁, h₂⟩ := exists_notMem_of_isWeaklyRegular_atPrime p h
  refine ⟨g, hgp, fun M S _ _ _ hg ↦ ?_⟩
  rw [isWeaklyRegular_pair_iff]
  constructor
  · intro z₁ z₂ hz
    rw [← sub_eq_zero]
    have hz' : algebraMap R S a * (z₁ - z₂) = 0 := by
      rw [mul_sub, sub_eq_zero]; exact hz
    generalize z₁ - z₂ = z at hz' ⊢
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M z
    have : algebraMap R S (a * r) = 0 := by
      rw [map_mul, ← hrs, ← mul_assoc, hz', zero_mul]
    obtain ⟨⟨t, ht⟩, htr⟩ := (IsLocalization.map_eq_zero_iff M S _).mp this
    have h0 : g * (t * r) = 0 := h₁ _ (by rw [mul_left_comm]; exact htr)
    have hs : IsUnit (algebraMap R S (g * t * s)) := by
      rw [map_mul, map_mul]
      exact (hg.mul (IsLocalization.map_units S ⟨t, ht⟩)).mul (IsLocalization.map_units S s)
    simp only at hrs
    apply hs.mul_right_injective
    change algebraMap R S (g * t * s) * z = algebraMap R S (g * t * s) * 0
    rw [mul_zero, map_mul, mul_assoc, mul_comm (algebraMap R S s) z, hrs, ← map_mul, mul_assoc, h0,
      map_zero]
  · intro z ⟨w, hw⟩
    obtain ⟨⟨r, s⟩, hrs⟩ := IsLocalization.surj M z
    obtain ⟨⟨c, s'⟩, hcs⟩ := IsLocalization.surj M w
    simp only at hrs hcs
    have : algebraMap R S (b * r * s') = algebraMap R S (a * c * s) := by
      rw [map_mul, map_mul, map_mul, map_mul, ← hrs, ← hcs]
      linear_combination (algebraMap R S s * algebraMap R S s') * hw
    obtain ⟨⟨t, ht⟩, hts⟩ := IsLocalization.exists_of_eq (M := M) this
    have hdvd : a ∣ b * (t * s' * r) := ⟨t * c * s, by linear_combination hts⟩
    obtain ⟨e, he⟩ := h₂ _ hdvd
    have hu : IsUnit (algebraMap R S (g * (t * s') * s)) := by
      rw [map_mul, map_mul, map_mul]
      exact (hg.mul ((IsLocalization.map_units S ⟨t, ht⟩).mul (IsLocalization.map_units S s'))).mul
        (IsLocalization.map_units S s)
    refine ⟨algebraMap R S e * ↑hu.unit⁻¹, ?_⟩
    rw [← mul_assoc, ← map_mul, ← he, Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]
    simp only [map_mul, ← hrs]
    ring

end Spreading
