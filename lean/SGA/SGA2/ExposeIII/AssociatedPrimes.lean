/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Regular.LinearMap

/-!
# SGA 2, Exposé III: associated primes and the depth-zero criterion

The definitions of annihilator and support in III.1 are `Module.annihilator`
and `Module.support`. `sgaAssociatedPrimeSpectrum` gives the source's exact
annihilator definition over any commutative ring. Over a noetherian ring,
mathlib's `associatedPrimes` agrees with it, as proved below.

This file proves III.1.1--III.1.3 and the five equivalent conditions of III.2.1.
-/

universe u v w

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- III.1, definition: a prime is associated in SGA's sense when it is the
annihilator of a nonzero element. This definition works over arbitrary rings. -/
def sgaAssociatedPrimeSpectrum : Set (PrimeSpectrum R) :=
  {p | ∃ m : M, m ≠ 0 ∧ p.asIdeal = (⊥ : Submodule R M).colon {m}}

/-- Mathlib's associated primes viewed as points of the prime spectrum.
They agree with SGA's definition under the noetherian hypotheses below. -/
def associatedPrimeSpectrum : Set (PrimeSpectrum R) :=
  {p | p.asIdeal ∈ associatedPrimes R M}

/-- III.2.1(iii): an element annihilated by every element of `I` is zero. -/
def IdealRegular (I : Ideal R) : Prop :=
  ∀ m : M, (∀ a ∈ I, a • m = 0) → m = 0

variable [IsNoetherianRing R]

/-- III.1, definition of an associated prime using an actual annihilator. -/
theorem mem_associatedPrimes_iff {p : Ideal R} :
    p ∈ associatedPrimes R M ↔
      p.IsPrime ∧ ∃ m : M, m ≠ 0 ∧ p = (⊥ : Submodule R M).colon {m} := by
  rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  constructor
  · rintro ⟨hp, m, rfl⟩
    refine ⟨hp, m, ?_, rfl⟩
    intro hm
    exact hp.ne_top (by simp [hm])
  · rintro ⟨hp, m, _, hm⟩
    exact ⟨hp, m, hm⟩

/-- Under the noetherian hypotheses of III.1.1 onward, the exact source
definition agrees with mathlib's radical-annihilator definition. -/
theorem sgaAssociatedPrimeSpectrum_eq :
    sgaAssociatedPrimeSpectrum (R := R) M = associatedPrimeSpectrum (R := R) M := by
  ext p
  constructor
  · rintro ⟨m, hm, hp⟩
    exact (mem_associatedPrimes_iff M).mpr ⟨p.isPrime, m, hm, hp⟩
  · intro hp
    exact ((mem_associatedPrimes_iff M).mp hp).2

/-- III.1.1(i): the associated primes of a finite module form a finite set. -/
theorem associatedPrimes_finite [Module.Finite R M] :
    (associatedPrimes R M).Finite := associatedPrimes.finite R M

/-- III.1.1(ii): zero divisors are exactly the union of the associated primes. -/
theorem exists_nonzero_smul_eq_zero_iff (a : R) :
    (∃ m : M, m ≠ 0 ∧ a • m = 0) ↔ ∃ p ∈ associatedPrimes R M, a ∈ p := by
  have h := Set.ext_iff.mp (biUnion_associatedPrimes_eq_zero_divisors R M) a
  simpa only [Set.mem_iUnion, SetLike.mem_coe, Set.mem_ofPred_eq, exists_prop] using h.symm

/-- A noetherian module is zero exactly when it has no associated primes. -/
theorem associatedPrimes_eq_empty_iff_subsingleton :
    associatedPrimes R M = ∅ ↔ Subsingleton M := by
  constructor
  · intro h
    by_contra hn
    have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hn
    have := associatedPrimes.nonempty R M
    simp [h] at this
  · intro h
    exact associatedPrimes.eq_empty_of_subsingleton

variable [Module.Finite R M]

/-- III.1.2(i) iff (ii): every point of the support contains an associated prime. -/
theorem mem_support_iff_exists_associatedPrime (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔ ∃ q ∈ associatedPrimes R M, q ≤ p.asIdeal := by
  rw [Module.mem_support_iff_of_finite]
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hp
    exact ⟨q, Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq,
      hqp⟩
  · rintro ⟨q, hq, hqp⟩
    apply le_trans (b := q) _ hqp
    simpa only [Submodule.annihilator_top] using hq.annihilator_le

omit [IsNoetherianRing R] in
/-- III.1.2(i) iff (iii): support is the variety of the annihilator. -/
theorem mem_support_iff_annihilator_le (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔ Module.annihilator R M ≤ p.asIdeal :=
  Module.mem_support_iff_of_finite

omit [IsNoetherianRing R] in
/-- III.1.2(i) iff (iii bis). -/
theorem mem_support_iff_radical_annihilator_le (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔ (Module.annihilator R M).radical ≤ p.asIdeal :=
  (mem_support_iff_annihilator_le M p).trans p.isPrime.radical_le_iff.symm

/-- The minimal associated primes are the minimal primes over the annihilator. -/
theorem minimal_associatedPrimes_eq :
    {p : Ideal R | Minimal (fun q ↦ q ∈ associatedPrimes R M) p} =
      (Module.annihilator R M).minimalPrimes := by
  ext p
  constructor
  · intro hp
    have hpa : Module.annihilator R M ≤ p := by
      simpa only [Submodule.annihilator_top] using hp.prop.annihilator_le
    have := hp.prop.isPrime
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hpa
    have hqa := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq
    exact (hp.eq_of_le hqa hqp) ▸ hq
  · intro hp
    refine ⟨Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hp, ?_⟩
    intro q hq hqp
    exact hp.2 ⟨hq.isPrime, by
      simpa only [Submodule.annihilator_top] using hq.annihilator_le⟩ hqp

/-- III.1.1(iii): the radical of the annihilator is the intersection of the
minimal associated primes. -/
theorem radical_annihilator_eq_sInf_minimal_associatedPrimes :
    (Module.annihilator R M).radical =
      sInf {p : Ideal R | Minimal (fun q ↦ q ∈ associatedPrimes R M) p} := by
  rw [minimal_associatedPrimes_eq M, Ideal.sInf_minimalPrimes]

/-- Prime avoidance gives the equivalence used in III.2.1(ii) iff (iv). -/
theorem exists_regular_iff_no_associatedPrime (I : Ideal R) :
    (∃ a ∈ I, IsSMulRegular M a) ↔ ∀ p ∈ associatedPrimes R M, ¬ I ≤ p := by
  constructor
  · rintro ⟨a, ha, hreg⟩ p hp hIp
    have hunion : a ∈ ⋃ q ∈ associatedPrimes R M, (q : Set R) :=
      Set.mem_iUnion₂_of_mem hp (hIp ha)
    rw [biUnion_associatedPrimes_eq_compl_regular R M] at hunion
    exact hunion hreg
  · intro h
    by_contra! hn
    have hsub : (I : Set R) ⊆ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
      rw [biUnion_associatedPrimes_eq_compl_regular R M]
      exact hn
    obtain ⟨p, hp, hIp⟩ :=
      (I.subset_union_prime_finite (associatedPrimes.finite R M)
        (f := id) 0 0 (fun p hp _ _ ↦ hp.isPrime)).mp hsub
    exact h p hp hIp

/-- III.2.1(iii) iff (iv). -/
theorem idealRegular_iff_exists_regular (I : Ideal R) :
    IdealRegular M I ↔ ∃ a ∈ I, IsSMulRegular M a := by
  constructor
  · intro h
    apply (exists_regular_iff_no_associatedPrime M I).mpr
    intro p hp hIp
    obtain ⟨_, m, hm, rfl⟩ := (mem_associatedPrimes_iff M).mp hp
    apply hm
    apply h m
    intro a ha
    simpa only [Submodule.mem_colon_singleton, Submodule.mem_bot] using hIp ha
  · rintro ⟨a, ha, hreg⟩ m hm
    exact hreg.right_eq_zero_of_smul (hm a ha)

variable (N : Type w) [AddCommGroup N] [Module R N] [Module.Finite R N]

/-- III.2.1(i) iff (iv), allowing any finite `N` whose support is `V(I)`. -/
theorem subsingleton_linearMap_iff_exists_regular (I : Ideal R)
    (hSupp : Module.support R N = PrimeSpectrum.zeroLocus (I : Set R)) :
    Subsingleton (N →ₗ[R] M) ↔ ∃ a ∈ I, IsSMulRegular M a := by
  rw [IsSMulRegular.subsingleton_linearMap_iff,
    exists_regular_iff_no_associatedPrime M,
    exists_regular_iff_no_associatedPrime M]
  apply forall_congr'
  intro p
  apply forall_congr'
  intro hp
  have heq := Set.ext_iff.mp hSupp ⟨p, hp.isPrime⟩
  simpa only [Module.mem_support_iff_of_finite, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe] using not_congr heq

omit [Module.Finite R N] in
/-- III.2.1(ii) iff (iv). -/
theorem disjoint_support_associatedPrimes_iff_exists_regular (I : Ideal R)
    (hSupp : Module.support R N = PrimeSpectrum.zeroLocus (I : Set R)) :
    Disjoint (Module.support R N) (associatedPrimeSpectrum (R := R) M) ↔
      ∃ a ∈ I, IsSMulRegular M a := by
  rw [exists_regular_iff_no_associatedPrime M]
  constructor
  · intro h p hp hIp
    have hpoint : (⟨p, hp.isPrime⟩ : PrimeSpectrum R) ∈
        associatedPrimeSpectrum (R := R) M := hp
    apply Set.disjoint_left.mp h ?_ hpoint
    rw [hSupp]
    exact hIp
  · intro h
    apply Set.disjoint_left.mpr
    intro p hp hpAss
    rw [hSupp] at hp
    exact h p.asIdeal hpAss hp

omit [Module.Finite R M] in
open Module.associatedPrimes in
/-- Association at the maximal ideal after localization detects association
of the original prime. This includes both local implications in III.2.1. -/
theorem maximalIdeal_associated_atPrime_iff (p : PrimeSpectrum R) :
    IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ∈
        associatedPrimes (Localization.AtPrime p.asIdeal)
          (LocalizedModule.AtPrime p.asIdeal M) ↔
      p.asIdeal ∈ associatedPrimes R M := by
  constructor
  · intro h
    have hh := comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
        p.asIdeal.primeCompl (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
        (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal)) h
        (IsNoetherian.noetherian _)
    simpa only [Localization.AtPrime.under_maximalIdeal] using hh
  · exact Module.associatedPrimes.mem_associatedPrimes_atPrime_of_mem_associatedPrimes

/-- III.2.1(iv) iff (v). -/
theorem exists_regular_iff_local_maximalIdeal_not_associated (I : Ideal R) :
    (∃ a ∈ I, IsSMulRegular M a) ↔
      ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ∉
          associatedPrimes (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M) := by
  simp_rw [maximalIdeal_associated_atPrime_iff M]
  rw [exists_regular_iff_no_associatedPrime M]
  constructor
  · intro h p hp hpAss
    exact h p.asIdeal hpAss hp
  · intro h p hp hIp
    exact h ⟨p, hp.isPrime⟩ hIp hp

/-- III.2.1, with all five conditions compared to the vanishing of `Hom`. -/
theorem lemma_2_1 (I : Ideal R)
    (hSupp : Module.support R N = PrimeSpectrum.zeroLocus (I : Set R)) :
    (Subsingleton (N →ₗ[R] M) ↔
      Disjoint (Module.support R N) (associatedPrimeSpectrum (R := R) M)) ∧
    (Subsingleton (N →ₗ[R] M) ↔ IdealRegular M I) ∧
    (Subsingleton (N →ₗ[R] M) ↔ ∃ a ∈ I, IsSMulRegular M a) ∧
    (Subsingleton (N →ₗ[R] M) ↔
      ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ∉
          associatedPrimes (Localization.AtPrime p.asIdeal)
            (LocalizedModule.AtPrime p.asIdeal M)) := by
  have h := subsingleton_linearMap_iff_exists_regular M N I hSupp
  exact ⟨h.trans (disjoint_support_associatedPrimes_iff_exists_regular M N I hSupp).symm,
    h.trans (idealRegular_iff_exists_regular M I).symm, h,
    h.trans (exists_regular_iff_local_maximalIdeal_not_associated M I)⟩

omit [IsNoetherianRing R] [Module.Finite R M] [Module.Finite R N] in
/-- The annihilator of a linear map as an element of `Hom` is the annihilator
of its image. -/
theorem annihilator_range_eq_colon (f : N →ₗ[R] M) :
    Module.annihilator R f.range = (⊥ : Submodule R (N →ₗ[R] M)).colon {f} := by
  ext a
  simp only [Module.mem_annihilator, Submodule.mem_colon_singleton, Submodule.mem_bot]
  constructor
  · intro h
    ext n
    exact congrArg Subtype.val (h ⟨f n, n, rfl⟩)
  · intro h x
    obtain ⟨m, hm⟩ := x.property
    apply Subtype.ext
    simpa only [Submodule.coe_smul, Submodule.coe_zero, hm,
      LinearMap.smul_apply, LinearMap.zero_apply] using
      LinearMap.congr_fun h m

omit [Module.Finite R M] in
/-- The two inclusions asserted in III.1.3, pointwise on the spectrum. -/
theorem mem_associatedPrimes_linearMap_iff (p : PrimeSpectrum R) :
    p.asIdeal ∈ associatedPrimes R (N →ₗ[R] M) ↔
      p ∈ Module.support R N ∧ p.asIdeal ∈ associatedPrimes R M := by
  constructor
  · intro hp
    obtain ⟨_, f, _, hf⟩ := (mem_associatedPrimes_iff (N →ₗ[R] M)).mp hp
    have hann : Module.annihilator R f.range = p.asIdeal :=
      (annihilator_range_eq_colon M N f).trans hf.symm
    constructor
    · apply Module.mem_support_iff_of_finite.mpr
      intro a ha
      rw [hf, Submodule.mem_colon_singleton, Submodule.mem_bot]
      ext n
      change a • f n = 0
      rw [← f.map_smul, Module.mem_annihilator.mp ha, map_zero]
    · have hmin : p.asIdeal ∈ (Module.annihilator R f.range).minimalPrimes := by
        rw [hann, Ideal.minimalPrimes_eq_subsingleton_self]
        exact Set.mem_singleton _
      exact (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
        R f.range hmin).map_of_injective f.range.subtype (Submodule.injective_subtype _)
  · rintro ⟨hpN, hpM⟩
    obtain ⟨_, i, hi⟩ := (isAssociatedPrime_iff_exists_injective_linearMap p.asIdeal M).mp hpM
    have hHom : Nontrivial (N →ₗ[R] R ⧸ p.asIdeal) := by
      apply not_subsingleton_iff_nontrivial.mp
      intro h
      obtain ⟨a, ha, hreg⟩ :=
        (IsSMulRegular.subsingleton_linearMap_iff (R := R) (M := R ⧸ p.asIdeal)
          (N := N)).mp h
      have hap : a ∈ p.asIdeal := (Module.mem_support_iff_of_finite.mp hpN) ha
      have hzero : a • (1 : R ⧸ p.asIdeal) = 0 := by
        simpa only [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq] using
          Ideal.Quotient.eq_zero_iff_mem.mpr hap
      exact one_ne_zero (hreg.right_eq_zero_of_smul hzero)
    obtain ⟨g, hg⟩ := exists_ne (0 : N →ₗ[R] R ⧸ p.asIdeal)
    have hgn : ∃ n, g n ≠ 0 := by
      by_contra! hh
      exact hg (LinearMap.ext hh)
    obtain ⟨n, hn⟩ := hgn
    rw [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
    refine ⟨p.isPrime, i.comp g, ?_⟩
    ext a
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    constructor
    · intro ha
      ext m
      change a • i (g m) = 0
      rw [← i.map_smul]
      have hq : a • g m = 0 := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
          Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_mul]
      rw [hq, map_zero]
    · intro ha
      have heq : a • i (g n) = 0 := LinearMap.congr_fun ha n
      have hzero : a • g n = 0 := hi (by simpa only [map_smul, map_zero] using heq)
      rw [Algebra.smul_def, mul_eq_zero] at hzero
      exact Ideal.Quotient.eq_zero_iff_mem.mp (hzero.resolve_right hn)

omit [Module.Finite R M] in
/-- III.1.3: `Ass Hom(N,M) = Supp N ∩ Ass M`. -/
theorem associatedPrimeSpectrum_linearMap :
    associatedPrimeSpectrum (R := R) (N →ₗ[R] M) =
      Module.support R N ∩ associatedPrimeSpectrum (R := R) M := by
  ext p
  exact mem_associatedPrimes_linearMap_iff M N p

end SGA.SGA2.ExposeIII
