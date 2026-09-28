/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.AssociatedPrimes
import Mathlib.RingTheory.Regular.Flat

/-!
# SGA 2, Exposé III, Proposition 2.9: depth and localization

We compare depth with the depths of the localizations at primes containing
the support ideal. The proof follows the source: localization preserves
regular sequences and their successive quotients, and III.2.1 supplies a
global regular element whenever all the relevant local depths are positive.
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- The depth of the localization at a prime, with respect to its maximal ideal. -/
def localDepth (M : ModuleCat.{u} R) (p : PrimeSpectrum R) : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (ModuleCat.of (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M))

/-- The quotient/localization identification in the exact sequence III.2.3. -/
def localizedQuotSMulTopEquiv (M : ModuleCat.{u} R) (p : PrimeSpectrum R) (f : R) :
    LocalizedModule.AtPrime p.asIdeal (QuotSMulTop f M) ≃ₗ[Localization.AtPrime p.asIdeal]
      QuotSMulTop (algebraMap R (Localization.AtPrime p.asIdeal) f)
        (LocalizedModule.AtPrime p.asIdeal M) :=
  (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl (QuotSMulTop f M))).equiv.symm ≪≫ₗ
  (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop f M
    (Localization.AtPrime p.asIdeal)).symm ≪≫ₗ
  QuotSMulTop.congr (algebraMap R (Localization.AtPrime p.asIdeal) f)
    (IsLocalizedModule.isBaseChange p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)).equiv

variable [IsNoetherianRing R]

/-- The positive-depth criterion in the induction for III.2.9. -/
theorem one_le_depth_iff_exists_regular (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] :
    1 ≤ depth I M ↔ ∃ f ∈ I, IsSMulRegular M f := by
  rw [show (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) from rfl, le_depth_iff_exists_regular]
  constructor
  · rintro ⟨rs, hlen, hmem, hreg⟩
    obtain ⟨f, rfl⟩ := List.length_eq_one_iff.mp hlen
    exact ⟨f, hmem f (by simp), (isWeaklyRegular_singleton_iff M f).mp hreg⟩
  · rintro ⟨f, hf, hreg⟩
    exact ⟨[f], rfl, by simpa using hf, (isWeaklyRegular_singleton_iff M f).mpr hreg⟩

/-- Localization at a prime containing `I` can only increase the `I`-depth. -/
theorem depth_le_localDepth (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M]
    (p : PrimeSpectrum R) (hp : p ∈ PrimeSpectrum.zeroLocus (I : Set R)) :
    depth I M ≤ localDepth M p := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  obtain ⟨rs, hlen, hmem, hreg⟩ := (le_depth_iff_exists_regular I M n).mp hn
  change (n : ℕ∞) ≤ depth _ _
  apply (le_depth_iff_exists_regular _ _ n).mpr
  refine ⟨rs.map (algebraMap R (Localization.AtPrime p.asIdeal)), by simpa using hlen,
    ?_, hreg.of_isLocalizedModule (Localization.AtPrime p.asIdeal) p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)⟩
  intro a ha
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
  exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime p.asIdeal) p.asIdeal r).mpr (hp (hmem r hr))

/-- Quotienting by a regular element lowers local depth bounds by one. -/
theorem succ_le_localDepth_iff (M : ModuleCat.{u} R) [Module.Finite R M]
    (p : PrimeSpectrum R) {f : R} (hf : f ∈ p.asIdeal) (hreg : IsSMulRegular M f)
    (n : ℕ) :
    ((n + 1 : ℕ) : ℕ∞) ≤ localDepth M p ↔
      (n : ℕ∞) ≤ localDepth (ModuleCat.of R (QuotSMulTop f M)) p := by
  let Rp := Localization.AtPrime p.asIdeal
  let Mp := ModuleCat.of Rp (LocalizedModule.AtPrime p.asIdeal M)
  have hf' : algebraMap R Rp f ∈ IsLocalRing.maximalIdeal Rp :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff Rp p.asIdeal f).mpr hf
  have hreg' : IsSMulRegular Mp (algebraMap R Rp f) :=
    hreg.of_isLocalizedModule Rp p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)
  change ((n + 1 : ℕ) : ℕ∞) ≤ depth _ Mp ↔ _
  rw [succ_le_depth_iff _ Mp hf' hreg' n]
  change (n : ℕ∞) ≤ depth _ _ ↔ (n : ℕ∞) ≤ depth _ _
  have heq := depth_eq_of_linearEquiv (IsLocalRing.maximalIdeal Rp)
    (M := ModuleCat.of Rp (LocalizedModule.AtPrime p.asIdeal (QuotSMulTop f M)))
    (N := ModuleCat.of Rp (QuotSMulTop (algebraMap R Rp f)
      (LocalizedModule.AtPrime p.asIdeal M))) (localizedQuotSMulTopEquiv M p f)
  exact (congrArg (fun d : ℕ∞ ↦ (n : ℕ∞) ≤ d) heq).to_iff.symm

/-- If every relevant local depth is positive, there is a global regular
element in `I`; this is the last argument in the proof of III.2.9. -/
theorem exists_regular_of_one_le_localDepth (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M]
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      1 ≤ localDepth M p) : ∃ f ∈ I, IsSMulRegular M f := by
  apply (exists_regular_iff_local_maximalIdeal_not_associated M I).mpr
  intro p hp hpAss
  have hpos := (one_le_depth_iff_exists_regular _ _).mp (h p hp)
  exact (exists_regular_iff_no_associatedPrime
    (LocalizedModule.AtPrime p.asIdeal M) _).mp hpos _ hpAss le_rfl

/-- All finite depth bounds can be checked at primes containing `I`. -/
theorem le_depth_iff_forall_localDepth (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
        (n : ℕ∞) ≤ localDepth M p := by
  constructor
  · intro h p hp
    exact h.trans (depth_le_localDepth I M p hp)
  · intro h
    induction n generalizing M with
    | zero => exact bot_le
    | succ n ih =>
      obtain ⟨f, hf, hreg⟩ := exists_regular_of_one_le_localDepth I M (fun p hp ↦
        le_trans (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)) (h p hp))
      apply (succ_le_depth_iff I M hf hreg n).mpr
      apply ih
      intro p hp
      exact (succ_le_localDepth_iff M p (hp hf) hreg n).mp (h p hp)

/-- III.2.9: global ideal depth is the infimum of depths at the primes of `V(I)`. -/
theorem III_2_9 (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M = ⨅ (p : PrimeSpectrum R) (_ : p ∈ PrimeSpectrum.zeroLocus (I : Set R)),
      localDepth M p := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  simp only [le_iInf_iff, le_depth_iff_forall_localDepth]

omit [IsNoetherianRing R] in
/-- In a semilocal ring, the primes containing the Jacobson radical are
exactly the maximal ideals, as used immediately after III.2.10. -/
theorem isMaximal_iff_jacobson_le [Finite (MaximalSpectrum R)] (p : PrimeSpectrum R) :
    p.asIdeal.IsMaximal ↔ Ring.jacobson R ≤ p.asIdeal := by
  constructor
  · intro hp
    exact Ring.jacobson_le_of_isMaximal p.asIdeal
  · intro hp
    classical
    have hfin : {m : Ideal R | m.IsMaximal}.Finite := by
      rw [← MaximalSpectrum.range_asIdeal]
      exact Set.finite_range MaximalSpectrum.asIdeal
    rw [Ring.jacobson_eq_sInf_isMaximal, ← hfin.coe_toFinset,
      ← hfin.toFinset.inf_id_eq_sInf] at hp
    obtain ⟨m, hm, hmp⟩ := p.isPrime.inf_le'.mp hp
    have hmmax : m.IsMaximal := hfin.mem_toFinset.mp hm
    exact (hmmax.eq_of_le p.isPrime.ne_top hmp) ▸ hmmax

/-- III.2.10: for a semilocal ring, depth is the infimum over its maximal ideals. -/
theorem III_2_10 [Finite (MaximalSpectrum R)]
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth (Ring.jacobson R) M = ⨅ m : MaximalSpectrum R, localDepth M m.toPrimeSpectrum := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff_forall_localDepth]
  simp only [le_iInf_iff]
  constructor
  · intro h m
    exact h m.toPrimeSpectrum (Ring.jacobson_le_of_isMaximal m.asIdeal)
  · intro h p hp
    exact h ⟨p.asIdeal, (isMaximal_iff_jacobson_le p).mpr hp⟩

end SGA.SGA2.ExposeIII
