/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.SimultaneousRegularElements
import SGA.SGA2.ExposeIV.NoetherianCompletion

/-!
# Original-ring parameters regular on completed modules

Contracting the finitely many associated primes of a finite completed-ring
module gives finitely many prime ideals in the original ring. Their
contractions cannot contain the original maximal ideal when the completed
module has no maximal-ideal torsion. Prime avoidance therefore chooses an
original scalar regular on both the coefficient and the completed module.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R S : Type u} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]

/-- Prime avoidance chooses a scalar in the original maximal ideal
regular on modules over both rings, when that ideal generates the new
maximal ideal. Finiteness over the original ring is not required of `N`. -/
theorem exists_simultaneous_regular_of_maximalIdeal_map
    (f : R →+* S) (hf : (maximalIdeal R).map f = maximalIdeal S)
    (M : ModuleCat.{u} R) (N : ModuleCat.{u} S)
    [Module.Finite R M] [Module.Finite S N]
    (hM : IdealRegular M (maximalIdeal R)) (hN : IdealRegular N (maximalIdeal S)) :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x ∧ IsSMulRegular N (f x) := by
  classical
  let P := associatedPrimes R M ∪ (associatedPrimes S N).image (Ideal.comap f)
  have hP : P.Finite := (associatedPrimes.finite R M).union
    ((associatedPrimes.finite S N).image (Ideal.comap f))
  have hprime : ∀ p ∈ P, p.IsPrime := by
    intro p hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact hp.isPrime
    · have := hq.isPrime
      exact Ideal.comap_isPrime f q
  have hnot : ∀ p ∈ P, ¬ maximalIdeal R ≤ p := by
    intro p hp
    rcases hp with hp | ⟨q, hq, rfl⟩
    · exact (exists_regular_iff_no_associatedPrime M (maximalIdeal R)).mp
        ((idealRegular_iff_exists_regular M (maximalIdeal R)).mp hM) p hp
    · intro h
      apply (exists_regular_iff_no_associatedPrime N (maximalIdeal S)).mp
        ((idealRegular_iff_exists_regular N (maximalIdeal S)).mp hN) q hq
      rw [← hf]
      exact Ideal.map_le_iff_le_comap.mpr h
  have hns : ¬ (maximalIdeal R : Set R) ⊆ ⋃ p ∈ P, (p : Set R) := by
    intro h
    obtain ⟨p, hp, hmp⟩ :=
      ((maximalIdeal R).subset_union_prime_finite hP (f := id) 0 0
        (fun p hp _ _ => hprime p hp)).mp h
    exact hnot p hp hmp
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hns
  refine ⟨x, hxm, ?_, ?_⟩
  · have hn : x ∉ ⋃ p ∈ associatedPrimes R M, (p : Set R) := by
      intro h
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp h
      exact hx (Set.mem_iUnion₂_of_mem (Or.inl hp) hxp)
    simpa only [biUnion_associatedPrimes_eq_compl_regular, Set.mem_compl_iff,
      Set.mem_ofPred_eq, not_not] using hn
  · have hn : f x ∉ ⋃ p ∈ associatedPrimes S N, (p : Set S) := by
      intro h
      obtain ⟨p, hp, hxp⟩ := Set.mem_iUnion₂.mp h
      exact hx (Set.mem_iUnion₂_of_mem (Or.inr ⟨p, hp, rfl⟩) hxp)
    simpa only [biUnion_associatedPrimes_eq_compl_regular, Set.mem_compl_iff,
      Set.mem_ofPred_eq, not_not] using hn

/-- The chosen parameter lies in the original ring and is regular both
on the original coefficient and on the actual completed-ring torsion quotient. -/
theorem exists_regular_coefficient_and_completion_torsion_quotient
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : IdealRegular M (maximalIdeal R))
    (N : ModuleCat.{u} (AdicCompletion (maximalIdeal R) R))
    [Module.Finite (AdicCompletion (maximalIdeal R) R) N] :
    ∃ x ∈ maximalIdeal R, IsSMulRegular M x ∧
      IsSMulRegular (N ⧸ powerTorsion
        (maximalIdeal (AdicCompletion (maximalIdeal R) R)) N)
        (algebraMap R (AdicCompletion (maximalIdeal R) R) x) :=
  exists_simultaneous_regular_of_maximalIdeal_map _ AdicCompletion.maximalIdeal_eq_map.symm
    M (ModuleCat.of _ (N ⧸ powerTorsion
      (maximalIdeal (AdicCompletion (maximalIdeal R) R)) N)) hM
    (idealRegular_powerTorsion_quotient _ N)

end SGA.SGA2.ExposeV
