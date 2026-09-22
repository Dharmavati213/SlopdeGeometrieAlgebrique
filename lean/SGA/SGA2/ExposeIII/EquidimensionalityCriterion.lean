/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.Catenary
import SGA.SGA2.ExposeIII.ComponentChains

/-!
# SGA 2, III.3.9: equidimensionality from depth and the chain condition

A noetherian local ring satisfying the source's local depth/dimension
condition and the chain condition is equidimensional. The depth hypothesis
produces the chains of III.3.7; catenarity compares successive components;
a maximal prime chain supplies one component of dimension `dim R`.
-/

noncomputable section

universe u

open Set TopologicalSpace AlgebraicGeometry Relation

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- The dimension of an affine structure stalk is the dimension of the
actual localization of the coordinate ring at that prime. -/
theorem structureStalkDim_spec_eq_localization {R : CommRingCat.{u}}
    (p : PrimeSpectrum R) :
    structureStalkDim (Spec R) p =
      ringKrullDim (Localization.AtPrime p.asIdeal) :=
  (ringKrullDim_eq_of_ringEquiv
    (affineStalkRingEquiv p).toRingEquiv).symm

/-- The local dimension of an affine scheme at a prime is that prime's height. -/
theorem structureStalkDim_spec_eq_height {R : CommRingCat.{u}}
    (p : PrimeSpectrum R) :
    structureStalkDim (Spec R) p = (p.asIdeal.height : WithBot ℕ∞) := by
  rw [structureStalkDim_spec_eq_localization,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal)]

/-- Successive components supplied by III.3.7 with `d = 2` have prime
quotients of the same dimension when the ring satisfies the chain condition. -/
theorem component_dimension_eq_of_codimension_one_meet {R : CommRingCat.{u}}
    [IsNoetherianRing R] [IsLocalRing R]
    (hcat : SatisfiesChainCondition R) {C D : Set (PrimeSpectrum R)}
    (hCD : ComponentsMeetInCodimensionLt (Spec R) 2 C D) :
    ringKrullDim (R ⧸ PrimeSpectrum.vanishingIdeal C) =
      ringKrullDim (R ⧸ PrimeSpectrum.vanishingIdeal D) := by
  have hCcomp : C ∈ irreducibleComponents (PrimeSpectrum R) := hCD.1.1
  have hDcomp : D ∈ irreducibleComponents (PrimeSpectrum R) := hCD.1.2.1
  have hC : PrimeSpectrum.vanishingIdeal C ∈ minimalPrimes R :=
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr
      (by rw [(isClosed_of_mem_irreducibleComponents _ hCcomp).closure_eq]; exact hCcomp)
  have hD : PrimeSpectrum.vanishingIdeal D ∈ minimalPrimes R :=
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes.mpr
      (by rw [(isClosed_of_mem_irreducibleComponents _ hDcomp).closure_eq]; exact hDcomp)
  let : (PrimeSpectrum.vanishingIdeal C).IsPrime := hC.isPrime
  let : (PrimeSpectrum.vanishingIdeal D).IsPrime := hD.isPrime
  obtain ⟨p, ⟨hpC, hpD⟩, hpdim⟩ := hCD.2
  apply consecutiveComponentsEquidimensional_of_chainCondition hcat
    (PrimeSpectrum.vanishingIdeal C) (PrimeSpectrum.vanishingIdeal D) p.asIdeal hC hD
  · intro r hr
    exact (PrimeSpectrum.mem_vanishingIdeal C r).mp hr p hpC
  · intro r hr
    exact (PrimeSpectrum.mem_vanishingIdeal D r).mp hr p hpD
  · rw [structureStalkDim_spec_eq_height] at hpdim
    have hlt : p.asIdeal.height < (2 : ℕ∞) := WithBot.coe_lt_coe.mp hpdim
    exact ENat.lt_two_iff.mp hlt

/-- **III.3.9:** a noetherian local ring satisfying the local depth/dimension
condition and the chain condition has all its minimal-prime quotients of
dimension `dim R`. Both dimensions and depths in the hypothesis belong to
the actual localized rings. -/
theorem III_3_9 {R : CommRingCat.{u}} [IsNoetherianRing R] [IsLocalRing R]
    (hdepth : ∀ p : PrimeSpectrum R,
      (2 : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p.asIdeal) →
      (2 : ℕ∞) ≤ depth (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
        (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)))
    (hcat : SatisfiesChainCondition R) (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    ringKrullDim (R ⧸ p) = ringKrullDim R := by
  let : p.IsPrime := hp.isPrime
  obtain ⟨q, hq, hqdim⟩ := exists_minimalPrime_ringKrullDim_eq (R := R)
  let : q.IsPrime := hq.isPrime
  have hC : PrimeSpectrum.zeroLocus (p : Set R) ∈ irreducibleComponents (PrimeSpectrum R) :=
    PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
      (by simpa only [hp.isPrime.radical] using hp)
  have hD : PrimeSpectrum.zeroLocus (q : Set R) ∈ irreducibleComponents (PrimeSpectrum R) :=
    PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents.mpr
      (by simpa only [hq.isPrime.radical] using hq)
  have hdepth' : ∀ x : Spec R,
      (2 : WithBot ℕ∞) ≤ structureStalkDim (Spec R) x →
      (2 : ℕ∞) ≤ structureStalkDepth (Spec R) x := by
    intro x hx
    rw [structureStalkDim_spec_eq_localization] at hx
    have h := hdepth x hx
    exact h.trans_eq (depth_self_eq_of_ringEquiv
      (affineStalkRingEquiv x).toRingEquiv)
  let : PreconnectedSpace (Spec R) := inferInstanceAs (PreconnectedSpace (PrimeSpectrum R))
  have hchain := III_3_7 2 hdepth' hC hD
  have hsame :
      ringKrullDim (R ⧸ PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (p : Set R))) =
        ringKrullDim (R ⧸ PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (q : Set R))) := by
    refine ReflTransGen.head_induction_on hchain rfl ?_
    intro C D hCD _ ih
    exact (component_dimension_eq_of_codimension_one_meet hcat hCD).trans ih
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hp.isPrime.radical,
    PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hq.isPrime.radical] at hsame
  exact hsame.trans hqdim

end SGA.SGA2.ExposeIII
