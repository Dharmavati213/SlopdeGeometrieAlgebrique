/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Original closed components and their minimal-prime generic points

Each actual irreducible component of the closed subspace `V(J)` has, in
the ambient spectrum, exactly the zero locus of a minimal prime over `J`.
The comparison retains the original component and its actual subtype inclusion.
-/

noncomputable section
universe u
open TopologicalSpace

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R]

/-- The image of an actual closed-subspace component is precisely the
closure of a minimal prime of its defining ideal. -/
theorem closedComponent_exists_minimalPrime (J : Ideal R)
    (C : Set (PrimeSpectrum.zeroLocus (J : Set R)))
    (hC : C ∈ irreducibleComponents (PrimeSpectrum.zeroLocus (J : Set R))) :
    ∃ p : PrimeSpectrum R, p.asIdeal ∈ J.minimalPrimes ∧
      Subtype.val '' C = PrimeSpectrum.zeroLocus (p.asIdeal : Set R) := by
  let Y := PrimeSpectrum.zeroLocus (J : Set R)
  let y : Y := hC.1.genericPoint
  have hgen : closure ({y} : Set Y) = C :=
    hC.1.closure_genericPoint (isClosed_of_mem_irreducibleComponents C hC)
  have hemb := (PrimeSpectrum.isClosed_zeroLocus (J : Set R)).isClosedEmbedding_subtypeVal
  have himage : Subtype.val '' C = PrimeSpectrum.zeroLocus (y.val.asIdeal : Set R) := by
    rw [← hgen, ← hemb.closure_image_eq, Set.image_singleton, PrimeSpectrum.closure_singleton]
  refine ⟨y.val, ⟨⟨y.val.isPrime, y.property⟩, ?_⟩, himage⟩
  intro q hq hqy
  let z : Y := ⟨⟨q, hq.1⟩, hq.2⟩
  have hyz : y ∈ closure ({z} : Set Y) := by
    rw [hemb.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton,
      PrimeSpectrum.closure_singleton]
    exact hqy
  have hCW : C ⊆ closure ({z} : Set Y) := by
    rw [← hgen]
    exact closure_minimal (Set.singleton_subset_iff.mpr hyz) isClosed_closure
  have hzC : z ∈ C := hC.2 isIrreducible_singleton.closure hCW (subset_closure (by simp))
  have hz : z.val ∈ Subtype.val '' C := ⟨z, hzC, rfl⟩
  rw [himage] at hz
  exact hz

end SGA.SGA2.ExposeV
