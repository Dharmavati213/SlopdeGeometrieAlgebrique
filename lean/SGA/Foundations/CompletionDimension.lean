/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import SGA.Foundations.Formal.CompletionNoetherian


/-!
# Dimension of completions and of local rings of the punctured spectrum

* `IsLocalRing.ringKrullDim_adicCompletion_le`: for a noetherian local ring `A`,
  `dim Â ≤ dim A` (a system of parameters of `A` generates an ideal of definition of `Â`;
  Matsumura, *Commutative ring theory*, Thm. 15.1 and Krull's height theorem).
* `AlgebraicGeometry.ringKrullDim_stalk_lt_of_ne_closedPoint`: the local rings of `Spec A` at
  points other than the closed point have smaller dimension.
* `AlgebraicGeometry.ringKrullDim_stalk_opens`: local rings of an open subscheme.
-/

open IsLocalRing

namespace IsLocalRing

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The completion of a noetherian local ring has dimension at most that of the ring (in fact
they are equal): a system of parameters of `A` generates an ideal of definition of `Â`. -/
theorem ringKrullDim_adicCompletion_le :
    ringKrullDim (AdicCompletion (maximalIdeal A) A) ≤ ringKrullDim A := by
  classical
  let Â := AdicCompletion (maximalIdeal A) A
  obtain ⟨s, hs, hcard⟩ := (maximalIdeal A).exists_finset_card_eq_height_of_isNoetherianRing
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
  have hmin : maximalIdeal Â ∈ (Ideal.span (s.image (algebraMap A Â) : Set Â)).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun P ⟨hP, hsP⟩ hPm ↦ ?_⟩
    · rw [Ideal.span_le]
      rintro _ hy
      obtain ⟨x, hxs, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hy)
      have : x ∈ maximalIdeal A := hs.1.2 (Ideal.subset_span (Finset.mem_coe.mpr hxs))
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ this
    · have hc : P.comap (algebraMap A Â) = maximalIdeal A := by
        refine ((hs.2 ⟨Ideal.comap_isPrime (algebraMap A Â) P, ?_⟩ (le_maximalIdeal
          (Ideal.comap_ne_top _ hP.ne_top))).antisymm (le_maximalIdeal
          (Ideal.comap_ne_top _ hP.ne_top))).symm
        rw [Ideal.span_le]
        intro x hx
        exact hsP (Ideal.subset_span (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hx)))
      rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_le_iff_le_comap, hc]
  have := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hle : ((s.image (algebraMap A Â)).card : ℕ∞) ≤ (maximalIdeal A).height := by
    rw [← hcard]; exact_mod_cast Finset.card_image_le
  exact_mod_cast this.trans hle

end IsLocalRing

namespace AlgebraicGeometry

open IsLocalRing

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- The local rings of a noetherian local scheme at points other than the closed point have
smaller dimension. -/
theorem ringKrullDim_stalk_lt_of_ne_closedPoint (y : Spec (.of R)) (hy : y ≠ closedPoint R) :
    ringKrullDim ((Spec (.of R)).presheaf.stalk y) < ringKrullDim R := by
  have : y.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := R) y
  let k : Algebra R ((Spec (.of R)).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec (.of R)).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height y.asIdeal ((Spec (.of R)).presheaf.stalk y),
    ← maximalIdeal_height_eq_ringKrullDim]
  have hlt : y.asIdeal < maximalIdeal R :=
    lt_of_le_of_ne (le_maximalIdeal y.isPrime.ne_top) fun h ↦ hy (PrimeSpectrum.ext h)
  exact_mod_cast Ideal.height_strict_mono_of_isPrime hlt

/-- The local rings of an open subscheme are those of the scheme. -/
theorem ringKrullDim_stalk_opens {X : Scheme.{u}} (U : X.Opens) (x : U) :
    ringKrullDim (U.toScheme.presheaf.stalk x) = ringKrullDim (X.presheaf.stalk x.1) :=
  ringKrullDim_eq_of_ringEquiv (U.stalkIso x).commRingCatIsoToRingEquiv

end AlgebraicGeometry
