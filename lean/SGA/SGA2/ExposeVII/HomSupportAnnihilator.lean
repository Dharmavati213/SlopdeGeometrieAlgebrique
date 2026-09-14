/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Support
import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# SGA 2, VII.1.1 (affine end): Hom killed by ideal powers

On an affine noetherian chart the comparison
`colim Hom(F/JᵏF, H) → Hom(F, H)` is an isomorphism whenever
`Supp H ⊆ V(J)`. The algebraic content recorded here is that every map into
such an `H` is annihilated by a power of `J`.
-/

universe u v w

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (J : Ideal R) (H : Type v) [AddCommGroup H] [Module R H] [Module.Finite R H]
variable (F : Type w) [AddCommGroup F] [Module R F]

/-- Finite modules supported in `V(J)` are annihilated by a power of `J`. -/
theorem exists_pow_le_annihilator_of_support_le_zeroLocus
    (hSupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ k : ℕ, J ^ k ≤ Module.annihilator R H := by
  have hzl : Module.support R H = PrimeSpectrum.zeroLocus (Module.annihilator R H : Set R) :=
    Module.support_eq_zeroLocus
  have hsub : PrimeSpectrum.zeroLocus (Module.annihilator R H : Set R) ⊆
      PrimeSpectrum.zeroLocus (J : Set R) := by
    simpa [hzl] using hSupp
  have hrad : J ≤ Ideal.radical (Module.annihilator R H) :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp hsub
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian J)

/-- Every linear map into a module supported in `V(J)` is killed by a power of `J`.
This is the affine end of the proof of VII.1.1. -/
theorem exists_pow_smul_eq_zero_linearMap_of_support_le
    (hSupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R))
    (f : F →ₗ[R] H) :
    ∃ k : ℕ, ∀ a ∈ J ^ k, a • f = 0 := by
  obtain ⟨k, hk⟩ := exists_pow_le_annihilator_of_support_le_zeroLocus J H hSupp
  refine ⟨k, fun a ha ↦ ?_⟩
  ext x
  exact Module.mem_annihilator.mp (hk ha) (f x)

/-- The whole Hom module is likewise annihilated by a power of `J`. -/
theorem exists_pow_le_annihilator_linearMap_of_support_le
    (hSupp : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    ∃ k : ℕ, J ^ k ≤ Module.annihilator R (F →ₗ[R] H) := by
  obtain ⟨k, hk⟩ := exists_pow_le_annihilator_of_support_le_zeroLocus J H hSupp
  refine ⟨k, fun a ha ↦ ?_⟩
  ext f x
  exact Module.mem_annihilator.mp (hk ha) (f x)

end SGA.SGA2.ExposeVII
