/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.AssociatedPrimes

/-!
# SGA 2, VII.1.3: Hom-vanishing detects the zero module

Algebraic input to the vanishing criteria of Exposé VII: if a finite module
`P` meets the support of a finite module `H`, and every linear map `P → H`
vanishes, then `H` itself is zero. The comparison uses the III.1.3 formula
`Ass Hom(P,H) = Supp P ∩ Ass H`.
-/

universe u

namespace SGA.SGA2.ExposeVII

open SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (P H : Type u) [AddCommGroup P] [Module R P] [Module.Finite R P]
variable [AddCommGroup H] [Module R H] [Module.Finite R H]

/-- VII.1.3: vanishing of `Hom(P,H)` with `Supp H ⊆ Supp P` forces `H = 0`. -/
theorem eq_zero_of_subsingleton_hom_of_support_le
    (hHom : Subsingleton (P →ₗ[R] H))
    (hSupp : Module.support R H ⊆ Module.support R P) :
    Subsingleton H := by
  have : Module.Finite R (P →ₗ[R] H) := inferInstance
  have hAssHomEmpty : associatedPrimes R (P →ₗ[R] H) = ∅ :=
    (associatedPrimes_eq_empty_iff_subsingleton (R := R) (P →ₗ[R] H)).mpr hHom
  refine (associatedPrimes_eq_empty_iff_subsingleton (R := R) H).mp ?_
  ext p
  constructor
  · intro hp
    let pSpec : PrimeSpectrum R := ⟨p, (mem_associatedPrimes_iff (R := R) H).mp hp |>.1⟩
    have hpSpec : pSpec ∈ associatedPrimeSpectrum (R := R) H := by
      simpa [associatedPrimeSpectrum, pSpec] using hp
    have hpSupp : pSpec ∈ Module.support R H :=
      (mem_support_iff_exists_associatedPrime (R := R) H pSpec).mpr ⟨p, hp, le_rfl⟩
    have hin : pSpec ∈ Module.support R P ∩ associatedPrimeSpectrum (R := R) H :=
      ⟨hSupp hpSupp, hpSpec⟩
    have hinHom : pSpec ∈ associatedPrimeSpectrum (R := R) (P →ₗ[R] H) := by
      rw [associatedPrimeSpectrum_linearMap (R := R) (M := H) (N := P)]
      exact hin
    have : pSpec.asIdeal ∈ associatedPrimes R (P →ₗ[R] H) := by
      simpa [associatedPrimeSpectrum] using hinHom
    simp [hAssHomEmpty] at this
  · intro h
    exact False.elim h

/-- Equivalent form: empty associated primes of `H`. -/
theorem associatedPrimes_eq_empty_of_subsingleton_hom_of_support_le
    (hHom : Subsingleton (P →ₗ[R] H))
    (hSupp : Module.support R H ⊆ Module.support R P) :
    associatedPrimes R H = ∅ :=
  (associatedPrimes_eq_empty_iff_subsingleton (R := R) H).mpr
    (eq_zero_of_subsingleton_hom_of_support_le P H hHom hSupp)

end SGA.SGA2.ExposeVII
