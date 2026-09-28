/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.PrincipalKoszul
import SGA.SGA2.ExposeII.FiniteGenerators
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# SGA 2, Exposé II: boundary cases for the algebraic constructions

For the zero generator over the integers, first Koszul homology is nonzero,
although its inverse system is essentially zero: the transition from exponent
two to exponent one already vanishes. Thus II.11 concerns transition maps and
does not assert that individual homology modules vanish.

An empty family generates the zero ideal even at exponent zero; cofinality
with ordinary ideal powers still applies in this case.
-/

open CategoryTheory Limits

namespace SGA.SGA2.ExposeII

/-- The zero generator has nonzero first Koszul homology over `ℤ`. -/
theorem principalKoszul_zero_int_homologyOne_nonzero :
    ¬ IsZero ((principalKoszul (ModuleCat.of ℤ ℤ) 0).homology 1) := by
  intro h
  have hz := (principalKoszulHomologyOneIso (ModuleCat.of ℤ ℤ) 0).isZero_iff.mp h
  have := ModuleCat.subsingleton_of_isZero hz
  let x : Submodule.torsionBy ℤ ℤ (0 : ℤ) := ⟨1, by simp⟩
  have hx : x = 0 := Subsingleton.elim _ _
  have : (1 : ℤ) = 0 := congrArg Subtype.val hx
  exact one_ne_zero this

/-- Despite its nonzero first homology terms, the zero-generator homology
system over `ℤ` is essentially zero. -/
theorem principalKoszul_zero_int_homologyOneSystem_essentiallyZero :
    IsEssentiallyZero (principalKoszulHomologySystem (ModuleCat.of ℤ ℤ) 0 1) := by
  have : IsNoetherian ℤ (ModuleCat.of ℤ ℤ) := inferInstanceAs (IsNoetherian ℤ ℤ)
  exact principalKoszulHomologySystem_isEssentiallyZero _ _ _ (by decide)

/-- For the zero generator, the transition from exponent two to exponent one
already induces zero on first Koszul homology. -/
theorem principalKoszul_zero_int_homologyTransition_two_one :
    HomologicalComplex.homologyMap
      (principalKoszulTransition (ModuleCat.of ℤ ℤ) (0 : ℤ)
        (show 1 ≤ 2 by decide)) 1 = 0 := by
  apply (cancel_mono (principalKoszulHomologyOneIso (ModuleCat.of ℤ ℤ)
    ((0 : ℤ) ^ 1)).hom).mp
  rw [principalKoszulHomologyOneIso_naturality]
  have ht : torsionTransition (M := ℤ) (0 : ℤ) (show 1 ≤ 2 by decide) = 0 := by
    ext x
    simp [torsionTransition]
  rw [ht]
  simp

/-- Empty families generate the zero ideal at every exponent, including zero. -/
theorem generatorPowerIdeal_empty {R : Type*} [CommRing R] (n : ℕ) :
    generatorPowerIdeal (Empty.elim : Empty → R) n = ⊥ := by
  simp [generatorPowerIdeal]

end SGA.SGA2.ExposeII
