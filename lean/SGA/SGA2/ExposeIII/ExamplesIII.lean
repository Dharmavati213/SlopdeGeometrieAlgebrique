/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.SheafExtDepth
import SGA.SGA2.ExposeIII.HigherVanishingOnStructure
import SGA.SGA2.ExposeIII.Equidimensionality
import SGA.SGA2.ExposeIII.AntifilterEquivalence
import SGA.SGA2.ExposeIII.ExamplesIII313
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.Ideal.UFD

/-!
# Concrete checks for III.3.3(v)/(vi) and III.3.12
-/

noncomputable section

open CategoryTheory Abelian AlgebraicGeometry

namespace SGA.SGA2.ExposeIII

/-- III.3.3(vi) for `ℤ` along `(2)`: depth one is detected by Ext of `ℤ/2`. -/
theorem III_3_3_vi_int_two :
    (1 : ℕ∞) ≤ depth (Ideal.span ({2} : Set ℤ)) (ModuleCat.of ℤ ℤ) ↔
      ∀ i < 1, Subsingleton
        (Abelian.Ext (ModuleCat.of ℤ (ℤ ⧸ Ideal.span ({2} : Set ℤ))) (ModuleCat.of ℤ ℤ) i) :=
  III_3_3_vi_quotient (Ideal.span ({2} : Set ℤ)) (ModuleCat.of ℤ ℤ) 1

/-- III.3.12: Koszul vanishing above one generator on `ℤ` along `(2)`. -/
theorem III_3_12_int_two :
    Subsingleton (ExposeI.H_Z
      (ExposeII.affineSupportClosed (R := CommRingCat.of ℤ)
        (ExposeII.koszulIdeal (R := CommRingCat.of ℤ) ([2] : List (CommRingCat.of ℤ))))
      (ExposeII.affineTildeAbSheaf (R := CommRingCat.of ℤ)
        (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ))) 2) :=
  III_3_12_structure (R := CommRingCat.of ℤ)
    ([2] : List (CommRingCat.of ℤ)) (by decide : (1 : ℕ) < 2)

/-- III.3.13, principal curve: vanishing above one equation on `ℤ` along `(2)`. -/
theorem III_3_13_int_two :
    Subsingleton (ExposeI.H_Z
      (ExposeII.affineSupportClosed (R := CommRingCat.of ℤ)
        (ExposeII.koszulIdeal (R := CommRingCat.of ℤ) ([2] : List (CommRingCat.of ℤ))))
      (ExposeII.affineTildeAbSheaf (R := CommRingCat.of ℤ)
        (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ))) 2) :=
  III_3_13_principal (R := CommRingCat.of ℤ) (2 : CommRingCat.of ℤ)
    (by decide : (1 : ℕ) < 2)

/-- The spectrum of a field is connected, as used in III.3.8–III.3.9. -/
theorem primeSpectrum_rat_connected :
    ConnectedSpace (PrimeSpectrum ℚ) :=
  connectedSpace_primeSpectrum (R := ℚ)

/-- III.3.13: a noetherian domain that is a UFD has every height-one prime
principal, so the converse obstruction is exactly failure of unique
factorization. -/
theorem III_3_13_int_UFD :
    UniqueFactorizationMonoid ℤ :=
  inferInstance

end SGA.SGA2.ExposeIII
