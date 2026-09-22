/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulSupportedComparison
import SGA.SGA2.ExposeII.TopologicalNoetherianFlasque
import SGA.SGA2.ExposeII.QuasiCoherentSupported
import SGA.SGA2.ExposeII.GeneralSchemeComparison
import Mathlib.Algebra.EuclideanDomain.Int

/-!
# Concrete checks for II.5 and II.10
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SGA.SGA2.ExposeII

/-- II.5 in degree zero for the singleton family `(2)` over `ℤ`. -/
def II_5_zero_int_two :
    let R := CommRingCat.of ℤ
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
        (stableKoszulCohomology (R := R) ([2] : List R) (ModuleCat.of R R) 0) ≃+
      ExposeI.gammaZ (affineTildeAbSheaf (R := R) (ModuleCat.of R R))
        (affineSupportClosed (R := R) (koszulIdeal (R := R) ([2] : List R))) :=
  II_5_zero (R := CommRingCat.of ℤ) ([2] : List (CommRingCat.of ℤ))
    (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ))

/-- II.5 in every degree over the noetherian ring `ℤ`, for the family `(2)`. -/
def II_5_int_two (n : ℕ) :
    let R := CommRingCat.of ℤ
    (forget₂ (ModuleCat R) AddCommGrpCat).obj
        (stableKoszulCohomology (R := R) ([2] : List R) (ModuleCat.of R R) n) ≃+
      ExposeI.H_Z (affineSupportClosed (R := R) (koszulIdeal (R := R) ([2] : List R)))
        (affineTildeAbSheaf (R := R) (ModuleCat.of R R)) n :=
  II_5_addEquiv (R := CommRingCat.of ℤ) ([2] : List (CommRingCat.of ℤ))
    (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ)) n

/-- The spectrum of `ℤ` is a noetherian space, so II.10 applies. -/
theorem primeSpectrum_int_noetherian :
    NoetherianSpace (PrimeSpectrum (CommRingCat.of ℤ)) :=
  inferInstance

/-- II.6.b over `ℤ` along `(2)`. -/
def II_6_b_int_two (n : ℕ) :
    let R := CommRingCat.of ℤ
    (_root_.localCohomology (Ideal.span ({2} : Set R)) n).obj (ModuleCat.of R R) ≃+
      ExposeI.H_Z (affineSupportClosed (Ideal.span ({2} : Set R)))
        (affineTildeAbSheaf (ModuleCat.of R R)) n :=
  II_6_b_of_sheaf (R := CommRingCat.of ℤ) (Ideal.span ({2} : Set (CommRingCat.of ℤ)))
    (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ)) n

/-- Associated sheaves on `Spec ℤ` are quasi-coherent. -/
instance affineTilde_int_isQuasicoherent :
    (tilde (R := CommRingCat.of ℤ)
      (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ))).IsQuasicoherent :=
  inferInstance

end SGA.SGA2.ExposeII
