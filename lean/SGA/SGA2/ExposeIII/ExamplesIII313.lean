/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.HigherVanishingOnStructure
import SGA.SGA2.ExposeII.AffineRelativeSequence
import Mathlib.RingTheory.Ideal.UFD

/-!
# SGA 2, III.3.13: curves on a normal surface

If a curve is cut by one equation, III.3.12 gives vanishing of supported
cohomology in degrees `> 1`. A noetherian domain fails to be a UFD precisely
when some height-one prime is not principal, so not every curve is a complete
intersection of one equation.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- **III.3.13, principal curve:** a closed set cut by one equation has
vanishing supported cohomology of the structure sheaf in degrees `> 1`. -/
theorem III_3_13_principal {R : CommRingCat.{u}} [IsNoetherianRing R] (f : R)
    {i : ℕ} (hi : 1 < i) :
    Subsingleton (ExposeI.H_Z
      (ExposeII.affineSupportClosed (ExposeII.koszulIdeal ([f] : List R)))
      (ExposeII.affineTildeAbSheaf (ModuleCat.of R R)) i) :=
  III_3_12_structure ([f] : List R) (by simpa using hi)

/-- **III.3.13, non-complete-intersection:** a noetherian domain that is not
a UFD has a height-one prime which is not principal, hence a curve not cut
by a single equation. -/
theorem III_3_13_exists_non_principal {R : Type u} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (h : ¬ UniqueFactorizationMonoid R) :
    ∃ (p : Ideal R) (_ : p.IsPrime), p.height = 1 ∧ ¬ p.IsPrincipal := by
  contrapose! h
  exact UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one fun p _ hp =>
    h p inferInstance hp

/-- **III.3.13, relative vanishing:** on a noetherian affine, supported
cohomology of the structure sheaf in degree `n+2` agrees with ordinary
cohomology of the complement in degree `n+1`. If the complement is affine,
the right-hand side vanishes for `n+1 > 0`. -/
def III_3_13_relative {R : CommRingCat.{u}} [IsNoetherianRing R]
    (Z : Closeds (Spec R)) (n : ℕ) :
    ExposeI.H_Z Z (ExposeII.affineTildeAbSheaf (ModuleCat.of R R)) (n + 2) ≃+
      ExposeI.H (ExposeI.restrictToOpen
        (ExposeII.affineTildeAbSheaf (ModuleCat.of R R)) Z.compl) (n + 1) :=
  ExposeII.affineSupportedCohomologyEquivOpen (ModuleCat.of R R) Z n

end SGA.SGA2.ExposeIII
