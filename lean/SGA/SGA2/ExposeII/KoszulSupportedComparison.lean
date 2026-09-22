/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.AffineCohomologyComparison
import SGA.SGA2.ExposeII.KoszulLocalCohomology
import SGA.SGA2.ExposeII.AffineComparisonZero

/-!
# SGA 2, II.5: stable Koszul cohomology versus topological supported cohomology

Over a noetherian ring, the already proved Ext-to-Koszul isomorphism II.8
and the affine comparison II.(7.3) identify stable Koszul cohomology of an
arbitrary finite family with the independently defined supported sheaf
cohomology of Exposé I, naturally in every degree.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Abelian

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- **II.5, noetherian case:** stable Koszul cohomology of a finite family
agrees with actual supported sheaf cohomology of the associated sheaf, in
every degree. -/
def II_5 [IsNoetherianRing R] (fs : List R) (n : ℕ) :
    stableKoszulCohomologyFunctor fs n ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      affineTildeAbFunctor ⋙
        extFunctorObj (ExposeI.zZX_closed (affineSupportClosed (koszulIdeal fs))) n :=
  Functor.isoWhiskerRight (localCohomologyIsoStableKoszul fs n).symm
      (forget₂ (ModuleCat R) AddCommGrpCat) ≪≫
    affineLocalCohomologyNatIso (koszulIdeal fs) n

/-- Objectwise form of II.5. -/
def II_5_addEquiv [IsNoetherianRing R] (fs : List R) (M : ModuleCat.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (stableKoszulCohomology fs M n) ≃+
      ExposeI.H_Z (affineSupportClosed (koszulIdeal fs)) (affineTildeAbSheaf M) n :=
  ((II_5 fs n).app M).addCommGroupIsoToAddEquiv

/-- Degree zero of II.5 holds without a noetherian hypothesis, by the
already proved torsion comparison. -/
def II_5_zero (fs : List R) (M : ModuleCat.{u} R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (stableKoszulCohomology fs M 0) ≃+
      ExposeI.gammaZ (affineTildeAbSheaf M) (affineSupportClosed (koszulIdeal fs)) :=
  (stableKoszulCohomologyZeroIsoGammaZ fs M).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeII
