/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.AffineCohomologyComparison
import SGA.SGA2.ExposeII.AffineCohomologyVanishing
import SGA.SGA2.ExposeII.KoszulSupportedComparison

/-!
# SGA 2, II.6–II.7 on noetherian affines

The sheaf and global Ext-colimit comparisons of II.6 reduce on a noetherian
affine to the already proved algebraic local-cohomology comparison, and II.5
identifies the Koszul form. The local-to-global spectral sequence of I.2.6
degenerates by affine vanishing, which is the affine case of II.7.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Abelian

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} [IsNoetherianRing R]

/-- **II.6.a, affine:** the Ext-colimit of quotient modules is actual
supported sheaf cohomology of the associated sheaf. -/
def II_6_a_affine (I : Ideal R) (n : ℕ) :
    _root_.localCohomology I n ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      affineTildeAbFunctor ⋙
        extFunctorObj (ExposeI.zZX_closed (affineSupportClosed I)) n :=
  affineLocalCohomologyNatIso I n

/-- **II.6.b, affine:** global Ext-colimit agrees with supported cohomology
because the sheaf comparison of II.6.a is an isomorphism and the space is
affine noetherian. -/
def II_6_b_affine (I : Ideal R) (M : ModuleCat.{u} R) (n : ℕ) :
    (_root_.localCohomology I n).obj M ≃+
      ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf M) n :=
  ((II_6_a_affine I n).app M).addCommGroupIsoToAddEquiv

/-- **II.7, affine:** the local-to-global spectral sequence of I.2.6
degenerates in positive horizontal degrees by ordinary affine vanishing of
associated sheaves. -/
theorem II_7_affine_ordinary_vanishing (M : ModuleCat.{u} R) (p : ℕ) :
    Subsingleton (ExposeI.H (affineTildeAbSheaf M) (p + 1)) :=
  affineTildeAb_H_pos_subsingleton M p

end SGA.SGA2.ExposeII
