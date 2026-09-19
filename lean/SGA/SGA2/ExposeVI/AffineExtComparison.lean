/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.AffineHomColimit
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeII.AffineExtColimitComparison

/-!
# SGA 2, VI.2.3: affine Ext-colimit comparison

Degree zero is the already constructed quotient-Hom colimit. For the
structure sheaf the comparison in every degree is the affine II.6
identification of algebraic local cohomology with supported sheaf
cohomology. Positive supported Ext vanishes on injective module sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry Abelian
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- **VI.2.3, degree zero:** the quotient-Hom colimit is ideal-power torsion
in ordinary Hom. -/
def VI_2_3_zero {R : Type u} [CommRing R] (I : Ideal R)
    (M N : ModuleCat.{u} R) :
    IsColimit (adicQuotientHomTorsionCocone I M N) :=
  adicQuotientHomTorsionIsColimit I M N

/-- **VI.2.3, structure sheaf, all degrees:** Ext-colimit along `I` agrees
with supported cohomology of the associated sheaf, on a noetherian affine. -/
def VI_2_3_structure [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{u} R) (n : ℕ) :
    (_root_.localCohomology I n).obj N ≃+
      ExposeI.H_Z (affineSupportClosed I) (affineTildeAbSheaf N) n :=
  II_6_b_affine I N n

/-- **VI.2.3, sheaf form on a noetherian affine:** the Ext-colimit functor
agrees with supported sheaf cohomology of associated sheaves. -/
def VI_2_3_sheaf [IsNoetherianRing R] (I : Ideal R) (n : ℕ) :
    _root_.localCohomology I n ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅
      affineTildeAbFunctor ⋙
        extFunctorObj (ExposeI.zZX_closed (affineSupportClosed I)) n :=
  II_6_a_affine I n

end SGA.SGA2.ExposeVI
