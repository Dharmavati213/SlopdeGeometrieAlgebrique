/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedHom
import SGA.SGA2.ExposeI.ClosedSupportHom
import SGA.SGA2.ExposeI.LocallyClosedSupportInternalHom

/-!
# SGA 2, VI.1.4: support-object forms of supported Hom

VI.1.4.1 is the closed Hom representation of Exposé I applied to the sheaf
of local linear maps. VI.1.4.3 is the already constructed factorization
through the supported coefficient sheaf. The locally closed case uses the
ambient locally closed Hom representation of Exposé I.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- **VI.1.4.1:** supported sections of the Hom sheaf are morphisms from
the closed integer support object. -/
def VI_1_4_1 (F G : SheafOfModules.{u} R) (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (ExposeI.zZX_closed Z ⟶
        moduleSheafHomAb (Opens.grothendieckTopology X) F G) :=
  (ExposeI.closedSupportHomEquiv Z
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G)).symm

/-- **VI.1.4.3:** supported linear Hom is Hom into the supported coefficient
sheaf. -/
def VI_1_4_3 (F G : SheafOfModules.{u} R) (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (F ⟶ moduleGammaZSheaf R Z G) :=
  moduleSupportedHomEquiv R F G Z

/-- **VI.1.4, locally closed:** supported sections of the Hom sheaf are
morphisms from the original locally closed integer support object. -/
def VI_1_4_locallyClosed (F G : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    W.gamma (moduleSheafHomAb (Opens.grothendieckTopology X) F G) ≃+
      (ExposeI.zZX_locallyClosed W ⟶
        moduleSheafHomAb (Opens.grothendieckTopology X) F G) :=
  (ExposeI.locallyClosedSupportHomEquiv W
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G)).symm

end SGA.SGA2.ExposeVI
