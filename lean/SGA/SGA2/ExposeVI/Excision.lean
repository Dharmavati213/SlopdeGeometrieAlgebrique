/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeI.SupportedExcision

/-!
# SGA 2, VI.1.3: excision for supported Hom

If the support lies in an open, additive excision of Exposé I applied to the
sheaf of local linear maps identifies supported cohomology of that Hom sheaf
on `X` with the same groups on the open. Degree zero is the original
supported linear Hom.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Excision for the Hom sheaf. If `Z ⊆ V`, supported cohomology
of local linear maps on `X` agrees with the same groups after restriction
to `V`. In positive degrees these groups differ from supported module Ext. -/
def homSheafCohomologyExcision {Z : Closeds X} {V : Opens X}
    (hZ : (Z : Set X) ⊆ (V : Set X))
    (F G : SheafOfModules.{u} R) (n : ℕ) :
    ExposeI.H_Z Z (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n ≃+
      ExposeI.H_Z (ExposeI.closedSupportOnOpen Z V)
        (ExposeI.restrictToOpen
          (moduleSheafHomAb (Opens.grothendieckTopology X) F G) V) n :=
  ExposeI.supportedExcisionEquiv hZ
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G) n

/-- Degree zero of VI.1.3 is excision of supported linear Hom. -/
def VI_1_3_zero {Z : Closeds X} {V : Opens X} (hZ : (Z : Set X) ⊆ (V : Set X))
    (F G : SheafOfModules.{u} R) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      ExposeI.gammaZ
        (ExposeI.restrictToOpen
          (moduleSheafHomAb (Opens.grothendieckTopology X) F G) V)
        (ExposeI.closedSupportOnOpen Z V) :=
  (ExposeI.H_Z_zero_gammaZ_addEquiv Z
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G)).symm.trans
    ((homSheafCohomologyExcision R hZ F G 0).trans
      (ExposeI.H_Z_zero_gammaZ_addEquiv (ExposeI.closedSupportOnOpen Z V)
        (ExposeI.restrictToOpen
          (moduleSheafHomAb (Opens.grothendieckTopology X) F G) V)))

end SGA.SGA2.ExposeVI
