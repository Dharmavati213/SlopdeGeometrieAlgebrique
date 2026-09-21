/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedHom
import SGA.SGA2.ExposeVI.TensorSupportHom
import SGA.SGA2.ExposeI.ClosedSupportHom
import SGA.SGA2.ExposeI.LocallyClosedSupportInternalHom

/-!
# SGA 2, VI.1.4: support-object forms of supported Hom

VI.1.4.1 uses the actual structure-module support object and module-valued
internal Hom. VI.1.4.3 is the factorization through the supported coefficient
sheaf. The underlying additive integer-support representations are retained
as separate helpers, for closed and locally closed support.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Supported sections of the additive Hom sheaf are morphisms from
the closed integer support object. -/
def supportedHomIntegerRepresentation (F G : SheafOfModules.{u} R) (Z : Closeds X) :
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

/-- Locally supported sections of the additive Hom sheaf are
morphisms from the original locally closed integer support object. -/
def locallyClosedSupportedHomIntegerRepresentation (F G : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    W.gamma (moduleSheafHomAb (Opens.grothendieckTopology X) F G) ≃+
      (ExposeI.zZX_locallyClosed W ⟶
        moduleSheafHomAb (Opens.grothendieckTopology X) F G) :=
  (ExposeI.locallyClosedSupportHomEquiv W
    (moduleSheafHomAb (Opens.grothendieckTopology X) F G)).symm

variable {R}

/-- **VI.1.4.1:** supported linear Hom is module Hom from the structure-module
support object into the actual module-valued internal Hom. -/
def VI_1_4_1 (S : Sheaf CommRingCat.{u} X)
    (F G : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
    (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (moduleClosedSupport (commRingSheafToRing (Opens.grothendieckTopology X) S) Z ⟶
        moduleSheafHom (Opens.grothendieckTopology X) F G) :=
  moduleSupportedHomStructureEquiv S F G Z

end SGA.SGA2.ExposeVI
