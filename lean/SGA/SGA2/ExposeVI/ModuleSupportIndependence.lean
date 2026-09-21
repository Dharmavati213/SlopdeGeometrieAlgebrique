/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.LocallyClosedExtSequences
import SGA.SGA2.ExposeI.OpenDerivedSupportedSheaves

/-!
# Independence of support presentations for actual supported module Ext

The locally closed functors depend only on the underlying support subset.
For the canonical presentation of a closed subset, the global functor is
naturally the original closed-support functor, in every derived degree.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R)

/-- The actual supported Hom sheaf is independent of its locally closed witness. -/
def moduleLocallyClosedSheafHomIndependenceIso {W W' : ExposeI.LocallyClosedIn X}
    (h : W.asSet = W'.asSet) :
    moduleLocallyClosedSheafHomFunctor R F W ≅ moduleLocallyClosedSheafHomFunctor R F W' :=
  Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
    (ExposeI.underlineGammaLocallyClosedIndependenceIso h)

/-- The original supported sheaf Ext is independent of the support witness. -/
def moduleLocallyClosedSheafExtIndependenceIso {W W' : ExposeI.LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (n : ℕ) :
    moduleLocallyClosedSheafExtFunctor R F W n ≅ moduleLocallyClosedSheafExtFunctor R F W' n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSheafHomIndependenceIso R F h) n

/-- The original global supported Hom is independent of the support witness. -/
def moduleLocallyClosedSupportedHomIndependenceIso {W W' : ExposeI.LocallyClosedIn X}
    (h : W.asSet = W'.asSet) :
    moduleLocallyClosedSupportedHomFunctor R F W ≅
      moduleLocallyClosedSupportedHomFunctor R F W' :=
  moduleLocallyClosedSupportedHomGammaIso R F W ≪≫
    Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.gammaLocallyClosedIndependenceIso h) ≪≫
        (moduleLocallyClosedSupportedHomGammaIso R F W').symm

/-- The actual supported Ext groups are independent of the support witness. -/
def moduleLocallyClosedSupportedExtIndependenceIso {W W' : ExposeI.LocallyClosedIn X}
    (h : W.asSet = W'.asSet) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ≅
      moduleLocallyClosedSupportedExtFunctor R F W' n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSupportedHomIndependenceIso R F h) n

/-- The canonical closed witness recovers the actual closed supported Hom functor. -/
def moduleLocallyClosedSupportedHomClosedIso (Z : Closeds X) :
    moduleLocallyClosedSupportedHomFunctor R F (ExposeI.LocallyClosedIn.ofOpenClosed ⊤ Z) ≅
      moduleSupportedHomFunctor R F Z :=
  moduleLocallyClosedSupportedHomGammaIso R F _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.gammaLocallyClosedAmbientIso (ExposeI.LocallyClosedIn.ofOpenClosed ⊤ Z) Z rfl)

/-- Closed support as a locally closed witness gives the original Ext groups,
derived in module sheaves, in every degree. -/
def moduleLocallyClosedSupportedExtClosedIso (Z : Closeds X) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F (ExposeI.LocallyClosedIn.ofOpenClosed ⊤ Z) n ≅
      moduleSupportedExtFunctor R F Z n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSupportedHomClosedIso R F Z) n

/-- Support on the whole space imposes no condition on the original module Hom. -/
def moduleSupportedHomTopIso :
    moduleSupportedHomFunctor R F (⊤ : Closeds X) ≅ preadditiveCoyoneda.obj (op F) :=
  NatIso.ofComponents (fun G ↦
    ((ExposeI.gammaZTopSectionsEquiv
      (moduleSheafHomAb (Opens.grothendieckTopology X) F G) ⊤).trans
        (moduleSheafHomAbGlobalEquiv R F G)).toAddCommGrpIso)
    (fun a ↦ by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      ext x
      rfl)

/-- Actual full-support Ext is ordinary Ext in the module-sheaf category. -/
def moduleSupportedExtTopIso (n : ℕ) :
    moduleSupportedExtFunctor R F (⊤ : Closeds X) n ≅ Abelian.extFunctorObj F n :=
  ExposeI.rightDerivedFunctorIso (moduleSupportedHomTopIso R F) n ≪≫
    ExposeI.rightDerivedCoyonedaNatIsoExt F n

/-- The canonical full-space locally closed witness recovers ordinary module Ext. -/
def moduleLocallyClosedSupportedExtTopIso (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F
        (ExposeI.LocallyClosedIn.ofOpenClosed ⊤ ⊤) n ≅ Abelian.extFunctorObj F n :=
  moduleLocallyClosedSupportedExtClosedIso R F ⊤ n ≪≫ moduleSupportedExtTopIso R F n

end SGA.SGA2.ExposeVI
