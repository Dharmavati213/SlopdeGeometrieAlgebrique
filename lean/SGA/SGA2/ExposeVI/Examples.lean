/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafExtLocal
import SGA.SGA2.ExposeVI.Excision
import SGA.SGA2.ExposeVI.SupportObjectHom
import SGA.SGA2.ExposeVI.AffineExtComparison
import SGA.SGA2.ExposeI.RingedSpaceSupportHom

/-!
# Concrete checks for VI.1.2 and the ringed-space Hom identity
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

/-- VI.1.2 in degree zero: sheafification of local module Ext is the
original local-linear Hom sheaf. -/
def VI_1_2_zero {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
    (F : SheafOfModules.{u} R) :
    moduleExtPresheafFunctor R F 0 ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F :=
  moduleSheafExtSheafificationIso_zero R F

/-- I.1.6/I.1.7 on a ringed space: maps from the structure sheaf into a
supported module sheaf are the supported sections. -/
def VI_ringedSupportHom {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
    (Z : Closeds X) (F : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ moduleGammaZSheaf R Z F) ≃
      (moduleGammaZSheaf R Z F).sections :=
  ExposeI.ringedSpaceSupportHomEquiv R Z F

/-- VI.1.4.3 on an arbitrary ringed space: supported Hom is Hom into the
supported coefficient sheaf. -/
def VI_1_4_3_check {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
    (F G : SheafOfModules.{u} R) (Z : Closeds X) :
    ExposeI.gammaZ (moduleSheafHomAb (Opens.grothendieckTopology X) F G) Z ≃+
      (F ⟶ moduleGammaZSheaf R Z G) :=
  VI_1_4_3 R F G Z

/-- VI.2.3 for the structure sheaf over `ℤ` along `(2)`, in every degree. -/
def VI_2_3_int_two (n : ℕ) :
    let R := CommRingCat.of ℤ
    (_root_.localCohomology (Ideal.span ({2} : Set R)) n).obj (ModuleCat.of R R) ≃+
      ExposeI.H_Z (ExposeII.affineSupportClosed (Ideal.span ({2} : Set R)))
        (ExposeII.affineTildeAbSheaf (ModuleCat.of R R)) n :=
  VI_2_3_structure (R := CommRingCat.of ℤ) (Ideal.span ({2} : Set (CommRingCat.of ℤ)))
    (ModuleCat.of (CommRingCat.of ℤ) (CommRingCat.of ℤ)) n

end SGA.SGA2.ExposeVI
