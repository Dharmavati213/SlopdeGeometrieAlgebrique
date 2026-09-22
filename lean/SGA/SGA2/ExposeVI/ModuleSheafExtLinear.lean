/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleInternalHomLinear
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeI.RightDerivedPostcomposition

/-!
# SGA 2, VI.1.1: module structures on actual sheaf Ext

Derive the genuine module-valued internal Hom functor in module sheaves.
Exact forgetting of scalars identifies its underlying additive sheaves
naturally with the already defined sheaf Ext. The same construction works
for closed-supported sheaf Ext using the actual supported module sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (S : Sheaf CommRingCat.{u} X)

local notation "R" => commRingSheafToRing (Opens.grothendieckTopology X) S

/-- The genuine module-valued internal Hom is left exact. -/
instance moduleSheafHomFunctor_preservesFiniteLimits (F : SheafOfModules.{u} R) :
    PreservesFiniteLimits (moduleSheafHomFunctor (Opens.grothendieckTopology X) F) := by
  have : PreservesFiniteLimits
      (moduleSheafHomFunctor (Opens.grothendieckTopology X) F ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteLimits_of_natIso
      (moduleSheafHomFunctorForgetIso (Opens.grothendieckTopology X) F).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleSheafHomFunctor (Opens.grothendieckTopology X) F) (SheafOfModules.toSheaf R)

/-- **VI.1.1:** ordinary sheaf Ext with its actual local module structures. -/
def moduleSheafExtFunctor (F : SheafOfModules.{u} R) (n : ℕ) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  (moduleSheafHomFunctor (Opens.grothendieckTopology X) F).rightDerived n

/-- Degree zero recovers the genuine internal Hom module sheaf. -/
def moduleSheafExtZeroIso (F : SheafOfModules.{u} R) :
    moduleSheafExtFunctor S F 0 ≅ moduleSheafHomFunctor (Opens.grothendieckTopology X) F :=
  (moduleSheafHomFunctor (Opens.grothendieckTopology X) F).rightDerivedZeroIsoSelf

/-- Exact forgetting of scalars recovers the unchanged additive sheaf Ext. -/
def moduleSheafExtForgetIso (F : SheafOfModules.{u} R) (n : ℕ) :
    moduleSheafExtFunctor S F n ⋙ SheafOfModules.toSheaf R ≅
      moduleSheafExtAbFunctor R F n :=
  (ExposeI.rightDerivedPostcomposeIso (moduleSheafHomFunctor (Opens.grothendieckTopology X) F)
    (SheafOfModules.toSheaf R) n).symm ≪≫
      ExposeI.rightDerivedFunctorIso
        (moduleSheafHomFunctorForgetIso (Opens.grothendieckTopology X) F) n

/-- Actual module-valued Hom with closed support, before derivation. -/
def moduleClosedSheafHomFunctor (F : SheafOfModules.{u} R) (Z : Closeds X) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  moduleSheafHomFunctor (Opens.grothendieckTopology X) F ⋙ moduleGammaZSheafFunctor R Z

instance (F : SheafOfModules.{u} R) (Z : Closeds X) :
    (moduleClosedSheafHomFunctor S F Z).Additive := by
  dsimp [moduleClosedSheafHomFunctor]
  infer_instance

instance moduleClosedSheafHomFunctor_preservesFiniteLimits
    (F : SheafOfModules.{u} R) (Z : Closeds X) :
    PreservesFiniteLimits (moduleClosedSheafHomFunctor S F Z) := by
  dsimp [moduleClosedSheafHomFunctor]
  infer_instance

/-- The original additive supported-Hom sheaf is the genuine underlying sheaf. -/
def moduleClosedSheafHomForgetIso (F : SheafOfModules.{u} R) (Z : Closeds X) :
    moduleClosedSheafHomFunctor S F Z ⋙ SheafOfModules.toSheaf R ≅
      moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.underlineGammaZFunctor Z :=
  Functor.isoWhiskerLeft (moduleSheafHomFunctor (Opens.grothendieckTopology X) F)
      (moduleGammaZSheafForgetIso R Z) ≪≫
    Functor.isoWhiskerRight (moduleSheafHomFunctorForgetIso (Opens.grothendieckTopology X) F)
      (ExposeI.underlineGammaZFunctor Z)

/-- **VI.1.1:** closed-supported sheaf Ext as an actual module sheaf. -/
def moduleClosedSheafExtFunctor (F : SheafOfModules.{u} R) (Z : Closeds X) (n : ℕ) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  (moduleClosedSheafHomFunctor S F Z).rightDerived n

/-- Degree zero is the actual closed-supported Hom module sheaf. -/
def moduleClosedSheafExtZeroIso (F : SheafOfModules.{u} R) (Z : Closeds X) :
    moduleClosedSheafExtFunctor S F Z 0 ≅ moduleClosedSheafHomFunctor S F Z :=
  (moduleClosedSheafHomFunctor S F Z).rightDerivedZeroIsoSelf

local instance (F : SheafOfModules.{u} R) (Z : Closeds X) :
    (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
      ExposeI.underlineGammaZFunctor Z).Additive := by
  have : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  have : (ExposeI.underlineGammaZFunctor Z).Additive := inferInstance
  infer_instance

/-- In every degree, forgetting scalar action gives the original additive
derived closed-supported Hom functor. -/
def moduleClosedSheafExtForgetIso (F : SheafOfModules.{u} R) (Z : Closeds X) (n : ℕ) :
    moduleClosedSheafExtFunctor S F Z n ⋙ SheafOfModules.toSheaf R ≅
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.underlineGammaZFunctor Z).rightDerived n := by
  have : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  have : (ExposeI.underlineGammaZFunctor Z).Additive := inferInstance
  exact (ExposeI.rightDerivedPostcomposeIso (moduleClosedSheafHomFunctor S F Z)
    (SheafOfModules.toSheaf R) n).symm ≪≫
      ExposeI.rightDerivedFunctorIso (moduleClosedSheafHomForgetIso S F Z) n

end SGA.SGA2.ExposeVI
