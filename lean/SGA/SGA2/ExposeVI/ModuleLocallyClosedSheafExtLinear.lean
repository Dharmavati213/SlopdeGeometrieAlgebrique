/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSheafExtLinear
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportedSheaf

/-!
# SGA 2, VI.1.1: locally supported Ext with actual scalar structures

The module-valued Hom and locally supported-section functors give supported
sheaf Ext as actual module sheaves and global supported Ext as modules over
the global structure ring. Exact forgetting of scalars recovers the original
additive-valued derived functors, naturally in coefficients and every degree.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (S : Sheaf CommRingCat.{u} X)

local notation "R" => commRingSheafToRing (Opens.grothendieckTopology X) S

variable (F : SheafOfModules.{u}
  (commRingSheafToRing (Opens.grothendieckTopology X) S)) (W : ExposeI.LocallyClosedIn X)

/-- The actual locally supported Hom functor with its local module structures. -/
def moduleLocallyClosedSheafHomLinearFunctor :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  moduleSheafHomFunctor (Opens.grothendieckTopology X) F ⋙
    moduleGammaLocallyClosedSheafFunctor R W

instance : (moduleLocallyClosedSheafHomLinearFunctor S F W).Additive := by
  dsimp [moduleLocallyClosedSheafHomLinearFunctor]
  infer_instance

instance moduleLocallyClosedSheafHomLinearFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleLocallyClosedSheafHomLinearFunctor S F W) := by
  dsimp [moduleLocallyClosedSheafHomLinearFunctor]
  infer_instance

/-- Forgetting scalar structure recovers the unchanged supported Hom sheaf functor. -/
def moduleLocallyClosedSheafHomLinearForgetIso :
    moduleLocallyClosedSheafHomLinearFunctor S F W ⋙ SheafOfModules.toSheaf R ≅
      moduleLocallyClosedSheafHomFunctor R F W :=
  Functor.isoWhiskerLeft (moduleSheafHomFunctor (Opens.grothendieckTopology X) F)
      (moduleGammaLocallyClosedSheafForgetIso R W) ≪≫
    Functor.isoWhiskerRight (moduleSheafHomFunctorForgetIso (Opens.grothendieckTopology X) F)
      (ExposeI.underlineGammaLocallyClosedFunctor W)

/-- **VI.1.1:** locally supported sheaf Ext as an actual sheaf of modules. -/
def moduleLocallyClosedSheafExtLinearFunctor (n : ℕ) :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  (moduleLocallyClosedSheafHomLinearFunctor S F W).rightDerived n

/-- The canonical underlying additive sheaf is the original supported sheaf Ext. -/
def moduleLocallyClosedSheafExtLinearForgetIso (n : ℕ) :
    moduleLocallyClosedSheafExtLinearFunctor S F W n ⋙ SheafOfModules.toSheaf R ≅
      moduleLocallyClosedSheafExtFunctor R F W n := by
  have : (moduleLocallyClosedSheafHomFunctor R F W).Additive := inferInstance
  exact (ExposeI.rightDerivedPostcomposeIso (moduleLocallyClosedSheafHomLinearFunctor S F W)
    (SheafOfModules.toSheaf R) n).symm ≪≫
      ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSheafHomLinearForgetIso S F W) n

/-- The original Hom module sheaf is recovered in degree zero. -/
def moduleLocallyClosedSheafExtLinearZeroIso :
    moduleLocallyClosedSheafExtLinearFunctor S F W 0 ≅
      moduleLocallyClosedSheafHomLinearFunctor S F W :=
  (moduleLocallyClosedSheafHomLinearFunctor S F W).rightDerivedZeroIsoSelf

/-- Global supported linear Hom, with its actual global-ring scalar action. -/
def moduleLocallyClosedSupportedHomLinearFunctor :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} (S.obj.obj (op (⊤ : Opens X))) :=
  moduleLocallyClosedSheafHomLinearFunctor S F W ⋙
    SheafOfModules.evaluation R (op (⊤ : Opens X))

instance : (moduleLocallyClosedSupportedHomLinearFunctor S F W).Additive := by
  have : (SheafOfModules.evaluation R (op (⊤ : Opens X))).Additive := ⟨rfl⟩
  dsimp [moduleLocallyClosedSupportedHomLinearFunctor]
  infer_instance

/-- The underlying additive global Hom agrees naturally with the original functor. -/
def moduleLocallyClosedSupportedHomLinearForgetIso :
    moduleLocallyClosedSupportedHomLinearFunctor S F W ⋙
        forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat ≅
      moduleLocallyClosedSupportedHomFunctor R F W :=
  Functor.isoWhiskerRight (moduleLocallyClosedSheafHomLinearForgetIso S F W)
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))

/-- **VI.1.1:** actual locally supported Ext modules over the global structure ring. -/
def moduleLocallyClosedSupportedExtLinearFunctor (n : ℕ) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} (S.obj.obj (op (⊤ : Opens X))) :=
  (moduleLocallyClosedSupportedHomLinearFunctor S F W).rightDerived n

/-- In every degree, the global scalar-valued construction recovers the
original supported Ext groups after forgetting scalars. -/
def moduleLocallyClosedSupportedExtLinearForgetIso (n : ℕ) :
    moduleLocallyClosedSupportedExtLinearFunctor S F W n ⋙
        forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat ≅
      moduleLocallyClosedSupportedExtFunctor R F W n :=
  (ExposeI.rightDerivedPostcomposeIso (moduleLocallyClosedSupportedHomLinearFunctor S F W)
    (forget₂ (ModuleCat (S.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat) n).symm ≪≫
      ExposeI.rightDerivedFunctorIso (moduleLocallyClosedSupportedHomLinearForgetIso S F W) n

end SGA.SGA2.ExposeVI
