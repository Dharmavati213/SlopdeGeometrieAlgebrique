/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedHom
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves

/-!
# SGA 2, VI.1.1: right-derived supported Hom on module sheaves

These derived functors use injective resolutions in the category of module
sheaves, with the genuine sheaf of local linear maps. We construct their
underlying additive groups and sheaves, for closed and locally closed support.
The degree-zero comparisons and positive-degree vanishing on injectives are
proved, and the closed supported-Hom identity of VI.1.4.3 is derived naturally.
Module structures on the internal Hom and derived sheaves, excision, and
VI.1.2's comparison with restriction-derived local Ext remain separate tasks.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

instance (F : SheafOfModules.{u} R) (Z : Closeds X) :
    (moduleSupportedHomFunctor R F Z).Additive := by
  have : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  have : (ExposeI.gammaZSectionsFunctor Z (⊤ : Opens X)).Additive := inferInstance
  dsimp [moduleSupportedHomFunctor]
  infer_instance

instance moduleSupportedHomFunctor_preservesFiniteLimits
    (F : SheafOfModules.{u} R) (Z : Closeds X) :
    PreservesFiniteLimits (moduleSupportedHomFunctor R F Z) := by
  have : PreservesFiniteLimits (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) :=
    inferInstance
  have : PreservesFiniteLimits (ExposeI.gammaZSectionsFunctor Z (⊤ : Opens X)) := inferInstance
  dsimp [moduleSupportedHomFunctor]
  infer_instance

/-- VI.1.1, closed support: the actual supported Ext groups, derived in module sheaves. -/
def moduleSupportedExtFunctor (F : SheafOfModules.{u} R) (Z : Closeds X) (n : ℕ) :
    SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  (moduleSupportedHomFunctor R F Z).rightDerived n

/-- Degree zero is naturally the original supported linear Hom. -/
def moduleSupportedExtZeroIso (F : SheafOfModules.{u} R) (Z : Closeds X) :
    moduleSupportedExtFunctor R F Z 0 ≅ moduleSupportedHomFunctor R F Z :=
  (moduleSupportedHomFunctor R F Z).rightDerivedZeroIsoSelf

/-- Positive supported Ext vanishes on actual injective coefficient module sheaves. -/
theorem moduleSupportedExt_isZero_of_injective
    (F G : SheafOfModules.{u} R) (Z : Closeds X) [Injective G] (n : ℕ) :
    IsZero ((moduleSupportedExtFunctor R F Z (n + 1)).obj G) :=
  (moduleSupportedHomFunctor R F Z).isZero_rightDerived_obj_injective_succ n G

/-- The original closed supported-Hom identity remains a natural comparison after derivation. -/
def moduleSupportedExtViaSupportedSheafIso (F : SheafOfModules.{u} R)
    (Z : Closeds X) (n : ℕ) :
    moduleSupportedExtFunctor R F Z n ≅
      (moduleGammaZSheafFunctor R Z ⋙ preadditiveCoyoneda.obj (op F)).rightDerived n :=
  ExposeI.rightDerivedFunctorIso (moduleSupportedHomFunctorIso R F Z) n

/-- Ordinary internal sheaf Ext, derived in module sheaves, with its additive sheaf values. -/
def moduleSheafExtAbFunctor (F : SheafOfModules.{u} R) (n : ℕ) :
    SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} X :=
  (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).rightDerived n

/-- Degree zero is the actual sheaf of local linear morphisms. -/
def moduleSheafExtAbZeroIso (F : SheafOfModules.{u} R) :
    moduleSheafExtAbFunctor R F 0 ≅
      moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F :=
  (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).rightDerivedZeroIsoSelf

/-- The actual locally closed supported internal Hom, before derivation. -/
def moduleLocallyClosedSheafHomFunctor (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} X :=
  moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
    ExposeI.underlineGammaLocallyClosedFunctor W

instance (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) :
    (moduleLocallyClosedSheafHomFunctor R F W).Additive := by
  have : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  have : (ExposeI.underlineGammaLocallyClosedFunctor W).Additive := inferInstance
  dsimp [moduleLocallyClosedSheafHomFunctor]
  infer_instance

instance moduleLocallyClosedSheafHomFunctor_preservesFiniteLimits
    (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) :
    PreservesFiniteLimits (moduleLocallyClosedSheafHomFunctor R F W) := by
  have : PreservesFiniteLimits (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) :=
    inferInstance
  have : PreservesFiniteLimits (ExposeI.underlineGammaLocallyClosedFunctor W) := inferInstance
  dsimp [moduleLocallyClosedSheafHomFunctor]
  infer_instance

/-- VI.1.1 for arbitrary locally closed support: underlying additive supported sheaf Ext. -/
def moduleLocallyClosedSheafExtFunctor (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} X :=
  (moduleLocallyClosedSheafHomFunctor R F W).rightDerived n

def moduleLocallyClosedSheafExtZeroIso (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSheafExtFunctor R F W 0 ≅ moduleLocallyClosedSheafHomFunctor R F W :=
  (moduleLocallyClosedSheafHomFunctor R F W).rightDerivedZeroIsoSelf

/-- Positive locally supported sheaf Ext vanishes on injective coefficient module sheaves. -/
theorem moduleLocallyClosedSheafExt_isZero_of_injective
    (F G : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) [Injective G] (n : ℕ) :
    IsZero ((moduleLocallyClosedSheafExtFunctor R F W (n + 1)).obj G) :=
  (moduleLocallyClosedSheafHomFunctor R F W).isZero_rightDerived_obj_injective_succ n G

/-- Actual global locally supported linear Hom. -/
def moduleLocallyClosedSupportedHomFunctor (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  moduleLocallyClosedSheafHomFunctor R F W ⋙
    (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X))

instance (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) :
    (moduleLocallyClosedSupportedHomFunctor R F W).Additive := by
  have : (moduleLocallyClosedSheafHomFunctor R F W).Additive := inferInstance
  have : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op (⊤ : Opens X))).Additive :=
    inferInstanceAs ((sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))).Additive)
  dsimp [moduleLocallyClosedSupportedHomFunctor]
  infer_instance

instance moduleLocallyClosedSupportedHomFunctor_preservesFiniteLimits
    (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) :
    PreservesFiniteLimits (moduleLocallyClosedSupportedHomFunctor R F W) := by
  have : PreservesFiniteLimits (moduleLocallyClosedSheafHomFunctor R F W) := inferInstance
  have : PreservesFiniteLimits ((sheafSections (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).obj (op (⊤ : Opens X))) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op (⊤ : Opens X))))
  dsimp [moduleLocallyClosedSupportedHomFunctor]
  infer_instance

/-- VI.1.1 for arbitrary locally closed support: actual supported Ext groups. -/
def moduleLocallyClosedSupportedExtFunctor (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) (n : ℕ) : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u} :=
  (moduleLocallyClosedSupportedHomFunctor R F W).rightDerived n

def moduleLocallyClosedSupportedExtZeroIso (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedExtFunctor R F W 0 ≅
      moduleLocallyClosedSupportedHomFunctor R F W :=
  (moduleLocallyClosedSupportedHomFunctor R F W).rightDerivedZeroIsoSelf

/-- Positive locally supported Ext groups vanish on injective coefficient module sheaves. -/
theorem moduleLocallyClosedSupportedExt_isZero_of_injective
    (F G : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) [Injective G] (n : ℕ) :
    IsZero ((moduleLocallyClosedSupportedExtFunctor R F W (n + 1)).obj G) :=
  (moduleLocallyClosedSupportedHomFunctor R F W).isZero_rightDerived_obj_injective_succ n G

end SGA.SGA2.ExposeVI
