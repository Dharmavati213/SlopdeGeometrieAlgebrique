/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleAdditiveResolution
import SGA.SGA2.ExposeI.SupportedCohomologyComparison

/-!
# Module-valued supported cohomology and the original additive cohomology

For every module sheaf and every degree, forgetting scalars in its derived
supported sections gives the original supported cohomology of its additive
sheaf. The comparison uses the flasque-resolution quasi-isomorphism, not
preservation of injectivity by forgetting scalars. Their naturality is proved
in `RingedModuleAdditiveNaturality`; the spectral sequence of V.3.2 remains
a separate task.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

local instance (Z : Closeds X) (U : Opens X) :
    (SheafOfModules.toSheaf.{u} R ⋙ ExposeI.gammaZSectionsFunctor Z U).Additive := by
  have : (SheafOfModules.toSheaf.{u} R).Additive := inferInstance
  have : (ExposeI.gammaZSectionsFunctor Z U).Additive := inferInstance
  infer_instance

/-- In all degrees, the additive group of module-derived supported sections
is the original right-derived supported sections of the underlying sheaf. -/
def derivedModuleGammaZSectionsObjForgetIso (Z : Closeds X) (U : Opens X)
    (M : SheafOfModules.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat (R.obj.obj (op U))) AddCommGrpCat).obj
        ((derivedModuleGammaZSections R Z U n).obj M) ≅
      (ExposeI.derivedGammaZSections Z U n).obj ((SheafOfModules.toSheaf R).obj M) :=
  ((ExposeI.rightDerivedPostcomposeIso (moduleGammaZSectionsFunctor R Z U)
    (forget₂ _ AddCommGrpCat) n).symm.app M) ≪≫
    (ExposeI.rightDerivedFunctorIso (moduleGammaZSectionsForgetIso R Z U) n).app M ≪≫
    moduleAdditiveResolutionHomologyIso R Z U (injectiveResolution M)
      (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) n

/-- Global module-derived supported sections recover the original `H_Z`,
not a newly defined additive cohomology theory. -/
def derivedModuleGammaZSectionsObjIsoH_Z (Z : Closeds X) (M : SheafOfModules.{u} R) (n : ℕ) :
    (forget₂ (ModuleCat (R.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat).obj
        ((derivedModuleGammaZSections R Z ⊤ n).obj M) ≅
      AddCommGrpCat.of (ExposeI.H_Z Z ((SheafOfModules.toSheaf R).obj M) n) :=
  derivedModuleGammaZSectionsObjForgetIso R Z ⊤ M n ≪≫
    ExposeI.derivedGammaZSectionsObjIsoH_Z Z ((SheafOfModules.toSheaf R).obj M) n

end SGA.SGA2.ExposeV
