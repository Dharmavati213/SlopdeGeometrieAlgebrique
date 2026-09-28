/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleCompositeDerived
import SGA.SGA2.ExposeI.FlasqueQuasiIso
import SGA.SGA2.ExposeI.KInjectiveDerivedComparison
import SGA.SGA2.ExposeI.InjectiveResolutionIntCohomology
import Mathlib.CategoryTheory.Abelian.Injective.Extend

/-!
# Comparing module resolutions with additive-sheaf resolutions

The additive sheaves underlying a module-injective resolution are flasque,
but need not be injective. A genuine cochain map to an additive-injective
resolution is obtained from their augmentations in the derived category.
Supported sections preserve that quasi-isomorphism by the flasque mapping-cone
argument. Its homology therefore computes the original additive-sheaf derived
supported sections, without a flatness hypothesis on the structure sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

local instance {F : Sheaf AddCommGrpCat.{u} X} (J : InjectiveResolution F) :
    J.cochainComplex.IsKInjective := by
  dsimp [InjectiveResolution.cochainComplex]
  infer_instance

/-- The underlying additive-sheaf complex of an integer-indexed module resolution. -/
def moduleUnderlyingResolutionInt {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    CochainComplex (Sheaf AddCommGrpCat.{u} X) ℤ :=
  ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).obj I.cochainComplex

instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    (moduleUnderlyingResolutionInt R I).IsStrictlyGE 0 := by
  dsimp [moduleUnderlyingResolutionInt]
  infer_instance

instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M) (n : ℤ) :
    ExposeI.IsFlasque ((moduleUnderlyingResolutionInt R I).X n) :=
  moduleIsFlasque_of_injective R (I.cochainComplex.X n)

/-- The actual augmentation of the underlying additive-sheaf resolution. -/
def moduleUnderlyingResolutionι {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj
      ((SheafOfModules.toSheaf R).obj M) ⟶ moduleUnderlyingResolutionInt R I :=
  (singleMapHomologicalComplex (SheafOfModules.toSheaf R) (ComplexShape.up ℤ) 0).inv.app M ≫
    ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map I.ι'

instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M) :
    QuasiIso (moduleUnderlyingResolutionι R I) := by
  have : QuasiIso (((SheafOfModules.toSheaf.{u} R).mapHomologicalComplex
      (ComplexShape.up ℤ)).map I.ι') :=
    quasiIso_map_of_preservesHomology I.ι' (SheafOfModules.toSheaf.{u} R)
  unfold moduleUnderlyingResolutionι
  infer_instance

/-- An actual cochain comparison from a module-injective resolution to an
additive-injective resolution of the underlying sheaf. -/
def moduleAdditiveResolutionCompare {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)) :
    moduleUnderlyingResolutionInt R I ⟶ J.cochainComplex := by
  have : J.cochainComplex.IsKInjective := by
    dsimp [InjectiveResolution.cochainComplex]
    infer_instance
  exact ExposeI.kInjectiveLiftDerivedMap
    (inv (DerivedCategory.Q.map (moduleUnderlyingResolutionι R I)) ≫ DerivedCategory.Q.map J.ι')

/-- The chosen cochain comparison has the prescribed augmentation-compatible
derived morphism. -/
@[simp]
theorem Q_map_moduleAdditiveResolutionCompare {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)) :
    DerivedCategory.Q.map (moduleAdditiveResolutionCompare R I J) =
      inv (DerivedCategory.Q.map (moduleUnderlyingResolutionι R I)) ≫
        DerivedCategory.Q.map J.ι' := by
  have : J.cochainComplex.IsKInjective := by
    dsimp [InjectiveResolution.cochainComplex]
    infer_instance
  exact ExposeI.Q_map_kInjectiveLiftDerivedMap _

instance {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)) :
    QuasiIso (moduleAdditiveResolutionCompare R I J) := by
  dsimp [moduleAdditiveResolutionCompare]
  infer_instance

/-- Supported sections preserve the actual comparison of the two resolutions. -/
instance moduleAdditiveResolutionCompare_supported_quasiIso
    (Z : Closeds X) (U : Opens X) {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)) :
    QuasiIso (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex (ComplexShape.up ℤ)).map
      (moduleAdditiveResolutionCompare R I J)) := by
  have : ∀ n : ℤ, ExposeI.IsFlasque (J.cochainComplex.X n) :=
    fun n ↦ ExposeI.isFlasque_of_injective _
  exact ExposeI.gammaZSections_quasiIso_of_boundedBelow_flasque Z U
    (moduleAdditiveResolutionCompare R I J) 0
    (fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)
    (fun n hn ↦ CochainComplex.isZero_of_isStrictlyGE _ 0 n hn)

/-- Supported cohomology computed using any module-injective resolution agrees
with the original right-derived supported sections of the underlying additive sheaf. -/
def moduleAdditiveResolutionHomologyIso (Z : Closeds X) (U : Opens X)
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)) (n : ℕ) :
    ((SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U).rightDerived n).obj M ≅
      (ExposeI.derivedGammaZSections Z U n).obj ((SheafOfModules.toSheaf R).obj M) :=
  (ExposeI.injectiveResolutionIntHomologyIso
    (SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U) I n).symm ≪≫
    asIso (homologyMap
      (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (moduleAdditiveResolutionCompare R I J)) (n : ℤ)) ≪≫
    ExposeI.injectiveResolutionIntHomologyIso (ExposeI.gammaZSectionsFunctor Z U) J n

end SGA.SGA2.ExposeV
