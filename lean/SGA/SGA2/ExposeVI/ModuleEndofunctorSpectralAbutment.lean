/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleEndofunctorSpectralFunctor
import SGA.SGA2.ExposeI.HomComplexSingleComparison

/-!
# The actual derived-composite abutment for an injective-preserving module functor

The mapped module resolution is K-injective. Its derived Hom from the
original source is therefore the homology of the genuine Hom complex,
hence the original right-derived composite. Applications supply their
proved injective-preservation instance; no abutment comparison is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
  (T : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R) [T.Additive]
  [T.PreservesInjectiveObjects]

/-- The actual mapped injective resolution has injective terms. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℤ) :
    Injective ((moduleEndofunctorResolutionInt R T I).X n) := by
  dsimp [moduleEndofunctorResolutionInt]
  infer_instance

/-- Its bounded-below injective terms make the original mapped resolution K-injective. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleEndofunctorResolutionInt R T I).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

local instance moduleEndofunctorAbutmentHasDerivedCategory :
    HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable (F : SheafOfModules.{u} R)

/-- The original Hom complex computes the genuine total interval of the spectral object. -/
def moduleEndofunctorHomComplexTotalEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) :
    (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (moduleEndofunctorResolutionInt R T I)).homology n ≃+
        moduleEndofunctorSpectralTotal R T F I n :=
  let e := (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
    (ExposeI.homComplexFromSingleIso F (moduleEndofunctorResolutionInt R T I))
  e.symm.addCommGroupIsoToAddEquiv.trans
    (ExposeI.homComplexHomologyDerivedHomEquiv
      ((CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj F)
      (moduleEndofunctorResolutionInt R T I) n)

/-- The actual filtered total is the original right-derived composite with module Hom. -/
def moduleEndofunctorSpectralDerivedCompositeEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleEndofunctorSpectralTotal R T F I n ≃+
      ((T ⋙ preadditiveCoyoneda.obj (op F)).rightDerived n).obj G :=
  (moduleEndofunctorHomComplexTotalEquiv R T F I n).symm.trans
    (ExposeI.injectiveResolutionIntHomologyIso
      (T ⋙ preadditiveCoyoneda.obj (op F)) I n).addCommGroupIsoToAddEquiv

/-- The unchanged total comparison followed by a proved natural identification
of the original right-derived composite. -/
def moduleEndofunctorSpectralComparedAbutmentEquiv
    (U : SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (e : (T ⋙ preadditiveCoyoneda.obj (op F)).rightDerived n ≅ U)
    {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    moduleEndofunctorSpectralTotal R T F I n ≃+ U.obj G :=
  (moduleEndofunctorSpectralDerivedCompositeEquiv R T F I n).trans
    (e.app G).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeVI
