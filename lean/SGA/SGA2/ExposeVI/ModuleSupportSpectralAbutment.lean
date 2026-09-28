/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportSpectralFunctor
import SGA.SGA2.ExposeVI.ModuleSupportedSheafInjective
import SGA.SGA2.ExposeI.HomComplexSingleComparison

/-!
# SGA 2, VI.1.6.3: the actual supported Ext abutment

The proved support adjunction preserves injective module sheaves, so the
original supported resolution is K-injective. Its genuine derived Hom from
`F` is the cohomology of the actual Hom complex. VI.1.4.3 identifies this with
the original supported Hom complex, hence with original supported Ext.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (Z : Closeds X)

/-- The original supported module resolution has injective terms. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) (n : ℤ) :
    Injective ((moduleSupportResolutionInt R Z I).X n) := by
  dsimp [moduleSupportResolutionInt]
  infer_instance

/-- The actual supported resolution is K-injective, without an additional hypothesis. -/
instance {G : SheafOfModules.{u} R} (I : InjectiveResolution G) :
    (moduleSupportResolutionInt R Z I).IsKInjective :=
  CochainComplex.isKInjective_of_injective _ 0

local instance : HasDerivedCategory.{u + 1} (SheafOfModules.{u} R) :=
  HasDerivedCategory.standard _

variable (F : SheafOfModules.{u} R)

/-- The original Hom complex computes the actual derived supported total group. -/
def moduleSupportHomComplexTotalEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℤ) :
    (((preadditiveCoyoneda.obj (op F)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (moduleSupportResolutionInt R Z I)).homology n ≃+
        moduleSupportSpectralTotal R Z F I n :=
  ((homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) n).mapIso
      (ExposeI.homComplexFromSingleIso F (moduleSupportResolutionInt R Z I))).symm
        |>.addCommGroupIsoToAddEquiv.trans
    (ExposeI.homComplexHomologyDerivedHomEquiv
      ((CochainComplex.singleFunctor (SheafOfModules.{u} R) 0).obj F)
      (moduleSupportResolutionInt R Z I) n)

/-- **VI.1.6.3, abutment:** the genuine filtered total is original supported module Ext. -/
def moduleSupportSpectralAbutmentEquiv {G : SheafOfModules.{u} R}
    (I : InjectiveResolution G) (n : ℕ) :
    moduleSupportSpectralTotal R Z F I n ≃+ (moduleSupportedExtFunctor R F Z n).obj G :=
  (moduleSupportHomComplexTotalEquiv R Z F I n).symm.trans
    ((ExposeI.injectiveResolutionIntHomologyIso
      (moduleGammaZSheafFunctor R Z ⋙ preadditiveCoyoneda.obj (op F)) I n ≪≫
        ((moduleSupportedExtViaSupportedSheafIso R F Z n).app G).symm)
          |>.addCommGroupIsoToAddEquiv)

end SGA.SGA2.ExposeVI
