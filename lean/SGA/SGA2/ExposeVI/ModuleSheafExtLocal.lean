/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt
import SGA.SGA2.ExposeI.SheafExtLocalComparison
import SGA.SGA2.ExposeI.RightDerivedPrecomposition

/-!
# SGA 2, VI.1.2: sheaf Ext is sheafification of local Ext

The original right-derived module-linear Hom sheaf is the sheafification of
a presheaf whose values are actual Ext groups of the restricted module
sheaves on each open, obtained by deriving the already constructed
local-linear Hom functor.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Local module Ext, obtained by deriving the local-linear Hom presheaf. -/
def moduleExtPresheafFunctor (F : SheafOfModules.{u} R) (n : ℕ) :
    SheafOfModules.{u} R ⥤ X.Presheaf AddCommGrpCat.{u} := by
  letI : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  letI := ExposeI.abelianSheafToPresheaf_additive (X := X)
  exact (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).rightDerived n

/-- **VI.1.2:** the original sheaf Ext is naturally the sheafification of
local module Ext. -/
def moduleSheafExtSheafificationIso (F : SheafOfModules.{u} R) (n : ℕ) :
    moduleExtPresheafFunctor R F n ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        moduleSheafExtAbFunctor R F n := by
  letI : (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).Additive := inferInstance
  letI := ExposeI.abelianSheafToPresheaf_additive (X := X)
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
    inferInstance
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology :=
    inferInstance
  exact ExposeI.rightDerivedExactRetractionIso
    (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit) n

/-- Degree zero of VI.1.2 is the original local-linear Hom sheaf. -/
def moduleSheafExtSheafificationIso_zero (F : SheafOfModules.{u} R) :
    moduleExtPresheafFunctor R F 0 ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F :=
  moduleSheafExtSheafificationIso R F 0 ≪≫ moduleSheafExtAbZeroIso R F

end SGA.SGA2.ExposeVI
