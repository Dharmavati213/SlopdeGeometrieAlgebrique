/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedExt

/-!
# First-variable functoriality of module sheaf Hom and supported Ext

Actual precomposition of local linear maps defines natural transformations
of coefficient functors. Deriving them gives the contravariant maps of
supported Ext and supported sheaf Ext.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Local-linear precomposition, natural in the coefficient module sheaf. -/
def moduleSheafHomAbPrecompNat {E F : SheafOfModules.{u} R} (a : E ⟶ F) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⟶
      moduleSheafHomAbFunctor (Opens.grothendieckTopology X) E where
  app G := moduleSheafHomAbPrecomp (Opens.grothendieckTopology X) a G
  naturality G H b := by
    ext U φ
    rfl

@[simp]
theorem moduleSheafHomAbPrecompNat_id (F : SheafOfModules.{u} R) :
    moduleSheafHomAbPrecompNat R (𝟙 F) = 𝟙 _ := by
  ext G U φ
  rfl

@[simp]
theorem moduleSheafHomAbPrecompNat_comp {E F G : SheafOfModules.{u} R}
    (a : E ⟶ F) (b : F ⟶ G) :
    moduleSheafHomAbPrecompNat R (a ≫ b) =
      moduleSheafHomAbPrecompNat R b ≫ moduleSheafHomAbPrecompNat R a := by
  ext H U φ
  rfl

/-- Actual precomposition on closed-supported Hom. -/
def moduleSupportedHomPrecomp {E F : SheafOfModules.{u} R}
    (a : E ⟶ F) (Z : Closeds X) :
    moduleSupportedHomFunctor R F Z ⟶ moduleSupportedHomFunctor R E Z :=
  Functor.whiskerRight (moduleSheafHomAbPrecompNat R a) (ExposeI.gammaZSectionsFunctor Z ⊤)

/-- Actual first-variable maps of the original closed-supported Ext functors. -/
def moduleSupportedExtPrecomp {E F : SheafOfModules.{u} R}
    (a : E ⟶ F) (Z : Closeds X) (n : ℕ) :
    moduleSupportedExtFunctor R F Z n ⟶ moduleSupportedExtFunctor R E Z n :=
  (moduleSupportedHomPrecomp R a Z).rightDerived n

/-- First-variable maps of original locally closed supported Hom sheaves. -/
def moduleLocallyClosedSheafHomPrecomp {E F : SheafOfModules.{u} R}
    (a : E ⟶ F) (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSheafHomFunctor R F W ⟶ moduleLocallyClosedSheafHomFunctor R E W :=
  Functor.whiskerRight (moduleSheafHomAbPrecompNat R a)
    (ExposeI.underlineGammaLocallyClosedFunctor W)

/-- First-variable maps of original global supported Hom. -/
def moduleLocallyClosedSupportedHomPrecomp {E F : SheafOfModules.{u} R}
    (a : E ⟶ F) (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedHomFunctor R F W ⟶
      moduleLocallyClosedSupportedHomFunctor R E W :=
  Functor.whiskerRight (moduleLocallyClosedSheafHomPrecomp R a W)
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))

/-- Actual precomposition on supported sheaf Ext. -/
def moduleLocallyClosedSheafExtPrecomp {E F : SheafOfModules.{u} R}
    (a : E ⟶ F) (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSheafExtFunctor R F W n ⟶
      moduleLocallyClosedSheafExtFunctor R E W n :=
  (moduleLocallyClosedSheafHomPrecomp R a W).rightDerived n

/-- Actual precomposition on supported Ext groups. -/
def moduleLocallyClosedSupportedExtPrecomp {E F : SheafOfModules.{u} R}
    (a : E ⟶ F) (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ⟶
      moduleLocallyClosedSupportedExtFunctor R E W n :=
  (moduleLocallyClosedSupportedHomPrecomp R a W).rightDerived n

@[simp]
theorem moduleLocallyClosedSheafHomPrecomp_id (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSheafHomPrecomp R (𝟙 F) W = 𝟙 _ := by
  ext G
  simp [moduleLocallyClosedSheafHomPrecomp]
  rfl

@[simp]
theorem moduleLocallyClosedSupportedHomPrecomp_id (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedHomPrecomp R (𝟙 F) W = 𝟙 _ := by
  ext G
  simp [moduleLocallyClosedSupportedHomPrecomp]
  rfl

theorem moduleLocallyClosedSheafHomPrecomp_comp {E F G : SheafOfModules.{u} R}
    (a : E ⟶ F) (b : F ⟶ G) (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSheafHomPrecomp R (a ≫ b) W =
      moduleLocallyClosedSheafHomPrecomp R b W ≫ moduleLocallyClosedSheafHomPrecomp R a W := by
  simp only [moduleLocallyClosedSheafHomPrecomp, moduleSheafHomAbPrecompNat_comp,
    Functor.whiskerRight_comp]

theorem moduleLocallyClosedSupportedHomPrecomp_comp {E F G : SheafOfModules.{u} R}
    (a : E ⟶ F) (b : F ⟶ G) (W : ExposeI.LocallyClosedIn X) :
    moduleLocallyClosedSupportedHomPrecomp R (a ≫ b) W =
      moduleLocallyClosedSupportedHomPrecomp R b W ≫
        moduleLocallyClosedSupportedHomPrecomp R a W := by
  simp only [moduleLocallyClosedSupportedHomPrecomp, moduleLocallyClosedSheafHomPrecomp_comp,
    Functor.whiskerRight_comp]

@[simp]
theorem moduleLocallyClosedSheafExtPrecomp_id (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSheafExtPrecomp R (𝟙 F) W n = 𝟙 _ := by
  rw [moduleLocallyClosedSheafExtPrecomp, moduleLocallyClosedSheafHomPrecomp_id,
    NatTrans.rightDerived_id]
  rfl

@[simp]
theorem moduleLocallyClosedSupportedExtPrecomp_id (F : SheafOfModules.{u} R)
    (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSupportedExtPrecomp R (𝟙 F) W n = 𝟙 _ := by
  rw [moduleLocallyClosedSupportedExtPrecomp, moduleLocallyClosedSupportedHomPrecomp_id,
    NatTrans.rightDerived_id]
  rfl

theorem moduleLocallyClosedSheafExtPrecomp_comp {E F G : SheafOfModules.{u} R}
    (a : E ⟶ F) (b : F ⟶ G) (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSheafExtPrecomp R (a ≫ b) W n =
      moduleLocallyClosedSheafExtPrecomp R b W n ≫
        moduleLocallyClosedSheafExtPrecomp R a W n := by
  rw [moduleLocallyClosedSheafExtPrecomp, moduleLocallyClosedSheafHomPrecomp_comp,
    NatTrans.rightDerived_comp]
  rfl

theorem moduleLocallyClosedSupportedExtPrecomp_comp {E F G : SheafOfModules.{u} R}
    (a : E ⟶ F) (b : F ⟶ G) (W : ExposeI.LocallyClosedIn X) (n : ℕ) :
    moduleLocallyClosedSupportedExtPrecomp R (a ≫ b) W n =
      moduleLocallyClosedSupportedExtPrecomp R b W n ≫
        moduleLocallyClosedSupportedExtPrecomp R a W n := by
  rw [moduleLocallyClosedSupportedExtPrecomp, moduleLocallyClosedSupportedHomPrecomp_comp,
    NatTrans.rightDerived_comp]
  rfl

end SGA.SGA2.ExposeVI
