/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleGlobalAction
import SGA.SGA2.ExposeV.RingedModuleSupportedSections
import SGA.SGA2.ExposeI.RightDerivedPostcomposition

/-!
# Original scalar actions under the homology-forgetful comparison

Scalars are natural endomorphisms of the additive forgetful functor, even
for noncommutative rings. Their homology maps are therefore the actual
scalar multiplication on module-valued homology through the canonical
forgetful comparison. The original ringed-space supported-section complex
has precisely this scalar action.
-/

noncomputable section

universe u v

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {B : Type u} [Ring B]

/-- Actual scalar multiplication on the underlying additive module complex. -/
def moduleComplexAdditiveScalar (K : CochainComplex (ModuleCat.{v} B) ℤ) (r : B) :
    End (((forget₂ (ModuleCat B) AddCommGrpCat).mapHomologicalComplex _).obj K) :=
  ((ModuleCat.smulNatTrans B r).mapHomologicalComplex (ComplexShape.up ℤ)).app K

/-- The canonical homology comparison intertwines actual scalar multiplication. -/
@[reassoc]
theorem moduleComplexAdditiveScalar_homology (K : CochainComplex (ModuleCat.{v} B) ℤ)
    (r : B) (n : ℤ) :
    (ExposeI.complexHomologyMapIso (forget₂ (ModuleCat B) AddCommGrpCat)
        (ComplexShape.up ℤ) K n).inv ≫ homologyMap (moduleComplexAdditiveScalar K r) n =
      (K.homology n).smul r ≫
        (ExposeI.complexHomologyMapIso (forget₂ (ModuleCat B) AddCommGrpCat)
          (ComplexShape.up ℤ) K n).inv := by
  change ((K.sc n).mapHomologyIso (forget₂ (ModuleCat B) AddCommGrpCat)).inv ≫
      ShortComplex.homologyMap ((K.sc n).mapNatTrans (ModuleCat.smulNatTrans B r)) = _
  rw [ShortComplex.homologyMap_mapNatTrans, Iso.inv_hom_id_assoc]
  rfl

theorem moduleComplexAdditiveScalar_homology_apply (K : CochainComplex (ModuleCat.{v} B) ℤ)
    (r : B) (n : ℤ) (x : K.homology n) :
    homologyMap (moduleComplexAdditiveScalar K r) n
        ((ExposeI.complexHomologyMapIso (forget₂ (ModuleCat B) AddCommGrpCat)
          (ComplexShape.up ℤ) K n).inv x) =
      (ExposeI.complexHomologyMapIso (forget₂ (ModuleCat B) AddCommGrpCat)
        (ComplexShape.up ℤ) K n).inv (r • x) :=
  ConcreteCategory.congr_hom (moduleComplexAdditiveScalar_homology K r n) x

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X) (Z : Closeds X)

/-- Supported sections of the original global scalar map are exactly the
scalar map of the actual module-valued supported-section complex. -/
theorem moduleGammaComplex_globalScalar (K : CochainComplex (SheafOfModules.{u} R) ℤ)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    ((ExposeI.gammaZSectionsFunctor Z ⊤).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (moduleUnderlyingComplexGlobalScalar R K r) =
      moduleComplexAdditiveScalar
        (((moduleGammaZSectionsFunctor R Z ⊤).mapHomologicalComplex _).obj K) r := by
  ext n x
  apply Subtype.ext
  let y : (K.X n).val.obj (op (⊤ : Opens X)) := x.val
  change R.obj.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op r • y = r • y
  rw [show (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _,
    R.obj.map_id]
  rfl

end SGA.SGA2.ExposeV
