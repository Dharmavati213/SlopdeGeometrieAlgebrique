/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.TopologicalInternalHom
import SGA.SGA2.ExposeI.DerivedSupportedSheaves
import SGA.SGA2.ExposeI.RightDerivedPrecomposition

/-!
# Sheaf Ext as sheafification of local Ext

The original right-derived internal Hom sheaf is the sheafification of a
presheaf whose values are actual Ext groups between the restrictions of its
arguments to each open. The comparisons are natural in the second argument.
Compatibility of these evaluation equivalences with standard Ext restriction
maps between nested opens, and an explicit connecting-map comparison, are not
asserted here.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Local Ext, obtained by deriving the actual local-morphism presheaf. -/
def internalExtPresheafFunctor (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ X.Presheaf AddCommGrpCat.{u} := by
  letI := abelianSheafToPresheaf_additive (X := X)
  exact (abelianSheafHomFunctor (Opens.grothendieckTopology X) F ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).rightDerived n

/-- The local Ext presheaf evaluates naturally to genuine Ext on each open. -/
def internalExtPresheafEvalIso (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) (n : ℕ) :
    internalExtPresheafFunctor F n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
        iShriek_open U ⋙ Abelian.extFunctorObj (restrictToOpen F U) n := by
  letI := abelianSheafToPresheaf_additive (X := X)
  letI := abelianPresheafEvaluation_additive (X := X) (op U)
  letI : ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (op U)).Additive := by
    change (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).Additive
    infer_instance
  letI : ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).PreservesHomology :=
    inferInstance
  letI := (openExtensionByZeroAdjunction U).isRightAdjoint
  letI : (iShriek_open U).Additive := inferInstance
  letI : (iShriek_open U).PreservesHomology := inferInstance
  exact (rightDerivedPostcomposeIso
    (abelianSheafHomFunctor (Opens.grothendieckTopology X) F ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) n).symm ≪≫
      rightDerivedFunctorIso (internalHomSectionsRestrictionFunctorIso U F) n ≪≫
      rightDerivedPrecomposeIso (iShriek_open U)
        (preadditiveCoyoneda.obj (op (restrictToOpen F U))) n ≪≫
      Functor.isoWhiskerLeft (iShriek_open U)
        (rightDerivedCoyonedaNatIsoExt (restrictToOpen F U) n)

/-- The original sheaf Ext is naturally the sheafification of local Ext. -/
def internalSheafExtSheafificationIso (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    internalExtPresheafFunctor F n ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        internalSheafExtFunctor (Opens.grothendieckTopology X) F n := by
  letI := abelianSheafToPresheaf_additive (X := X)
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
    inferInstance
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology :=
    inferInstance
  exact rightDerivedExactRetractionIso
    (abelianSheafHomFunctor (Opens.grothendieckTopology X) F)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit) n

/-- Objectwise, local Ext means Ext of the genuine ordinary restrictions. -/
def internalExtPresheafSectionsEquiv (F G : Sheaf AddCommGrpCat.{u} X)
    (U : Opens X) (n : ℕ) :
    ((internalExtPresheafFunctor F n).obj G).obj (op U) ≃+
      Abelian.Ext (restrictToOpen F U) (restrictToOpen G U) n :=
  ((internalExtPresheafEvalIso F U n).app G).addCommGroupIsoToAddEquiv

/-- Local Ext identifies coefficient maps with actual Ext postcomposition. -/
theorem internalExtPresheafSectionsEquiv_naturality (F : Sheaf AddCommGrpCat.{u} X)
    {G G' : Sheaf AddCommGrpCat.{u} X} (f : G ⟶ G') (U : Opens X) (n : ℕ)
    (x : ((internalExtPresheafFunctor F n).obj G).obj (op U)) :
    internalExtPresheafSectionsEquiv F G' U n
        (((internalExtPresheafFunctor F n).map f).app (op U) x) =
      (Abelian.Ext.mk₀ ((iShriek_open U).map f)).postcomp _ (add_zero n)
        (internalExtPresheafSectionsEquiv F G U n x) :=
  ConcreteCategory.congr_hom ((internalExtPresheafEvalIso F U n).hom.naturality f) x

end SGA.SGA2.ExposeI
