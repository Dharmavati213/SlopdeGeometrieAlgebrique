/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.RightDerivedPostcomposition
import SGA.SGA2.ExposeI.SupportedSheafSections
import SGA.SGA2.ExposeI.FlasqueResolution
import SGA.SGA2.ExposeI.LocallyClosedCohomology

/-!
# Original derived supported sheaves and sheafification

We derive the original kernel-sheaf functor `underlineGammaZFunctor`. Its
derived sheaves are the sheafifications of the presheaves obtained by deriving
supported sections on each open. In particular they vanish in positive degrees
on flasque coefficients. Comparison with the separate kernel/cokernel/derived
pushforward model `sheafH_Z_n` is not asserted in this file.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

instance abelianSheafToPresheaf_additive :
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive where
  map_add := rfl

instance abelianPresheafEvaluation_additive (U : (Opens X)ᵒᵖ) :
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj U).Additive where
  map_add := rfl

/-- The original right-derived supported-sheaf functor. -/
def derivedUnderlineGammaZ (Z : Closeds X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ Sheaf AddCommGrpCat.{u} X :=
  (underlineGammaZFunctor Z).rightDerived n

/-- Degree zero is naturally the original kernel sheaf. -/
def derivedUnderlineGammaZZeroIso (Z : Closeds X) :
    derivedUnderlineGammaZ Z 0 ≅ underlineGammaZFunctor Z :=
  (underlineGammaZFunctor Z).rightDerivedZeroIsoSelf

/-- The local supported-cohomology presheaf, derived before sheafification.
Its evaluation on each open is identified with the original derived supported
sections by `supportedCohomologyPresheafEvalIso`. -/
def supportedCohomologyPresheafFunctor (Z : Closeds X) (n : ℕ) :
    Sheaf AddCommGrpCat.{u} X ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (gammaZSectionsPresheafFunctor Z).rightDerived n

/-- Evaluation of local supported-cohomology presheaves is the original
right-derived supported-section functor on that open. -/
def supportedCohomologyPresheafEvalIso (Z : Closeds X) (U : Opens X) (n : ℕ) :
    supportedCohomologyPresheafFunctor Z n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
        derivedGammaZSections Z U n := by
  letI := abelianPresheafEvaluation_additive (X := X) (op U)
  letI : ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).PreservesHomology :=
    inferInstance
  exact (rightDerivedPostcomposeIso (gammaZSectionsPresheafFunctor Z)
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) n).symm

/-- Supported sections on an open can be computed on that open as a space. -/
def gammaZSectionsLocallyClosedIso (Z : Closeds X) (U : Opens X) :
    gammaLocallyClosedFunctor (LocallyClosedIn.ofOpenClosed U Z) ≅
      gammaZSectionsFunctor Z U :=
  NatIso.ofComponents (fun F ↦ (restrictToOpenGammaZEquiv Z U F).toAddCommGrpIso)
    (fun f ↦ by ext s; exact restrictToOpenGammaZEquiv_naturality Z U f s)

/-- Original derived supported sections on an open are represented by Ext
from its actual locally closed support sheaf. -/
def derivedGammaZSectionsIsoLocallyClosed (Z : Closeds X) (U : Opens X) (n : ℕ) :
    derivedGammaZSections Z U n ≅
      Abelian.extFunctorObj (zZX_locallyClosed (LocallyClosedIn.ofOpenClosed U Z)) n :=
  (rightDerivedFunctorIso (gammaZSectionsLocallyClosedIso Z U) n).symm ≪≫
    derivedGammaLocallyClosedIsoExt (LocallyClosedIn.ofOpenClosed U Z) n

/-- The local cohomology presheaf on `U` has the actual closed-support
cohomology of the restricted coefficient sheaf as its group of sections. -/
def supportedCohomologyPresheafSectionsEquiv (Z : Closeds X) (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ((supportedCohomologyPresheafFunctor Z n).obj F).obj (op U) ≃+
      H_Z (closedSupportOnOpen Z U) (restrictToOpen F U) n :=
  ((((supportedCohomologyPresheafEvalIso Z U n).app F) ≪≫
    ((derivedGammaZSectionsIsoLocallyClosed Z U n).app F)).addCommGroupIsoToAddEquiv).trans
      (locallyClosedSupportExtEquiv (LocallyClosedIn.ofOpenClosed U Z) F n)

private theorem cohomologyNatIso_addEquiv_naturality
    {C : Type*} [Category C] {P Q : C ⥤ AddCommGrpCat.{u}}
    (e : P ≅ Q) {A B : C} (f : A ⟶ B) (x : P.obj A) :
    (e.app B).addCommGroupIsoToAddEquiv (P.map f x) =
      Q.map f ((e.app A).addCommGroupIsoToAddEquiv x) :=
  ConcreteCategory.congr_hom (e.hom.naturality f) x

/-- The identification of local presheaf sections with actual supported
cohomology is natural in coefficient sheaves. -/
theorem supportedCohomologyPresheafSectionsEquiv_naturality
    (Z : Closeds X) (U : Opens X) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ)
    (x : ((supportedCohomologyPresheafFunctor Z n).obj F).obj (op U)) :
    supportedCohomologyPresheafSectionsEquiv Z U G n
        (((supportedCohomologyPresheafFunctor Z n).map f).app (op U) x) =
      H_Z_map (closedSupportOnOpen Z U) ((iShriek_open U).map f) n
        (supportedCohomologyPresheafSectionsEquiv Z U F n x) := by
  let e := supportedCohomologyPresheafEvalIso Z U n ≪≫
    derivedGammaZSectionsIsoLocallyClosed Z U n
  change locallyClosedSupportExtEquiv (LocallyClosedIn.ofOpenClosed U Z) G n
      ((e.app G).addCommGroupIsoToAddEquiv
        (((supportedCohomologyPresheafFunctor Z n).map f).app (op U) x)) = _
  erw [cohomologyNatIso_addEquiv_naturality e f x]
  exact locallyClosedSupportExtEquiv_naturality (LocallyClosedIn.ofOpenClosed U Z) f n _

/-- **I.2.4:** original derived supported sheaves are the sheafifications of
the local supported-cohomology presheaves, naturally in the coefficient sheaf. -/
def supportedCohomologySheafificationIso (Z : Closeds X) (n : ℕ) :
    supportedCohomologyPresheafFunctor Z n ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        derivedUnderlineGammaZ Z n := by
  letI := abelianSheafToPresheaf_additive (X := X)
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive :=
    inferInstance
  letI : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology :=
    inferInstance
  letI : (gammaZSectionsPresheafFunctor Z).Additive := inferInstance
  exact Functor.isoWhiskerRight
    (rightDerivedFunctorIso (underlineGammaZPresheafFunctorIso Z) n).symm
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ≪≫
  rightDerivedExactRetractionIso (underlineGammaZFunctor Z)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X)
      AddCommGrpCat.{u}).counit) n

/-- Local supported-cohomology presheaves vanish in positive degrees on
flasque coefficients. -/
theorem supportedCohomologyPresheaf_isZero_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero ((supportedCohomologyPresheafFunctor Z (n + 1)).obj F) := by
  apply Functor.isZero
  intro U
  exact (derivedGammaZSections_isZero_of_isFlasque Z U.unop F n).of_iso
    ((supportedCohomologyPresheafEvalIso Z U.unop (n + 1)).app F)

/-- **I.2.12, sheaf-valued forward direction:** the original derived supported
sheaves of a flasque sheaf vanish in every positive degree. -/
theorem derivedUnderlineGammaZ_isZero_of_isFlasque (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] (n : ℕ) :
    IsZero ((derivedUnderlineGammaZ Z (n + 1)).obj F) :=
  ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map_isZero
    (supportedCohomologyPresheaf_isZero_of_isFlasque Z F n)).of_iso
      ((supportedCohomologySheafificationIso Z (n + 1)).app F).symm

/-- Injective coefficients have no positive original derived supported sheaves. -/
theorem derivedUnderlineGammaZ_isZero_of_injective (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) [Injective F] (n : ℕ) :
    IsZero ((derivedUnderlineGammaZ Z (n + 1)).obj F) :=
  (underlineGammaZFunctor Z).isZero_rightDerived_obj_injective_succ n F

end SGA.SGA2.ExposeI
