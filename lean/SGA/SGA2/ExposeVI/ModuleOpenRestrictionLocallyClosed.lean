/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionSupport
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionNested
import SGA.SGA2.ExposeVI.ModuleSupportIndependence

/-!
# SGA 2, VI.1.2–VI.1.3 for locally closed supports

Local supported Ext is derived in the actual category of module sheaves on
the given open. On a witness for a locally closed support, its degree-zero
functor is supported Hom after restriction to the witness. Exactness and
preservation of injectives of open restriction give the local Ext comparison
and excision in every degree, naturally in the coefficient module.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
    (U : Opens X) (W : ExposeI.LocallyClosedIn X)

/-- The intrinsic locally supported Hom functor on the open site: restrict
to the witness intersected with `U`, then take the supported morphisms there. -/
def moduleLocallySupportedHomOnOpenFunctor (F : SheafOfModules.{u} (R.over U)) :
    SheafOfModules.{u} (R.over U) ⥤ AddCommGrpCat.{u} :=
  moduleNestedOpenRestriction R (homOfLE (inf_le_right : W.V ⊓ U ≤ U)) ⋙
    moduleSupportedHomOnOpenFunctor R (W.V ⊓ U) W.closedHull
      ((moduleNestedOpenRestriction R (homOfLE (inf_le_right : W.V ⊓ U ≤ U))).obj F)

instance moduleLocallySupportedHomOnOpenFunctor_additive
    (F : SheafOfModules.{u} (R.over U)) :
    (moduleLocallySupportedHomOnOpenFunctor R U W F).Additive := by
  dsimp [moduleLocallySupportedHomOnOpenFunctor]
  infer_instance

/-- Locally supported Ext, derived in the actual module category on `U`. -/
def moduleLocallySupportedExtOnOpenFunctor (F : SheafOfModules.{u} (R.over U)) (n : ℕ) :
    SheafOfModules.{u} (R.over U) ⥤ AddCommGrpCat.{u} :=
  (moduleLocallySupportedHomOnOpenFunctor R U W F).rightDerived n

/-- Supported local maps on the intersection are supported morphisms on
the open site, with its actual restriction of source and coefficients. -/
def moduleSupportedHomIntersectionRestrictionIso (F : SheafOfModules.{u} R) :
    moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaZSectionsFunctor W.closedHull (W.V ⊓ U) ≅
      moduleOpenRestriction R U ⋙ moduleLocallySupportedHomOnOpenFunctor R U W (F.over U) := by
  let i : W.V ⊓ U ⟶ U := homOfLE inf_le_right
  let e := SheafOfModules.overFunctorMap R i
  exact moduleSupportedHomSectionsRestrictionIso R (W.V ⊓ U) W.closedHull F ≪≫
    Functor.isoWhiskerRight e.symm
      (moduleSupportedHomOnOpenFunctor R (W.V ⊓ U) W.closedHull (F.over (W.V ⊓ U))) ≪≫
    Functor.isoWhiskerLeft (moduleOpenRestriction R U ⋙ moduleNestedOpenRestriction R i)
      (moduleSupportedHomOnOpenSourceIso R (W.V ⊓ U) W.closedHull (e.app F).symm)

/-- Sections of the actual locally supported Hom sheaf are naturally the
intrinsic supported Hom on each open site. -/
def moduleLocallyClosedHomSectionsRestrictionIso (F : SheafOfModules.{u} R) :
    (moduleLocallyClosedSheafHomFunctor R F W ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
      moduleOpenRestriction R U ⋙ moduleLocallySupportedHomOnOpenFunctor R U W (F.over U) :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.underlineGammaLocallyClosedPresheafFunctorIso W ≪≫
        ExposeI.locallyClosedAmbientPresheafIso W W.closedHull W.closedSupportOnOpen_closedHull))
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) ≪≫
      moduleSupportedHomIntersectionRestrictionIso R U W F

/-- The presheaf obtained by deriving actual locally supported Hom sections. -/
def moduleLocallySupportedExtPresheafFunctor (F : SheafOfModules.{u} R) (n : ℕ) :
    SheafOfModules.{u} R ⥤ (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u} := by
  let := ExposeI.abelianSheafToPresheaf_additive (X := X)
  exact (moduleLocallyClosedSheafHomFunctor R F W ⋙
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).rightDerived n

/-- **VI.1.2, local values:** local supported Ext is derived in the actual
module-sheaf category of `U`, with its genuine restricted coefficients. -/
def moduleLocallySupportedExtPresheafEvalIso (F : SheafOfModules.{u} R) (n : ℕ) :
    moduleLocallySupportedExtPresheafFunctor R W F n ⋙
      (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅
        moduleOpenRestriction R U ⋙ moduleLocallySupportedExtOnOpenFunctor R U W (F.over U) n := by
  let := ExposeI.abelianSheafToPresheaf_additive (X := X)
  let := ExposeI.abelianPresheafEvaluation_additive (X := X) (op U)
  let : ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)).PreservesHomology := inferInstance
  exact (ExposeI.rightDerivedPostcomposeIso
    (moduleLocallyClosedSheafHomFunctor R F W ⋙
      sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((evaluation (Opens X)ᵒᵖ AddCommGrpCat.{u}).obj (op U)) n).symm ≪≫
      ExposeI.rightDerivedFunctorIso (moduleLocallyClosedHomSectionsRestrictionIso R U W F) n ≪≫
      ExposeI.rightDerivedPrecomposeIso (moduleOpenRestriction R U)
        (moduleLocallySupportedHomOnOpenFunctor R U W (F.over U)) n

/-- **VI.1.2, sheafification:** the original supported module sheaf Ext is
the associated sheaf of the presheaf with the actual local Ext values above. -/
def moduleLocallySupportedExtSheafificationIso (F : SheafOfModules.{u} R) (n : ℕ) :
    moduleLocallySupportedExtPresheafFunctor R W F n ⋙
      presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
        moduleLocallyClosedSheafExtFunctor R F W n := by
  let := ExposeI.abelianSheafToPresheaf_additive (X := X)
  let : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).Additive := inferInstance
  let : (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).PreservesHomology :=
    inferInstance
  exact ExposeI.rightDerivedExactRetractionIso (moduleLocallyClosedSheafHomFunctor R F W)
    (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (asIso (sheafificationAdjunction (Opens.grothendieckTopology X) AddCommGrpCat.{u}).counit) n

/-- Degree-zero excision for an arbitrary locally closed support. -/
def moduleLocallySupportedHomExcisionIso (hWU : W.asSet ⊆ (U : Set X))
    (F : SheafOfModules.{u} R) :
    moduleLocallyClosedSupportedHomFunctor R F W ≅
      moduleOpenRestriction R U ⋙ moduleLocallySupportedHomOnOpenFunctor R U W (F.over U) := by
  have hcover : W.V ≤ (W.V ⊓ U) ⊔ (W.V ⊓ W.closedHull.compl) := by
    intro x hx
    by_cases hxZ : x ∈ W.closedHull
    · exact Or.inl ⟨hx, hWU (W.inter_closedHull ▸ ⟨hx, hxZ⟩)⟩
    · exact Or.inr ⟨hx, hxZ⟩
  exact moduleLocallyClosedSupportedHomGammaIso R F W ≪≫
    Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.gammaLocallyClosedAmbientIso W W.closedHull W.closedSupportOnOpen_closedHull ≪≫
        ExposeI.gammaZSectionsRestrictionIsoOfCover inf_le_left hcover) ≪≫
      moduleSupportedHomIntersectionRestrictionIso R U W F

/-- **VI.1.3:** supported module Ext in every degree is unchanged on an
open neighborhood of an arbitrary locally closed support. Both sides are
derived in their actual module-sheaf categories. -/
def VI_1_3 (hWU : W.asSet ⊆ (U : Set X)) (F : SheafOfModules.{u} R) (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F W n ≅
      moduleOpenRestriction R U ⋙ moduleLocallySupportedExtOnOpenFunctor R U W (F.over U) n :=
  ExposeI.rightDerivedFunctorIso (moduleLocallySupportedHomExcisionIso R U W hWU F) n ≪≫
    ExposeI.rightDerivedPrecomposeIso (moduleOpenRestriction R U)
      (moduleLocallySupportedHomOnOpenFunctor R U W (F.over U)) n

end SGA.SGA2.ExposeVI
