/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportObject
import SGA.SGA2.ExposeVI.LocallyClosedExtSequences
import SGA.SGA2.ExposeI.RepresentedFunctorSequence

/-!
# SGA 2, VI.1.7.1: the actual module support-object sequence

The original supported-section inclusion and restriction determine the
canonical arrows of the genuine module support objects. Their short
exactness follows from the proved section sequence and flasqueness of the
underlying additive sheaves of injective module sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The actual support object represents the original supported-section functor. -/
def moduleLocallyClosedSupportHomFunctorIso (W : ExposeI.LocallyClosedIn X) :
    preadditiveCoyoneda.obj (op (moduleLocallyClosedSupport R W)) ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.gammaLocallyClosedFunctor W :=
  NatIso.ofComponents (fun G ↦ (moduleLocallyClosedSupportHomEquiv R W G).toAddCommGrpIso)
    (fun a ↦ by ext φ; exact moduleLocallyClosedSupportHomEquiv_naturality R W a φ)

variable (L : SheafOfModules.{u} R ⥤ Sheaf AddCommGrpCat.{u} X)
  (W : ExposeI.LocallyClosedIn X) (T : Closeds W.asSet)

/-- Apply an actual coefficient-sheaf functor to the original nested section sequence. -/
def moduleSupportSectionsFunctorSequence :
    ShortComplex (SheafOfModules.{u} R ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk
    (Functor.whiskerLeft L
      (ExposeI.locallyClosedNestedGammaInclusion W (ExposeI.nestedClosedSubspace W T)))
    (Functor.whiskerLeft L
      (ExposeI.locallyClosedNestedGammaRestriction W (ExposeI.nestedClosedSubspace W T)))
    (by
      apply NatTrans.ext
      funext G
      exact congrArg (fun a ↦ a.app (L.obj G))
        (ExposeI.locallyClosedNestedGamma_comp W (ExposeI.nestedClosedSubspace W T)))

/-- Left exactness holds for all actual coefficient module sheaves. -/
theorem moduleSupportSectionsFunctorSequence_leftExact (G : SheafOfModules.{u} R) :
    ((moduleSupportSectionsFunctorSequence R L W T).map
      ((evaluation (SheafOfModules.{u} R) AddCommGrpCat.{u}).obj G)).Exact ∧
        Mono ((moduleSupportSectionsFunctorSequence R L W T).f.app G) :=
  ExposeI.locallyClosedNestedGammaSequence_exact_and_mono W
    (ExposeI.nestedClosedSubspace W T) (L.obj G)

/-- Flasque image coefficients give the original surjectivity at the difference. -/
theorem moduleSupportSectionsFunctorSequence_epi (G : SheafOfModules.{u} R)
    [TopCat.Sheaf.IsFlasque (L.obj G)] :
    Epi ((moduleSupportSectionsFunctorSequence R L W T).g.app G) :=
  (ExposeI.locallyClosedNestedGammaSequence_shortExact W
    (ExposeI.nestedClosedSubspace W T) (L.obj G)).epi_g

variable {L}

/-- The canonical inclusion of the difference support module. -/
def moduleNestedSupportObjectInclusion :
    moduleLocallyClosedSupport R
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) ⟶
      moduleLocallyClosedSupport R W :=
  ExposeI.RepresentedSequence.firstMap
    (moduleSupportSectionsFunctorSequence R (SheafOfModules.toSheaf R) W T)
    (moduleLocallyClosedSupportHomFunctorIso R W)
    (moduleLocallyClosedSupportHomFunctorIso R _)

/-- The canonical map onto the smaller closed support module. -/
def moduleNestedSupportObjectRestriction :
    moduleLocallyClosedSupport R W ⟶
      moduleLocallyClosedSupport R
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) :=
  ExposeI.RepresentedSequence.secondMap
    (moduleSupportSectionsFunctorSequence R (SheafOfModules.toSheaf R) W T)
    (moduleLocallyClosedSupportHomFunctorIso R _)
    (moduleLocallyClosedSupportHomFunctorIso R W)

/-- The inclusion acts on Hom by the original supported-section restriction. -/
theorem moduleNestedSupportObjectInclusion_sections {G : SheafOfModules.{u} R}
    (φ : moduleLocallyClosedSupport R W ⟶ G) :
    moduleLocallyClosedSupportHomEquiv R
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T)) G
        (moduleNestedSupportObjectInclusion R W T ≫ φ) =
      (ExposeI.locallyClosedNestedGammaRestriction W (ExposeI.nestedClosedSubspace W T)).app
        ((SheafOfModules.toSheaf R).obj G) (moduleLocallyClosedSupportHomEquiv R W G φ) :=
  ExposeI.RepresentedSequence.firstMap_precomp
    (moduleSupportSectionsFunctorSequence R (SheafOfModules.toSheaf R) W T)
    (moduleLocallyClosedSupportHomFunctorIso R W)
    (moduleLocallyClosedSupportHomFunctorIso R _) φ

/-- The quotient acts on Hom by the original support-increasing section map. -/
theorem moduleNestedSupportObjectRestriction_sections {G : SheafOfModules.{u} R}
    (φ : moduleLocallyClosedSupport R
      (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T)) ⟶ G) :
    moduleLocallyClosedSupportHomEquiv R W G
        (moduleNestedSupportObjectRestriction R W T ≫ φ) =
      (ExposeI.locallyClosedNestedGammaInclusion W (ExposeI.nestedClosedSubspace W T)).app
        ((SheafOfModules.toSheaf R).obj G)
        (moduleLocallyClosedSupportHomEquiv R _ G φ) :=
  ExposeI.RepresentedSequence.secondMap_precomp
    (moduleSupportSectionsFunctorSequence R (SheafOfModules.toSheaf R) W T)
    (moduleLocallyClosedSupportHomFunctorIso R _)
    (moduleLocallyClosedSupportHomFunctorIso R W) φ

/-- The actual support modules and original represented arrows form a short complex. -/
def moduleNestedSupportObjectSequence : ShortComplex (SheafOfModules.{u} R) :=
  ExposeI.RepresentedSequence.shortComplex
    (moduleSupportSectionsFunctorSequence R (SheafOfModules.toSheaf R) W T)
    (moduleLocallyClosedSupportHomFunctorIso R _)
    (moduleLocallyClosedSupportHomFunctorIso R W)
    (moduleLocallyClosedSupportHomFunctorIso R _)

/-- **VI.1.7.1:** the original module support-object sequence is short exact
for every locally closed support and every closed subset of it. -/
theorem moduleNestedSupportObjectSequence_shortExact :
    (moduleNestedSupportObjectSequence R W T).ShortExact :=
  ExposeI.RepresentedSequence.shortExact _ _ _ _
    (moduleSupportSectionsFunctorSequence_leftExact R (SheafOfModules.toSheaf R) W T)
    (fun G _ ↦ by
      let := ExposeV.moduleIsFlasque_of_injective R G
      exact moduleSupportSectionsFunctorSequence_epi R (SheafOfModules.toSheaf R) W T G)

end SGA.SGA2.ExposeVI
