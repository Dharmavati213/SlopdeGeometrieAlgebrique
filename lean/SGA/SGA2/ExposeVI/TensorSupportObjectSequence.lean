/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportObjectSequence
import SGA.SGA2.ExposeVI.LocallyClosedTensorSupportHom

/-!
# SGA 2, VI.1.7.2: the actual supported tensor sequence

The literal tensor sources represent the original supported Hom functors.
The original supported-Hom exactness and injective-coefficient flasqueness
therefore prove a short exact sequence of these tensor sources for every
module sheaf, without any flatness hypothesis on it.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (S : Sheaf CommRingCat.{u} X)
  (F : SheafOfModules.{u} (commRingSheafToRing (Opens.grothendieckTopology X) S))
  (W : ExposeI.LocallyClosedIn X) (T : Closeds W.asSet)

local notation "R" => commRingSheafToRing (Opens.grothendieckTopology X) S

/-- Inclusion of the literal tensor supported on the difference. -/
def moduleNestedTensorSupportInclusion :
    moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleLocallyClosedSupport R
          (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T))) F ⟶
      moduleSheafTensor (Opens.grothendieckTopology X) S (moduleLocallyClosedSupport R W) F :=
  ExposeI.RepresentedSequence.firstMap
    (moduleSupportSectionsFunctorSequence R
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T)
    (locallyClosedTensorSupportHomFunctorIso S F W)
    (locallyClosedTensorSupportHomFunctorIso S F _)

/-- Restriction of the literal tensor to the smaller closed support. -/
def moduleNestedTensorSupportRestriction :
    moduleSheafTensor (Opens.grothendieckTopology X) S (moduleLocallyClosedSupport R W) F ⟶
      moduleSheafTensor (Opens.grothendieckTopology X) S
        (moduleLocallyClosedSupport R
          (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T))) F :=
  ExposeI.RepresentedSequence.secondMap
    (moduleSupportSectionsFunctorSequence R
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T)
    (locallyClosedTensorSupportHomFunctorIso S F _)
    (locallyClosedTensorSupportHomFunctorIso S F W)

/-- The original section restriction is precomposition by the tensor inclusion. -/
theorem moduleNestedTensorSupportInclusion_sections {G : SheafOfModules.{u} R}
    (φ : moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleLocallyClosedSupport R W) F ⟶ G) :
    locallyClosedTensorSupportHomEquiv S F G
        (ExposeI.nestedDifferenceSupportWitness W (ExposeI.nestedClosedSubspace W T))
        (moduleNestedTensorSupportInclusion S F W T ≫ φ) =
      (ExposeI.locallyClosedNestedGammaRestriction W (ExposeI.nestedClosedSubspace W T)).app
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G)
        (locallyClosedTensorSupportHomEquiv S F G W φ) :=
  ExposeI.RepresentedSequence.firstMap_precomp
    (moduleSupportSectionsFunctorSequence R
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T)
    (locallyClosedTensorSupportHomFunctorIso S F W)
    (locallyClosedTensorSupportHomFunctorIso S F _) φ

/-- The original section inclusion is precomposition by the tensor restriction. -/
theorem moduleNestedTensorSupportRestriction_sections {G : SheafOfModules.{u} R}
    (φ : moduleSheafTensor (Opens.grothendieckTopology X) S
      (moduleLocallyClosedSupport R
        (ExposeI.nestedClosedSupportWitness W (ExposeI.nestedClosedSubspace W T))) F ⟶ G) :
    locallyClosedTensorSupportHomEquiv S F G W
        (moduleNestedTensorSupportRestriction S F W T ≫ φ) =
      (ExposeI.locallyClosedNestedGammaInclusion W (ExposeI.nestedClosedSubspace W T)).app
        (moduleSheafHomAb (Opens.grothendieckTopology X) F G)
        (locallyClosedTensorSupportHomEquiv S F G _ φ) :=
  ExposeI.RepresentedSequence.secondMap_precomp
    (moduleSupportSectionsFunctorSequence R
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T)
    (locallyClosedTensorSupportHomFunctorIso S F _)
    (locallyClosedTensorSupportHomFunctorIso S F W) φ

/-- The actual supported tensor sources and the original represented arrows. -/
def moduleNestedTensorSupportSequence : ShortComplex (SheafOfModules.{u} R) :=
  ExposeI.RepresentedSequence.shortComplex
    (moduleSupportSectionsFunctorSequence R
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T)
    (locallyClosedTensorSupportHomFunctorIso S F _)
    (locallyClosedTensorSupportHomFunctorIso S F W)
    (locallyClosedTensorSupportHomFunctorIso S F _)

/-- **VI.1.7.2:** the literal supported tensor sequence is short exact
for arbitrary coefficients and arbitrary locally closed support. -/
theorem moduleNestedTensorSupportSequence_shortExact :
    (moduleNestedTensorSupportSequence S F W T).ShortExact :=
  ExposeI.RepresentedSequence.shortExact _ _ _ _
    (moduleSupportSectionsFunctorSequence_leftExact R
      (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T)
    (fun G _ ↦ by
      let : TopCat.Sheaf.IsFlasque
          ((moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F).obj G) :=
        moduleSheafHomAb_isFlasque_of_injective R F G
      exact moduleSupportSectionsFunctorSequence_epi R
        (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F) W T G)

end SGA.SGA2.ExposeVI
