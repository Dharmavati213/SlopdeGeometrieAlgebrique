/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.NestedSupportSubspace

/-!
# I.1.8 for the original locally closed supported-section groups

The original `gammaLocallyClosedFunctor` values are retained. Their proved
ambient section comparisons turn actual inclusion and restriction into a
natural left exact sequence, short exact for flasque coefficients.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (W : LocallyClosedIn X) (T : Closeds (W.ZV : Set W.V))

/-- The smaller original supported-section functor in ambient coordinates. -/
def nestedGammaLeftIso :
    gammaLocallyClosedFunctor (nestedClosedSupportWitness W T) ≅
      gammaZSectionsFunctor (nestedClosedSupportWitness W T).closedHull W.V :=
  gammaLocallyClosedAmbientIso (nestedClosedSupportWitness W T)
    (nestedClosedSupportWitness W T).closedHull
    (nestedClosedSupportWitness W T).closedSupportOnOpen_closedHull

/-- The middle original supported-section functor in ambient coordinates. -/
def nestedGammaMiddleIso :
    gammaLocallyClosedFunctor W ≅ gammaZSectionsFunctor W.closedHull W.V :=
  gammaLocallyClosedAmbientIso W W.closedHull W.closedSupportOnOpen_closedHull

/-- The original difference's supported-section functor in ambient coordinates. -/
def nestedGammaRightIso :
    gammaLocallyClosedFunctor (nestedDifferenceSupportWitness W T) ≅
      gammaZSectionsFunctor W.closedHull
        (W.V ⊓ (nestedClosedSupportWitness W T).closedHull.compl) :=
  gammaLocallyClosedAmbientIso (nestedDifferenceSupportWitness W T) W.closedHull rfl

/-- Actual inclusion of original locally closed supported-section groups. -/
def locallyClosedNestedGammaInclusion :
    gammaLocallyClosedFunctor (nestedClosedSupportWitness W T) ⟶ gammaLocallyClosedFunctor W :=
  (nestedGammaLeftIso W T).hom ≫
    nestedSupportInclusion (nestedSupportClosedHulls_le W T) W.V ≫
      (nestedGammaMiddleIso W).inv

/-- Actual restriction of original supported sections to the difference. -/
def locallyClosedNestedGammaRestriction :
    gammaLocallyClosedFunctor W ⟶ gammaLocallyClosedFunctor (nestedDifferenceSupportWitness W T) :=
  (nestedGammaMiddleIso W).hom ≫
    nestedSupportRestriction (nestedClosedSupportWitness W T).closedHull W.closedHull W.V ≫
      (nestedGammaRightIso W T).inv

/-- The original group maps have zero composite. -/
theorem locallyClosedNestedGamma_comp :
    locallyClosedNestedGammaInclusion W T ≫ locallyClosedNestedGammaRestriction W T = 0 := by
  simp only [locallyClosedNestedGammaInclusion, locallyClosedNestedGammaRestriction,
    Category.assoc, Iso.inv_hom_id_assoc]
  have hz : nestedSupportInclusion (nestedSupportClosedHulls_le W T) W.V ≫
      nestedSupportRestriction (nestedClosedSupportWitness W T).closedHull
        W.closedHull W.V = 0 := by
    ext F s
    exact (nestedSupportSections_exact (nestedSupportClosedHulls_le W T) W.V F _).mpr
      ⟨s, rfl⟩
  rw [← Category.assoc _ _ (nestedGammaRightIso W T).inv, hz, zero_comp, comp_zero]

/-- The actual original section sequence, naturally in the coefficient sheaf. -/
def locallyClosedNestedGammaFunctorSequence :
    ShortComplex (Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u}) :=
  ShortComplex.mk (locallyClosedNestedGammaInclusion W T)
    (locallyClosedNestedGammaRestriction W T) (locallyClosedNestedGamma_comp W T)

/-- The original locally closed supported-section short complex. -/
def locallyClosedNestedGammaSequence (F : Sheaf AddCommGrpCat.{u} X) :
    ShortComplex AddCommGrpCat.{u} :=
  (locallyClosedNestedGammaFunctorSequence W T).map
    ((evaluation (Sheaf AddCommGrpCat.{u} X) AddCommGrpCat.{u}).obj F)

/-- The comparison preserves both actual inclusion and restriction maps. -/
def locallyClosedNestedGammaSequenceIso (F : Sheaf AddCommGrpCat.{u} X) :
    locallyClosedNestedGammaSequence W T F ≅
      nestedSupportSectionsSequence (nestedSupportClosedHulls_le W T) W.V F :=
  ShortComplex.isoMk ((nestedGammaLeftIso W T).app F) ((nestedGammaMiddleIso W).app F)
    ((nestedGammaRightIso W T).app F)
    (by simp [locallyClosedNestedGammaSequence, locallyClosedNestedGammaFunctorSequence,
      locallyClosedNestedGammaInclusion, nestedSupportSectionsSequence])
    (by simp [locallyClosedNestedGammaSequence, locallyClosedNestedGammaFunctorSequence,
      locallyClosedNestedGammaRestriction, nestedSupportSectionsSequence])

/-- **I.1.8:** left exactness for every original locally closed support and coefficient. -/
theorem locallyClosedNestedGammaSequence_exact_and_mono (F : Sheaf AddCommGrpCat.{u} X) :
    (locallyClosedNestedGammaSequence W T F).Exact ∧
      Mono ((locallyClosedNestedGammaInclusion W T).app F) :=
  (ShortComplex.exact_and_mono_f_iff_of_iso (locallyClosedNestedGammaSequenceIso W T F)).mpr
    ⟨(ShortComplex.ab_exact_iff_function_exact _).mpr
      (nestedSupportSections_exact (nestedSupportClosedHulls_le W T) W.V F),
      (AddCommGrpCat.mono_iff_injective _).mpr
        (nestedSupportSectionsInclusion_injective (nestedSupportClosedHulls_le W T) W.V F)⟩

/-- **I.1.8:** original supported-section surjectivity for flasque coefficients. -/
theorem locallyClosedNestedGammaSequence_shortExact (F : Sheaf AddCommGrpCat.{u} X)
    [IsFlasque F] : (locallyClosedNestedGammaSequence W T F).ShortExact :=
  ShortComplex.shortExact_of_iso (locallyClosedNestedGammaSequenceIso W T F).symm
    (nestedSupportSectionsSequence_shortExact (nestedSupportClosedHulls_le W T) W.V F)

/-- **I.1.8**, for a closed subset of the literal original support space. -/
theorem nestedClosedSubspaceGammaSequence_shortExact (T : Closeds W.asSet)
    (F : Sheaf AddCommGrpCat.{u} X) [IsFlasque F] :
    (locallyClosedNestedGammaSequence W (nestedClosedSubspace W T) F).ShortExact :=
  locallyClosedNestedGammaSequence_shortExact W (nestedClosedSubspace W T) F

end SGA.SGA2.ExposeI
