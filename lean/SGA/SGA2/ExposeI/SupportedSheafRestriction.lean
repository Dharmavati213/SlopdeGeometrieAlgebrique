/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedSupportedSheaves

/-!
# Open restriction of original supported sheaves and all their derived sheaves

The degree-zero comparison is proved on genuine supported sections on every
open. Full faithfulness of direct-image presheaves then gives the actual sheaf
comparison. Exact pre- and postcomposition yield all original derived degrees.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open CategoryTheory.Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

private def openPresheafRestrictionAdjunction (U : Opens X) :
    (whiskeringLeft _ _ AddCommGrpCat.{u}).obj U.isOpenEmbedding.functor.op ⊣
      (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map U.inclusion').op :=
  (U.isOpenEmbedding.isOpenMap.adjunction.op).whiskerLeft AddCommGrpCat.{u}

private instance openPresheafRestrictionAdjunction_counit_isIso (U : Opens X) :
    IsIso (openPresheafRestrictionAdjunction U).counit := by
  have : ∀ P, IsIso ((openPresheafRestrictionAdjunction U).counit.app P) := by
    intro P
    have : ∀ V, IsIso (((openPresheafRestrictionAdjunction U).counit.app P).app V) := by
      intro V
      change IsIso (P.map (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop).op)
      have h : U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop =
          eqToHom (Opens.map_functor_eq V.unop).symm := Subsingleton.elim _ _
      rw [h]
      infer_instance
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

/-- Presheaf direct image along an open inclusion is fully faithful. -/
def fullyFaithfulOpenPresheafPushforward (U : Opens X) :
    ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map U.inclusion').op).FullyFaithful :=
  (openPresheafRestrictionAdjunction U).fullyFaithfulROfIsIsoCounit

/-- Actual sheaf direct image along an open inclusion is fully faithful. -/
def fullyFaithfulOpenPushforward (U : Opens X) :
    (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').FullyFaithful where
  preimage f := ⟨(fullyFaithfulOpenPresheafPushforward U).preimage f.hom⟩
  map_preimage f := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (fullyFaithfulOpenPresheafPushforward U).map_preimage f.hom
  preimage_map f := by
    apply CategoryTheory.Sheaf.hom_ext
    exact (fullyFaithfulOpenPresheafPushforward U).preimage_map f.hom

/-- The support/restriction comparison after faithful presheaf direct image.
Both sides identify with the original supported sections on intersections. -/
def supportedSheafRestrictionPresheafIso (Z : Closeds X) (U : Opens X) :
    (underlineGammaZFunctor Z ⋙ iShriek_open U) ⋙
      sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u} ⋙
        (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map U.inclusion').op ≅
    (iShriek_open U ⋙ underlineGammaZFunctor (closedSupportOnOpen Z U)) ⋙
      sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u} ⋙
        (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map U.inclusion').op :=
  isoWhiskerLeft (underlineGammaZFunctor Z) (openRestrictionSectionsFunctorIso U) ≪≫
    isoWhiskerRight (underlineGammaZPresheafFunctorIso Z)
      ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor U).op) ≪≫
    (locallyClosedAmbientPresheafIso (LocallyClosedIn.ofOpenClosed U Z) Z rfl).symm ≪≫
    (isoWhiskerLeft (iShriek_open U)
      (isoWhiskerRight (underlineGammaZPresheafFunctorIso (closedSupportOnOpen Z U))
        ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map U.inclusion').op))).symm

/-- Original closed-support sheaves commute with actual restriction to every
open, without requiring the support to lie inside that open. -/
def supportedSheafRestrictionIso (Z : Closeds X) (U : Opens X) :
    underlineGammaZFunctor Z ⋙ iShriek_open U ≅
      iShriek_open U ⋙ underlineGammaZFunctor (closedSupportOnOpen Z U) :=
  (((fullyFaithfulSheafToPresheaf
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u}).comp
      (fullyFaithfulOpenPresheafPushforward U)).whiskeringRight
        (Sheaf AddCommGrpCat.{u} X)).preimageIso (supportedSheafRestrictionPresheafIso Z U)

/-- Open base change for the original derived supported sheaves, naturally
in arbitrary coefficient sheaves and in every cohomological degree. -/
def derivedSupportedSheafRestrictionIso (Z : Closeds X) (U : Opens X) (n : ℕ) :
    derivedUnderlineGammaZ Z n ⋙ iShriek_open U ≅
      iShriek_open U ⋙ derivedUnderlineGammaZ (closedSupportOnOpen Z U) n := by
  let := (openExtensionByZeroAdjunction U).isRightAdjoint
  letI : (iShriek_open U).PreservesHomology := inferInstance
  exact (rightDerivedPostcomposeIso (underlineGammaZFunctor Z) (iShriek_open U) n).symm ≪≫
    rightDerivedFunctorIso (supportedSheafRestrictionIso Z U) n ≪≫
      rightDerivedPrecomposeIso (iShriek_open U)
        (underlineGammaZFunctor (closedSupportOnOpen Z U)) n

theorem derivedSupportedSheafRestrictionIso_hom_naturality
    (Z : Closeds X) (U : Opens X) (n : ℕ)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) :
    (iShriek_open U).map ((derivedUnderlineGammaZ Z n).map f) ≫
      (derivedSupportedSheafRestrictionIso Z U n).hom.app G =
        (derivedSupportedSheafRestrictionIso Z U n).hom.app F ≫
          (derivedUnderlineGammaZ (closedSupportOnOpen Z U) n).map ((iShriek_open U).map f) :=
  (derivedSupportedSheafRestrictionIso Z U n).hom.naturality f

end SGA.SGA2.ExposeI
