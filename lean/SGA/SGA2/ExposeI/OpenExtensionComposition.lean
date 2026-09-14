/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenClosedExtensionComposition

/-! # I.1, (13): composition with an outer open immersion

The ambient open is the actual image of the inner open. Its canonical
homeomorphism with the iterated subspace compares actual restriction and
extension functors, rather than introducing another extension model.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

/-- The iterated open subspace is its literal image in the ambient space. -/
def nestedOpenExtensionHomeomorph (U : Opens X) (V : Opens ((Opens.toTopCat X).obj U)) :
    V ≃ₜ U.isOpenEmbedding.functor.obj V :=
  Topology.IsEmbedding.subtypeVal.homeomorphImage (V : Set ((Opens.toTopCat X).obj U))

def nestedOpenExtensionSpaceIso (U : Opens X) (V : Opens ((Opens.toTopCat X).obj U)) :
    (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj V ≅
      (Opens.toTopCat X).obj (U.isOpenEmbedding.functor.obj V) :=
  TopCat.isoOfHomeo (nestedOpenExtensionHomeomorph U V)

/-- Flattening preserves the actual inclusion in `X`. -/
theorem nestedOpenExtensionSpaceIso_comp (U : Opens X)
    (V : Opens ((Opens.toTopCat X).obj U)) :
    (nestedOpenExtensionSpaceIso U V).hom ≫
        (U.isOpenEmbedding.functor.obj V).inclusion' = V.inclusion' ≫ U.inclusion' := rfl

/-- Actual ordinary restrictions compose after the canonical subspace transport. -/
def openOpenUpperShriekCompIso (U : Opens X) (V : Opens ((Opens.toTopCat X).obj U)) :
    iShriek_open U ⋙ iShriek_open V ≅
      iShriek_open (U.isOpenEmbedding.functor.obj V) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (nestedOpenExtensionSpaceIso U V).inv :=
  extensionSheafPullbackCompIso V.inclusion' U.inclusion' ≪≫
    eqToIso (congrArg (Sheaf.pullback AddCommGrpCat.{u})
      (nestedOpenExtensionSpaceIso_comp U V).symm) ≪≫
    (extensionSheafPullbackCompIso (nestedOpenExtensionSpaceIso U V).hom
      (U.isOpenEmbedding.functor.obj V).inclusion').symm ≪≫
    isoWhiskerLeft (iShriek_open (U.isOpenEmbedding.functor.obj V))
      (extensionSheafPullbackIsoPushforward (nestedOpenExtensionSpaceIso U V))

/-- The extension from the single ambient open, in the original coordinates. -/
def openOpenSingleExtensionAdjunction (U : Opens X)
    (V : Opens ((Opens.toTopCat X).obj U)) :
    (Sheaf.pushforward AddCommGrpCat.{u} (nestedOpenExtensionSpaceIso U V).hom ⋙
      iBang_open (U.isOpenEmbedding.functor.obj V)) ⊣
    (iShriek_open (U.isOpenEmbedding.functor.obj V) ⋙
      Sheaf.pushforward AddCommGrpCat.{u} (nestedOpenExtensionSpaceIso U V).inv) :=
  (extensionSpaceSheafEquivalence (nestedOpenExtensionSpaceIso U V)).toAdjunction.comp
    (openExtensionByZeroAdjunction (U.isOpenEmbedding.functor.obj V))

/-- **I.1, (13), two open immersions:** genuine extension by zero composes. -/
def openOpenExtensionCompIso (U : Opens X) (V : Opens ((Opens.toTopCat X).obj U)) :
    Sheaf.pushforward AddCommGrpCat.{u} (nestedOpenExtensionSpaceIso U V).hom ⋙
        iBang_open (U.isOpenEmbedding.functor.obj V) ≅ iBang_open V ⋙ iBang_open U :=
  (openOpenSingleExtensionAdjunction U V).leftAdjointUniq
    (((openExtensionByZeroAdjunction V).comp (openExtensionByZeroAdjunction U)).ofNatIsoRight
      (openOpenUpperShriekCompIso U V))

end SGA.SGA2.ExposeI
