/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.OpenExtensionComposition

/-! # Flattening locally closed extension through an outer open immersion -/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

/-- The inner closed support, transported to the single ambient open. -/
def outerOpenExtensionClosedPart (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) :
    Closeds ((Opens.toTopCat X).obj (U.isOpenEmbedding.functor.obj W.V)) :=
  ⟨nestedOpenExtensionHomeomorph U W.V '' (W.ZV : Set W.V),
    (nestedOpenExtensionHomeomorph U W.V).isClosedMap _ W.ZV.isClosed⟩

/-- A genuine single locally closed witness for the composite immersion. -/
def outerOpenExtensionWitness (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) : LocallyClosedIn X :=
  ⟨U.isOpenEmbedding.functor.obj W.V, outerOpenExtensionClosedPart U W⟩

/-- Canonical transport of the actual support space to single-witness coordinates. -/
def outerOpenExtensionHomeomorph (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) :
    (W.ZV : Set W.V) ≃ₜ
      (outerOpenExtensionClosedPart U W :
        Set ((Opens.toTopCat X).obj (U.isOpenEmbedding.functor.obj W.V))) :=
  (nestedOpenExtensionHomeomorph U W.V).isEmbedding.homeomorphImage (W.ZV : Set W.V)

def outerOpenExtensionSpaceIso (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) :
    TopCat.of (W.ZV : Set W.V) ≅
      TopCat.of ((outerOpenExtensionWitness U W).ZV : Set (outerOpenExtensionWitness U W).V) :=
  TopCat.isoOfHomeo (outerOpenExtensionHomeomorph U W)

/-- Both closed direct images are along the very same map after flattening. -/
def outerOpenClosedPushforwardIso (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) :
    Sheaf.pushforward AddCommGrpCat.{u} (outerOpenExtensionSpaceIso U W).hom ⋙
        iBang_closed (X := (Opens.toTopCat X).obj (outerOpenExtensionWitness U W).V)
          (outerOpenExtensionWitness U W).ZV ≅
      iBang_closed (X := (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj W.V) W.ZV ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (nestedOpenExtensionSpaceIso U W.V).hom :=
  eqToIso (by
    rw [← pushforward_comp, ← pushforward_comp]
    rfl)

/-- **I.1, (13), outer open immersion:** the original composite is the
extension from a genuine single locally closed witness. -/
def outerOpenLocallyClosedExtensionCompIso (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) :
    Sheaf.pushforward AddCommGrpCat.{u} (outerOpenExtensionSpaceIso U W).hom ⋙
        iBang_locallyClosed (outerOpenExtensionWitness U W) ≅
      iBang_locallyClosed W ⋙ iBang_open U :=
  isoWhiskerRight (outerOpenClosedPushforwardIso U W)
      (iBang_open (U.isOpenEmbedding.functor.obj W.V)) ≪≫
    isoWhiskerLeft
      (iBang_closed (X := (Opens.toTopCat ((Opens.toTopCat X).obj U)).obj W.V) W.ZV)
      (openOpenExtensionCompIso U W.V)

/-- The single support is literally the image of the inner support in `X`. -/
theorem outerOpenExtensionWitness_asSet (U : Opens X)
    (W : LocallyClosedIn ((Opens.toTopCat X).obj U)) :
    (outerOpenExtensionWitness U W).asSet = Subtype.val '' W.asSet := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z.val, ⟨z, hz, rfl⟩, rfl⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨nestedOpenExtensionHomeomorph U W.V z, ⟨z, hz, rfl⟩, rfl⟩

end SGA.SGA2.ExposeI
