/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedExtensionEndpoints

/-! # Actual support geometry for arbitrary locally closed composition

An arbitrary open in a locally closed support has the existing genuine
single-witness extension comparison. Transporting an inner closed subset
through its actual homeomorphism then produces a single witness for an
arbitrary locally closed subset of that support.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X Y : TopCat.{u}}

/-- The original continuous inclusion of the actual support space. -/
def locallyClosedExtensionInclusion (W : LocallyClosedIn X) :
    TopCat.of (W.ZV : Set W.V) ⟶ X :=
  closedInclusion (X := (Opens.toTopCat X).obj W.V) W.ZV ≫ W.V.inclusion'

/-- Equality transport between opens leaves every underlying point unchanged. -/
theorem openExtensionEqSpaceIso_val {U V : Opens X} (h : U = V) (x : U) :
    ((openExtensionEqSpaceIso h).hom x).val = x.val := by
  subst V
  rfl

/-- The already constructed difference-space comparison is over the original
ambient space, not just an abstract isomorphism of support spaces. -/
theorem nestedDifferenceExtensionSpaceIso_inclusion (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedDifferenceExtensionSpaceIso W T).hom ≫
        locallyClosedExtensionInclusion (nestedDifferenceExtensionWitness W T) =
      T.compl.inclusion' ≫ locallyClosedExtensionInclusion W := by
  ext x
  exact congrArg (fun y : (W.ZV : Set W.V) => y.val.val)
    (openExtensionEqSpaceIso_val (X := TopCat.of (W.ZV : Set W.V))
      (nestedDifferenceOpen_eq W T) x)

/-- A genuine ambient witness for any open in the original support. -/
def locallyClosedOpenCompositionWitness (W : LocallyClosedIn X)
    (U : Opens (W.ZV : Set W.V)) : LocallyClosedIn X :=
  nestedDifferenceExtensionWitness W U.compl

/-- Its actual support space is the original open subspace, canonically. -/
def locallyClosedOpenCompositionSpaceIso (W : LocallyClosedIn X)
    (U : Opens (W.ZV : Set W.V)) :
    (Opens.toTopCat (TopCat.of (W.ZV : Set W.V))).obj U ≅
      TopCat.of ((locallyClosedOpenCompositionWitness W U).ZV :
        Set (locallyClosedOpenCompositionWitness W U).V) :=
  openExtensionEqSpaceIso (X := TopCat.of (W.ZV : Set W.V)) (Opens.compl_compl U).symm ≪≫
    nestedDifferenceExtensionSpaceIso W U.compl

/-- The open-composition comparison retains the actual ambient inclusion. -/
theorem locallyClosedOpenCompositionSpaceIso_inclusion (W : LocallyClosedIn X)
    (U : Opens (W.ZV : Set W.V)) :
    (locallyClosedOpenCompositionSpaceIso W U).hom ≫
        locallyClosedExtensionInclusion (locallyClosedOpenCompositionWitness W U) =
      U.inclusion' ≫ locallyClosedExtensionInclusion W := by
  change (openExtensionEqSpaceIso (X := TopCat.of (W.ZV : Set W.V))
      (Opens.compl_compl U).symm).hom ≫
    (nestedDifferenceExtensionSpaceIso W U.compl).hom ≫
      locallyClosedExtensionInclusion (nestedDifferenceExtensionWitness W U.compl) = _
  rw [nestedDifferenceExtensionSpaceIso_inclusion]
  ext x
  exact congrArg (fun y : (W.ZV : Set W.V) => y.val.val)
    (openExtensionEqSpaceIso_val (X := TopCat.of (W.ZV : Set W.V))
      (Opens.compl_compl U).symm x)

/-- Actual extension by zero composes for every open in a locally closed support. -/
def locallyClosedOpenExtensionCompIso (W : LocallyClosedIn X)
    (U : Opens (W.ZV : Set W.V)) :
    Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedOpenCompositionSpaceIso W U).hom ⋙
        iBang_locallyClosed (locallyClosedOpenCompositionWitness W U) ≅
      iBang_open (X := TopCat.of (W.ZV : Set W.V)) U ⋙ iBang_locallyClosed W :=
  isoWhiskerLeft
      (Sheaf.pushforward AddCommGrpCat.{u}
        (openExtensionEqSpaceIso (X := TopCat.of (W.ZV : Set W.V))
          (Opens.compl_compl U).symm).hom)
      (locallyClosedDifferenceExtensionCompIso W U.compl) ≪≫
    isoWhiskerRight
      (openExtensionEqIso (X := TopCat.of (W.ZV : Set W.V)) (Opens.compl_compl U).symm)
      (iBang_locallyClosed W)

/-- Transport of an actual closed subset along a specified homeomorphism. -/
def extensionClosedImage (e : X ≅ Y) (A : Closeds X) : Closeds Y :=
  ⟨e.hom '' (A : Set X), (TopCat.homeoOfIso e).isClosedMap _ A.isClosed⟩

/-- The actual closed support spaces are canonically homeomorphic under transport. -/
def extensionClosedImageSpaceIso (e : X ≅ Y) (A : Closeds X) :
    TopCat.of (A : Set X) ≅ TopCat.of (extensionClosedImage e A : Set Y) :=
  TopCat.isoOfHomeo ((TopCat.homeoOfIso e).isEmbedding.homeomorphImage (A : Set X))

/-- The support-space comparison commutes with the original closed inclusions. -/
theorem extensionClosedImageSpaceIso_inclusion (e : X ≅ Y) (A : Closeds X) :
    (extensionClosedImageSpaceIso e A).hom ≫ closedInclusion (extensionClosedImage e A) =
      closedInclusion A ≫ e.hom := rfl

/-- Closed extension is transported by the actual same continuous map. -/
def extensionClosedImagePushforwardIso (e : X ≅ Y) (A : Closeds X) :
    Sheaf.pushforward AddCommGrpCat.{u} (extensionClosedImageSpaceIso e A).hom ⋙
        iBang_closed (extensionClosedImage e A) ≅
      iBang_closed A ⋙ Sheaf.pushforward AddCommGrpCat.{u} e.hom :=
  eqToIso (by rw [← pushforward_comp, ← pushforward_comp,
    extensionClosedImageSpaceIso_inclusion])

/-- The inner closed part in the single-witness coordinates of its open support. -/
def locallyClosedCompositionClosedPart (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    Closeds ((locallyClosedOpenCompositionWitness W V.V).ZV :
      Set (locallyClosedOpenCompositionWitness W V.V).V) :=
  extensionClosedImage (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV

/-- A genuine single locally closed witness for an arbitrary nested locally
closed support, with no extra factorization or comparison hypothesis. -/
def locallyClosedCompositionWitness (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) : LocallyClosedIn X :=
  nestedClosedSupportWitness (locallyClosedOpenCompositionWitness W V.V)
    (locallyClosedCompositionClosedPart W V)

/-- Flattening the original nested support space to the genuine single witness. -/
def locallyClosedCompositionSpaceIso (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    TopCat.of (V.ZV : Set V.V) ≅
      TopCat.of ((locallyClosedCompositionWitness W V).ZV :
        Set (locallyClosedCompositionWitness W V).V) :=
  extensionClosedImageSpaceIso (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV ≪≫
    nestedClosedExtensionSpaceIso (locallyClosedOpenCompositionWitness W V.V)
      (locallyClosedCompositionClosedPart W V)

/-- The single-witness homeomorphism commutes with the original composite
inclusion of the nested locally closed support into `X`. -/
theorem locallyClosedCompositionSpaceIso_inclusion (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedCompositionSpaceIso W V).hom ≫
        locallyClosedExtensionInclusion (locallyClosedCompositionWitness W V) =
      locallyClosedExtensionInclusion V ≫ locallyClosedExtensionInclusion W := by
  calc
    _ = (extensionClosedImageSpaceIso (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV).hom ≫
        closedInclusion (X := TopCat.of ((locallyClosedOpenCompositionWitness W V.V).ZV :
          Set (locallyClosedOpenCompositionWitness W V.V).V))
          (locallyClosedCompositionClosedPart W V) ≫
        locallyClosedExtensionInclusion (locallyClosedOpenCompositionWitness W V.V) := by
      exact congrArg
        (fun f => (extensionClosedImageSpaceIso
          (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV).hom ≫ f ≫
            (locallyClosedOpenCompositionWitness W V.V).V.inclusion')
        (nestedClosedExtensionSpaceIso_comp (locallyClosedOpenCompositionWitness W V.V)
          (locallyClosedCompositionClosedPart W V))
    _ = closedInclusion (X := (Opens.toTopCat (TopCat.of (W.ZV : Set W.V))).obj V.V) V.ZV ≫
        (locallyClosedOpenCompositionSpaceIso W V.V).hom ≫
        locallyClosedExtensionInclusion (locallyClosedOpenCompositionWitness W V.V) := by
      exact congrArg
        (fun f => f ≫ locallyClosedExtensionInclusion (locallyClosedOpenCompositionWitness W V.V))
        (extensionClosedImageSpaceIso_inclusion (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV)
    _ = _ := congrArg
      (fun f => closedInclusion (X := (Opens.toTopCat (TopCat.of (W.ZV : Set W.V))).obj V.V)
        V.ZV ≫ f) (locallyClosedOpenCompositionSpaceIso_inclusion W V.V)

/-- The actual inclusion has exactly the recorded locally closed support as range. -/
theorem locallyClosedExtensionInclusion_range (W : LocallyClosedIn X) :
    Set.range (locallyClosedExtensionInclusion W) = W.asSet := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, y.property, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hy⟩, rfl⟩

/-- The single witness represents literally the original nested locally closed
subset included in the ambient space. -/
theorem locallyClosedCompositionWitness_asSet (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    (locallyClosedCompositionWitness W V).asSet =
      (fun x : (W.ZV : Set W.V) => x.val.val) '' V.asSet := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := (TopCat.homeoOfIso (locallyClosedCompositionSpaceIso W V)).surjective
      (⟨y, hy⟩ : (locallyClosedCompositionWitness W V).ZV)
    change (locallyClosedCompositionSpaceIso W V).hom z = ⟨y, hy⟩ at hz
    have h := ConcreteCategory.congr_hom (locallyClosedCompositionSpaceIso_inclusion W V) z
    change locallyClosedExtensionInclusion (locallyClosedCompositionWitness W V)
      ((locallyClosedCompositionSpaceIso W V).hom z) =
        locallyClosedExtensionInclusion W (locallyClosedExtensionInclusion V z) at h
    exact ⟨z.val.val, ⟨z.val, z.property, rfl⟩,
      h.symm.trans (congrArg
        (locallyClosedExtensionInclusion (locallyClosedCompositionWitness W V)) hz)⟩
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    let z' : TopCat.of (V.ZV : Set V.V) := ⟨z, hz⟩
    let w := (locallyClosedCompositionSpaceIso W V).hom z'
    have h := ConcreteCategory.congr_hom (locallyClosedCompositionSpaceIso_inclusion W V) z'
    exact ⟨w.val, w.property, h⟩

end SGA.SGA2.ExposeI
