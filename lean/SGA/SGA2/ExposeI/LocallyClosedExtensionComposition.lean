/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedExtensionSequence
import SGA.SGA2.ExposeI.NestedSupportSubspace

/-! # I.1, (13): a closed immersion inside a locally closed immersion

The two closed inclusions flatten to the genuine closed subset of the
original open neighbourhood. Its extension by zero is compared with the
original composite, naturally in arbitrary coefficient sheaves. The
extraordinary inverse-image comparison is obtained from these actual
adjunctions. No composition comparison is a hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

/-- The actual support of the closed subspace in single-witness coordinates. -/
def nestedClosedExtensionHomeomorph (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (T : Set (W.ZV : Set W.V)) ≃ₜ (nestedClosedPart W T : Set W.V) :=
  Topology.IsEmbedding.subtypeVal.homeomorphImage (T : Set (W.ZV : Set W.V))

/-- The two actual support spaces are canonically isomorphic as spaces. -/
def nestedClosedExtensionSpaceIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    TopCat.of (T : Set (W.ZV : Set W.V)) ≅
      TopCat.of (nestedClosedPart W T : Set W.V) :=
  TopCat.isoOfHomeo (nestedClosedExtensionHomeomorph W T)

/-- Flattening commutes with the original closed inclusion maps. -/
theorem nestedClosedExtensionSpaceIso_comp (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedClosedExtensionSpaceIso W T).hom ≫
        closedInclusion (X := (Opens.toTopCat X).obj W.V) (nestedClosedPart W T) =
      closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T ≫
        closedInclusion (X := (Opens.toTopCat X).obj W.V) W.ZV := rfl

/-- Transport of arbitrary abelian sheaves along an actual isomorphism of spaces. -/
def extensionSpaceSheafEquivalence {Y Z : TopCat.{u}} (e : Y ≅ Z) :
    Sheaf AddCommGrpCat.{u} Y ≌ Sheaf AddCommGrpCat.{u} Z :=
  CategoryTheory.Equivalence.mk (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
    (Sheaf.pushforward AddCommGrpCat.{u} e.inv)
    (eqToIso (by rw [← pushforward_comp, e.hom_inv_id]; rfl))
    (eqToIso (by rw [← pushforward_comp, e.inv_hom_id]; rfl))

/-- **I.1, (13), closed inner immersion:** extension of arbitrary coefficients
on the single nested witness is the original composite extension. -/
def locallyClosedClosedExtensionCompIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).hom ⋙
        iBang_locallyClosed (nestedClosedSupportWitness W T) ≅
      iBang_closed (X := TopCat.of (W.ZV : Set W.V)) T ⋙ iBang_locallyClosed W :=
  eqToIso (by
    change (Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).hom ⋙
      Sheaf.pushforward AddCommGrpCat.{u}
        (closedInclusion (X := (Opens.toTopCat X).obj W.V) (nestedClosedPart W T))) ⋙
        iBang_open W.V =
      (Sheaf.pushforward AddCommGrpCat.{u}
          (closedInclusion (X := TopCat.of (W.ZV : Set W.V)) T) ⋙
        Sheaf.pushforward AddCommGrpCat.{u}
          (closedInclusion (X := (Opens.toTopCat X).obj W.V) W.ZV)) ⋙ iBang_open W.V
    rw [← pushforward_comp, ← pushforward_comp, nestedClosedExtensionSpaceIso_comp])

/-- The single-witness extension, with its genuine extraordinary inverse-image
right adjoint in the original nested support coordinates. -/
def locallyClosedClosedSingleAdjunction (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).hom ⋙
      iBang_locallyClosed (nestedClosedSupportWitness W T)) ⊣
    (iUpperShriek_locallyClosed (nestedClosedSupportWitness W T) ⋙
      Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).inv) :=
  (extensionSpaceSheafEquivalence (nestedClosedExtensionSpaceIso W T)).toAdjunction.comp
    (locallyClosedSupportAdjunction (nestedClosedSupportWitness W T))

/-- **I.1, (13), closed inner immersion:** extraordinary inverse image for
the single witness equals the actual composite of extraordinary inverse images. -/
def locallyClosedClosedUpperShriekCompIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    iUpperShriek_locallyClosed (nestedClosedSupportWitness W T) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (nestedClosedExtensionSpaceIso W T).inv ≅
      iUpperShriek_locallyClosed W ⋙
        iUpperShriek_closed (X := TopCat.of (W.ZV : Set W.V)) T :=
  (locallyClosedClosedSingleAdjunction W T).rightAdjointUniq
    (((closedSupportAdjunction (X := TopCat.of (W.ZV : Set W.V)) T).comp
      (locallyClosedSupportAdjunction W)).ofNatIsoLeft
      (locallyClosedClosedExtensionCompIso W T).symm)

end SGA.SGA2.ExposeI
