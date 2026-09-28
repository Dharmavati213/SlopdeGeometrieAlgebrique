/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedCompositionGeometry

/-! # I.1, (13): arbitrary locally closed composition

The original extensions by zero compose, with a proved homeomorphism from
the actual nested support space to a genuine single ambient witness. The
comparison applies to all abelian coefficient sheaves. Its conjugate under
the actual adjunctions gives composition of extraordinary inverse images.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

/-- **I.1, (13), arbitrary locally closed immersions:** extension by zero
from the single actual composite support is naturally the original iterated
extension by zero, for arbitrary coefficient sheaves. -/
def locallyClosedExtensionCompIso (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).hom ⋙
        iBang_locallyClosed (locallyClosedCompositionWitness W V) ≅
      iBang_locallyClosed V ⋙ iBang_locallyClosed W :=
  isoWhiskerLeft
      (Sheaf.pushforward AddCommGrpCat.{u}
        (extensionClosedImageSpaceIso (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV).hom)
      (locallyClosedClosedExtensionCompIso (locallyClosedOpenCompositionWitness W V.V)
        (locallyClosedCompositionClosedPart W V)) ≪≫
    isoWhiskerRight
      (extensionClosedImagePushforwardIso (locallyClosedOpenCompositionSpaceIso W V.V) V.ZV)
      (iBang_locallyClosed (locallyClosedOpenCompositionWitness W V.V)) ≪≫
    isoWhiskerLeft
      (iBang_closed (X := (Opens.toTopCat (TopCat.of (W.ZV : Set W.V))).obj V.V) V.ZV)
      (locallyClosedOpenExtensionCompIso W V.V)

/-- The actual coefficient morphisms commute with the extension comparison. -/
@[reassoc]
theorem locallyClosedExtensionCompIso_naturality (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V)))
    {G H : Sheaf AddCommGrpCat.{u} (TopCat.of (V.ZV : Set V.V))} (f : G ⟶ H) :
    (Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).hom ⋙
        iBang_locallyClosed (locallyClosedCompositionWitness W V)).map f ≫
        (locallyClosedExtensionCompIso W V).hom.app H =
      (locallyClosedExtensionCompIso W V).hom.app G ≫
        (iBang_locallyClosed V ⋙ iBang_locallyClosed W).map f :=
  (locallyClosedExtensionCompIso W V).hom.naturality f

/-- The single-witness extension carries the actual original extraordinary
inverse image, transported back along the same support-space homeomorphism. -/
def locallyClosedCompositeSingleAdjunction (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    (Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).hom ⋙
      iBang_locallyClosed (locallyClosedCompositionWitness W V)) ⊣
    (iUpperShriek_locallyClosed (locallyClosedCompositionWitness W V) ⋙
      Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).inv) :=
  (extensionSpaceSheafEquivalence (locallyClosedCompositionSpaceIso W V)).toAdjunction.comp
    (locallyClosedSupportAdjunction (locallyClosedCompositionWitness W V))

/-- The original iterated adjunction, with only its left side replaced by
the proved extension comparison. -/
def locallyClosedCompositeIteratedAdjunction (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    (Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).hom ⋙
      iBang_locallyClosed (locallyClosedCompositionWitness W V)) ⊣
    (iUpperShriek_locallyClosed W ⋙ iUpperShriek_locallyClosed V) :=
  ((locallyClosedSupportAdjunction V).comp (locallyClosedSupportAdjunction W)).ofNatIsoLeft
    (locallyClosedExtensionCompIso W V).symm

/-- The transported counit is the original two counits, composed with the
proved extension comparison; it is not a separately chosen support map. -/
theorem locallyClosedCompositeIteratedAdjunction_counit (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V)))
    (F : Sheaf AddCommGrpCat.{u} X) :
    (locallyClosedCompositeIteratedAdjunction W V).counit.app F =
      (locallyClosedExtensionCompIso W V).hom.app
        ((iUpperShriek_locallyClosed W ⋙ iUpperShriek_locallyClosed V).obj F) ≫
      (iBang_locallyClosed W).map
        ((locallyClosedSupportAdjunction V).counit.app ((iUpperShriek_locallyClosed W).obj F)) ≫
      (locallyClosedSupportAdjunction W).counit.app F := rfl

/-- Likewise the transported unit is the original two units, followed by
the inverse extension comparison under the actual extraordinary functors. -/
theorem locallyClosedCompositeIteratedAdjunction_unit (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V)))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (V.ZV : Set V.V))) :
    (locallyClosedCompositeIteratedAdjunction W V).unit.app G =
      (locallyClosedSupportAdjunction V).unit.app G ≫
      (iUpperShriek_locallyClosed V).map
        ((locallyClosedSupportAdjunction W).unit.app ((iBang_locallyClosed V).obj G)) ≫
      (iUpperShriek_locallyClosed W ⋙ iUpperShriek_locallyClosed V).map
        ((locallyClosedExtensionCompIso W V).inv.app G) := rfl

/-- **I.1, (13), arbitrary locally closed immersions:** the original
extraordinary inverse images compose, naturally in the ambient sheaf. -/
def locallyClosedUpperShriekCompIso (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V))) :
    iUpperShriek_locallyClosed (locallyClosedCompositionWitness W V) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).inv ≅
      iUpperShriek_locallyClosed W ⋙ iUpperShriek_locallyClosed V :=
  (locallyClosedCompositeSingleAdjunction W V).rightAdjointUniq
    (locallyClosedCompositeIteratedAdjunction W V)

/-- The extraordinary comparison is compatible with the actual adjunction
counits. This controls the support-to-ambient maps as well as the functors. -/
@[reassoc]
theorem locallyClosedUpperShriekCompIso_counit (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V)))
    (F : Sheaf AddCommGrpCat.{u} X) :
    (Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).hom ⋙
      iBang_locallyClosed (locallyClosedCompositionWitness W V)).map
        ((locallyClosedUpperShriekCompIso W V).hom.app F) ≫
        (locallyClosedCompositeIteratedAdjunction W V).counit.app F =
      (locallyClosedCompositeSingleAdjunction W V).counit.app F :=
  (locallyClosedCompositeSingleAdjunction W V).rightAdjointUniq_hom_app_counit
    (locallyClosedCompositeIteratedAdjunction W V) F

/-- The same comparison preserves the actual units on arbitrary coefficients. -/
@[reassoc]
theorem locallyClosedUpperShriekCompIso_unit (W : LocallyClosedIn X)
    (V : LocallyClosedIn (TopCat.of (W.ZV : Set W.V)))
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (V.ZV : Set V.V))) :
    (locallyClosedCompositeSingleAdjunction W V).unit.app G ≫
        (locallyClosedUpperShriekCompIso W V).hom.app
          ((Sheaf.pushforward AddCommGrpCat.{u} (locallyClosedCompositionSpaceIso W V).hom ⋙
            iBang_locallyClosed (locallyClosedCompositionWitness W V)).obj G) =
      (locallyClosedCompositeIteratedAdjunction W V).unit.app G :=
  (locallyClosedCompositeSingleAdjunction W V).unit_rightAdjointUniq_hom_app
    (locallyClosedCompositeIteratedAdjunction W V) G

end SGA.SGA2.ExposeI
