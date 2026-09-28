/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedExtensionComposition
import SGA.SGA2.ExposeI.SupportedSheafRestriction

/-! # Actual open–closed interchange for extension by zero

The comparison is deduced from the proved open restriction theorem for
the original supported sheaf, and from actual pullback adjunctions. This
is the mixed composition step in I.1, (13), for arbitrary coefficients.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X Y Z : TopCat.{u}}

/-- Composition of genuine sheaf inverse images, obtained from the literal
composition of direct images and the original adjunctions. -/
def extensionSheafPullbackCompIso (f : X ⟶ Y) (g : Y ⟶ Z) :
    Sheaf.pullback AddCommGrpCat.{u} g ⋙ Sheaf.pullback AddCommGrpCat.{u} f ≅
      Sheaf.pullback AddCommGrpCat.{u} (f ≫ g) :=
  ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} g).comp
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)).leftAdjointUniq
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} (f ≫ g))

/-- Along an actual homeomorphism, inverse image agrees with direct image
along the inverse map. -/
def extensionSheafPullbackIsoPushforward (e : X ≅ Y) :
    Sheaf.pullback AddCommGrpCat.{u} e.hom ≅
      Sheaf.pushforward AddCommGrpCat.{u} e.inv :=
  (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} e.hom).leftAdjointUniq
    (extensionSpaceSheafEquivalence e).symm.toAdjunction

/-- Three inverse images, with the associativity comparison isolated before
specializing to the actual support square. -/
def extensionSheafPullbackTripleIso {Q : TopCat.{u}}
    (f : Q ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z) :
    (Sheaf.pullback AddCommGrpCat.{u} h ⋙ Sheaf.pullback AddCommGrpCat.{u} g) ⋙
        Sheaf.pullback AddCommGrpCat.{u} f ≅
      Sheaf.pullback AddCommGrpCat.{u} (f ≫ g ≫ h) :=
  isoWhiskerRight (extensionSheafPullbackCompIso g h)
    (Sheaf.pullback AddCommGrpCat.{u} f) ≪≫ extensionSheafPullbackCompIso f (g ≫ h)

/-- Pullback comparison for an actual commuting square with a homeomorphism
on the source. Only equality of the underlying continuous maps is used. -/
def extensionSheafPullbackSquareIso {P Q : TopCat.{u}}
    (a : P ⟶ X) (b : X ⟶ Z) (e : P ≅ Q) (c : Q ⟶ Y) (d : Y ⟶ Z)
    (h : e.hom ≫ c ≫ d = a ≫ b) :
    Sheaf.pullback AddCommGrpCat.{u} b ⋙ Sheaf.pullback AddCommGrpCat.{u} a ≅
      (Sheaf.pullback AddCommGrpCat.{u} d ⋙ Sheaf.pullback AddCommGrpCat.{u} c) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} e.inv :=
  extensionSheafPullbackCompIso a b ≪≫
    eqToIso (congrArg (Sheaf.pullback AddCommGrpCat.{u}) h.symm) ≪≫
    (extensionSheafPullbackTripleIso e.hom c d).symm ≪≫
    isoWhiskerLeft (Sheaf.pullback AddCommGrpCat.{u} d ⋙ Sheaf.pullback AddCommGrpCat.{u} c)
      (extensionSheafPullbackIsoPushforward e)

/-- The open part of a closed support, viewed as an actual open of that support. -/
def closedSupportOpenPart (A : Closeds X) (U : Opens X) : Opens (A : Set X) :=
  (Opens.map (closedInclusion A)).obj U

/-- Interchanging the two subtype coordinates of `A ∩ U`. -/
def openClosedExtensionHomeomorph (A : Closeds X) (U : Opens X) :
    (closedSupportOpenPart A U : Set (A : Set X)) ≃ₜ
      (closedSupportOnOpen A U : Set ((Opens.toTopCat X).obj U)) where
  toFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  invFun x := ⟨⟨x.val.val, x.property⟩, x.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def openClosedExtensionSpaceIso (A : Closeds X) (U : Opens X) :
    (Opens.toTopCat (TopCat.of (A : Set X))).obj (closedSupportOpenPart A U) ≅
      TopCat.of (closedSupportOnOpen A U : Set ((Opens.toTopCat X).obj U)) :=
  TopCat.isoOfHomeo (openClosedExtensionHomeomorph A U)

/-- The comparison is over the ambient space, not merely an abstract homeomorphism. -/
theorem openClosedExtensionSpaceIso_comp (A : Closeds X) (U : Opens X) :
    (openClosedExtensionSpaceIso A U).hom ≫
        closedInclusion (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U) ≫
          U.inclusion' =
      (closedSupportOpenPart A U).inclusion' ≫ closedInclusion A := rfl

set_option maxHeartbeats 1000000 in
-- The actual sheaf categories contain several definitionally equal subtype spaces.
/-- Ordinary inverse images around the actual open–closed square commute. -/
def openClosedOrdinaryPullbackIso (A : Closeds X) (U : Opens X) :
    Sheaf.pullback AddCommGrpCat.{u} (closedInclusion A) ⋙
        iShriek_open (X := TopCat.of (A : Set X)) (closedSupportOpenPart A U) ≅
      iShriek_open U ⋙
        Sheaf.pullback AddCommGrpCat.{u}
          (closedInclusion (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U)) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).inv :=
  extensionSheafPullbackSquareIso (closedSupportOpenPart A U).inclusion' (closedInclusion A)
    (openClosedExtensionSpaceIso A U)
    (closedInclusion (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U)) U.inclusion'
    (openClosedExtensionSpaceIso_comp A U)

/-- Actual extraordinary inverse image commutes with open restriction.
The key non-formal input is `supportedSheafRestrictionIso`. -/
def openClosedUpperShriekCompIso (A : Closeds X) (U : Opens X) :
    iUpperShriek_closed A ⋙
        iShriek_open (X := TopCat.of (A : Set X)) (closedSupportOpenPart A U) ≅
      iShriek_open U ⋙
        iUpperShriek_closed (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).inv :=
  isoWhiskerRight (closedSupportPullbackIso A)
      (iShriek_open (X := TopCat.of (A : Set X)) (closedSupportOpenPart A U)) ≪≫
    isoWhiskerLeft (underlineGammaZFunctor A) (openClosedOrdinaryPullbackIso A U) ≪≫
    isoWhiskerRight (supportedSheafRestrictionIso A U)
      (Sheaf.pullback AddCommGrpCat.{u}
        (closedInclusion (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U)) ⋙
        Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).inv) ≪≫
    isoWhiskerLeft (iShriek_open U)
      (isoWhiskerRight
        (closedSupportPullbackIso (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U)).symm
        (Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).inv))

/-- The single open–closed factorization with the original support coordinates. -/
def openClosedSingleExtensionAdjunction (A : Closeds X) (U : Opens X) :
    (Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).hom ⋙
      iBang_closed (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U) ⋙
      iBang_open U) ⊣
    (iShriek_open U ⋙
      iUpperShriek_closed (X := (Opens.toTopCat X).obj U) (closedSupportOnOpen A U) ⋙
      Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).inv) :=
  ((extensionSpaceSheafEquivalence (openClosedExtensionSpaceIso A U)).toAdjunction.comp
    (closedSupportAdjunction (X := (Opens.toTopCat X).obj U)
      (closedSupportOnOpen A U))).comp (openExtensionByZeroAdjunction U)

/-- **I.1, (13), open inside closed:** the single-witness extension is
the original open extension followed by the closed direct image. -/
def openClosedExtensionCompIso (A : Closeds X) (U : Opens X) :
    Sheaf.pushforward AddCommGrpCat.{u} (openClosedExtensionSpaceIso A U).hom ⋙
        iBang_locallyClosed (LocallyClosedIn.ofOpenClosed U A) ≅
      iBang_open (X := TopCat.of (A : Set X)) (closedSupportOpenPart A U) ⋙ iBang_closed A :=
  (openClosedSingleExtensionAdjunction A U).leftAdjointUniq
    (((openExtensionByZeroAdjunction (X := TopCat.of (A : Set X))
      (closedSupportOpenPart A U)).comp (closedSupportAdjunction A)).ofNatIsoRight
        (openClosedUpperShriekCompIso A U))

end SGA.SGA2.ExposeI
