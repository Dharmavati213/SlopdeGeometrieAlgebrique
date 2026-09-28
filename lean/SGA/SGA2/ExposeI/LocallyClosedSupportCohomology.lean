/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedSheafBoundary
import SGA.SGA2.ExposeI.ClosedSupportCohomology

/-!
# Cohomology on the closure of a locally closed support

The cohomology groups occurring in I.2.6 may be computed on the actual
closure of the locally closed support, as asserted in I.2.7. The comparison
uses ordinary closed pullback and is natural in the original coefficient sheaf.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite TopologicalSpace TopCat Functor Abelian

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

private theorem natIsoAddEquiv_naturality {C : Type*} [Category C]
    {P Q : C ⥤ AddCommGrpCat.{u}} (e : P ≅ Q) {A B : C} (f : A ⟶ B)
    (x : P.obj A) :
    (e.app B).addCommGroupIsoToAddEquiv (P.map f x) =
      Q.map f ((e.app A).addCommGroupIsoToAddEquiv x) :=
  ConcreteCategory.congr_hom (C := AddCommGrpCat.{u}) (e.hom.naturality f) x

/-- The canonical supported-kernel inclusion is an isomorphism if the
coefficient sheaf is already zero on the complement. -/
theorem underlineGammaZ_ι_isIso_of_restrict_isZero (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (hF : IsZero (restrictToOpen F Z.compl)) :
    IsIso (underlineGammaZ_ι F Z) := by
  apply kernel.ι_of_zero
  exact ((Sheaf.pushforward AddCommGrpCat.{u} (complementInclusion Z)).map_isZero hF).eq_of_tgt _ _

/-- A functor whose values vanish off `Z` identifies naturally with its
original closed-support kernel. -/
def supportedFunctorKernelIso {C : Type v} [Category.{w} C]
    (Z : Closeds X) (L : C ⥤ Sheaf AddCommGrpCat.{u} X)
    (hL : ∀ F, IsZero (restrictToOpen (L.obj F) Z.compl)) :
    L ⋙ underlineGammaZFunctor Z ≅ L := by
  letI (F : C) : IsIso (underlineGammaZ_ι (L.obj F) Z) :=
    underlineGammaZ_ι_isIso_of_restrict_isZero Z (L.obj F) (hL F)
  exact NatIso.ofComponents (fun F ↦ asIso (underlineGammaZ_ι (L.obj F) Z)) (fun f ↦ by
    change underlineGammaZMap (L.map f) Z ≫ underlineGammaZ_ι _ Z =
      underlineGammaZ_ι _ Z ≫ L.map f
    exact underlineGammaZMap_comp_ι (L.map f) Z)

/-- A sheaf-valued functor supported on a closed subspace is the actual
closed direct image of its ordinary closed pullback. -/
def supportedFunctorClosedPullbackPushforwardIso {C : Type v} [Category.{w} C]
    (Z : Closeds X) (L : C ⥤ Sheaf AddCommGrpCat.{u} X)
    (hL : ∀ F, IsZero (restrictToOpen (L.obj F) Z.compl)) :
    L ≅ (L ⋙ Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)) ⋙ iBang_closed Z :=
  (supportedFunctorKernelIso Z L hL).symm ≪≫
    isoWhiskerLeft L ((closedSupportPushforwardIso Z).symm ≪≫
      isoWhiskerRight (closedSupportPullbackIso Z) (iBang_closed Z)) ≪≫
    isoWhiskerRight
      (isoWhiskerRight (supportedFunctorKernelIso Z L hL)
        (Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z))) (iBang_closed Z)

/-- Original derived locally closed supported sheaves are the actual
closed direct images of their ordinary pullbacks to the closure. -/
def derivedLocallyClosedSupportClosedPushforwardIso (W : LocallyClosedIn X) (q : ℕ) :
    derivedUnderlineGammaLocallyClosed W q ≅
      (derivedUnderlineGammaLocallyClosed W q ⋙
        Sheaf.pullback AddCommGrpCat.{u} (closedInclusion W.closedHull)) ⋙
          iBang_closed W.closedHull :=
  supportedFunctorClosedPullbackPushforwardIso W.closedHull
    (derivedUnderlineGammaLocallyClosed W q) (fun F ↦
      derivedUnderlineGammaLocallyClosed_restrict_isZero_of_le_compl W F _ le_rfl q)

/-- **I.2.7, locally closed supports:** cohomology of the original supported
derived sheaf is cohomology of its actual restriction to the closure. -/
def derivedLocallyClosedSupportCohomologyFunctorIso (W : LocallyClosedIn X) (p q : ℕ) :
    derivedUnderlineGammaLocallyClosed W q ⋙ extFunctorObj (constantZ X) p ≅
      (derivedUnderlineGammaLocallyClosed W q ⋙
        Sheaf.pullback AddCommGrpCat.{u} (closedInclusion W.closedHull)) ⋙
          extFunctorObj (constantZ (TopCat.of (W.closedHull : Set X))) p :=
  isoWhiskerRight (derivedLocallyClosedSupportClosedPushforwardIso W q)
      (extFunctorObj (constantZ X) p) ≪≫
    Functor.associator _ _ _ ≪≫
    isoWhiskerLeft
      (derivedUnderlineGammaLocallyClosed W q ⋙
        Sheaf.pullback AddCommGrpCat.{u} (closedInclusion W.closedHull))
      (closedPushforwardCohomologyFunctorIso W.closedHull p)

def derivedLocallyClosedSupportCohomologyEquiv (W : LocallyClosedIn X)
    (F : Sheaf AddCommGrpCat.{u} X) (p q : ℕ) :
    H ((derivedUnderlineGammaLocallyClosed W q).obj F) p ≃+
      H ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion W.closedHull)).obj
        ((derivedUnderlineGammaLocallyClosed W q).obj F)) p :=
  ((derivedLocallyClosedSupportCohomologyFunctorIso W p q).app F).addCommGroupIsoToAddEquiv

theorem derivedLocallyClosedSupportCohomologyEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (p q : ℕ)
    (x : H ((derivedUnderlineGammaLocallyClosed W q).obj F) p) :
    derivedLocallyClosedSupportCohomologyEquiv W G p q
        (CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaLocallyClosed W q).map f) p x) =
      CategoryTheory.Sheaf.H.map
        ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion W.closedHull)).map
          ((derivedUnderlineGammaLocallyClosed W q).map f)) p
        (derivedLocallyClosedSupportCohomologyEquiv W F p q x) :=
  natIsoAddEquiv_naturality (derivedLocallyClosedSupportCohomologyFunctorIso W p q) f x

end SGA.SGA2.ExposeI
