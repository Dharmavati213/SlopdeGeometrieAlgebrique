/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafInjective
import SGA.SGA2.ExposeI.DerivedSupportedSheaves
import SGA.SGA2.ExposeI.RightDerivedPrecomposition
import SGA.SGA2.ExposeI.FlasqueVanishingCriterion

/-!
# Cohomology on the actual closed support space

Closed direct image preserves ordinary cohomology in every degree. The
original derived supported sheaves are actual closed direct images of the
derived extraordinary inverse image. Consequently their ordinary cohomology
can be computed on the closed subspace, using ordinary closed pullback.
All comparisons are natural in the coefficient sheaf.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

private theorem natIsoAddEquiv_naturality {C : Type*} [Category C]
    {P Q : C ⥤ AddCommGrpCat.{u}} (e : P ≅ Q) {A B : C} (f : A ⟶ B)
    (x : P.obj A) :
    (e.app B).addCommGroupIsoToAddEquiv (P.map f x) =
      Q.map f ((e.app A).addCommGroupIsoToAddEquiv x) :=
  ConcreteCategory.congr_hom (C := AddCommGrpCat.{u}) (e.hom.naturality f) x

/-- Actual global sections of a closed direct image are global sections on
the closed subspace. -/
def closedPushforwardGlobalSectionsIso (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))) :
    ((iBang_closed Z).obj G).presheaf.obj (op ⊤) ≅ G.presheaf.obj (op ⊤) :=
  G.presheaf.mapIso (eqToIso (congrArg op (show
    (Opens.map (closedInclusion Z)).obj ⊤ = ⊤ by ext; rfl)))

/-- The global-section identification is the identity on the actual groups. -/
theorem closedPushforwardGlobalSectionsIso_hom (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))) :
    (closedPushforwardGlobalSectionsIso Z G).hom = 𝟙 (G.presheaf.obj (op ⊤)) := by
  change G.presheaf.map _ = 𝟙 _
  rw [Subsingleton.elim (eqToIso _).hom (𝟙 _), G.presheaf.map_id]

/-- Closed direct image identifies the actual global-section functors. -/
def closedPushforwardGlobalSectionsFunctorIso (Z : Closeds X) :
    iBang_closed Z ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) ≅
    (sheafSections (Opens.grothendieckTopology (TopCat.of (Z : Set X)))
      AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (closedPushforwardGlobalSectionsIso Z) (fun f ↦ by
    change f.hom.app _ ≫ (closedPushforwardGlobalSectionsIso Z _).hom =
      (closedPushforwardGlobalSectionsIso Z _).hom ≫ f.hom.app _
    rw [closedPushforwardGlobalSectionsIso_hom, closedPushforwardGlobalSectionsIso_hom]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

private def constantHomGlobalSectionsIso (Y : TopCat.{u}) :
    preadditiveCoyoneda.obj (op (constantZ Y)) ≅
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F ↦ (constantZHomEquiv F).toAddCommGrpIso)
    (by intro F G f; ext g; rfl)

/-- The original constant integer sheaf represents the actual global
sections of closed direct images. -/
def closedPushforwardConstantHomFunctorIso (Z : Closeds X) :
    iBang_closed Z ⋙ preadditiveCoyoneda.obj (op (constantZ X)) ≅
      preadditiveCoyoneda.obj (op (constantZ (TopCat.of (Z : Set X)))) :=
  Functor.isoWhiskerLeft (iBang_closed Z) (constantHomGlobalSectionsIso X) ≪≫
    closedPushforwardGlobalSectionsFunctorIso Z ≪≫
      (constantHomGlobalSectionsIso (TopCat.of (Z : Set X))).symm

/-- Closed direct image preserves the original Ext-defined ordinary
cohomology functor, in every degree. -/
def closedPushforwardCohomologyFunctorIso (Z : Closeds X) (n : ℕ) :
    iBang_closed Z ⋙ extFunctorObj (constantZ X) n ≅
      extFunctorObj (constantZ (TopCat.of (Z : Set X))) n :=
  Functor.isoWhiskerLeft (iBang_closed Z)
      (rightDerivedCoyonedaNatIsoExt (constantZ X) n).symm ≪≫
    (rightDerivedPrecomposeIso (iBang_closed Z)
      (preadditiveCoyoneda.obj (op (constantZ X))) n).symm ≪≫
    rightDerivedFunctorIso (closedPushforwardConstantHomFunctorIso Z) n ≪≫
    rightDerivedCoyonedaNatIsoExt (constantZ (TopCat.of (Z : Set X))) n

/-- **I.2.7, closed-space comparison:** ordinary cohomology of a genuine
closed direct image is ordinary cohomology on the closed subspace. -/
def closedPushforwardCohomologyEquiv (Z : Closeds X)
    (G : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))) (n : ℕ) :
    H ((iBang_closed Z).obj G) n ≃+ H G n :=
  ((closedPushforwardCohomologyFunctorIso Z n).app G).addCommGroupIsoToAddEquiv

/-- The closed-space comparison respects the actual cohomology maps. -/
theorem closedPushforwardCohomologyEquiv_naturality (Z : Closeds X)
    {G G' : Sheaf AddCommGrpCat.{u} (TopCat.of (Z : Set X))} (f : G ⟶ G')
    (n : ℕ) (x : H ((iBang_closed Z).obj G) n) :
    closedPushforwardCohomologyEquiv Z G' n
        (CategoryTheory.Sheaf.H.map ((iBang_closed Z).map f) n x) =
      CategoryTheory.Sheaf.H.map f n (closedPushforwardCohomologyEquiv Z G n x) :=
  natIsoAddEquiv_naturality (closedPushforwardCohomologyFunctorIso Z n) f x

/-- Original derived supported sheaves are actual closed direct images of
the derived extraordinary inverse image. Exactness is used only for closed
direct image, not for extraordinary inverse image. -/
def derivedUnderlineGammaZClosedPushforwardIso (Z : Closeds X) (q : ℕ) :
    derivedUnderlineGammaZ Z q ≅ (iUpperShriek_closed Z).rightDerived q ⋙ iBang_closed Z :=
  rightDerivedFunctorIso (closedSupportPushforwardIso Z).symm q ≪≫
    rightDerivedPostcomposeIso (iUpperShriek_closed Z) (iBang_closed Z) q

/-- Derived extraordinary inverse image is ordinary closed pullback of the
original derived supported sheaf. -/
def derivedClosedSupportPullbackIso (Z : Closeds X) (q : ℕ) :
    (iUpperShriek_closed Z).rightDerived q ≅
      derivedUnderlineGammaZ Z q ⋙ Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z) :=
  rightDerivedFunctorIso (closedSupportPullbackIso Z) q ≪≫
    rightDerivedPostcomposeIso (underlineGammaZFunctor Z)
      (Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)) q

/-- The original derived supported sheaves are recovered by pushing forward
their actual ordinary closed pullbacks. -/
def derivedUnderlineGammaZClosedPullbackPushforwardIso (Z : Closeds X) (q : ℕ) :
    derivedUnderlineGammaZ Z q ≅
      (derivedUnderlineGammaZ Z q ⋙
        Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)) ⋙ iBang_closed Z :=
  derivedUnderlineGammaZClosedPushforwardIso Z q ≪≫
    Functor.isoWhiskerRight (derivedClosedSupportPullbackIso Z q) (iBang_closed Z)

/-- Closed-space cohomology of the original derived supported sheaves,
as an isomorphism of actual coefficient functors. -/
def derivedSupportedSheafClosedCohomologyFunctorIso (Z : Closeds X) (p q : ℕ) :
    derivedUnderlineGammaZ Z q ⋙ extFunctorObj (constantZ X) p ≅
      (derivedUnderlineGammaZ Z q ⋙
        Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)) ⋙
          extFunctorObj (constantZ (TopCat.of (Z : Set X))) p :=
  Functor.isoWhiskerRight (derivedUnderlineGammaZClosedPullbackPushforwardIso Z q)
      (extFunctorObj (constantZ X) p) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (derivedUnderlineGammaZ Z q ⋙ Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z))
      (closedPushforwardCohomologyFunctorIso Z p)

/-- **I.2.7:** the cohomology of the original derived supported sheaf can be
computed on the actual closed support space, with ordinary closed pullback. -/
def derivedSupportedSheafClosedCohomologyEquiv (Z : Closeds X)
    (F : Sheaf AddCommGrpCat.{u} X) (p q : ℕ) :
    H ((derivedUnderlineGammaZ Z q).obj F) p ≃+
      H ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).obj
        ((derivedUnderlineGammaZ Z q).obj F)) p :=
  ((derivedSupportedSheafClosedCohomologyFunctorIso Z p q).app F).addCommGroupIsoToAddEquiv

/-- Closed-space computation is natural in the original coefficient sheaf. -/
theorem derivedSupportedSheafClosedCohomologyEquiv_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (p q : ℕ)
    (x : H ((derivedUnderlineGammaZ Z q).obj F) p) :
    derivedSupportedSheafClosedCohomologyEquiv Z G p q
        (CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaZ Z q).map f) p x) =
      CategoryTheory.Sheaf.H.map
        ((Sheaf.pullback AddCommGrpCat.{u} (closedInclusion Z)).map
          ((derivedUnderlineGammaZ Z q).map f)) p
        (derivedSupportedSheafClosedCohomologyEquiv Z F p q x) :=
  natIsoAddEquiv_naturality (derivedSupportedSheafClosedCohomologyFunctorIso Z p q) f x

end SGA.SGA2.ExposeI
