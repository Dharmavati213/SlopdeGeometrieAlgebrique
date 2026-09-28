/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.HomeomorphismSupportedCohomology

/-!
# Ordinary cohomology under an actual homeomorphism

The actual direct image identifies global sections. Its exact equivalence
therefore identifies the original Ext-defined cohomology in every degree.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}}

private def constantHomSectionsIso (X : TopCat.{u}) :
    preadditiveCoyoneda.obj (op (constantZ X)) ≅
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F => (constantZHomEquiv F).toAddCommGrpIso)
    (by intro F G f; ext g; rfl)

/-- Direct image preserves the actual global Hom from the constant integer sheaf. -/
def pushforwardConstantHomFunctorIso (f : X ⟶ Y) :
    Sheaf.pushforward AddCommGrpCat.{u} f ⋙ preadditiveCoyoneda.obj (op (constantZ Y)) ≅
      preadditiveCoyoneda.obj (op (constantZ X)) :=
  Functor.isoWhiskerLeft (Sheaf.pushforward AddCommGrpCat.{u} f) (constantHomSectionsIso Y) ≪≫
    (Iso.refl _) ≪≫ (constantHomSectionsIso X).symm

/-- Actual ordinary cohomology is invariant under direct image by a homeomorphism. -/
def homeomorphismCohomologyFunctorIso (e : X ≅ Y) (n : ℕ) :
    Sheaf.pushforward AddCommGrpCat.{u} e.hom ⋙ extFunctorObj (constantZ Y) n ≅
      extFunctorObj (constantZ X) n :=
  Functor.isoWhiskerLeft (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
      (rightDerivedCoyonedaNatIsoExt (constantZ Y) n).symm ≪≫
    (rightDerivedPrecomposeIso (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
      (preadditiveCoyoneda.obj (op (constantZ Y))) n).symm ≪≫
    rightDerivedFunctorIso (pushforwardConstantHomFunctorIso e.hom) n ≪≫
    rightDerivedCoyonedaNatIsoExt (constantZ X) n

/-- The original cohomology groups before and after a homeomorphism. -/
def homeomorphismCohomologyEquiv (e : X ≅ Y) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H ((Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n ≃+ H F n :=
  ((homeomorphismCohomologyFunctorIso e n).app F).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeIII
