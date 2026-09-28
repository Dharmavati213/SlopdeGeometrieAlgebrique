/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ClosedSupportCohomology

/-!
# Actual supported cohomology under a homeomorphism

Ordinary direct image identifies the actual degree-zero supported-section
kernels. For a homeomorphism its genuine inverse makes direct image an
equivalence; deriving the kernel identification therefore gives all degrees.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian Functor
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X Y : TopCat.{u}}

/-- Actual direct images under mutually inverse maps give an equivalence
of the original abelian sheaf categories. -/
def homeomorphismSheafPushforwardEquivalence (e : X ≅ Y) :
    Sheaf AddCommGrpCat.{u} X ≌ Sheaf AddCommGrpCat.{u} Y :=
  CategoryTheory.Equivalence.mk (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
    (Sheaf.pushforward AddCommGrpCat.{u} e.inv)
    (eqToIso (by rw [← pushforward_comp, e.hom_inv_id]; rfl))
    (eqToIso (by rw [← pushforward_comp, e.inv_hom_id]; rfl))

instance homeomorphismSheafPushforward_isEquivalence (e : X ≅ Y) :
    (Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (homeomorphismSheafPushforwardEquivalence e).isEquivalence_functor

/-- Supported global sections of an actual direct image are the actual
supported global sections for the inverse-image closed subset. -/
def pushforwardGammaZFunctorIso (f : X ⟶ Y) (Z : Closeds Y) :
    Sheaf.pushforward AddCommGrpCat.{u} f ⋙ gammaZSectionsFunctor Z ⊤ ≅
      gammaZSectionsFunctor (Z.preimage f.hom.continuous) ⊤ :=
  Iso.refl _

/-- Original supported cohomology is transported by a genuine homeomorphism,
as a natural isomorphism in arbitrary coefficient sheaves and every degree. -/
def homeomorphismSupportedCohomologyFunctorIso (e : X ≅ Y) (Z : Closeds Y) (n : ℕ) :
    Sheaf.pushforward AddCommGrpCat.{u} e.hom ⋙ extFunctorObj (zZX_closed Z) n ≅
      extFunctorObj (zZX_closed (Z.preimage e.hom.hom.continuous)) n :=
  isoWhiskerLeft (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
      (derivedGammaZSectionsIsoH_Z Z n).symm ≪≫
    (rightDerivedPrecomposeIso (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
      (gammaZSectionsFunctor Z ⊤) n).symm ≪≫
    rightDerivedFunctorIso (pushforwardGammaZFunctorIso e.hom Z) n ≪≫
    derivedGammaZSectionsIsoH_Z (Z.preimage e.hom.hom.continuous) n

/-- The actual supported cohomology groups before and after a homeomorphism. -/
def homeomorphismSupportedCohomologyEquiv (e : X ≅ Y) (Z : Closeds Y)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_Z Z ((Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n ≃+
      H_Z (Z.preimage e.hom.hom.continuous) F n :=
  ((homeomorphismSupportedCohomologyFunctorIso e Z n).app F).addCommGroupIsoToAddEquiv

end SGA.SGA2.ExposeIII
