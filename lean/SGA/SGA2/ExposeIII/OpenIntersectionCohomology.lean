/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.OrdinaryCohomologyRestriction
import SGA.SGA2.ExposeIII.HomeomorphismSupportedCohomology

/-!
# Nested open restriction and the ambient intersection

The iterated open subspace is genuinely homeomorphic to the ambient
intersection. Actual inverse-image sheaves agree under that homeomorphism,
as proved by their naive open-restriction models. Ordinary cohomology is
transported in every degree by exact direct image under the homeomorphism.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian Functor
open SGA.SGA2.ExposeI

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- The literal iterated subspace `W` inside `V` is the ambient intersection. -/
def openIntersectionHomeomorph (V W : Opens X) :
    ((Opens.map V.inclusion').obj W) ≃ₜ (V ⊓ W : Opens X) where
  toFun x := ⟨x.val.val, x.val.property, x.property⟩
  invFun x := ⟨⟨x.val, x.property.1⟩, x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The canonical homeomorphism, as a genuine isomorphism of topological spaces. -/
def openIntersectionIso (V W : Opens X) :
    (Opens.toTopCat ((Opens.toTopCat X).obj V)).obj
      ((Opens.map V.inclusion').obj W) ≅ (Opens.toTopCat X).obj (V ⊓ W) :=
  TopCat.isoOfHomeo (openIntersectionHomeomorph V W)

/-- The homeomorphism commutes with the actual inclusions into the ambient space. -/
theorem openIntersectionIso_inclusion (V W : Opens X) :
    (openIntersectionIso V W).hom ≫ (V ⊓ W).inclusion' =
      ((Opens.map V.inclusion').obj W).inclusion' ≫ V.inclusion' := rfl

/-- Images of opens under the iterated inclusion are the same ambient opens
as images under the intersection inclusion. -/
theorem openIntersection_image_eq (V W : Opens X)
    (A : Opens ((Opens.toTopCat X).obj (V ⊓ W))) :
    V.isOpenEmbedding.functor.obj
      (((Opens.map V.inclusion').obj W).isOpenEmbedding.functor.obj
        ((Opens.map (openIntersectionIso V W).hom).obj A)) =
      (V ⊓ W).isOpenEmbedding.functor.obj A := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨(openIntersectionHomeomorph V W) z, hz, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.val, y.property.1⟩,
      ⟨⟨⟨y.val, y.property.1⟩, y.property.2⟩, hy, rfl⟩, rfl⟩

/-- The open-set functors in the two restriction constructions agree. -/
def openIntersectionImageFunctorIso (V W : Opens X) :
    Opens.map (openIntersectionIso V W).hom ⋙
        ((Opens.map V.inclusion').obj W).isOpenEmbedding.functor ⋙
        V.isOpenEmbedding.functor ≅ (V ⊓ W).isOpenEmbedding.functor :=
  NatIso.ofComponents (fun A => eqToIso (openIntersection_image_eq V W A))
    (by intros; apply Subsingleton.elim)

/-- Actual direct image of the naive iterated restriction is the naive
restriction to the ambient intersection, section by section. -/
def naiveOpenIntersectionSheafIso (V W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (Sheaf.pushforward AddCommGrpCat.{u} (openIntersectionIso V W).hom).obj
      ((((Opens.map V.inclusion').obj W).isOpenEmbedding.sheafPullback
        AddCommGrpCat.{u}).obj ((V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)) ≅
      ((V ⊓ W).isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F :=
  (fullyFaithfulSheafToPresheaf
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj (V ⊓ W)))
    AddCommGrpCat.{u}).preimageIso
    (isoWhiskerRight (NatIso.op (openIntersectionImageFunctorIso V W)).symm F.presheaf)

/-- Genuine inverse-image restriction to `V` and then to `W` in `V` agrees
with restriction to `V ∩ W`, transported by the literal homeomorphism. -/
def openIntersectionSheafIso (V W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) :
    (Sheaf.pushforward AddCommGrpCat.{u} (openIntersectionIso V W).hom).obj
      (restrictToOpen (restrictToOpen F V) ((Opens.map V.inclusion').obj W)) ≅
      restrictToOpen F (V ⊓ W) :=
  (Sheaf.pushforward AddCommGrpCat.{u} (openIntersectionIso V W).hom).mapIso
      (((((Opens.map V.inclusion').obj W).isOpenEmbedding.sheafPullbackIso
        AddCommGrpCat.{u}).app (restrictToOpen F V)) ≪≫
        (((Opens.map V.inclusion').obj W).isOpenEmbedding.sheafPullback
          AddCommGrpCat.{u}).mapIso
            ((V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app F)) ≪≫
    naiveOpenIntersectionSheafIso V W F ≪≫
    (((V ⊓ W).isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).app F).symm

private def constantZGlobalSectionsFunctorIso (Y : TopCat.{u}) :
    preadditiveCoyoneda.obj (op (constantZ Y)) ≅
      (sheafSections (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj (op ⊤) :=
  NatIso.ofComponents (fun F => (constantZHomEquiv F).toAddCommGrpIso)
    (by intro F G f; ext g; rfl)

/-- The ordinary global-section functors agree under actual direct image. -/
def pushforwardConstantZHomFunctorIso {Y : TopCat.{u}} (f : X ⟶ Y) :
    Sheaf.pushforward AddCommGrpCat.{u} f ⋙ preadditiveCoyoneda.obj (op (constantZ Y)) ≅
      preadditiveCoyoneda.obj (op (constantZ X)) :=
  isoWhiskerLeft (Sheaf.pushforward AddCommGrpCat.{u} f)
      (constantZGlobalSectionsFunctorIso Y) ≪≫
    (constantZGlobalSectionsFunctorIso X).symm

/-- Actual ordinary cohomology is preserved by direct image under a
homeomorphism, in all degrees and naturally in the coefficient sheaf. -/
def homeomorphismOrdinaryCohomologyFunctorIso {Y : TopCat.{u}}
    (e : X ≅ Y) (n : ℕ) :
    Sheaf.pushforward AddCommGrpCat.{u} e.hom ⋙ extFunctorObj (constantZ Y) n ≅
      extFunctorObj (constantZ X) n :=
  isoWhiskerLeft (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
      (rightDerivedCoyonedaNatIsoExt (constantZ Y) n).symm ≪≫
    (rightDerivedPrecomposeIso (Sheaf.pushforward AddCommGrpCat.{u} e.hom)
      (preadditiveCoyoneda.obj (op (constantZ Y))) n).symm ≪≫
    rightDerivedFunctorIso (pushforwardConstantZHomFunctorIso e.hom) n ≪≫
    rightDerivedCoyonedaNatIsoExt (constantZ X) n

/-- The additive cohomology equivalence for a genuine homeomorphism. -/
def homeomorphismOrdinaryCohomologyEquiv {Y : TopCat.{u}}
    (e : X ≅ Y) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H ((Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n ≃+ H F n :=
  ((homeomorphismOrdinaryCohomologyFunctorIso e n).app F).addCommGroupIsoToAddEquiv

/-- The actual cohomology of the twice restricted sheaf is the cohomology
of the original sheaf restricted to the ambient intersection. -/
def openIntersectionCohomologyEquiv (V W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H (restrictToOpen (restrictToOpen F V) ((Opens.map V.inclusion').obj W)) n ≃+
      H (restrictToOpen F (V ⊓ W)) n :=
  (homeomorphismOrdinaryCohomologyEquiv (openIntersectionIso V W)
      (restrictToOpen (restrictToOpen F V) ((Opens.map V.inclusion').obj W)) n).symm.trans
    (((extFunctorObj (constantZ ((Opens.toTopCat X).obj (V ⊓ W))) n).mapIso
      (openIntersectionSheafIso V W F)).addCommGroupIsoToAddEquiv)

/-- Ordinary restriction `Hⁿ(V,F) → Hⁿ(V ∩ W,F)`, with the target expressed
using the actual ambient intersection rather than a nested subtype. -/
def ordinaryCohomologyRestrictionToIntersection (V W : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H (restrictToOpen F V) n →+ H (restrictToOpen F (V ⊓ W)) n :=
  (openIntersectionCohomologyEquiv V W F n).toAddMonoidHom.comp
    (ordinaryCohomologyRestriction ((Opens.map V.inclusion').obj W) (restrictToOpen F V) n)

/-- Target transport to the literal intersection does not change injectivity. -/
theorem ordinaryCohomologyRestrictionToIntersection_injective_iff
    (V W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Injective (ordinaryCohomologyRestrictionToIntersection V W F n) ↔
      Function.Injective (ordinaryCohomologyRestriction
        ((Opens.map V.inclusion').obj W) (restrictToOpen F V) n) :=
  (openIntersectionCohomologyEquiv V W F n).injective.of_comp_iff _

/-- Target transport to the literal intersection does not change bijectivity. -/
theorem ordinaryCohomologyRestrictionToIntersection_bijective_iff
    (V W : Opens X) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    Function.Bijective (ordinaryCohomologyRestrictionToIntersection V W F n) ↔
      Function.Bijective (ordinaryCohomologyRestriction
        ((Opens.map V.inclusion').obj W) (restrictToOpen F V) n) :=
  (openIntersectionCohomologyEquiv V W F n).bijective.of_comp_iff' _

end SGA.SGA2.ExposeIII
