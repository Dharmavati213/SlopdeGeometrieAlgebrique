/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SupportedSheafSections

/-! # Supported sections after actual open restriction, on every open -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Topology
open CategoryTheory.Functor
open scoped ConcreteCategory

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Intersection with a fixed open, as a functor on opens. -/
def openIntersectionFunctor (V : Opens X) : Opens X ⥤ Opens X where
  obj U := V ⊓ U
  map f := homOfLE (inf_le_inf_left V f.le)

def openImagePreimageIso (V : Opens X) :
    Opens.map V.inclusion' ⋙ V.isOpenEmbedding.functor ≅ openIntersectionFunctor V :=
  NatIso.ofComponents (fun U => eqToIso ((Opens.functor_map_eq_inf V U).trans (inf_comm U V)))

/-- The actual open pullback has the ordinary intersection sections,
naturally in the ambient open and in the coefficient sheaf. -/
def openRestrictionSectionsFunctorIso (V : Opens X) :
    iShriek_open V ⋙
      sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) AddCommGrpCat.{u} ⋙
        (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map V.inclusion').op ≅
    sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⋙
      (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openIntersectionFunctor V).op :=
  isoWhiskerRight
    (isoWhiskerRight (V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u})
      (sheafToPresheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj V)) AddCommGrpCat.{u}))
    ((whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map V.inclusion').op) ≪≫
  isoWhiskerLeft (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    ((whiskeringLeft _ _ AddCommGrpCat.{u}).mapIso (NatIso.op (openImagePreimageIso V).symm))

theorem openImage_preimage_inter_closedCompl (Z : Closeds X) (V U : Opens X) :
    V.isOpenEmbedding.functor.obj
      ((Opens.map V.inclusion').obj U ⊓ (closedSupportOnOpen Z V).compl) =
        (V ⊓ U) ⊓ Z.compl := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y.property, hy.1⟩, hy.2⟩
  · rintro ⟨⟨hv, hu⟩, hz⟩
    exact ⟨⟨x, hv⟩, ⟨hu, hz⟩, rfl⟩

def naiveRestrictGammaZSectionsEquiv (Z : Closeds X) (V U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZSections ((V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F)
      (closedSupportOnOpen Z V) ((Opens.map V.inclusion').obj U) ≃+
        gammaZSections F Z (V ⊓ U) := by
  let G := (V.isOpenEmbedding.sheafPullback AddCommGrpCat.{u}).obj F
  let a : G.presheaf.obj (op ((Opens.map V.inclusion').obj U)) ≅
      F.presheaf.obj (op (V ⊓ U)) :=
    F.presheaf.mapIso
      (eqToIso (congrArg op ((Opens.functor_map_eq_inf V U).trans (inf_comm U V))))
  let b : G.presheaf.obj (op
      ((Opens.map V.inclusion').obj U ⊓ (closedSupportOnOpen Z V).compl)) ≅
      F.presheaf.obj (op ((V ⊓ U) ⊓ Z.compl)) :=
    F.presheaf.mapIso (eqToIso (congrArg op (openImage_preimage_inter_closedCompl Z V U)))
  exact kerAddEquivOfCommSq
    (restrictToComplement G (closedSupportOnOpen Z V) ((Opens.map V.inclusion').obj U)).hom
    (restrictToComplement F Z (V ⊓ U)).hom
    a.addCommGroupIsoToAddEquiv b.addCommGroupIsoToAddEquiv (fun x => by
      change (G.presheaf.map (homOfLE inf_le_left).op ≫ b.hom) x =
        (a.hom ≫ F.presheaf.map (homOfLE inf_le_left).op) x
      apply ConcreteCategory.congr_hom
      change F.presheaf.map _ ≫ F.presheaf.map _ = F.presheaf.map _ ≫ F.presheaf.map _
      rw [← F.presheaf.map_comp, ← F.presheaf.map_comp]
      congr 1)

/-- Supported sections after actual restriction are ambient supported sections
on the intersection, for every ambient open. -/
def restrictToOpenGammaZSectionsEquiv (Z : Closeds X) (V U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    gammaZSections (restrictToOpen F V) (closedSupportOnOpen Z V)
      ((Opens.map V.inclusion').obj U) ≃+ gammaZSections F Z (V ⊓ U) :=
  (((gammaZSectionsFunctor (closedSupportOnOpen Z V) ((Opens.map V.inclusion').obj U)).mapIso
      ((V.isOpenEmbedding.sheafPullbackIso
        AddCommGrpCat.{u}).app F)).addCommGroupIsoToAddEquiv).trans
    (naiveRestrictGammaZSectionsEquiv Z V U F)

theorem restrictToOpenGammaZSectionsEquiv_val (Z : Closeds X) (V U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X)
    (s : gammaZSections (restrictToOpen F V) (closedSupportOnOpen Z V)
      ((Opens.map V.inclusion').obj U)) :
    (restrictToOpenGammaZSectionsEquiv Z V U F s).val =
      (((openRestrictionSectionsFunctorIso V).app F).hom.app (op U)) s.val := by
  change F.presheaf.map _
      (((V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app F).hom.app
        (op ((Opens.map V.inclusion').obj U)) s.val) =
    F.presheaf.map _
      (((V.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}).hom.app F).hom.app
        (op ((Opens.map V.inclusion').obj U)) s.val)
  congr 2
  exact congrArg F.presheaf.map (Subsingleton.elim _ _)

theorem restrictToOpenGammaZSectionsEquiv_naturality (Z : Closeds X) (V U : Opens X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (s : gammaZSections (restrictToOpen F V) (closedSupportOnOpen Z V)
      ((Opens.map V.inclusion').obj U)) :
    restrictToOpenGammaZSectionsEquiv Z V U G
        (gammaZSectionsMap ((iShriek_open V).map f) (closedSupportOnOpen Z V) _ s) =
      gammaZSectionsMap f Z (V ⊓ U) (restrictToOpenGammaZSectionsEquiv Z V U F s) := by
  apply Subtype.ext
  rw [restrictToOpenGammaZSectionsEquiv_val, gammaZSectionsMap_apply,
    gammaZSectionsMap_apply, restrictToOpenGammaZSectionsEquiv_val]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.app (op U))
      ((openRestrictionSectionsFunctorIso V).hom.naturality f)) s.val

theorem restrictToOpenGammaZSectionsEquiv_restrict (Z : Closeds X) (V : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) {U U' : Opens X} (i : U' ⟶ U)
    (s : gammaZSections (restrictToOpen F V) (closedSupportOnOpen Z V)
      ((Opens.map V.inclusion').obj U)) :
    restrictToOpenGammaZSectionsEquiv Z V U' F
        (gammaZSectionsRestriction (restrictToOpen F V) (closedSupportOnOpen Z V)
          ((Opens.map V.inclusion').map i) s) =
      gammaZSectionsRestriction F Z ((openIntersectionFunctor V).map i)
        (restrictToOpenGammaZSectionsEquiv Z V U F s) := by
  apply Subtype.ext
  rw [restrictToOpenGammaZSectionsEquiv_val]
  change _ = F.presheaf.map _ (restrictToOpenGammaZSectionsEquiv Z V U F s).val
  rw [restrictToOpenGammaZSectionsEquiv_val]
  exact ConcreteCategory.congr_hom
    (((openRestrictionSectionsFunctorIso V).app F).hom.naturality i.op) s.val

end SGA.SGA2.ExposeI
