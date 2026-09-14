/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InternalHom
import SGA.SGA2.ExposeI.OpenSupportCohomology
import Mathlib.CategoryTheory.HomCongr

/-! # Internal Hom and actual restriction to open subspaces -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Actual open pullback agrees with the restriction used by slice sites. -/
def openPullbackSheafRestrictIso (U : Opens X) :
    iShriek_open U ≅ U.sheafRestrict (C := AddCommGrpCat.{u}) :=
  U.isOpenEmbedding.sheafPullbackIso AddCommGrpCat.{u}

/-- The slice-site equivalence preserves addition of local morphisms. -/
def sheafEquivOverHomAddEquiv (U : Opens X)
    (F G : CategoryTheory.Sheaf ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u}) :
    (F ⟶ G) ≃+
      ((U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.obj F ⟶
        (U.sheafEquivOver (A := AddCommGrpCat.{u})).functor.obj G) where
  toEquiv := (U.sheafEquivOver (A := AddCommGrpCat.{u})).fullyFaithfulFunctor.homEquiv
  map_add' _ _ := rfl

/-- The additive change of source and target along actual sheaf isomorphisms. -/
def sheafHomAddCongr {Y : TopCat.{u}} {F F' G G' : Sheaf AddCommGrpCat.{u} Y}
    (eF : F ≅ F') (eG : G ≅ G') : (F ⟶ G) ≃+ (F' ⟶ G') where
  toEquiv := Iso.homCongr eF eG
  map_add' _ _ := by simp [Iso.homCongr, Preadditive.comp_add, Preadditive.add_comp]

/-- Internal Hom sections on an open are genuine morphisms between the
ordinary pullbacks of the two coefficient sheaves to that open. -/
def internalHomSectionsRestrictEquiv (U : Opens X) (F G : Sheaf AddCommGrpCat.{u} X) :
    (abelianSheafHom (Opens.grothendieckTopology X) F G).obj.obj (op U) ≃+
      (restrictToOpen F U ⟶ restrictToOpen G U) :=
  (abelianSheafHomSectionsOverEquiv (Opens.grothendieckTopology X) F G U).trans
    ((sheafEquivOverHomAddEquiv U _ _).trans
      (sheafHomAddCongr ((openPullbackSheafRestrictIso U).app F).symm
        ((openPullbackSheafRestrictIso U).app G).symm))

/-- The intermediate identification with the naive restriction used by sites. -/
def internalHomSectionsNaiveEquiv (U : Opens X) (F G : Sheaf AddCommGrpCat.{u} X) :
    (abelianSheafHom (Opens.grothendieckTopology X) F G).obj.obj (op U) ≃+
      (U.sheafRestrict.obj F ⟶ U.sheafRestrict.obj G) :=
  (abelianSheafHomSectionsOverEquiv (Opens.grothendieckTopology X) F G U).trans
    (sheafEquivOverHomAddEquiv U _ _)

theorem internalHomSectionsNaiveEquiv_naturality (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) {G G' : Sheaf AddCommGrpCat.{u} X}
    (f : G ⟶ G')
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) F G).obj.obj (op U)) :
    internalHomSectionsNaiveEquiv U F G'
        ((abelianSheafHomMap (Opens.grothendieckTopology X) F f).hom.app (op U) φ) =
      internalHomSectionsNaiveEquiv U F G φ ≫ U.sheafRestrict.map f := rfl

/-- Explicitly, the actual restriction comparison conjugates the naive local
morphism by the actual pullback/restriction isomorphisms. -/
theorem internalHomSectionsRestrictEquiv_apply (U : Opens X)
    (F G : Sheaf AddCommGrpCat.{u} X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) F G).obj.obj (op U)) :
    internalHomSectionsRestrictEquiv U F G φ =
      ((openPullbackSheafRestrictIso U).app F).hom ≫
        internalHomSectionsNaiveEquiv U F G φ ≫
          ((openPullbackSheafRestrictIso U).app G).inv := rfl

/-- The local internal-Hom comparison respects actual coefficient maps. -/
theorem internalHomSectionsRestrictEquiv_naturality (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) {G G' : Sheaf AddCommGrpCat.{u} X}
    (f : G ⟶ G')
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) F G).obj.obj (op U)) :
    internalHomSectionsRestrictEquiv U F G'
        ((abelianSheafHomMap (Opens.grothendieckTopology X) F f).hom.app (op U) φ) =
      internalHomSectionsRestrictEquiv U F G φ ≫ (iShriek_open U).map f := by
  rw [internalHomSectionsRestrictEquiv_apply, internalHomSectionsNaiveEquiv_naturality,
    internalHomSectionsRestrictEquiv_apply]
  simp only [Category.assoc]
  erw [(openPullbackSheafRestrictIso U).inv.naturality f]
  rfl

/-- Internal Hom evaluated on an open is naturally Hom out of the actual
restriction of its first argument. -/
def internalHomSectionsRestrictionFunctorIso (U : Opens X)
    (F : Sheaf AddCommGrpCat.{u} X) :
    abelianSheafHomFunctor (Opens.grothendieckTopology X) F ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op U) ≅
        iShriek_open U ⋙ preadditiveCoyoneda.obj (op (restrictToOpen F U)) :=
  NatIso.ofComponents (fun G ↦ (internalHomSectionsRestrictEquiv U F G).toAddCommGrpIso)
    (fun f ↦ by
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro φ
      exact internalHomSectionsRestrictEquiv_naturality U F f φ)

end SGA.SGA2.ExposeI
