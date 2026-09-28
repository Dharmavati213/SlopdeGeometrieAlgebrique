/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.TopologicalInternalHom
import SGA.SGA2.ExposeI.OpenSupportedSections

/-! # Local morphisms and genuine intersection sections

The sheaf with sections `F(V ∩ U)` is the ordinary restriction/direct image
of `F`. Local internal-Hom sections on `U` are global morphisms into this
sheaf, naturally both in `F` and in the ambient open `U`.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI
variable {X : TopCat.{u}}

def rightIntersectionFunctor (U : Opens X) : Opens X ⥤ Opens X where
  obj V := V ⊓ U
  map f := homOfLE (inf_le_inf_right U f.le)

def intersectionSectionsSheaf (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    Sheaf AddCommGrpCat.{u} X where
  obj := (rightIntersectionFunctor U).op ⋙ F.obj
  property := by
    let G := (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj
      (U.sheafRestrict.obj F)
    let e : G.obj ≅ (rightIntersectionFunctor U).op ⋙ F.obj :=
      NatIso.ofComponents (fun V =>
        F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U V.unop))))
        (fun f => by
          change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
          rw [← F.obj.map_comp, ← F.obj.map_comp]
          congr 1)
    exact (Presheaf.isSheaf_of_iso_iff e).mp G.property

/-- The intersection model is isomorphic to the actual naive restriction
followed by the actual direct image; its sheaf condition is not postulated. -/
def intersectionSectionsSheafIso (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj (U.sheafRestrict.obj F) ≅
      intersectionSectionsSheaf F U :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun V =>
      F.obj.mapIso (eqToIso (congrArg op (Opens.functor_map_eq_inf U V.unop))))
      (fun f => by
        change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
        rw [← F.obj.map_comp, ← F.obj.map_comp]
        congr 1))

/-- The same intersection sheaf computes the original sheaf pullback and
direct image, not only the naive restriction model. -/
def intersectionSectionsActualIso (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').obj (restrictToOpen F U) ≅
      intersectionSectionsSheaf F U :=
  (Sheaf.pushforward AddCommGrpCat.{u} U.inclusion').mapIso
      ((openPullbackSheafRestrictIso U).app F) ≪≫
    intersectionSectionsSheafIso F U

def intersectionSectionsSheafMap {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (U : Opens X) :
    intersectionSectionsSheaf F U ⟶ intersectionSectionsSheaf G U :=
  ⟨Functor.whiskerLeft (rightIntersectionFunctor U).op f.hom⟩

def intersectionSectionsSheafRestrict (F : Sheaf AddCommGrpCat.{u} X)
    {U U' : Opens X} (i : U' ⟶ U) :
    intersectionSectionsSheaf F U ⟶ intersectionSectionsSheaf F U' :=
  ⟨{ app V := F.obj.map (homOfLE (inf_le_inf_left V.unop i.le)).op
     naturality {_ _} f := by
       change F.obj.map _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map _
       rw [← F.obj.map_comp, ← F.obj.map_comp]
       congr 1 }⟩

def internalHomToIntersection (A F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) A F).obj.obj (op U)) :
    A ⟶ intersectionSectionsSheaf F U :=
  ⟨{ app V := A.obj.map (homOfLE inf_le_left).op ≫
       φ.app (op (Over.mk (homOfLE (inf_le_right : V.unop ⊓ U ≤ U))))
     naturality {V W} f := by
       change A.obj.map _ ≫ (A.obj.map _ ≫ φ.app _) =
         (A.obj.map _ ≫ φ.app _) ≫ F.obj.map _
       rw [← Category.assoc, ← A.obj.map_comp]
       have h := φ.naturality
         (Over.homMk (homOfLE (inf_le_inf_right U f.unop.le)) :
           Over.mk (homOfLE (inf_le_right : W.unop ⊓ U ≤ U)) ⟶
           Over.mk (homOfLE (inf_le_right : V.unop ⊓ U ≤ U))).op
       change A.obj.map ((rightIntersectionFunctor U).op.map f) ≫
         φ.app (op (Over.mk (homOfLE (inf_le_right : W.unop ⊓ U ≤ U)))) =
         φ.app (op (Over.mk (homOfLE (inf_le_right : V.unop ⊓ U ≤ U)))) ≫
           F.obj.map ((rightIntersectionFunctor U).op.map f) at h
       simp only [Category.assoc]
       rw [← h, ← Category.assoc, ← A.obj.map_comp]
       congr 1 }⟩

def intersectionToInternalHom (A F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (ψ : A ⟶ intersectionSectionsSheaf F U) :
    (abelianSheafHom (Opens.grothendieckTopology X) A F).obj.obj (op U) :=
  { app V := ψ.hom.app (op V.unop.left) ≫
      F.obj.map (homOfLE (le_inf le_rfl V.unop.hom.le)).op
    naturality {V W} f := by
      dsimp only [intersectionSectionsSheaf, Functor.comp_map, Functor.op_map]
      erw [← Category.assoc, ψ.hom.naturality f.unop.left.op]
      dsimp only [intersectionSectionsSheaf, Functor.comp_map, Functor.op_map]
      rw [Category.assoc, Category.assoc, ← F.obj.map_comp, ← F.obj.map_comp]
      congr 1 }

def internalHomIntersectionEquiv (A F : Sheaf AddCommGrpCat.{u} X) (U : Opens X) :
    (abelianSheafHom (Opens.grothendieckTopology X) A F).obj.obj (op U) ≃+
      (A ⟶ intersectionSectionsSheaf F U) where
  toFun := internalHomToIntersection A F U
  invFun := intersectionToInternalHom A F U
  left_inv φ := by
    apply NatTrans.ext
    funext V
    change (A.obj.map _ ≫ φ.app _) ≫ F.obj.map _ = φ.app V
    have h := φ.naturality
      (Over.homMk (homOfLE (le_inf le_rfl V.unop.hom.le)) :
        V.unop ⟶ Over.mk (homOfLE (inf_le_right : V.unop.left ⊓ U ≤ U))).op
    dsimp at h
    erw [Category.assoc, ← h, ← Category.assoc, ← A.obj.map_comp]
    have hId : (homOfLE (inf_le_left : V.unop.left ⊓ U ≤ V.unop.left)).op ≫
        (homOfLE (le_inf le_rfl V.unop.hom.le)).op = 𝟙 (op V.unop.left) :=
      Subsingleton.elim _ _
    erw [hId, A.obj.map_id, Category.id_comp]
  right_inv ψ := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change A.obj.map _ ≫ (ψ.hom.app _ ≫ F.obj.map _) = ψ.hom.app V
    rw [← Category.assoc, ψ.hom.naturality]
    dsimp only [intersectionSectionsSheaf, Functor.comp_map, Functor.op_map]
    rw [Category.assoc, ← F.obj.map_comp]
    have h : ((rightIntersectionFunctor U).map
        (homOfLE (inf_le_left : V.unop ⊓ U ≤ V.unop))).op ≫
        (homOfLE (le_inf le_rfl (inf_le_right : V.unop ⊓ U ≤ U))).op =
          𝟙 (op (V.unop ⊓ U)) := Subsingleton.elim _ _
    erw [h, F.obj.map_id, Category.comp_id]
  map_add' φ ψ := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    apply Preadditive.comp_add

theorem internalHomIntersectionEquiv_naturality (A : Sheaf AddCommGrpCat.{u} X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G) (U : Opens X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) A F).obj.obj (op U)) :
    internalHomIntersectionEquiv A G U
        ((abelianSheafHomMap (Opens.grothendieckTopology X) A f).hom.app (op U) φ) =
      internalHomIntersectionEquiv A F U φ ≫ intersectionSectionsSheafMap f U := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  exact (Category.assoc _ _ _).symm

theorem internalHomIntersectionEquiv_restrict (A F : Sheaf AddCommGrpCat.{u} X)
    {U U' : Opens X} (i : U' ⟶ U)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) A F).obj.obj (op U)) :
    internalHomIntersectionEquiv A F U'
        ((abelianSheafHom (Opens.grothendieckTopology X) A F).obj.map i.op φ) =
      internalHomIntersectionEquiv A F U φ ≫ intersectionSectionsSheafRestrict F i := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change A.obj.map _ ≫ φ.app _ = (A.obj.map _ ≫ φ.app _) ≫ F.obj.map _
  have h := φ.naturality
    (Over.homMk (homOfLE (inf_le_inf_left V.unop i.le)) :
      Over.mk (homOfLE (inf_le_right.trans i.le : V.unop ⊓ U' ≤ U)) ⟶
      Over.mk (homOfLE (inf_le_right : V.unop ⊓ U ≤ U))).op
  dsimp at h
  erw [Category.assoc, ← h, ← Category.assoc, ← A.obj.map_comp]
  congr 1

end SGA.SGA2.ExposeI
