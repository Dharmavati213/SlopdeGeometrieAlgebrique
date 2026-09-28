/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSections
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.Topology.Sheaves.Over
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits

/-!
# Internal Hom for abelian sheaves

The internal Hom is the genuine sheaf of local morphisms, with its pointwise
abelian-group structure. Its sheaf condition is inherited from the proved
sheaf condition for local morphisms, rather than imposed as an assumption.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- The presheaf of local morphisms, with its natural additive structure. -/
def abelianPresheafHom (F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of ((Over.forget U.unop).op ⋙ F ⟶ (Over.forget U.unop).op ⋙ G)
  map f := AddCommGrpCat.ofHom
    { toFun := Functor.whiskerLeft (Over.map f.unop).op
      map_zero' := rfl
      map_add' _ _ := rfl }
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    exact ConcreteCategory.congr_hom ((presheafHom F G).map_id U) φ
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    exact ConcreteCategory.congr_hom ((presheafHom F G).map_comp f g) φ

/-- Forgetting addition recovers mathlib's presheaf of local morphisms. -/
def abelianPresheafHomForgetIso (F G : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    abelianPresheafHom F G ⋙ forget AddCommGrpCat.{u} ≅ presheafHom F G :=
  Iso.refl _

/-- The actual local-morphism presheaf is an abelian sheaf when the target is
a sheaf. No sheafification changes its local morphisms. -/
def abelianSheafHom (F G : CategoryTheory.Sheaf J AddCommGrpCat.{u}) :
    CategoryTheory.Sheaf J AddCommGrpCat.{u} where
  obj := abelianPresheafHom F.obj G.obj
  property := (Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat.{u})).mpr
    ((Presheaf.isSheaf_of_iso_iff (abelianPresheafHomForgetIso F.obj G.obj)).mpr
      (G.property.hom F.obj))

/-- Local sections are morphisms of the actual sheaves on the slice site. -/
def abelianSheafHomSectionsOverEquiv (F G : CategoryTheory.Sheaf J AddCommGrpCat.{u})
    (U : C) :
    (abelianSheafHom J F G).obj.obj (op U) ≃+
      ((J.overPullback AddCommGrpCat.{u} U).obj F ⟶
        (J.overPullback AddCommGrpCat.{u} U).obj G) where
  toFun φ := ⟨φ⟩
  invFun φ := φ.hom
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Postcomposition gives the actual coefficient map of internal Hom. -/
def abelianSheafHomMap (F : CategoryTheory.Sheaf J AddCommGrpCat.{u})
    {G H : CategoryTheory.Sheaf J AddCommGrpCat.{u}} (f : G ⟶ H) :
    abelianSheafHom J F G ⟶ abelianSheafHom J F H where
  hom :=
    { app U := AddCommGrpCat.ofHom
        { toFun := fun φ ↦ φ ≫ Functor.whiskerLeft (Over.forget U.unop).op f.hom
          map_zero' := by simp
          map_add' _ _ := by simp only [Preadditive.add_comp] }
      naturality {U V} i := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro φ
        rfl }

/-- Internal Hom in a fixed first variable, as an additive coefficient functor. -/
def abelianSheafHomFunctor (F : CategoryTheory.Sheaf J AddCommGrpCat.{u}) :
    CategoryTheory.Sheaf J AddCommGrpCat.{u} ⥤ CategoryTheory.Sheaf J AddCommGrpCat.{u} where
  obj G := abelianSheafHom J F G
  map f := abelianSheafHomMap J F f
  map_id G := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change φ ≫ Functor.whiskerLeft (Over.forget U.unop).op (𝟙 G.obj) = φ
    simp
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change φ ≫ Functor.whiskerLeft (Over.forget U.unop).op (f ≫ g).hom =
      (φ ≫ Functor.whiskerLeft (Over.forget U.unop).op f.hom) ≫
        Functor.whiskerLeft (Over.forget U.unop).op g.hom
    simp [Category.assoc]

instance abelianSheafHomFunctor_additive (F : CategoryTheory.Sheaf J AddCommGrpCat.{u}) :
    (abelianSheafHomFunctor J F).Additive where
  map_add := by
    intro G H f g
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change φ ≫ (Functor.whiskerLeft (Over.forget U.unop).op f.hom +
      Functor.whiskerLeft (Over.forget U.unop).op g.hom) =
        (φ ≫ Functor.whiskerLeft (Over.forget U.unop).op f.hom) +
          (φ ≫ Functor.whiskerLeft (Over.forget U.unop).op g.hom)
    apply Preadditive.comp_add

/-- Local morphisms on `U` as a composite of actual restriction and Hom. -/
def localMorphismFunctor (F : CategoryTheory.Sheaf J AddCommGrpCat.{u}) (U : C) :
    CategoryTheory.Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
  sheafToPresheaf J AddCommGrpCat.{u} ⋙
    (Functor.whiskeringLeft (Over U)ᵒᵖ Cᵒᵖ AddCommGrpCat.{u}).obj (Over.forget U).op ⋙
      preadditiveCoyoneda.obj (op ((Over.forget U).op ⋙ F.obj))

/-- The internal Hom has exactly the local morphisms as sections. -/
def abelianSheafHomSectionsFunctorIso (F : CategoryTheory.Sheaf J AddCommGrpCat.{u})
    (U : C) :
    abelianSheafHomFunctor J F ⋙ sheafToPresheaf J AddCommGrpCat.{u} ⋙
      (evaluation Cᵒᵖ AddCommGrpCat.{u}).obj (op U) ≅ localMorphismFunctor J F U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by
    simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
    rfl)

/-- Internal Hom is left exact in its coefficient sheaf. -/
instance abelianSheafHomFunctor_preservesFiniteLimits
    (F : CategoryTheory.Sheaf J AddCommGrpCat.{u}) :
    PreservesFiniteLimits (abelianSheafHomFunctor J F) := by
  let P := sheafToPresheaf J AddCommGrpCat.{u}
  have : PreservesFiniteLimits (abelianSheafHomFunctor J F ⋙ P) :=
    preservesFiniteLimits_of_evaluation _ (fun U ↦ by
      have : PreservesFiniteLimits (localMorphismFunctor J F U.unop) := by
        dsimp [localMorphismFunctor]
        infer_instance
      exact preservesFiniteLimits_of_natIso (abelianSheafHomSectionsFunctorIso J F U.unop).symm)
  exact preservesFiniteLimits_of_reflects_of_preserves (abelianSheafHomFunctor J F) P

section Derived

variable [HasSheafify J AddCommGrpCat.{u}]
  [HasInjectiveResolutions (CategoryTheory.Sheaf J AddCommGrpCat.{u})]

/-- Actual sheaf Ext: right-derived internal Hom in its second variable. -/
def internalSheafExtFunctor (F : CategoryTheory.Sheaf J AddCommGrpCat.{u}) (n : ℕ) :
    CategoryTheory.Sheaf J AddCommGrpCat.{u} ⥤ CategoryTheory.Sheaf J AddCommGrpCat.{u} :=
  (abelianSheafHomFunctor J F).rightDerived n

/-- Degree zero of sheaf Ext is naturally the genuine internal Hom sheaf. -/
def internalSheafExtZeroIso (F : CategoryTheory.Sheaf J AddCommGrpCat.{u}) :
    internalSheafExtFunctor J F 0 ≅ abelianSheafHomFunctor J F :=
  (abelianSheafHomFunctor J F).rightDerivedZeroIsoSelf

/-- Positive sheaf Ext vanishes on actual injective coefficient sheaves. -/
theorem internalSheafExt_isZero_of_injective (F G : CategoryTheory.Sheaf J AddCommGrpCat.{u})
    [Injective G] (n : ℕ) : IsZero ((internalSheafExtFunctor J F (n + 1)).obj G) :=
  (abelianSheafHomFunctor J F).isZero_rightDerived_obj_injective_succ n G

end Derived

end SGA.SGA2.ExposeI
