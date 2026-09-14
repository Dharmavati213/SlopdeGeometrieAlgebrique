/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InternalHomIntersection

/-! # Actual first-variable maps of internal Hom -/

noncomputable section
universe u
open CategoryTheory Limits Opposite TopologicalSpace TopCat

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

section Site
variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  {A B D : CategoryTheory.Sheaf J AddCommGrpCat.{u}}

/-- Precomposition by an actual sheaf map, acting on local morphisms. -/
def abelianSheafHomPrecomp (f : A ⟶ B) :
    abelianSheafHomFunctor J B ⟶ abelianSheafHomFunctor J A where
  app F :=
    { hom :=
        { app U := AddCommGrpCat.ofHom
            { toFun φ := Functor.whiskerLeft (Over.forget U.unop).op f.hom ≫ φ
              map_zero' := by simp
              map_add' _ _ := by simp only [Preadditive.comp_add] }
          naturality {_ _} _ := by
            apply AddCommGrpCat.hom_ext
            apply AddMonoidHom.ext
            intro φ
            rfl } }
  naturality {_ _} g := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    change Functor.whiskerLeft (Over.forget U.unop).op f.hom ≫
        (φ ≫ Functor.whiskerLeft (Over.forget U.unop).op g.hom) =
      (Functor.whiskerLeft (Over.forget U.unop).op f.hom ≫ φ) ≫
        Functor.whiskerLeft (Over.forget U.unop).op g.hom
    exact (Category.assoc _ _ _).symm

theorem abelianSheafHomPrecomp_comp (f : A ⟶ B) (g : B ⟶ D) :
    abelianSheafHomPrecomp J (f ≫ g) =
      abelianSheafHomPrecomp J g ≫ abelianSheafHomPrecomp J f := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change (Functor.whiskerLeft (Over.forget U.unop).op f.hom ≫
    Functor.whiskerLeft (Over.forget U.unop).op g.hom) ≫ φ = _
  exact Category.assoc _ _ _

theorem abelianSheafHomPrecomp_zero :
    abelianSheafHomPrecomp J (0 : A ⟶ B) = 0 := by
  apply NatTrans.ext
  funext F
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro φ
  change (0 : (Over.forget U.unop).op ⋙ A.obj ⟶ _) ≫ φ = 0
  exact zero_comp

end Site

/-- The genuine intersection-Hom equivalence is contravariantly natural in
the first sheaf, with actual precomposition on both sides. -/
theorem internalHomIntersectionEquiv_precomp {X : TopCat.{u}}
    {A B : Sheaf AddCommGrpCat.{u} X} (f : A ⟶ B)
    (F : Sheaf AddCommGrpCat.{u} X) (U : Opens X)
    (φ : (abelianSheafHom (Opens.grothendieckTopology X) B F).obj.obj (op U)) :
    internalHomIntersectionEquiv A F U
        (((abelianSheafHomPrecomp (Opens.grothendieckTopology X) f).app F).hom.app
          (op U) φ) =
      f ≫ internalHomIntersectionEquiv B F U φ := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  change A.obj.map _ ≫ (f.hom.app _ ≫ φ.app _) =
    f.hom.app V ≫ (B.obj.map _ ≫ φ.app _)
  rw [← Category.assoc, f.hom.naturality, Category.assoc]

end SGA.SGA2.ExposeI
