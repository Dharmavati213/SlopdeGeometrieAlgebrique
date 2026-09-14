/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Category.FGModuleCat.Abelian
import Mathlib.CategoryTheory.Linear.Yoneda
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Canonical modules associated to additive functors

The scalar action in the opening of SGA 2, Exposé IV is induced by scalar
endomorphisms in the source category. No linearity of the original abelian-group
valued functor is assumed. Its maps become linear for this canonical action.
-/

noncomputable section

universe u v w

open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]
variable {C : Type v} [Category.{w} C] [Preadditive C] [Linear R C]

/-- The opposite category retains the scalar action on its morphisms. -/
instance oppositeLinear : Linear R Cᵒᵖ where
  homModule M N :=
    ({ opEquiv M N with map_add' := fun _ _ ↦ rfl } :
      (M ⟶ N) ≃+ (N.unop ⟶ M.unop)).module R
  smul_comp M N P r f g := by
    apply Quiver.Hom.unop_inj
    exact Linear.comp_smul _ _ _ _ _ _
  comp_smul M N P f r g := by
    apply Quiver.Hom.unop_inj
    exact Linear.smul_comp _ _ _ _ _ _

@[simp] theorem oppositeLinear_op_smul {M N : C} (r : R) (f : M ⟶ N) :
    (r • f).op = r • f.op := rfl

/-- The canonical scalar action is the image of scalar multiplication on the
source object. This also applies to a contravariant functor by taking `Cᵒᵖ`. -/
@[instance_reducible] def additiveFunctorModule (T : C ⥤ AddCommGrpCat.{u})
    [T.Additive] (M : C) :
    Module R (T.obj M) where
  smul r x := T.map (r • 𝟙 M) x
  one_smul x := by
    change T.map ((1 : R) • 𝟙 M) x = x
    simp
  mul_smul r s x := by
    change T.map ((r * s) • 𝟙 M) x =
      (T.map (s • 𝟙 M) ≫ T.map (r • 𝟙 M)) x
    rw [← T.map_comp]
    simp [smul_smul]
  smul_zero r := map_zero _
  smul_add r x y := map_add _ x y
  add_smul r s x := by
    change T.map ((r + s) • 𝟙 M) x = T.map (r • 𝟙 M) x + T.map (s • 𝟙 M) x
    simp [add_smul]
  zero_smul x := by
    change T.map ((0 : R) • 𝟙 M) x = 0
    simp

attribute [local instance] additiveFunctorModule

/-- Functorial maps respect the canonical scalar actions. -/
theorem additiveFunctor_map_smul (T : C ⥤ AddCommGrpCat.{u}) [T.Additive]
    {M N : C} (f : M ⟶ N) (r : R) (x : T.obj M) :
    T.map f (r • x) = r • T.map f x := by
  change (T.map (r • 𝟙 M) ≫ T.map f) x =
    (T.map f ≫ T.map (r • 𝟙 N)) x
  rw [← T.map_comp, ← T.map_comp]
  simp

/-- The canonical factorization of an additive functor through modules. -/
def additiveFunctorModuleLift (T : C ⥤ AddCommGrpCat.{u}) [T.Additive] :
    C ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (T.obj M)
  map f := ModuleCat.ofHom
    { (T.map f).hom with map_smul' := additiveFunctor_map_smul T f }
  map_id M := by ext x; exact ConcreteCategory.congr_hom (T.map_id M) x
  map_comp f g := by ext x; exact ConcreteCategory.congr_hom (T.map_comp f g) x

instance (T : C ⥤ AddCommGrpCat.{u}) [T.Additive] :
    (additiveFunctorModuleLift (R := R) T).Additive where
  map_add {X Y} f g := by
    ext x
    exact ConcreteCategory.congr_hom (T.map_add (f := f) (g := g)) x

/-- Forgetting the canonical module structure gives back the original functor. -/
def additiveFunctorModuleLiftForgetIso (T : C ⥤ AddCommGrpCat.{u}) [T.Additive] :
    additiveFunctorModuleLift (R := R) T ⋙ forget₂ (ModuleCat R) AddCommGrpCat ≅ T :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

instance (T : C ⥤ AddCommGrpCat.{u}) [T.Additive] :
    (additiveFunctorModuleLift (R := R) T).Linear R where
  map_smul f r := by
    ext x
    change T.map (r • f) x = (T.map f ≫ T.map (r • 𝟙 _)) x
    rw [← T.map_comp]
    simp

end SGA.SGA2.ExposeIV
