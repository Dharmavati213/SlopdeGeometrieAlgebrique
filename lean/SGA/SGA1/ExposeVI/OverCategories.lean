/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.Products.Basic

/-!
# SGA 1, Exposé VI, §2: categories over a base

We use mathlib's `BasedCategory`, `BasedFunctor`, and `BasedNatTrans` for
categories over `E`, functors commuting strictly with the projections,
and natural transformations whose components lie over identities.
Mathlib already equips them with categories and a strict bicategory.

Here we spell out SGA's horizontal composition, equations I–IV, and
the composition and pre/postcomposition functors. The construction also
allows the three total categories to have different universe levels.
-/

universe v v₁ v₂ v₃ v₄ u u₁ u₂ u₃ u₄

namespace SGA.SGA1.ExposeVI

open CategoryTheory

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}
  {Z : BasedCategory.{v₃, u₃} E} {W : BasedCategory.{v₄, u₄} E}

/-- VI.2: SGA's `β * α`, a natural transformation over the base. -/
def horizontalComp {F F' : BasedFunctor X Y} {G G' : BasedFunctor Y Z}
    (α : F ⟶ F') (β : G ⟶ G') :
    BasedFunctor.comp F G ⟶ BasedFunctor.comp F' G' :=
  BasedCategory.whiskerRight α G ≫ BasedCategory.whiskerLeft F' β

/-- VI.2: the first componentwise formula for horizontal composition. -/
theorem horizontalComp_app {F F' : BasedFunctor X Y} {G G' : BasedFunctor Y Z}
    (α : F ⟶ F') (β : G ⟶ G') (x : X.obj) :
    (horizontalComp α β).app x = G.map (α.app x) ≫ β.app (F'.obj x) := rfl

/-- VI.2: the alternative componentwise formula, by naturality. -/
theorem horizontalComp_app' {F F' : BasedFunctor X Y} {G G' : BasedFunctor Y Z}
    (α : F ⟶ F') (β : G ⟶ G') (x : X.obj) :
    (horizontalComp α β).app x = β.app (F.obj x) ≫ G'.map (α.app x) :=
  β.naturality (α.app x)

/-- VI.2(I): horizontal composition preserves identities. -/
@[simp] theorem horizontalComp_id (F : BasedFunctor X Y) (G : BasedFunctor Y Z) :
    horizontalComp (𝟙 F) (𝟙 G) = 𝟙 (BasedFunctor.comp F G) := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change G.map (𝟙 (F.obj x)) ≫ 𝟙 _ = 𝟙 _
  simp

/-- VI.2(II): the interchange law for horizontal and vertical composition. -/
theorem horizontalComp_comp {F F' F'' : BasedFunctor X Y}
    {G G' G'' : BasedFunctor Y Z} (α : F ⟶ F') (α' : F' ⟶ F'')
    (β : G ⟶ G') (β' : G' ⟶ G'') :
    horizontalComp (α ≫ α') (β ≫ β') = horizontalComp α β ≫ horizontalComp α' β' := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change G.map (α.app x ≫ α'.app x) ≫ (β.app (F''.obj x) ≫ β'.app (F''.obj x)) =
    (G.map (α.app x) ≫ β.app (F'.obj x)) ≫
      (G'.map (α'.app x) ≫ β'.app (F''.obj x))
  simp only [Functor.map_comp, Category.assoc]
  rw [← β.naturality_assoc (α'.app x)]

/-- VI.2(III): associativity of horizontal composition. -/
theorem horizontalComp_assoc {F F' : BasedFunctor X Y} {G G' : BasedFunctor Y Z}
    {H H' : BasedFunctor Z W} (α : F ⟶ F') (β : G ⟶ G') (γ : H ⟶ H') :
    horizontalComp (horizontalComp α β) γ = horizontalComp α (horizontalComp β γ) := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change H.map (G.map (α.app x) ≫ β.app (F'.obj x)) ≫ γ.app (G'.obj (F'.obj x)) =
    H.map (G.map (α.app x)) ≫
      (H.map (β.app (F'.obj x)) ≫ γ.app (G'.obj (F'.obj x)))
  simp only [Functor.map_comp, Category.assoc]

/-- VI.2(IV): the identity of the base-side identity functor is a left unit. -/
@[simp] theorem horizontalComp_left_id {F F' : BasedFunctor X Y} (α : F ⟶ F') :
    horizontalComp (𝟙 (BasedFunctor.id X)) α = α := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change F.map (𝟙 x) ≫ α.app x = α.app x
  simp

/-- VI.2(IV): the identity of the target-side identity functor is a right unit. -/
@[simp] theorem horizontalComp_right_id {F F' : BasedFunctor X Y} (α : F ⟶ F') :
    horizontalComp α (𝟙 (BasedFunctor.id Y)) = α := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  change α.app x ≫ 𝟙 _ = α.app x
  simp

/-- VI.2(i): composition is a functor on the categories of based functors. -/
def basedComposition :
    (BasedFunctor X Y × BasedFunctor Y Z) ⥤ BasedFunctor X Z where
  obj FG := BasedFunctor.comp FG.1 FG.2
  map αβ := horizontalComp αβ.1 αβ.2
  map_id FG := horizontalComp_id FG.1 FG.2
  map_comp αβ αβ' := horizontalComp_comp αβ.1 αβ'.1 αβ.2 αβ'.2

/-- VI.2: precomposition by a based functor, SGA's `F*`. -/
def basedPrecomp (F : BasedFunctor X Y) : BasedFunctor Y Z ⥤ BasedFunctor X Z where
  obj G := BasedFunctor.comp F G
  map α := BasedCategory.whiskerLeft F α

/-- VI.2: postcomposition by a based functor, SGA's `G_*`. -/
def basedPostcomp (G : BasedFunctor Y Z) : BasedFunctor X Y ⥤ BasedFunctor X Z where
  obj F := BasedFunctor.comp F G
  map α := BasedCategory.whiskerRight α G

/-- VI.2: forgetting that natural transformations are over the base is faithful. -/
instance basedForgetful_faithful : (BasedNatTrans.forgetful X Y).Faithful where
  map_injective h := BasedNatTrans.ext _ _ h

end SGA.SGA1.ExposeVI
