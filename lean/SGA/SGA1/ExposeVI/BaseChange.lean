/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.OverCategories
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# SGA 1, Exposé VI, §3: change of base

`BaseChange p L` is the strict fiber product: objects have equal images in
the base and morphisms have equal images after transporting their endpoints.
This is the fiber product used in SGA, not an iso-comma category.

We construct its projections, universal lifting functor, and change of
base on based functors and transformations. The ordinary slice-category
adjunction and preservation of limits are supplied using `Over.pullback`.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} {C : Type u₁} {D : Type u₂}
  [Category.{v} E] [Category.{v₁} C] [Category.{v₂} D]

/-- VI.3: the objects of the strict fiber product `C ×_E D`. -/
def BaseChange (p : C ⥤ E) (L : D ⥤ E) := {x : C × D // p.obj x.1 = L.obj x.2}

namespace BaseChange

variable {p : C ⥤ E} {L : D ⥤ E}

/-- VI.3: morphisms are pairs with the same image in the base. -/
@[ext] structure Hom (x y : BaseChange p L) where
  left : x.val.1 ⟶ y.val.1
  right : x.val.2 ⟶ y.val.2
  over : IsHomLift p (L.map right) left

instance : Category (BaseChange p L) where
  Hom := Hom
  id x := ⟨𝟙 x.val.1, 𝟙 x.val.2, by
    rw [L.map_id]
    exact IsHomLift.id x.property⟩
  comp f g := ⟨f.left ≫ g.left, f.right ≫ g.right, by
    have := f.over
    have := g.over
    rw [L.map_comp]
    infer_instance⟩
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Category.assoc]

/-- VI.3: the first projection of the strict fiber product. -/
def fst (p : C ⥤ E) (L : D ⥤ E) : BaseChange p L ⥤ C where
  obj x := x.val.1
  map f := f.left

/-- VI.3: the second projection, used as the new structure functor. -/
def snd (p : C ⥤ E) (L : D ⥤ E) : BaseChange p L ⥤ D where
  obj x := x.val.2
  map f := f.right

/-- The two projections commute with the structure functors. -/
def projectionIso (p : C ⥤ E) (L : D ⥤ E) : fst p L ⋙ p ≅ snd p L ⋙ L :=
  NatIso.ofComponents (fun x ↦ eqToIso x.property) (fun {x y} f ↦ by
    have := f.over
    exact (IsHomLift.commSq p (L.map f.right) f.left).w)

/-- VI.3: commutation here is equality of functors, not just an isomorphism. -/
theorem condition (p : C ⥤ E) (L : D ⥤ E) : fst p L ⋙ p = snd p L ⋙ L :=
  Functor.ext_of_iso (projectionIso p L) (fun x ↦ x.property)

variable {A : Type u₃} [Category.{v₃} A]

/-- VI.3: the functor to the fiber product induced by a commuting pair. -/
def lift (F : A ⥤ C) (G : A ⥤ D) (h : F ⋙ p = G ⋙ L) : A ⥤ BaseChange p L where
  obj a := ⟨(F.obj a, G.obj a), Functor.congr_obj h a⟩
  map {a b} f := ⟨F.map f, G.map f,
    IsHomLift.of_commsq p _ _ (Functor.congr_obj h a) (Functor.congr_obj h b)
      (by simpa using (eqToIso h).hom.naturality f)⟩

@[simp] theorem lift_fst (F : A ⥤ C) (G : A ⥤ D) (h : F ⋙ p = G ⋙ L) :
    lift F G h ⋙ fst p L = F := rfl

@[simp] theorem lift_snd (F : A ⥤ C) (G : A ⥤ D) (h : F ⋙ p = G ⋙ L) :
    lift F G h ⋙ snd p L = G := rfl

/-- VI.3: a functor to the fiber product is recovered from its projections. -/
theorem lift_projections (H : A ⥤ BaseChange p L) :
    lift (H ⋙ fst p L) (H ⋙ snd p L)
      (by rw [Functor.assoc, condition, ← Functor.assoc]) = H := rfl

/-- VI.3: the universal bijection on functors into a fiber product. -/
def functorEquiv (p : C ⥤ E) (L : D ⥤ E) :
    (A ⥤ BaseChange p L) ≃ {FG : (A ⥤ C) × (A ⥤ D) // FG.1 ⋙ p = FG.2 ⋙ L} where
  toFun H := ⟨(H ⋙ fst p L, H ⋙ snd p L), by
    rw [Functor.assoc, condition, ← Functor.assoc]⟩
  invFun FG := lift FG.val.1 FG.val.2 FG.property
  left_inv := lift_projections
  right_inv FG := by cases FG; rfl

/-- VI.3: natural transformations to the fiber product are precisely compatible
pairs of natural transformations. This is the morphism part of the universal property. -/
def natTransEquiv (H K : A ⥤ BaseChange p L) :
    (H ⟶ K) ≃ {αβ : (H ⋙ fst p L ⟶ K ⋙ fst p L) × (H ⋙ snd p L ⟶ K ⋙ snd p L) //
      ∀ a, IsHomLift p (L.map (αβ.2.app a)) (αβ.1.app a)} where
  toFun τ := ⟨(whiskerRight τ (fst p L), whiskerRight τ (snd p L)),
    fun a ↦ (τ.app a).over⟩
  invFun αβ :=
    { app := fun a ↦ ⟨αβ.val.1.app a, αβ.val.2.app a, αβ.property a⟩
      naturality := fun {_ _} f ↦ Hom.ext (αβ.val.1.naturality f) (αβ.val.2.naturality f) }
  left_inv τ := by
    apply NatTrans.ext
    funext a
    rfl
  right_inv αβ := by rcases αβ with ⟨⟨α, β⟩, h⟩; rfl

end BaseChange

/-- VI.3: a based category after change of base along `L`. -/
abbrev changeOfBase (X : BasedCategory.{v₁, u₁} E) (L : D ⥤ E) : BasedCategory D :=
  BasedCategory.ofFunctor (BaseChange.snd X.p L)

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₃, u₃} E}

/-- VI.3: change of base of an `E`-functor. -/
def changeOfBaseMap (F : BasedFunctor X Y) (L : D ⥤ E) :
    BasedFunctor (changeOfBase X L) (changeOfBase Y L) where
  obj x := ⟨(F.obj x.val.1, x.val.2), (F.w_obj x.val.1).trans x.property⟩
  map f := ⟨F.map f.left, f.right, by
    have := f.over
    exact BasedFunctor.preserves_isHomLift F _ _⟩
  map_id x := by
    apply BaseChange.Hom.ext
    · exact F.map_id x.val.1
    · rfl
  map_comp f g := by
    apply BaseChange.Hom.ext
    · exact F.map_comp f.left g.left
    · rfl

/-- VI.3: base change sends a component `α(x)` to `(α(x), id)`. -/
def changeOfBaseNatTrans {F G : BasedFunctor X Y} (α : F ⟶ G) (L : D ⥤ E) :
    changeOfBaseMap F L ⟶ changeOfBaseMap G L where
  app x := ⟨α.app x.val.1, 𝟙 x.val.2, by
    change IsHomLift Y.p (L.map (𝟙 x.val.2)) (α.app x.val.1)
    rw [L.map_id]
    exact α.isHomLift x.property⟩
  naturality {x y} f := by
    apply BaseChange.Hom.ext
    · exact α.naturality f.left
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right
      simp
  isHomLift' x := by
    change IsHomLift (BaseChange.snd Y.p L) (𝟙 x.val.2) _
    apply IsHomLift.of_fac' _ _ _ rfl rfl
    change 𝟙 x.val.2 = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp

/-- VI.3: change of base is a functor between categories of based functors. -/
def changeOfBaseHom (L : D ⥤ E) :
    BasedFunctor X Y ⥤ BasedFunctor (changeOfBase X L) (changeOfBase Y L) where
  obj F := changeOfBaseMap F L
  map α := changeOfBaseNatTrans α L
  map_id F := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    rfl
  map_comp α β := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    apply BaseChange.Hom.ext
    · rfl
    · change 𝟙 x.val.2 = 𝟙 x.val.2 ≫ 𝟙 x.val.2
      simp

section SmallCategories

open CategoryTheory.Limits

/-- VI.3: the change-of-base functor on the ordinary slice of small categories. -/
noncomputable def baseChangeOnOver {B B' : Cat.{u, u}} (L : B' ⥤ B) : Over B ⥤ Over B' :=
  Over.pullback L.toCatHom

/-- VI.3: restriction of the base is left adjoint to change of base. -/
noncomputable def baseChangeAdjunction {B B' : Cat.{u, u}} (L : B' ⥤ B) :
    Over.map L.toCatHom ⊣ baseChangeOnOver L := Over.mapPullbackAdj L.toCatHom

/-- VI.3: change of base commutes with small projective limits. -/
theorem baseChange_preservesLimits {B B' : Cat.{u, u}} (L : B' ⥤ B) :
    PreservesLimitsOfSize.{u, u} (baseChangeOnOver L) :=
  (baseChangeAdjunction L).rightAdjoint_preservesLimits

/-- VI.3: change of base along the identity is naturally isomorphic to the identity. -/
noncomputable def baseChangeIdentity (B : Cat.{u, u}) :
    baseChangeOnOver (𝟭 B) ≅ 𝟭 (Over B) := Over.pullbackId

/-- VI.3: transitivity of change of base on the slice of small categories. -/
noncomputable def baseChangeComposition {B B' B'' : Cat.{u, u}}
    (L : B' ⥤ B) (K : B'' ⥤ B') :
    baseChangeOnOver (K ⋙ L) ≅ baseChangeOnOver L ⋙ baseChangeOnOver K :=
  Over.pullbackComp K.toCatHom L.toCatHom

end SmallCategories

end SGA.SGA1.ExposeVI
