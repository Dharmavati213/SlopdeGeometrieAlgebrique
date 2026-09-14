/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Split
import SGA.SGA1.ExposeVI.Fibered
import SGA.SGA1.ExposeVI.Cartesian
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# SGA 1, Exposé VI, VI.11: examples beyond the discrete base

* (a) Arrow category with target/source functors
* (b) Functors into a fixed category as a split fibered category over `Cat`
* (d) An equivalence of categories as cleavage data over a two-object groupoid
* (f) Walking-arrow base; prefiberedness from cartesian lifts of `arr`
* (g)/(c) Constant product via split fibered category
-/

universe v v₁ u u₁

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite

variable {E : Type u} [Category.{v} E] {C : Type u₁} [Category.{v₁} C]

/-! ### VI.11(a): arrow category -/

/-- VI.11(a): the target functor of the arrow category. -/
abbrev arrowTarget : Arrow E ⥤ E := Comma.snd (𝟭 E) (𝟭 E)

/-- VI.11(a): the source functor of the arrow category. -/
abbrev arrowSource : Arrow E ⥤ E := Comma.fst (𝟭 E) (𝟭 E)

/-- VI.11(a): an object of the fiber of `arrowTarget` over `S` is an arrow with target `S`. -/
theorem arrowTarget_fiber_obj (S : E) (x : Fiber (arrowTarget (E := E)) S) :
    x.val.right = S :=
  x.property

/-! ### VI.11(b): functor categories over `Cat` (equal Hom/object universes) -/

/-- VI.11(b): `U ↦ (U ⥤ C)` as a contravariant functor `Catᵒᵖ ⥤ Cat`. -/
def functorValued (C : Type u) [Category.{u} C] : Cat.{u, u}ᵒᵖ ⥤ Cat.{u, u} where
  obj U := Cat.of (U.unop ⥤ C)
  map {U V} F :=
    CategoryTheory.Functor.toCatHom
      ((whiskeringLeft (V.unop : Type u) (U.unop : Type u) C).obj F.unop.toFunctor)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- VI.11(b): the associated split fibered category over `Cat` (SGA's `Cat_{//C}`). -/
abbrev catOverCat (C : Type u) [Category.{u} C] := SplitFibered (functorValued C)

/-- VI.11(b): projection `Cat_{//C} → Cat`. -/
abbrev catOverCatForget (C : Type u) [Category.{u} C] : catOverCat C ⥤ Cat.{u, u} :=
  SplitFibered.forget (functorValued C)

theorem catOverCat_isFibered (C : Type u) [Category.{u} C] :
    IsFibered (catOverCatForget C) :=
  SplitFibered.forget_isFibered _

instance (C : Type u) [Category.{u} C] : IsFibered (catOverCatForget C) :=
  catOverCat_isFibered C

/-! ### VI.11(g): product via constant split fibered category -/

/-- VI.11(g): constant functor `Eᵒᵖ ⥤ Cat` with value `C`. -/
def constCat : Eᵒᵖ ⥤ Cat.{v₁, u₁} :=
  (Functor.const _).obj (Cat.of C)

/-- VI.11(g): the associated split fibered category. -/
abbrev productSplit := SplitFibered (constCat (E := E) (C := C))

/-- VI.11(g): projection to the base. -/
abbrev productSplitForget : productSplit (E := E) (C := C) ⥤ E :=
  SplitFibered.forget (constCat (E := E) (C := C))

/-- VI.11(g)/(c): the constant split category is fibered (product projection). -/
theorem productSplit_isFibered :
    IsFibered (productSplitForget (E := E) (C := C)) :=
  SplitFibered.forget_isFibered _

theorem productSplit_isPreFibered :
    IsPreFibered (productSplitForget (E := E) (C := C)) :=
  SplitFibered.forget_isPreFibered _

instance : IsFibered (productSplitForget (E := E) (C := C)) :=
  productSplit_isFibered

/-- VI.11(g): fibers are equivalent to `C`. -/
noncomputable def productSplit_fiberEquiv (S : E) :
    (constCat (E := E) (C := C)).obj (op S) ≌
      Fiber (productSplitForget (E := E) (C := C)) S :=
  SplitFibered.fiberEquiv (constCat (E := E) (C := C)) S

theorem productSplit_fiberCat_eq (S : E) :
    SplitFibered.fiberCat (constCat (E := E) (C := C)) S = Cat.of C := by
  change ((Functor.const _).obj (Cat.of C)).obj (op S) = Cat.of C
  rfl

/-! ### VI.11(d): equivalences over a two-object groupoid -/

/-- Base category for VI.11(d): two objects linked by inverse isomorphisms. -/
inductive EquivBase : Type
  | left
  | right

namespace EquivBase

inductive Hom : EquivBase → EquivBase → Type
  | id_left : Hom .left .left
  | id_right : Hom .right .right
  | toRight : Hom .left .right
  | toLeft : Hom .right .left

end EquivBase

instance : Category EquivBase where
  Hom := EquivBase.Hom
  id
    | .left => .id_left
    | .right => .id_right
  comp
    | .id_left, g => g
    | .id_right, g => g
    | .toRight, .id_right => .toRight
    | .toRight, .toLeft => .id_left
    | .toLeft, .id_left => .toLeft
    | .toLeft, .toRight => .id_right
  id_comp := by rintro _ _ ⟨⟩ <;> rfl
  comp_id := by rintro _ _ ⟨⟩ <;> rfl
  assoc := by rintro _ _ _ _ ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl

/-- VI.11(d): fiber assignment of an equivalence on `EquivBase`. -/
def equivalenceFiber {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B] (_e : A ≌ B) :
    EquivBase → Cat.{v₁, u₁}
  | .left => Cat.of A
  | .right => Cat.of B

/-- VI.11(d): inverse-image functors along arrows of `EquivBase`. -/
def equivalencePullback {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B] (e : A ≌ B) :
    ∀ {X Y : EquivBase}, (X ⟶ Y) → (equivalenceFiber e Y ⥤ equivalenceFiber e X)
  | _, _, .id_left => 𝟭 _
  | _, _, .id_right => 𝟭 _
  | _, _, .toRight => e.inverse
  | _, _, .toLeft => e.functor

/-- VI.11(d): transporting along `toLeft` recovers the forward functor of the equivalence. -/
theorem equivalencePullback_toLeft {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B]
    (e : A ≌ B) : equivalencePullback e EquivBase.Hom.toLeft = e.functor :=
  rfl

/-- VI.11(d): transporting along `toRight` recovers the inverse functor of the equivalence. -/
theorem equivalencePullback_toRight {A B : Type u₁} [Category.{v₁} A] [Category.{v₁} B]
    (e : A ≌ B) : equivalencePullback e EquivBase.Hom.toRight = e.inverse :=
  rfl

/-! ### VI.11(f): walking arrow -/

/-- Walking-arrow base: two objects and a single non-identity arrow `arr : src ⟶ tgt`. -/
inductive WalkingArr : Type
  | src
  | tgt

namespace WalkingArr

inductive Hom : WalkingArr → WalkingArr → Type
  | id_src : Hom .src .src
  | id_tgt : Hom .tgt .tgt
  | arr : Hom .src .tgt

end WalkingArr

instance : Category WalkingArr where
  Hom := WalkingArr.Hom
  id
    | .src => .id_src
    | .tgt => .id_tgt
  comp
    | .id_src, g => g
    | .id_tgt, g => g
    | .arr, .id_tgt => .arr
  id_comp := by rintro _ _ ⟨⟩ <;> rfl
  comp_id := by rintro _ _ ⟨⟩ <;> rfl
  assoc := by rintro _ _ _ _ ⟨⟩ ⟨⟩ ⟨⟩ <;> rfl

/-- VI.11(f): the unique non-identity arrow of the walking-arrow base. -/
abbrev walkingArrArrow : WalkingArr.src ⟶ WalkingArr.tgt := WalkingArr.Hom.arr

/-- VI.11(f): existence of a cartesian lift of `arr` at an object over `tgt`
(representability of `Hom_arr(-, ξ)` in the target variable, as in SGA). -/
def HasCartesianLiftOfArr {X : Type u₁} [Category.{v₁} X] (p : X ⥤ WalkingArr) (a : X) : Prop :=
  p.obj a = WalkingArr.tgt ∧ ∃ (b : X) (φ : b ⟶ a), IsCartesian p walkingArrArrow φ

/-- VI.11(f): the walking-arrow Hom-sets are exactly the three constructors. -/
theorem WalkingArr.hom_src_src (f : WalkingArr.src ⟶ WalkingArr.src) :
    f = WalkingArr.Hom.id_src := by cases f; rfl

theorem WalkingArr.hom_tgt_tgt (f : WalkingArr.tgt ⟶ WalkingArr.tgt) :
    f = WalkingArr.Hom.id_tgt := by cases f; rfl

theorem WalkingArr.hom_src_tgt (f : WalkingArr.src ⟶ WalkingArr.tgt) :
    f = WalkingArr.Hom.arr := by cases f; rfl


/-- VI.11(f): the identity on an object is a cartesian lift of the identity in the base. -/
theorem hasCartesianLift_id_walkingArr {X : Type u₁} [Category.{v₁} X] (p : X ⥤ WalkingArr)
    (a : X) : ∃ (b : X) (φ : b ⟶ a), IsCartesian p (𝟙 (p.obj a)) φ :=
  ⟨a, 𝟙 a, (vertical_isCartesian_iff_isIso (p := p) (𝟙 a)).mpr inferInstance⟩

/-- VI.11(f): cartesian lifts of `arr` at objects over `tgt` imply prefiberedness.
Identity arrows of the walking-arrow base lift by `hasCartesianLift_id_walkingArr`. -/
lemma WalkingArr.eq_src_or_tgt (x : WalkingArr) : x = .src ∨ x = .tgt := by
  cases x <;> simp

theorem isPreFibered_of_hasCartesianLiftOfArr {X : Type u₁} [Category.{v₁} X]
    (p : X ⥤ WalkingArr)
    (h : ∀ a, p.obj a = WalkingArr.tgt → HasCartesianLiftOfArr p a) :
    IsPreFibered p := by
  refine (isPreFibered_iff p).mpr ?_
  intro a R f
  rcases R with ⟨⟩ | ⟨⟩
  · rcases WalkingArr.eq_src_or_tgt (p.obj a) with ha | ha
    · revert f
      rw [ha]
      intro f
      have hf := WalkingArr.hom_src_src f
      cases hf
      obtain ⟨b, φ, hφ⟩ := hasCartesianLift_id_walkingArr p a
      rw [ha] at hφ
      exact ⟨b, φ, hφ⟩
    · revert f
      rw [ha]
      intro f
      have hf := WalkingArr.hom_src_tgt f
      cases hf
      obtain ⟨_, ⟨b, φ, hφ⟩⟩ := h a ha
      exact ⟨b, φ, hφ⟩
  · rcases WalkingArr.eq_src_or_tgt (p.obj a) with ha | ha
    · revert f
      rw [ha]
      intro f
      cases f
    · revert f
      rw [ha]
      intro f
      have hf := WalkingArr.hom_tgt_tgt f
      cases hf
      obtain ⟨b, φ, hφ⟩ := hasCartesianLift_id_walkingArr p a
      rw [ha] at hφ
      exact ⟨b, φ, hφ⟩


end SGA.SGA1.ExposeVI
