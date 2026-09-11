/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import SGA.SGA1.ExposeVI.Cartesian
import SGA.SGA1.ExposeVI.Fibered

/-!
# SGA 1, Exposé VI, VI.10: cofibered and bifibered categories

Cocartesian morphisms are mathlib's `IsCocartesian`. Prefibered / fibered
in the opposite direction are `IsPreCofibered` / `IsCofibered`. A category
that is both fibered and cofibered is `IsBifibered`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Category IsHomLift

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]
  (p : C ⥤ E)

/-- VI.10, co-Fib I: direct images exist for every base arrow and source object. -/
class IsPreCofibered (p : C ⥤ E) : Prop where
  exists_isCocartesian' {a : C} {S : E} (f : p.obj a ⟶ S) :
    ∃ (b : C) (φ : a ⟶ b), IsCocartesian p f φ

/-- Version of `exists_isCocartesian'` usable with non-definitional equalities. -/
protected lemma IsPreCofibered.exists_isCocartesian (p : C ⥤ E) [IsPreCofibered p]
    {a : C} {R S : E} (ha : p.obj a = R) (f : R ⟶ S) :
    ∃ (b : C) (φ : a ⟶ b), IsCocartesian p f φ := by
  subst ha
  exact IsPreCofibered.exists_isCocartesian' f

/-- VI.10, co-Fib II. -/
class IsCofibered (p : C ⥤ E) : Prop extends IsPreCofibered p where
  comp {R S T : E} (f : R ⟶ S) (g : S ⟶ T) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c)
    [IsCocartesian p f φ] [IsCocartesian p g ψ] :
    IsCocartesian p (f ≫ g) (φ ≫ ψ)

/-- VI.10: fibered and cofibered. -/
class IsBifibered (p : C ⥤ E) : Prop where
  [isFibered : IsFibered p]
  [isCofibered : IsCofibered p]

attribute [instance] IsBifibered.isFibered IsBifibered.isCofibered

instance (p : C ⥤ E) [IsFibered p] [IsCofibered p] : IsBifibered p where

instance (p : C ⥤ E) [IsCofibered p] {R S T : E} (f : R ⟶ S) (g : S ⟶ T)
    {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) [IsCocartesian p f φ] [IsCocartesian p g ψ] :
    IsCocartesian p (f ≫ g) (φ ≫ ψ) :=
  IsCofibered.comp f g φ ψ

/-- VI.10, co-Fib I. -/
theorem isPreCofibered_iff : IsPreCofibered p ↔
    ∀ (a : C) (S : E) (f : p.obj a ⟶ S), ∃ (b : C) (φ : a ⟶ b), IsCocartesian p f φ :=
  ⟨fun _ _ _ f ↦ IsPreCofibered.exists_isCocartesian' f,
    fun h ↦ ⟨fun {a S} f ↦ h a S f⟩⟩

/-- VI.10, co-Fib II, under co-Fib I. -/
theorem isCofibered_iff_comp [IsPreCofibered p] : IsCofibered p ↔
    ∀ {R S T : E} (f : R ⟶ S) (g : S ⟶ T) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c),
      IsCocartesian p f φ → IsCocartesian p g ψ → IsCocartesian p (f ≫ g) (φ ≫ ψ) := by
  constructor
  · intro h R S T f g a b c φ ψ hφ hψ
    infer_instance
  · intro h
    refine { comp := ?_ }
    intro R S T f g a b c φ ψ hφ hψ
    exact h f g φ ψ hφ hψ

namespace IsPreCofibered

variable [IsPreCofibered p] {R S : E} {a : C} (ha : p.obj a = R) (f : R ⟶ S)

/-- Codomain of a chosen cocartesian lift of `f` starting at `a`. -/
noncomputable def pushforwardObj : C :=
  Classical.choose (IsPreCofibered.exists_isCocartesian p ha f)

/-- A chosen cocartesian lift of `f` starting at `a`. -/
noncomputable def pushforwardMap : a ⟶ pushforwardObj (p := p) ha f :=
  Classical.choose (Classical.choose_spec (IsPreCofibered.exists_isCocartesian p ha f))

instance pushforwardMap.IsCocartesian :
    IsCocartesian p f (pushforwardMap (p := p) ha f) :=
  Classical.choose_spec (Classical.choose_spec (IsPreCofibered.exists_isCocartesian p ha f))

lemma pushforwardObj_proj : p.obj (pushforwardObj (p := p) ha f) = S :=
  codomain_eq p f (pushforwardMap (p := p) ha f)

end IsPreCofibered

/-- VI.10: composition with a cocartesian arrow, restricted to vertical morphisms. -/
def verticalPrecomp {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsHomLift p f φ] (b' : C) : HomOver p (𝟙 S) b b' → HomOver p f a b' :=
  fun u ↦ ⟨φ ≫ u.val, by have := u.property; infer_instance⟩

/-- VI.10: a cocartesian arrow represents `Hom_f(a,-)` on the fiber over `S`. -/
noncomputable def cocartesianHomEquiv {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b)
    [IsCocartesian p f φ] (b' : C) : HomOver p (𝟙 S) b b' ≃ HomOver p f a b' where
  toFun := verticalPrecomp p f φ b'
  invFun u := by
    have := u.property
    exact ⟨IsCocartesian.map p f φ u.val, inferInstance⟩
  left_inv u := by
    have := u.property
    apply Subtype.ext
    exact (IsCocartesian.map_uniq p f φ (φ ≫ u.val) u.val rfl).symm
  right_inv u := by
    have := u.property
    apply Subtype.ext
    exact IsCocartesian.fac p f φ u.val

end SGA.SGA1.ExposeVI
