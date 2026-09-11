/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# SGA 1, Exposé VI, VI.6.1 and VI.6.11–13

The two axioms of VI.6.1 are mathlib's `IsPreFibered` and `IsFibered`.
VI.6.11 identifies Fib II with the stronger universal property. We give
both an iff and the actual bijection of sets of arrows over base arrows.
The isomorphism criterion and cancellation are VI.6.12 and VI.6.13.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]
  (p : C ⥤ E)

/-- VI.6.1, Fib I: inverse images exist for every base arrow and target object. -/
theorem isPreFibered_iff : IsPreFibered p ↔
    ∀ (a : C) (R : E) (f : R ⟶ p.obj a), ∃ (b : C) (φ : b ⟶ a), IsCartesian p f φ :=
  ⟨fun _ _ _ f ↦ IsPreFibered.exists_isCartesian' f,
    fun h ↦ ⟨fun {a R} f ↦ h a R f⟩⟩

/-- VI.6.1, Fib II, under Fib I: cartesian arrows are closed under composition. -/
theorem isFibered_iff_comp [IsPreFibered p] : IsFibered p ↔
    ∀ {R S T : E} (f : R ⟶ S) (g : S ⟶ T) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c),
      IsCartesian p f φ → IsCartesian p g ψ → IsCartesian p (f ≫ g) (φ ≫ ψ) := by
  constructor
  · intro h R S T f g a b c φ ψ hφ hψ
    infer_instance
  · intro h
    refine { comp := ?_ }
    intro R S T f g a b c φ ψ hφ hψ
    exact h f g φ ψ hφ hψ

/-- VI.6.11: on a prefibered category, Fib II is equivalent to Fib II'. -/
theorem isFibered_iff_cartesian_isStronglyCartesian [IsPreFibered p] :
    IsFibered p ↔ ∀ {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b),
      IsCartesian p f φ → IsStronglyCartesian p f φ := by
  constructor
  · intro h R S f a b φ hφ
    infer_instance
  · intro h
    apply IsFibered.of_exists_isStronglyCartesian
    intro a R f
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p) f
    exact ⟨b, φ, h f φ hφ⟩

/-- VI.6.1 and VI.6.11: the modern definition by strongly cartesian lifts
is equivalent to Grothendieck's two axioms. -/
theorem isFibered_iff_exists_stronglyCartesian : IsFibered p ↔
    ∀ (a : C) (R : E) (f : R ⟶ p.obj a),
      ∃ (b : C) (φ : b ⟶ a), IsStronglyCartesian p f φ := by
  constructor
  · intro h a R f
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p) f
    exact ⟨b, φ, inferInstance⟩
  · exact IsFibered.of_exists_isStronglyCartesian

/-- VI.6.11, Fib II': `Hom_g(c,a) ≃ Hom_{fg}(c,b)` by composition with
a cartesian arrow `φ : a ⟶ b`. -/
noncomputable def fiberedHomEquiv [IsFibered p] {R S T : E}
    (f : R ⟶ S) (g : T ⟶ R) {a b : C} (φ : a ⟶ b) [IsCartesian p f φ] (c : C) :
    HomOver p g c a ≃ HomOver p (g ≫ f) c b where
  toFun u := ⟨u.val ≫ φ, by have := u.property; infer_instance⟩
  invFun u := by
    have := u.property
    exact ⟨IsStronglyCartesian.map p f φ (g := g) rfl u.val, inferInstance⟩
  left_inv u := by
    have := u.property
    apply Subtype.ext
    exact (IsStronglyCartesian.map_uniq p f φ rfl (u.val ≫ φ) u.val rfl).symm
  right_inv u := by
    have := u.property
    apply Subtype.ext
    exact IsStronglyCartesian.fac p f φ rfl u.val

/-- VI.6.12, necessity: an isomorphism is cartesian and projects to an isomorphism. -/
theorem isIso_base_and_isCartesian {R S : E} (f : R ⟶ S) {a b : C}
    (φ : a ⟶ b) [IsHomLift p f φ] [IsIso φ] : IsIso f ∧ IsCartesian p f φ :=
  ⟨IsHomLift.isIso_of_lift_isIso p f φ, inferInstance⟩

/-- VI.6.12: in a fibered category an arrow is invertible exactly when it is
cartesian and its image in the base is invertible. -/
theorem isIso_iff_base_isIso_and_isCartesian [IsFibered p] {R S : E} (f : R ⟶ S)
    {a b : C} (φ : a ⟶ b) [IsHomLift p f φ] :
    IsIso φ ↔ IsIso f ∧ IsCartesian p f φ := by
  constructor
  · intro h
    exact isIso_base_and_isCartesian p f φ
  · rintro ⟨hf, hφ⟩
    exact IsStronglyCartesian.isIso_of_base_isIso p f φ

/-- VI.6.13: cancel a cartesian right factor when testing cartesianness. -/
theorem isCartesian_comp_iff [IsFibered p] {R S T : E} (f : R ⟶ S) (g : S ⟶ T)
    {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) [IsHomLift p f φ] [IsCartesian p g ψ] :
    IsCartesian p (f ≫ g) (φ ≫ ψ) ↔ IsCartesian p f φ := by
  constructor
  · intro h
    have := IsStronglyCartesian.of_comp p (f := f) (g := g) (φ := φ) (ψ := ψ)
    infer_instance
  · intro h
    infer_instance

end SGA.SGA1.ExposeVI
