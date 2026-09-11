/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Fibered
import SGA.SGA1.ExposeVI.Fibers
import Mathlib.CategoryTheory.Groupoid

/-!
# SGA 1, Exposé VI, remark after VI.6.1

We prove the all-morphisms-cartesian criterion for a **prefibered** category.
The lifting assumption is essential and is missing from condition (i) in
the English draft. `Examples.oneToTwo_not_prefibered` supplies a counterexample
to dropping it. The fibers use their existing category structures.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]
  (p : C ⥤ E)

/-- Every morphism is cartesian, expressed with explicit base arrows. -/
def AllMorphismsCartesian : Prop :=
  ∀ {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b),
    IsHomLift p f φ → IsCartesian p f φ

/-- VI.6.1, remark: a fibered category whose fibers are groupoids. -/
def IsFiberedInGroupoids : Prop := IsFibered p ∧ ∀ S : E, IsGroupoid (Fiber p S)

/-- Corrected VI.6.1 remark: in a prefibered category, all arrows are cartesian
iff the category is fibered and every fiber is a groupoid. -/
theorem allMorphismsCartesian_iff_fiberedInGroupoids [IsPreFibered p] :
    AllMorphismsCartesian p ↔ IsFiberedInGroupoids p := by
  constructor
  · intro h
    refine ⟨(isFibered_iff_comp p).mpr ?_, ?_⟩
    · intro R S T f g a b c φ ψ hφ hψ
      exact h (f ≫ g) (φ ≫ ψ) (by infer_instance)
    · intro S
      refine ⟨?_⟩
      intro a b φ
      have : IsCartesian p (𝟙 S) φ.val := h (𝟙 S) φ.val φ.property
      have : IsIso φ.val := isIso_of_vertical_isCartesian p (S := S) φ.val
      have : IsHomLift p (𝟙 S) (inv φ.val) := IsHomLift.lift_id_inv_isIso p S φ.val
      exact ⟨⟨⟨inv φ.val, inferInstance⟩,
        Subtype.ext (IsIso.hom_inv_id φ.val),
        Subtype.ext (IsIso.inv_hom_id φ.val)⟩⟩
  · rintro ⟨hp, hG⟩ R S f a b φ hφ
    have : IsGroupoid (Fiber p R) := hG R
    obtain ⟨c, ψ, hψ⟩ := IsPreFibered.exists_isCartesian p
      (IsHomLift.codomain_eq p f φ) f
    let χ := IsCartesian.map p f ψ φ
    let aR : Fiber p R := ⟨a, IsHomLift.domain_eq p f φ⟩
    let cR : Fiber p R := ⟨c, IsHomLift.domain_eq p f ψ⟩
    let χR : aR ⟶ cR := ⟨χ, inferInstance⟩
    have : IsIso χ := inferInstanceAs (IsIso (Fiber.fiberInclusion.map χR))
    have : IsHomLift p (𝟙 R) (asIso χ).hom :=
      IsCartesian.map_isHomLift p f ψ φ
    have hc : IsCartesian p f (χ ≫ ψ) := IsCartesian.of_iso_comp p f ψ (asIso χ)
    simpa only [χ, IsCartesian.fac] using hc

end SGA.SGA1.ExposeVI
