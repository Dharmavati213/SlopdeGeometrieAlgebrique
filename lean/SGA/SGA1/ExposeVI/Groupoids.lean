/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Fibered
import SGA.SGA1.ExposeVI.BasedEquivalences
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.SingleObj

/-!
# SGA 1, Exposé VI, remarks after VI.6.1: categories fibered in groupoids

We prove the all-morphisms-cartesian criterion (i) ⇔ (ii) for a **prefibered** category.
The lifting assumption is essential and is missing from condition (i) in SGA;
`Examples.oneToTwo_not_prefibered` supplies a counterexample to dropping it. Over a groupoid
base, (i) ⇔ (iii): `𝒳` is a groupoid and `p` is transportable. For groups, `SingleObj F` is
fibered over `SingleObj E` iff the homomorphism `F → E` is surjective.
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

/-- VI.6.1, remark (iii): over a groupoid, a prefibered category all of whose arrows are
cartesian is exactly a groupoid with transportable projection (VI.4.4). As for (i), the
prefiberedness hypothesis is needed. -/
theorem allMorphismsCartesian_and_isPreFibered_iff [IsGroupoid E] :
    (AllMorphismsCartesian p ∧ IsPreFibered p) ↔ (IsGroupoid C ∧ IsTransportable p) := by
  constructor
  · rintro ⟨h, _⟩
    have : IsFibered p := ((allMorphismsCartesian_iff_fiberedInGroupoids p).mp h).1
    refine ⟨⟨fun {a b} φ ↦ ?_⟩, fun x S e ↦ ?_⟩
    · have := h (p.map φ) φ inferInstance
      exact ((isIso_iff_base_isIso_and_isCartesian p (p.map φ) φ).mpr ⟨inferInstance, this⟩)
    · obtain ⟨x', φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p) (a := x) e.inv
      have : IsIso φ := IsStronglyCartesian.isIso_of_base_isIso p e.inv φ
      refine ⟨x', (asIso φ).symm, ?_⟩
      have : IsHomLift p e.symm.hom (asIso φ).hom := hφ.toIsHomLift
      exact IsHomLift.inv_lift_inv p e.symm (asIso φ)
  · rintro ⟨_, ht⟩
    refine ⟨fun {_ _} f {_ _} φ h ↦ ?_, ⟨fun {a R} f ↦ ?_⟩⟩
    · have := h
      infer_instance
    obtain ⟨x', e', he'⟩ := ht a R (asIso f).symm
    have : IsHomLift p (asIso f).symm.hom e'.hom := he'
    have : IsHomLift p f e'.inv := by
      simpa using IsHomLift.inv_lift_inv p (asIso f).symm e'
    exact ⟨x', e'.inv, inferInstance⟩

/-- VI.6.1, remark: for a homomorphism of groups `φ : F →* E`, the functor
`SingleObj F ⥤ SingleObj E` is fibered iff `φ` is surjective, i.e. `F` is an extension of
`E` by `ker φ`. -/
theorem singleObj_isFibered_iff {F G : Type*} [Group F] [Group G] (φ : F →* G) :
    IsFibered (SingleObj.mapHom F G φ) ↔ Function.Surjective φ := by
  let q := SingleObj.mapHom F G φ
  have hall : AllMorphismsCartesian q := fun {_ _} f {_ _} ψ h ↦ by
    have := h
    infer_instance
  constructor
  · intro _ g
    let g' : SingleObj.star G ⟶ SingleObj.star G := g
    obtain ⟨b, ψ, hψ⟩ := IsPreFibered.exists_isCartesian' (p := q) (a := SingleObj.star F) g'
    have h₁ := IsHomLift.fac' q g' ψ
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h₁
    exact ⟨ψ, h₁⟩
  · intro hφ
    have : IsPreFibered q := ⟨fun {a R} g ↦ by
      obtain ⟨x, hx⟩ := hφ g
      let x' : SingleObj.star F ⟶ a := x
      have : IsHomLift q g x' := by
        rw [← hx]
        exact IsHomLift.map q x'
      exact ⟨SingleObj.star F, x', hall g x' this⟩⟩
    exact ((allMorphismsCartesian_iff_fiberedInGroupoids q).mp hall).1

end SGA.SGA1.ExposeVI
