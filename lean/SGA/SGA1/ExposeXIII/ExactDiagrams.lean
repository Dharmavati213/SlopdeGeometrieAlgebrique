/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.NatIso

/-!
# SGA 1, Exposé XIII, 1.10–1.11: exact diagrams

XIII 1.10 defines exact diagrams `Φ → Φ₁ ⇉ Φ₂` and `Φ → Φ₁ ⇉ Φ₂ ⇶ Φ₃` of fibered categories;
the conditions are fiberwise, and are stated here for a diagram of categories
(`IsExactDiagram`, `IsExactDiagram₂`). For categories which are discrete, i.e. for stacks in
discrete categories attached to sheaves of sets, exactness is the condition that
`F → G ⇉ H` is an equalizer (the remark in XIII 1.11 1)): `isExactDiagram₂_discrete_iff`.
For sheaves of sets, XIII 1.13 1) is `IsCohomologicallyProperLEZero.of_isLimit_fork` in
`SGA.SGA1.ExposeXIII.CohomologicalProperness`. The permanence of exact diagrams of stacks
under direct and inverse images (1.10.4) and 1.12 are not formalized: inverse images of stacks
are missing.
-/

open CategoryTheory

namespace SGA.SGA1.ExposeXIII

section

variable {Φ Φ₁ Φ₂ Φ₃ : Type*} [Category* Φ] [Category* Φ₁] [Category* Φ₂] [Category* Φ₃]

/-- XIII 1.10.1: the diagram `Φ → Φ₁ ⇉ Φ₂`, with `a : p ⋙ p₁ ≅ p ⋙ p₂`, is exact if every
morphism `φ : p x ⟶ p y` with `p₁ φ = p₂ φ` (modulo `a`) comes from a unique `ψ : x ⟶ y`. -/
def IsExactDiagram (p : Φ ⥤ Φ₁) (p₁ p₂ : Φ₁ ⥤ Φ₂) (a : p ⋙ p₁ ≅ p ⋙ p₂) : Prop :=
  ∀ ⦃x y : Φ⦄ (φ : p.obj x ⟶ p.obj y), p₁.map φ ≫ a.hom.app y = a.hom.app x ≫ p₂.map φ →
    ∃! ψ : x ⟶ y, p.map ψ = φ

/-- XIII 1.10.2: the diagram `Φ → Φ₁ ⇉ Φ₂ ⇶ Φ₃` is exact if it satisfies condition a) of
1.10.1 and condition b): every object `x₁` of `Φ₁` with an isomorphism `u : p₁ x₁ ≅ p₂ x₁`
satisfying the cocycle condition `p₂₃(u) p₃₁(u) = p₁₂(u)⁻¹` (modulo the identifications
`a₁, a₂, a₃`) is isomorphic to some `p x`, compatibly with `u`. -/
def IsExactDiagram₂ (p : Φ ⥤ Φ₁) (p₁ p₂ : Φ₁ ⥤ Φ₂) (p₁₂ p₂₃ p₃₁ : Φ₂ ⥤ Φ₃)
    (a : p ⋙ p₁ ≅ p ⋙ p₂) (a₁ : p₂ ⋙ p₃₁ ≅ p₁ ⋙ p₁₂) (a₂ : p₂ ⋙ p₁₂ ≅ p₁ ⋙ p₂₃)
    (a₃ : p₂ ⋙ p₂₃ ≅ p₁ ⋙ p₃₁) : Prop :=
  IsExactDiagram p p₁ p₂ a ∧
    ∀ (x₁ : Φ₁) (u : p₁.obj x₁ ≅ p₂.obj x₁),
      p₂₃.map u.hom ≫ a₃.hom.app x₁ ≫ p₃₁.map u.hom ≫ a₁.hom.app x₁ ≫ p₁₂.map u.hom ≫
        a₂.hom.app x₁ = 𝟙 _ →
      ∃ (x : Φ) (i : p.obj x ≅ x₁), p₁.map i.hom ≫ u.hom = a.hom.app x ≫ p₂.map i.hom

end

section Discrete

variable {A B C D : Type*} (f : A → B) (g₁ g₂ : B → C) (hf : ∀ a, g₁ (f a) = g₂ (f a))

/-- The functor between discrete categories induced by a map. -/
abbrev discreteFunctor {A B : Type*} (f : A → B) : Discrete A ⥤ Discrete B :=
  Discrete.functor (Discrete.mk ∘ f)

/-- The isomorphism `p ⋙ p₁ ≅ p ⋙ p₂` for discrete categories given `g₁ ∘ f = g₂ ∘ f`. -/
def discreteIso :
    discreteFunctor f ⋙ discreteFunctor g₁ ≅ discreteFunctor f ⋙ discreteFunctor g₂ :=
  Discrete.natIso (fun a ↦ Discrete.eqToIso (hf a.as))

/-- XIII 1.11 1) (the comparison it makes): for stacks in discrete categories, condition a) of
exactness says that `F → G` is injective. -/
lemma isExactDiagram_discrete_iff :
    IsExactDiagram (discreteFunctor f) (discreteFunctor g₁) (discreteFunctor g₂)
      (discreteIso f g₁ g₂ hf) ↔ Function.Injective f := by
  constructor
  · intro h a b hab
    obtain ⟨ψ, -, -⟩ := h (x := ⟨a⟩) (y := ⟨b⟩) (Discrete.eqToHom hab) (Subsingleton.elim _ _)
    exact Discrete.eq_of_hom ψ
  · intro h x y φ _
    refine ⟨Discrete.eqToHom (h (Discrete.eq_of_hom φ)), Subsingleton.elim _ _,
      fun _ _ ↦ Subsingleton.elim _ _⟩

variable (k₁₂ k₂₃ k₃₁ : C → D) (h₁ : ∀ b, k₃₁ (g₂ b) = k₁₂ (g₁ b))
  (h₂ : ∀ b, k₁₂ (g₂ b) = k₂₃ (g₁ b)) (h₃ : ∀ b, k₂₃ (g₂ b) = k₃₁ (g₁ b))

/-- XIII 1.11 1): a diagram of sets `F → G ⇉ H` is exact (an equalizer) if and only if the
associated diagram of stacks in discrete categories (completed by any `H ⇶ K`) is exact in the
sense of 1.10.2. -/
lemma isExactDiagram₂_discrete_iff :
    IsExactDiagram₂ (discreteFunctor f) (discreteFunctor g₁) (discreteFunctor g₂)
      (discreteFunctor k₁₂) (discreteFunctor k₂₃) (discreteFunctor k₃₁) (discreteIso f g₁ g₂ hf)
      (Discrete.natIso (fun b ↦ Discrete.eqToIso (h₁ b.as)))
      (Discrete.natIso (fun b ↦ Discrete.eqToIso (h₂ b.as)))
      (Discrete.natIso (fun b ↦ Discrete.eqToIso (h₃ b.as))) ↔
      Function.Injective f ∧ ∀ b, g₁ b = g₂ b → ∃ a, f a = b := by
  rw [IsExactDiagram₂, isExactDiagram_discrete_iff]
  refine and_congr_right fun _ ↦ ⟨fun h b hb ↦ ?_, fun h x₁ u _ ↦ ?_⟩
  · obtain ⟨x, i, -⟩ := h ⟨b⟩ (Discrete.eqToIso hb) (Subsingleton.elim _ _)
    exact ⟨x.as, Discrete.eq_of_hom i.hom⟩
  · obtain ⟨a, ha⟩ := h x₁.as (Discrete.eq_of_hom u.hom)
    exact ⟨⟨a⟩, Discrete.eqToIso ha, Subsingleton.elim _ _⟩

end Discrete

end SGA.SGA1.ExposeXIII
