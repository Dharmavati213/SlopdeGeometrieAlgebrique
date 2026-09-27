/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVIII.Effectiveness

/-!
# SGA 1, Exposé VIII, VIII.2.1: descent of affine morphisms over an arbitrary base

`exists_isPullback_of_isAffineHom_of_flat` is VIII.2.1 for arbitrary `S` and `S'`, in the form of
`exists_isPullback_of_isAffineHom` (`AffineSchemeDescent`, affine `S` and `S'`): for `g : S' → S`
faithfully flat and quasi-compact, a descent datum (an equivalence pair `q₁, q₂ : X'' ⇉ X'` over
`S' ×_S S' ⇉ S'` with cartesian squares) on an `S'`-scheme `X'` affine over `S'` is effective.
Only reflexivity and transitivity are assumed: symmetry follows from them and the cartesian
squares (`symm_of_refl_of_trans`). The proof applies `DescentDatum.isEffective_of_isAffineHom`
(`Effectiveness`), which reduces to an affine base.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeVIII

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {X' X'' : Scheme.{u}} {a : X' ⟶ S'}
  {b : X'' ⟶ pullback g g} {q₁ q₂ : X'' ⟶ X'}

/-- For an equivalence pair over `S' ×_S S' ⇉ S'` with cartesian squares, symmetry follows from
reflexivity and transitivity. -/
lemma symm_of_refl_of_trans (h₁ : IsPullback q₁ b a (pullback.fst g g))
    (h₂ : IsPullback q₂ b a (pullback.snd g g))
    (refl : ∀ ⦃T : Scheme.{u}⦄ (x : T ⟶ X'), ∃ r : T ⟶ X'', r ≫ q₁ = x ∧ r ≫ q₂ = x)
    (trans : ∀ ⦃T : Scheme.{u}⦄ (r r' : T ⟶ X''), r ≫ q₂ = r' ≫ q₁ →
      ∃ r'' : T ⟶ X'', r'' ≫ q₁ = r ≫ q₁ ∧ r'' ≫ q₂ = r' ≫ q₂)
    ⦃T : Scheme.{u}⦄ (r : T ⟶ X'') : ∃ r' : T ⟶ X'', r' ≫ q₁ = r ≫ q₂ ∧ r' ≫ q₂ = r ≫ q₁ := by
  have hσ : (r ≫ q₂ ≫ a) ≫ g = (r ≫ q₁ ≫ a) ≫ g := by
    rw [h₂.w, h₁.w]
    simp only [Category.assoc, pullback.condition]
  let σ : T ⟶ pullback g g := pullback.lift (r ≫ q₂ ≫ a) (r ≫ q₁ ≫ a) hσ
  let r' : T ⟶ X'' := h₁.lift (r ≫ q₂) σ (by
    rw [Category.assoc]; exact (pullback.lift_fst _ _ _).symm)
  have hr'₁ : r' ≫ q₁ = r ≫ q₂ := h₁.lift_fst _ _ _
  have hr'b : r' ≫ b = σ := h₁.lift_snd _ _ _
  refine ⟨r', hr'₁, ?_⟩
  obtain ⟨r'', hr''₁, hr''₂⟩ := trans r r' hr'₁.symm
  obtain ⟨s, hs₁, hs₂⟩ := refl (r ≫ q₁)
  have e₁ : (r'' ≫ b) ≫ pullback.fst g g = r ≫ q₁ ≫ a := by
    rw [Category.assoc, ← h₁.w, ← Category.assoc, hr''₁, Category.assoc]
  have e₂ : (s ≫ b) ≫ pullback.fst g g = r ≫ q₁ ≫ a := by
    rw [Category.assoc, ← h₁.w, ← Category.assoc, hs₁, Category.assoc]
  have e₃ : (r'' ≫ b) ≫ pullback.snd g g = r ≫ q₁ ≫ a := by
    rw [Category.assoc, ← h₂.w, ← Category.assoc, hr''₂, Category.assoc, h₂.w,
      ← Category.assoc, hr'b, pullback.lift_snd]
  have e₄ : (s ≫ b) ≫ pullback.snd g g = r ≫ q₁ ≫ a := by
    rw [Category.assoc, ← h₂.w, ← Category.assoc, hs₂, Category.assoc]
  have hb : r'' ≫ b = s ≫ b := pullback.hom_ext (e₁.trans e₂.symm) (e₃.trans e₄.symm)
  have hrs : r'' = s := h₁.hom_ext (hr''₁.trans hs₁.symm) hb
  rw [← hr''₂, hrs, hs₂]

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.2.1: let `g : S' → S` be faithfully flat and quasi-compact, and `q₁, q₂ : X'' ⇉ X'` an
equivalence pair over `p₁, p₂ : S' ×_S S' ⇉ S'` with both squares cartesian (a descent datum on
the `S'`-scheme `X'`, VIII.7), where `X' → S'` is affine. Then the descent datum is effective:
there is a cartesian square `X' → X` over `g` with `h ∘ q₁ = h ∘ q₂`. Only reflexivity and
transitivity of the equivalence pair are used. For affine `S` and `S'` this is
`exists_isPullback_of_isAffineHom`. -/
theorem exists_isPullback_of_isAffineHom_of_flat (g : S' ⟶ S) [Flat g] [Surjective g]
    [QuasiCompact g] (a : X' ⟶ S') [IsAffineHom a] (b : X'' ⟶ pullback g g) (q₁ q₂ : X'' ⟶ X')
    (h₁ : IsPullback q₁ b a (pullback.fst g g)) (h₂ : IsPullback q₂ b a (pullback.snd g g))
    (refl : ∀ ⦃T : Scheme.{u}⦄ (x : T ⟶ X'), ∃ r : T ⟶ X'', r ≫ q₁ = x ∧ r ≫ q₂ = x)
    (trans : ∀ ⦃T : Scheme.{u}⦄ (r r' : T ⟶ X''), r ≫ q₂ = r' ≫ q₁ →
      ∃ r'' : T ⟶ X'', r'' ≫ q₁ = r ≫ q₁ ∧ r'' ≫ q₂ = r' ≫ q₂) :
    ∃ (X : Scheme.{u}) (f : X ⟶ S) (h : X' ⟶ X), IsPullback h a f g ∧ q₁ ≫ h = q₂ ≫ h := by
  let D : DescentDatum g :=
    { X' := X', a := a, X'' := X'', b := b, q₁ := q₁, q₂ := q₂, isPullback₁ := h₁,
      isPullback₂ := h₂, refl := refl, symm := symm_of_refl_of_trans h₁ h₂ refl trans,
      trans := trans }
  have : IsAffineHom D.a := ‹IsAffineHom a›
  exact D.isEffective_of_isAffineHom

end SGA.SGA1.ExposeVIII
