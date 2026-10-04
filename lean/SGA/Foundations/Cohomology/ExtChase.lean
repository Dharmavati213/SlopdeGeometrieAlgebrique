/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Four and five lemmas for maps between long exact `Ext` sequences

Let `S` be a short exact sequence in an abelian category `C`, `S'` one in an abelian category `D`,
`A : C`, `A' : D`, and let `αᵢ : Extⁿ(A, S.Xᵢ) → Extⁿ(A', S'.Xᵢ)` (`i = 1, 2, 3`, all `n`) be
additive maps commuting with the maps `Extⁿ(A, S.f)`, `Extⁿ(A, S.g)` of the long exact sequences
and with their connecting maps (composition with `S.extClass`). Then:

* `CategoryTheory.Abelian.ExtChase.surjective₃`, `injective₃`: the four lemmas on the third terms;
* `CategoryTheory.Abelian.ExtChase.bijective₂`: the five lemma on the middle terms (if `α₁` and
  `α₃` are bijective in every degree, so is `α₂`).

The categories `C` and `D` may differ: in GAGA (SGA 1 XII.4.2, XII.4.3; Serre, GAGA, no. 12) the
`αᵢ` are the comparison maps `Hⁿ(X, F) → Hⁿ(X^an, F^an)` between sheaf cohomology on a scheme
and on its analytification. The proofs are direct diagram chases with the exactness of the
covariant long exact `Ext` sequence (`Ext.covariant_sequence_exact₁`, `₂`, `₃`). Mathlib's four
and five lemmas (`Abelian.mono_of_epi_of_mono_of_mono`,
`Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono`) need a morphism of `ComposableArrows` in one
category; packaging the `αᵢ` as such is longer than the chase.

Reference: S. Mac Lane, *Homology*, Chapter I, Lemma 3.3 (the five lemma).
-/

open CategoryTheory Abelian

namespace CategoryTheory.Abelian.ExtChase

variable {C D : Type*} [Category C] [Abelian C] [HasExt C] [Category D] [Abelian D] [HasExt D]
  {A : C} {A' : D} {S : ShortComplex C} {S' : ShortComplex D}
  (hS : S.ShortExact) (hS' : S'.ShortExact)
  (α₁ : ∀ n, Ext A S.X₁ n →+ Ext A' S'.X₁ n) (α₂ : ∀ n, Ext A S.X₂ n →+ Ext A' S'.X₂ n)
  (α₃ : ∀ n, Ext A S.X₃ n →+ Ext A' S'.X₃ n)
  (h₁₂ : ∀ n x, α₂ n (x.comp (Ext.mk₀ S.f) (add_zero n)) =
    (α₁ n x).comp (Ext.mk₀ S'.f) (add_zero n))
  (h₂₃ : ∀ n x, α₃ n (x.comp (Ext.mk₀ S.g) (add_zero n)) =
    (α₂ n x).comp (Ext.mk₀ S'.g) (add_zero n))
  (hδ : ∀ n x, α₁ (n + 1) (x.comp hS.extClass rfl) = (α₃ n x).comp hS'.extClass rfl)

include h₁₂ h₂₃ hδ

/-- Four lemma, surjectivity on the third terms: if `α₂` is onto in degree `p`, `α₁` onto and `α₂`
injective in degree `p + 1`, then `α₃` is onto in degree `p`. -/
theorem surjective₃ (p : ℕ) (h₂ : Function.Surjective (α₂ p))
    (h₁' : Function.Surjective (α₁ (p + 1))) (h₂' : Function.Injective (α₂ (p + 1))) :
    Function.Surjective (α₃ p) := by
  intro y
  obtain ⟨x', hx'⟩ := h₁' (y.comp hS'.extClass rfl)
  have hx'0 : x'.comp (Ext.mk₀ S.f) (add_zero (p + 1)) = 0 := by
    apply h₂'
    rw [h₁₂, hx', map_zero, Ext.comp_assoc_of_third_deg_zero, hS'.extClass_comp, Ext.comp_zero]
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ _ hS x' hx'0 rfl
  have hyz : (y - α₃ p z).comp hS'.extClass rfl = 0 := by
    rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, ← hδ, hz, hx', add_neg_cancel]
  obtain ⟨w', hw'⟩ := Ext.covariant_sequence_exact₃ _ hS' (y - α₃ p z) rfl hyz
  obtain ⟨w, rfl⟩ := h₂ w'
  refine ⟨z + w.comp (Ext.mk₀ S.g) (add_zero p), ?_⟩
  rw [map_add, h₂₃, hw', add_sub_cancel]

/-- Four lemma, injectivity on the third terms: if `α₁` is injective in degree `p + 1`, `α₂`
injective and `α₁` onto in degree `p`, then `α₃` is injective in degree `p`. -/
theorem injective₃ (p : ℕ) (h₁' : Function.Injective (α₁ (p + 1)))
    (h₂ : Function.Injective (α₂ p)) (h₁ : Function.Surjective (α₁ p)) :
    Function.Injective (α₃ p) := by
  rw [injective_iff_map_eq_zero]
  intro z hz
  have hδz : z.comp hS.extClass rfl = 0 := by
    apply h₁'
    rw [hδ, hz, map_zero, Ext.zero_comp]
  obtain ⟨w, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS z rfl hδz
  have hw : (α₂ p w).comp (Ext.mk₀ S'.g) (add_zero p) = 0 := by rw [← h₂₃, hz]
  obtain ⟨u', hu'⟩ := Ext.covariant_sequence_exact₂ _ hS' (α₂ p w) hw
  obtain ⟨u, rfl⟩ := h₁ u'
  have : w = u.comp (Ext.mk₀ S.f) (add_zero p) := by
    apply h₂
    rw [h₁₂, hu']
  rw [this, Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, S.zero, Ext.mk₀_zero,
    Ext.comp_zero]

/-- Five lemma, middle terms: if `α₁` and `α₃` are bijective in every degree, so is `α₂`. -/
theorem bijective₂ (h₁ : ∀ n, Function.Bijective (α₁ n)) (h₃ : ∀ n, Function.Bijective (α₃ n))
    (p : ℕ) : Function.Bijective (α₂ p) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hgx : x.comp (Ext.mk₀ S.g) (add_zero p) = 0 := by
      apply (h₃ p).1
      rw [h₂₃, hx, map_zero, Ext.zero_comp]
    obtain ⟨y, rfl⟩ := Ext.covariant_sequence_exact₂ _ hS x hgx
    have hfy : (α₁ p y).comp (Ext.mk₀ S'.f) (add_zero p) = 0 := by rw [← h₁₂, hx]
    cases p with
    | zero =>
      have := hS'.mono_f
      have h0 : α₁ 0 y = 0 := by
        rw [← Ext.mk₀_addEquiv₀_apply (α₁ 0 y)] at hfy ⊢
        rw [Ext.mk₀_comp_mk₀, Ext.mk₀_eq_zero_iff] at hfy
        rw [(cancel_mono S'.f).mp (hfy.trans Limits.zero_comp.symm), Ext.mk₀_zero]
      have hy : y = 0 := (h₁ 0).1 (h0.trans (map_zero _).symm)
      rw [hy, Ext.zero_comp]
    | succ q =>
      obtain ⟨z', hz'⟩ := Ext.covariant_sequence_exact₁ _ hS' (α₁ (q + 1) y) hfy rfl
      obtain ⟨z, rfl⟩ := (h₃ q).2 z'
      have : y = z.comp hS.extClass rfl := by
        apply (h₁ (q + 1)).1
        rw [hδ, hz']
      rw [this, Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  · intro y'
    obtain ⟨z, hz⟩ := (h₃ p).2 (y'.comp (Ext.mk₀ S'.g) (add_zero p))
    have hδz : z.comp hS.extClass rfl = 0 := by
      apply (h₁ (p + 1)).1
      rw [hδ, hz, map_zero, Ext.comp_assoc_of_second_deg_zero, hS'.comp_extClass, Ext.comp_zero]
    obtain ⟨w, rfl⟩ := Ext.covariant_sequence_exact₃ _ hS z rfl hδz
    have hw : (y' - α₂ p w).comp (Ext.mk₀ S'.g) (add_zero p) = 0 := by
      rw [sub_eq_add_neg, Ext.add_comp, Ext.neg_comp, ← h₂₃, hz, add_neg_cancel]
    obtain ⟨u', hu'⟩ := Ext.covariant_sequence_exact₂ _ hS' _ hw
    obtain ⟨u, rfl⟩ := (h₁ p).2 u'
    refine ⟨w + u.comp (Ext.mk₀ S.f) (add_zero p), ?_⟩
    rw [map_add, h₁₂, hu', add_sub_cancel]

end CategoryTheory.Abelian.ExtChase
