/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Constructible
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sober

/-!
# A criterion for constructibility in noetherian spaces

EGA 0_III 9.2.3 (Stacks 053Y), which is also SGA 1 IV.6.1:

* `Topology.isConstructible_iff_of_noetherianSpace`: in a noetherian space, `E` is constructible if
  and only if, for every irreducible closed `Z`, either `E ∩ Z` is not dense in `Z` or `E ∩ Z`
  contains a nonempty open subset of `Z`. Both directions; the converse is proved by noetherian
  induction on the closed set `Z`.
* `Topology.IsConstructible.of_noetherianSpace`: the converse direction in the form used to prove
  constructibility by generic arguments (for instance in EGA IV 9.7.7).
* `Topology.IsConstructible.exists_isOpen_of_isGenericPoint`: a constructible set containing the
  generic point of a closed set `Z` contains a neighbourhood of it in `Z` (EGA 0_III 9.2.2).
* `Topology.IsConstructible.of_noetherianSpace_of_genericPoint`: in a noetherian quasi-sober space
  (e.g. a noetherian scheme), `E` is constructible if for every irreducible closed `Z` with generic
  point `η`, `E ∩ Z` contains a nonempty open subset of `Z` when `η ∈ E`, and `Z \ E` does when
  `η ∉ E`.

This file is the Foundations copy of SGA 1 IV.6.1
(`SGA.SGA1.ExposeIV.isConstructible_iff_of_noetherianSpace`, with
`SGA.SGA1.ExposeIV.isConstructible_of_isOpen`, `isConstructible_of_isClosed`), which Foundations
cannot import; those should become corollaries of the statements here.

## References

* [EGA 0_III, 9.2.3][EGA3]
* [Stacks Project, Tag 053Y](https://stacks.math.columbia.edu/tag/053Y)
* SGA 1, Exposé IV, 6.1
-/
open Set TopologicalSpace

namespace Topology

variable {X : Type*} [TopologicalSpace X] [NoetherianSpace X]

/-- In a noetherian space every open set is constructible. -/
lemma IsConstructible.of_isOpen_of_noetherianSpace {U : Set X} (hU : IsOpen U) :
    IsConstructible U :=
  (NoetherianSpace.isCompact U).isConstructible hU

/-- In a noetherian space every closed set is constructible. -/
lemma IsConstructible.of_isClosed_of_noetherianSpace {Z : Set X} (hZ : IsClosed Z) :
    IsConstructible Z := by
  rw [← isConstructible_compl]
  exact IsConstructible.of_isOpen_of_noetherianSpace hZ.isOpen_compl

/-- **EGA 0_III 9.2.3** (Stacks 053Y; SGA 1 IV.6.1), the converse direction: in a noetherian space,
`E` is constructible if, for every irreducible closed `Z` in which `E ∩ Z` is dense, `E ∩ Z`
contains a nonempty open subset of `Z`. The full equivalence is
`Topology.isConstructible_iff_of_noetherianSpace`. -/
theorem IsConstructible.of_noetherianSpace {E : Set X}
    (h : ∀ Z : Set X, IsClosed Z → IsIrreducible Z → Z ⊆ closure (E ∩ Z) →
      ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ E) :
    IsConstructible E := by
  suffices H : ∀ F : Closeds X, IsConstructible (E ∩ F) by
    simpa using H ⊤
  intro F
  induction F using WellFoundedLT.induction with
  | ind F ih =>
  by_cases hne : (F : Set X).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hne, inter_empty]
    exact IsConstructible.empty
  by_cases hirr : IsPreirreducible (F : Set X)
  · by_cases hd : (F : Set X) ⊆ closure (E ∩ F)
    · -- `E ∩ F` contains a nonempty open `U ∩ F`; the rest lies in the smaller `F \ U`
      obtain ⟨U, hU, hUne, hUE⟩ := h F F.isClosed ⟨hne, hirr⟩ hd
      let F' : Closeds X := ⟨F ∩ Uᶜ, F.isClosed.inter hU.isClosed_compl⟩
      have hlt : F' < F := by
        refine lt_of_le_of_ne (fun x hx ↦ hx.1) fun heq ↦ ?_
        obtain ⟨x, hxU, hxF⟩ := hUne
        have : x ∈ (F' : Set X) := by rw [heq]; exact hxF
        exact this.2 hxU
      have e : E ∩ F = (U ∩ F) ∪ (E ∩ F') := by
        ext x
        constructor
        · rintro ⟨hxE, hxF⟩
          by_cases hxU : x ∈ U
          · exact Or.inl ⟨hxU, hxF⟩
          · exact Or.inr ⟨hxE, hxF, hxU⟩
        · rintro (hx | ⟨hxE, hxF, -⟩)
          · exact ⟨hUE hx, hx.2⟩
          · exact ⟨hxE, hxF⟩
      rw [e]
      exact IsConstructible.union (IsConstructible.inter
        (IsConstructible.of_isOpen_of_noetherianSpace hU)
        (IsConstructible.of_isClosed_of_noetherianSpace F.isClosed)) (ih F' hlt)
    · -- `E ∩ F` lies in the smaller closed set `closure (E ∩ F)`
      let F' : Closeds X := ⟨closure (E ∩ F), isClosed_closure⟩
      have hle : (F' : Set X) ⊆ F := closure_minimal inter_subset_right F.isClosed
      have hlt : F' < F := lt_of_le_of_ne hle fun heq ↦
        hd (subset_of_eq (congrArg (fun G : Closeds X ↦ (G : Set X)) heq).symm)
      have e : E ∩ F = E ∩ F' := by
        ext x
        exact ⟨fun hx ↦ ⟨hx.1, subset_closure hx⟩, fun hx ↦ ⟨hx.1, hle hx.2⟩⟩
      rw [e]
      exact ih F' hlt
  · -- `F` is the union of two smaller closed sets
    obtain ⟨z₁, z₂, hz₁, hz₂, hF, h₁, h₂⟩ : ∃ z₁ z₂ : Set X, IsClosed z₁ ∧ IsClosed z₂ ∧
        (F : Set X) ⊆ z₁ ∪ z₂ ∧ ¬ (F : Set X) ⊆ z₁ ∧ ¬ (F : Set X) ⊆ z₂ := by
      rw [isPreirreducible_iff_isClosed_union_isClosed] at hirr
      push Not at hirr
      exact hirr
    let F₁ : Closeds X := ⟨F ∩ z₁, F.isClosed.inter hz₁⟩
    let F₂ : Closeds X := ⟨F ∩ z₂, F.isClosed.inter hz₂⟩
    have hlt₁ : F₁ < F := lt_of_le_of_ne (fun x hx ↦ hx.1) fun heq ↦
      h₁ fun x hx ↦ by
        have : x ∈ (F₁ : Set X) := by rw [heq]; exact hx
        exact this.2
    have hlt₂ : F₂ < F := lt_of_le_of_ne (fun x hx ↦ hx.1) fun heq ↦
      h₂ fun x hx ↦ by
        have : x ∈ (F₂ : Set X) := by rw [heq]; exact hx
        exact this.2
    have e : E ∩ F = (E ∩ F₁) ∪ (E ∩ F₂) := by
      ext x
      constructor
      · rintro ⟨hxE, hxF⟩
        rcases hF hxF with hx | hx
        · exact Or.inl ⟨hxE, hxF, hx⟩
        · exact Or.inr ⟨hxE, hxF, hx⟩
      · rintro (⟨hxE, hxF, -⟩ | ⟨hxE, hxF, -⟩) <;> exact ⟨hxE, hxF⟩
    rw [e]
    exact IsConstructible.union (ih F₁ hlt₁) (ih F₂ hlt₂)

/-- **EGA 0_III 9.2.3** (Stacks 053Y), the easy direction: if `E` is constructible, then for every
irreducible closed `Z`, either `E ∩ Z` is not dense in `Z`, or `E ∩ Z` contains a nonempty open
subset of `Z`. (Noetherianity is not needed here.) -/
theorem IsConstructible.not_subset_closure_or_exists_isOpen {X : Type*} [TopologicalSpace X]
    {E : Set X} (hE : IsConstructible E) (Z : Set X) (hZc : IsClosed Z) (hZ : IsIrreducible Z) :
    ¬ Z ⊆ closure (E ∩ Z) ∨ ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ E := by
  induction hE using IsConstructible.empty_union_induction generalizing Z with
  | open_retrocompact U hU _ =>
    by_cases hUZ : (U ∩ Z).Nonempty
    · exact Or.inr ⟨U, hU, hUZ, inter_subset_left⟩
    · left
      rw [not_nonempty_iff_eq_empty.1 hUZ, closure_empty, subset_empty_iff]
      exact hZ.nonempty.ne_empty
  | union s _ t _ hs ht =>
    rcases hs Z hZc hZ with hs | ⟨U, hU, hUZ, hUs⟩
    · rcases ht Z hZc hZ with ht | ⟨U, hU, hUZ, hUt⟩
      · left
        intro h
        rw [union_inter_distrib_right, closure_union] at h
        rcases isPreirreducible_iff_isClosed_union_isClosed.1 hZ.isPreirreducible _ _
          isClosed_closure isClosed_closure h with h | h
        · exact hs h
        · exact ht h
      · exact Or.inr ⟨U, hU, hUZ, hUt.trans subset_union_right⟩
    · exact Or.inr ⟨U, hU, hUZ, hUs.trans subset_union_left⟩
  | compl s _ hs =>
    rcases hs Z hZc hZ with hs | ⟨U, hU, hUZ, hUs⟩
    · refine Or.inr ⟨(closure (s ∩ Z))ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
      · obtain ⟨y, hyZ, hy⟩ := not_subset.1 hs
        exact ⟨y, hy, hyZ⟩
      · rintro y ⟨hy, hyZ⟩ hys
        exact hy (subset_closure ⟨hys, hyZ⟩)
    · left
      intro h
      have : closure (sᶜ ∩ Z) ⊆ Z ∩ Uᶜ :=
        closure_minimal (fun y ⟨hys, hyZ⟩ ↦ ⟨hyZ, fun hyU ↦ hys (hUs ⟨hyU, hyZ⟩)⟩)
          (hZc.inter hU.isClosed_compl)
      obtain ⟨y, hyU, hyZ⟩ := hUZ
      exact (this (h hyZ)).2 hyU

/-- A constructible set containing the generic point `η` of a closed set `Z` contains `U ∩ Z` for an
open neighbourhood `U` of `η` (EGA 0_III 9.2.2). (Noetherianity is not needed.) -/
theorem IsConstructible.exists_isOpen_of_isGenericPoint {X : Type*} [TopologicalSpace X]
    {E : Set X} (hE : IsConstructible E) {Z : Set X} (hZc : IsClosed Z) {η : X}
    (hη : IsGenericPoint η Z) (h : η ∈ E) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ U ∩ Z ⊆ E := by
  have hηZ : η ∈ Z := hη.mem
  rcases hE.not_subset_closure_or_exists_isOpen Z hZc hη.isIrreducible with hd | ⟨U, hU, hUZ, hUE⟩
  · refine absurd ?_ hd
    calc Z = closure {η} := hη.def.symm
      _ ⊆ closure (E ∩ Z) := closure_mono (Set.singleton_subset_iff.mpr ⟨h, hηZ⟩)
  · refine ⟨U, hU, ?_, hUE⟩
    exact (hη.mem_open_set_iff hU).mpr (by rwa [Set.inter_comm])

/-- **EGA 0_III 9.2.3** (Stacks 053Y; SGA 1 IV.6.1): in a noetherian space, `E` is constructible if
and only if for every irreducible closed `Z`, either `E ∩ Z` is not dense in `Z`, or `E ∩ Z`
contains a nonempty open subset of `Z`. -/
theorem isConstructible_iff_of_noetherianSpace {E : Set X} :
    IsConstructible E ↔ ∀ Z : Set X, IsClosed Z → IsIrreducible Z →
      ¬ Z ⊆ closure (E ∩ Z) ∨ ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ E := by
  refine ⟨fun hE Z hZc hZ ↦ hE.not_subset_closure_or_exists_isOpen Z hZc hZ, fun h ↦ ?_⟩
  exact IsConstructible.of_noetherianSpace fun Z hZc hZ hd ↦ (h Z hZc hZ).resolve_left (· hd)

/-- EGA 0_III 9.2.3 with generic points: in a noetherian quasi-sober space (for instance a
noetherian scheme), `E` is constructible if for every irreducible closed `Z` with generic point
`η`, `E ∩ Z` contains a nonempty open subset of `Z` when `η ∈ E`, and `Z \ E` contains one when
`η ∉ E`. -/
theorem IsConstructible.of_noetherianSpace_of_genericPoint [QuasiSober X] {E : Set X}
    (h₁ : ∀ (Z : Set X) (_ : IsClosed Z) (hZi : IsIrreducible Z), hZi.genericPoint ∈ E →
      ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ E)
    (h₂ : ∀ (Z : Set X) (_ : IsClosed Z) (hZi : IsIrreducible Z), hZi.genericPoint ∉ E →
      ∃ U : Set X, IsOpen U ∧ (U ∩ Z).Nonempty ∧ U ∩ Z ⊆ Eᶜ) :
    IsConstructible E := by
  refine IsConstructible.of_noetherianSpace fun Z hZ hZi hd ↦ ?_
  by_cases hη : hZi.genericPoint ∈ E
  · exact h₁ Z hZ hZi hη
  · obtain ⟨U, hU, ⟨x, hxU, hxZ⟩, hUE⟩ := h₂ Z hZ hZi hη
    exfalso
    have hsub : E ∩ Z ⊆ Uᶜ := fun y ⟨hyE, hyZ⟩ hyU ↦ hUE ⟨hyU, hyZ⟩ hyE
    exact closure_minimal hsub hU.isClosed_compl (hd hxZ) hxU

end Topology
