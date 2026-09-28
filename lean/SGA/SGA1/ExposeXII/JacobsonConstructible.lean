/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Constructible
import Mathlib.Topology.JacobsonSpace

/-!
# Constructible sets in Jacobson spaces

The Jacobson property used throughout XII §§2–3 (EGA IV 10.4.8): in a Jacobson space, a nonempty
locally constructible set contains a closed point. Hence two locally constructible sets with the
same closed points are equal (used for XII.2.3 and XII.3.2 (i)).

A constructible set is a finite union of locally closed sets
(`IsConstructible.exists_finite_isLocallyClosed`), and a nonempty locally closed subset of a
Jacobson space contains a closed point (mathlib's `nonempty_inter_closedPoints`).
-/

namespace SGA.SGA1.ExposeXII

open Set Topology

variable {X : Type*} [TopologicalSpace X]

/-- Finite unions of locally closed sets. -/
private def FinUnionLC (s : Set X) : Prop :=
  ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsLocallyClosed t) ∧ s = ⋃₀ S

private lemma FinUnionLC.inter {s t : Set X} (hs : FinUnionLC s) (ht : FinUnionLC t) :
    FinUnionLC (s ∩ t) := by
  obtain ⟨S, hS, hSlc, rfl⟩ := hs
  obtain ⟨T, hT, hTlc, rfl⟩ := ht
  refine ⟨image2 (· ∩ ·) S T, hS.image2 _ hT, ?_, ?_⟩
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact (hSlc a ha).inter (hTlc b hb)
  · ext x
    simp only [mem_inter_iff, mem_sUnion, mem_image2]
    constructor
    · rintro ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩
      exact ⟨a ∩ b, ⟨a, ha, b, hb, rfl⟩, hxa, hxb⟩
    · rintro ⟨_, ⟨a, ha, b, hb, rfl⟩, hxa, hxb⟩
      exact ⟨⟨a, ha, hxa⟩, ⟨b, hb, hxb⟩⟩

private lemma FinUnionLC.compl_of_isLocallyClosed {t : Set X} (ht : IsLocallyClosed t) :
    FinUnionLC tᶜ := by
  obtain ⟨U, Z, hU, hZ, rfl⟩ := ht
  refine ⟨{Uᶜ, Zᶜ}, toFinite _, ?_, by rw [compl_inter, sUnion_pair]⟩
  rintro _ (rfl | rfl)
  · exact hU.isClosed_compl.isLocallyClosed
  · exact hZ.isOpen_compl.isLocallyClosed

private lemma FinUnionLC.compl {s : Set X} (hs : FinUnionLC s) : FinUnionLC sᶜ := by
  obtain ⟨S, hS, hSlc, rfl⟩ := hs
  rw [compl_sUnion]
  induction S, hS using Set.Finite.induction_on with
  | empty => exact ⟨{univ}, toFinite _, by simp [isOpen_univ.isLocallyClosed], by simp⟩
  | @insert t S _ _ ih =>
    rw [image_insert_eq, sInter_insert]
    exact (compl_of_isLocallyClosed (hSlc t (mem_insert t S))).inter
      (ih fun u hu ↦ hSlc u (mem_insert_of_mem t hu))

/-- A constructible set is a finite union of locally closed sets. -/
theorem IsConstructible.exists_finite_isLocallyClosed {s : Set X} (hs : IsConstructible s) :
    ∃ S : Set (Set X), S.Finite ∧ (∀ t ∈ S, IsLocallyClosed t) ∧ s = ⋃₀ S := by
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ => exact ⟨{U}, toFinite _, by simp [hU.isLocallyClosed], by simp⟩
  | union s _ t _ hs ht =>
    obtain ⟨S, hS, hSlc, rfl⟩ := hs
    obtain ⟨T, hT, hTlc, rfl⟩ := ht
    exact ⟨S ∪ T, hS.union hT, fun u hu ↦ hu.elim (hSlc u) (hTlc u), (sUnion_union S T).symm⟩
  | compl s _ hs => exact FinUnionLC.compl hs

/-- In a Jacobson space, a nonempty constructible set contains a closed point. -/
theorem IsConstructible.nonempty_inter_closedPoints [JacobsonSpace X] {s : Set X}
    (hs : IsConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨S, -, hSlc, rfl⟩ := IsConstructible.exists_finite_isLocallyClosed hs
  obtain ⟨x, t, ht, hxt⟩ := hne
  obtain ⟨y, hyt, hy⟩ := _root_.nonempty_inter_closedPoints ⟨x, hxt⟩ (hSlc t ht)
  exact ⟨y, ⟨t, ht, hyt⟩, hy⟩

lemma IsLocallyConstructible.compl {s : Set X} (hs : IsLocallyConstructible s) :
    IsLocallyConstructible sᶜ := fun x ↦ by
  obtain ⟨U, hU, hUo, hUs⟩ := hs x
  exact ⟨U, hU, hUo, by simpa [preimage_compl] using hUs.compl⟩

/-- In a Jacobson space, a nonempty locally constructible set contains a closed point. -/
theorem IsLocallyConstructible.nonempty_inter_closedPoints [JacobsonSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) (hne : s.Nonempty) : (s ∩ closedPoints X).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨U, hU, hUo, hUs⟩ := hs x
  have hemb : IsOpenEmbedding ((↑) : U → X) := hUo.isOpenEmbedding_subtypeVal
  have : JacobsonSpace U := JacobsonSpace.of_isOpenEmbedding hemb
  obtain ⟨u, hus, huc⟩ :=
    IsConstructible.nonempty_inter_closedPoints hUs ⟨⟨x, mem_of_mem_nhds hU⟩, hx⟩
  rw [← hemb.preimage_closedPoints] at huc
  exact ⟨u, hus, huc⟩

/-- In a Jacobson space, a locally constructible set containing every closed point is
everything. -/
theorem IsLocallyConstructible.eq_univ_of_closedPoints_subset [JacobsonSpace X] {s : Set X}
    (hs : IsLocallyConstructible s) (h : closedPoints X ⊆ s) : s = univ := by
  by_contra hne
  obtain ⟨x, hxs, hx⟩ := IsLocallyConstructible.nonempty_inter_closedPoints
    (IsLocallyConstructible.compl hs) ((ne_univ_iff_exists_notMem s).mp hne)
  exact hxs (h hx)

end SGA.SGA1.ExposeXII
