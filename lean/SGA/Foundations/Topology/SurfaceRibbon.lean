/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.GroupTheory.Perm.List
import Mathlib.Data.List.Rotate

/-!
# Ribbon graphs as cyclic lists of darts

A *ribbon graph* (a graph embedded in an oriented surface) is described by its darts (half-edges),
the involution `β` exchanging the two darts of an edge, the cyclic order of the darts at each vertex
(the *rotation*) and the resulting *faces*: the successor of a dart `d` in its face is the
successor of `β d` in the rotation at its vertex. Here rotations and faces are nodup lists read
cyclically (`List.formPerm`), and `Ribbon.FaceCompat L Vs β` is the compatibility condition
between faces `L` and rotations `Vs`.

The two operations of the classification of surfaces are expressed with two list lemmas:

* deleting a dart from a cyclic list is the first-return map (`List.formPerm_erase_apply`), so
  compatibility survives the deletion of the two darts of an edge
  (`Ribbon.FaceCompat.erase`), once the two darts are made fixed points of `β`;
* splicing two cyclic lists `x :: u` and `y :: v` into `x :: u ++ y :: v`
  (`List.formPerm_splice`): this merges two vertices along an edge (contraction) and two faces
  along an edge (deletion), or splits a face in two.

This is the combinatorial input of the presentation of the fundamental group of a punctured
compact orientable surface (`Foundations/Topology/SurfaceOneVertex.lean`).

## References

* [W. S. Massey, *Algebraic Topology: An Introduction*, Chapter 1][massey1967]
* [B. Mohar, C. Thomassen, *Graphs on Surfaces*, §3.2–3.3][mohar2001]
-/

open Function

namespace List

variable {α : Type*} [DecidableEq α] {l : List α}

/-- In a nodup list `s ++ a :: b :: t`, the cyclic successor of `a` is `b`. -/
theorem formPerm_apply_of_eq_append (hl : l.Nodup) {s t : List α} {a b : α}
    (h : l = s ++ a :: b :: t) : l.formPerm a = b := by
  subst h
  have hlen : s.length + 1 < (s ++ a :: b :: t).length := by simp
  have := formPerm_apply_lt_getElem _ hl s.length hlen
  simpa [getElem_append_right] using this

/-- In `b :: (s ++ [a])`, the cyclic successor of `a` is `b`. -/
theorem formPerm_apply_of_eq_cons_concat {s : List α} {a b : α} (h : l = b :: (s ++ [a])) :
    l.formPerm a = b := by
  subst h
  exact formPerm_cons_concat_apply_last b a s

/-- **Deleting an element of a cyclic list is the first-return map**: in `l.erase y`, the
successor of `z ≠ y` is its successor in `l`, unless that is `y`, in which case it is the
successor of `y` in `l`. -/
theorem formPerm_erase_apply (hl : l.Nodup) {y z : α} (hz : z ∈ l) (hzy : z ≠ y) :
    (l.erase y).formPerm z = if l.formPerm z = y then l.formPerm y else l.formPerm z := by
  by_cases hy : y ∈ l
  swap
  · rw [erase_of_not_mem hy]
    split_ifs with h
    · exact absurd (h ▸ formPerm_apply_mem_of_mem hz) hy
    · rfl
  obtain ⟨P, S, rfl⟩ := append_of_mem hy
  have hyP : y ∉ P := fun h ↦ (nodup_append.mp hl).2.2 y h y (mem_cons_self ..) rfl
  have herase : (P ++ y :: S).erase y = P ++ S := by
    rw [erase_append_right _ hyP, erase_cons_head]
  have hrot : (P ++ y :: S) ~r (y :: (S ++ P)) := by
    simpa using (isRotated_append (l := P) (l' := y :: S))
  have hnd' : (P ++ S).Nodup := herase ▸ hl.erase y
  rw [herase, formPerm_eq_of_isRotated hnd' isRotated_append, formPerm_eq_of_isRotated hl hrot]
  have hnd : (y :: (S ++ P)).Nodup := hrot.nodup_iff.mp hl
  have hz' : z ∈ S ++ P := by
    have : z ∈ P ++ S := by
      rw [← herase]
      exact (mem_erase_of_ne hzy).mpr hz
    exact mem_append.mpr ((mem_append.mp this).symm)
  generalize S ++ P = S' at hz' hnd
  obtain _ | ⟨s, S''⟩ := S'
  · simp at hz'
  have hyS : y ∉ s :: S'' := (nodup_cons.mp hnd).1
  rw [formPerm_cons_cons, Equiv.Perm.coe_mul, comp_apply, comp_apply,
    formPerm_apply_of_notMem hyS, Equiv.swap_apply_left]
  have hw : (s :: S'').formPerm z ∈ s :: S'' := formPerm_apply_mem_of_mem hz'
  have hwy : (s :: S'').formPerm z ≠ y := fun h ↦ hyS (h ▸ hw)
  by_cases hws : (s :: S'').formPerm z = s
  · rw [hws, Equiv.swap_apply_right]
    simp
  · rw [Equiv.swap_apply_of_ne_of_ne hwy hws]
    simp [hwy]

/-- **Splicing two cyclic lists.** In `x :: u ++ y :: v` (nodup), the successors are those of
`y :: u` on `u ∪ {x}` (with `x` in the role of `y`) and those of `x :: v` on `v ∪ {y}` (with `y` in
the role of `x`): `x :: u ++ y :: v` is the cyclic permutation `(y :: u) ∘ (x :: v) ∘ (x y)`. -/
theorem formPerm_splice {x y : α} {u v : List α} (hl : (x :: (u ++ y :: v)).Nodup) :
    (∀ z ∈ u, (x :: (u ++ y :: v)).formPerm z = (y :: u).formPerm z) ∧
    (∀ z ∈ v, (x :: (u ++ y :: v)).formPerm z = (x :: v).formPerm z) ∧
    (x :: (u ++ y :: v)).formPerm x = (y :: u).formPerm y ∧
    (x :: (u ++ y :: v)).formPerm y = (x :: v).formPerm x := by
  have hx := (nodup_cons.mp hl).1
  have huv := (nodup_cons.mp hl).2
  have hu : u.Nodup := (nodup_append.mp huv).1
  have hyv : (y :: v).Nodup := (nodup_append.mp huv).2.1
  have hdisj := (nodup_append.mp huv).2.2
  have hyu : (y :: u).Nodup := nodup_cons.mpr ⟨fun h ↦ hdisj y h y (mem_cons_self ..) rfl, hu⟩
  have hxv : (x :: v).Nodup :=
    nodup_cons.mpr ⟨fun h ↦ hx (mem_append_right _ (mem_cons_of_mem _ h)),
      (nodup_cons.mp hyv).2⟩
  refine ⟨fun z hz ↦ ?_, fun z hz ↦ ?_, ?_, ?_⟩
  · obtain ⟨u₁, w, rfl⟩ := append_of_mem hz
    obtain _ | ⟨z', w'⟩ := w
    · rw [formPerm_apply_of_eq_append hl (s := x :: u₁) (t := v) (a := z) (b := y) (by simp),
        formPerm_apply_of_eq_cons_concat (s := u₁) (a := z) (b := y) rfl]
    · rw [formPerm_apply_of_eq_append hl (s := x :: u₁) (t := w' ++ y :: v) (a := z) (b := z')
          (by simp),
        formPerm_apply_of_eq_append hyu (s := y :: u₁) (t := w') (a := z) (b := z') (by simp)]
  · obtain ⟨v₁, w, rfl⟩ := append_of_mem hz
    obtain _ | ⟨z', w'⟩ := w
    · rw [formPerm_apply_of_eq_cons_concat (s := u ++ y :: v₁) (a := z) (b := x) (by simp),
        formPerm_apply_of_eq_cons_concat (s := v₁) (a := z) (b := x) rfl]
    · rw [formPerm_apply_of_eq_append hl (s := x :: (u ++ y :: v₁)) (t := w') (a := z) (b := z')
          (by simp),
        formPerm_apply_of_eq_append hxv (s := x :: v₁) (t := w') (a := z) (b := z') (by simp)]
  · obtain _ | ⟨u₀, u'⟩ := u
    · rw [formPerm_apply_of_eq_append hl (s := []) (t := v) (a := x) (b := y) (by simp),
        formPerm_singleton, Equiv.Perm.one_apply]
    · rw [formPerm_apply_of_eq_append hl (s := []) (t := u' ++ y :: v) (a := x) (b := u₀)
          (by simp),
        formPerm_apply_of_eq_append hyu (s := []) (t := u') (a := y) (b := u₀) (by simp)]
  · obtain _ | ⟨v₀, v'⟩ := v
    · rw [formPerm_apply_of_eq_cons_concat (s := u) (a := y) (b := x) (by simp),
        formPerm_singleton, Equiv.Perm.one_apply]
    · rw [formPerm_apply_of_eq_append hl (s := x :: u) (t := v') (a := y) (b := v₀) (by simp),
        formPerm_apply_of_eq_append hxv (s := []) (t := v') (a := x) (b := v₀) (by simp)]

omit [DecidableEq α] in
/-- Every element of a list can be rotated to the front. -/
theorem exists_isRotated_cons {z : α} (hz : z ∈ l) : ∃ t, l ~r z :: t := by
  obtain ⟨P, S, rfl⟩ := append_of_mem hz
  exact ⟨S ++ P, by simpa using (isRotated_append (l := P) (l' := z :: S))⟩

omit [DecidableEq α] in
/-- Two distinct elements of a list: rotate the first to the front, the second is then in the
middle. -/
theorem exists_isRotated_cons_append {x y : α} (hx : x ∈ l) (hy : y ∈ l) (hxy : x ≠ y) :
    ∃ u v, l ~r x :: (u ++ y :: v) := by
  obtain ⟨t, ht⟩ := exists_isRotated_cons hx
  have hyt : y ∈ t := by
    have := ht.mem_iff.mp hy
    rcases mem_cons.mp this with h | h
    · exact absurd h.symm hxy
    · exact h
  obtain ⟨u, v, rfl⟩ := append_of_mem hyt
  exact ⟨u, v, ht⟩

end List

namespace Ribbon

variable {D : Type*} [DecidableEq D]

/-- **Faces and rotations of a ribbon graph.** The faces `L` and the vertex rotations `Vs` (cyclic
lists of darts) are compatible through `β : D → D` (the exchange of the two darts of an edge, or a
twisted version of it during an operation) if the successor of a dart `d` in its face is the
successor of `β d` in its rotation. -/
def FaceCompat (L Vs : List (List D)) (β : D → D) : Prop :=
  ∀ f ∈ L, ∀ r ∈ Vs, ∀ d ∈ f, β d ∈ r → f.formPerm d = r.formPerm (β d)

variable {L L' Vs Vs' : List (List D)} {β : D → D}

/-- Compatibility passes to rotated faces and rotations (in particular to permutations of the
lists of faces and of rotations, and to sublists). -/
theorem FaceCompat.mono (hc : FaceCompat L Vs β)
    (hL : ∀ f' ∈ L', ∃ f ∈ L, f.Nodup ∧ f ~r f') (hV : ∀ r' ∈ Vs', ∃ r ∈ Vs, r.Nodup ∧ r ~r r') :
    FaceCompat L' Vs' β := by
  intro f' hf' r' hr' d hd hβd
  obtain ⟨f, hf, hfn, hff'⟩ := hL f' hf'
  obtain ⟨r, hr, hrn, hrr'⟩ := hV r' hr'
  rw [← List.formPerm_eq_of_isRotated hfn hff', ← List.formPerm_eq_of_isRotated hrn hrr']
  exact hc f hf r hr d (hff'.mem_iff.mpr hd) (hrr'.mem_iff.mpr hβd)

/-- **Deleting a dart fixed by `β`** from all faces and rotations keeps compatibility
(`List.formPerm_erase_apply`). -/
theorem FaceCompat.erase (hc : FaceCompat L Vs β) (hL : ∀ f ∈ L, f.Nodup)
    (hV : ∀ r ∈ Vs, r.Nodup) (hβ : Injective β) {t : D} (ht : β t = t) :
    FaceCompat (L.map (·.erase t)) (Vs.map (·.erase t)) β := by
  intro f' hf' r' hr' d hd hβd
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hf'
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr'
  have hdt : d ≠ t := fun h ↦ by
    subst h
    exact (List.Nodup.not_mem_erase (hL f hf)) hd
  have hdf : d ∈ f := List.mem_of_mem_erase hd
  have hβdt : β d ≠ t := fun h ↦ hdt (hβ (h.trans ht.symm))
  have hβdr : β d ∈ r := List.mem_of_mem_erase hβd
  rw [List.formPerm_erase_apply (hL f hf) hdf hdt, List.formPerm_erase_apply (hV r hr) hβdr hβdt,
    hc f hf r hr d hdf hβdr]
  split_ifs with h
  · have htf : t ∈ f := by
      rw [← h, ← hc f hf r hr d hdf hβdr]
      exact List.formPerm_apply_mem_of_mem hdf
    have htr : t ∈ r := h ▸ List.formPerm_apply_mem_of_mem hβdr
    rw [hc f hf r hr t htf (by rw [ht]; exact htr), ht]
  · rfl

end Ribbon
