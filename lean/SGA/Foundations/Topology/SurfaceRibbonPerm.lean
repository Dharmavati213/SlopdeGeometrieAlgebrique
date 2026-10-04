/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfaceContract
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Data.List.Iterate

/-!
# Ribbon graphs from permutations

A ribbon graph on a finite set of darts `ι × Bool` is determined by its rotation, a permutation
`ρ` of the darts whose cycles are the vertices; its faces are the cycles of `d ↦ ρ (flip d)`
(`Ribbon.facePerm`). Writing each cycle as the list `[d, p d, p (p d), …]` (`Ribbon.cyc`), a list
of representatives of the cycles of `ρ` and one of the cycles of `facePerm ρ` give a ribbon graph
in the sense of `Ribbon.IsRibbon` (`Ribbon.isRibbon_of_perm`).

## References

* [B. Mohar, C. Thomassen, *Graphs on Surfaces*, §3.2][mohar2001]
-/

open Function

namespace Ribbon

section Cyc

variable {α : Type*} [Finite α]

omit [Finite α] in
lemma isPeriodicPt_perm (p : Equiv.Perm α) (d : α) : IsPeriodicPt p (orderOf p) d := by
  change (⇑p)^[orderOf p] d = d
  rw [Equiv.Perm.iterate_eq_pow, pow_orderOf_eq_one]
  rfl

lemma minimalPeriod_perm_pos (p : Equiv.Perm α) (d : α) : 0 < minimalPeriod p d :=
  (isPeriodicPt_perm p d).minimalPeriod_pos (orderOf_pos p)

/-- The cycle of `d` under a permutation `p`, as the list `[d, p d, p (p d), …]` whose length is
the minimal period of `d` (so `[d]` for a fixed point). -/
noncomputable def cyc (p : Equiv.Perm α) (d : α) : List α := List.iterate p d (minimalPeriod p d)

variable {p : Equiv.Perm α} {d : α}

omit [Finite α] in
lemma length_cyc : (cyc p d).length = minimalPeriod p d := List.length_iterate ..

lemma cyc_ne_nil : cyc p d ≠ [] := by
  rw [cyc, Ne, List.iterate_eq_nil]
  exact (minimalPeriod_perm_pos p d).ne'

omit [Finite α] in
lemma nodup_cyc : (cyc p d).Nodup := by
  rw [cyc, ← List.range_map_iterate]
  refine List.Nodup.map_on (fun i hi j hj h ↦ ?_) List.nodup_range
  exact iterate_injOn_Iio_minimalPeriod (List.mem_range.mp hi) (List.mem_range.mp hj) h

lemma mem_cyc {y : α} : y ∈ cyc p d ↔ p.SameCycle d y := by
  rw [cyc, List.mem_iterate]
  constructor
  · rintro ⟨m, -, rfl⟩
    exact ⟨m, by rw [zpow_natCast, ← Equiv.Perm.iterate_eq_pow]⟩
  · intro h
    obtain ⟨i, -, hi⟩ := h.exists_pow_eq'
    refine ⟨i % minimalPeriod p d, Nat.mod_lt _ (minimalPeriod_perm_pos p d), ?_⟩
    rw [iterate_mod_minimalPeriod_eq, Equiv.Perm.iterate_eq_pow, hi]

lemma self_mem_cyc : d ∈ cyc p d := mem_cyc.mpr (Equiv.Perm.SameCycle.refl _ _)

omit [Finite α] in
lemma formPerm_cyc [DecidableEq α] {y : α} (hy : y ∈ cyc p d) : (cyc p d).formPerm y = p y := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  rw [List.formPerm_apply_getElem _ nodup_cyc]
  simp only [cyc, List.getElem_iterate, List.length_iterate]
  rw [iterate_mod_minimalPeriod_eq, iterate_succ_apply']

end Cyc

variable {ι : Type*} [DecidableEq ι] [Finite ι]

/-- The exchange `flip` of the two darts of an edge, as a permutation. -/
def flipEquiv : Equiv.Perm (ι × Bool) := ⟨flip, flip, flip_flip, flip_flip⟩

omit [DecidableEq ι] [Finite ι] in
@[simp] lemma flipEquiv_apply (d : ι × Bool) : flipEquiv d = flip d := rfl

/-- The face permutation `d ↦ ρ (flip d)` of the ribbon graph with rotation `ρ`. -/
def facePerm (ρ : Equiv.Perm (ι × Bool)) : Equiv.Perm (ι × Bool) := ρ * flipEquiv

omit [DecidableEq ι] [Finite ι] in
@[simp] lemma facePerm_apply (ρ : Equiv.Perm (ι × Bool)) (d : ι × Bool) :
    facePerm ρ d = ρ (flip d) := rfl

omit [DecidableEq ι] in
lemma nodup_flatten_map_cyc (p : Equiv.Perm (ι × Bool)) {Vr : List (ι × Bool)} (hVn : Vr.Nodup)
    (hV' : ∀ v ∈ Vr, ∀ w ∈ Vr, p.SameCycle v w → v = w) : (Vr.map (cyc p)).flatten.Nodup := by
  rw [List.nodup_flatten]
  refine ⟨fun l hl ↦ ?_, ?_⟩
  · obtain ⟨v, -, rfl⟩ := List.mem_map.mp hl
    exact nodup_cyc
  · rw [List.pairwise_map]
    refine hVn.pairwise_of_forall_ne fun v hv w hw hvw ↦ ?_
    rw [List.disjoint_left]
    intro d hdv hdw
    exact hvw (hV' v hv w hw ((mem_cyc.mp hdv).trans (mem_cyc.mp hdw).symm))

omit [DecidableEq ι] in
lemma mem_flatten_map_cyc (p : Equiv.Perm (ι × Bool)) {Vr : List (ι × Bool)}
    (hV : ∀ d, ∃ v ∈ Vr, p.SameCycle v d) (d : ι × Bool) : d ∈ (Vr.map (cyc p)).flatten := by
  obtain ⟨v, hv, hvd⟩ := hV d
  exact List.mem_flatten.mpr ⟨cyc p v, List.mem_map_of_mem hv, mem_cyc.mpr hvd⟩

/-- **Ribbon graphs from permutations.** Given the rotation `ρ` (a permutation of the darts whose
cycles are the vertices), a list `Vr` with exactly one dart in each cycle of `ρ` and a list `Fr`
with exactly one dart in each cycle of `facePerm ρ`, the cycles of `ρ` and of `facePerm ρ` through
these darts form a ribbon graph. -/
theorem isRibbon_of_perm (ρ : Equiv.Perm (ι × Bool)) {Vr Fr : List (ι × Bool)}
    (hV : ∀ d, ∃ v ∈ Vr, ρ.SameCycle v d) (hVn : Vr.Nodup)
    (hV' : ∀ v ∈ Vr, ∀ w ∈ Vr, ρ.SameCycle v w → v = w)
    (hF : ∀ d, ∃ f ∈ Fr, (facePerm ρ).SameCycle f d) (hFn : Fr.Nodup)
    (hF' : ∀ v ∈ Fr, ∀ w ∈ Fr, (facePerm ρ).SameCycle v w → v = w) :
    IsRibbon (Vr.map (cyc ρ)) (Fr.map (cyc (facePerm ρ))) where
  nodup := nodup_flatten_map_cyc ρ hVn hV'
  flip_mem d _ := mem_flatten_map_cyc ρ hV (flip d)
  perm := (List.perm_ext_iff_of_nodup (nodup_flatten_map_cyc _ hFn hF')
    (nodup_flatten_map_cyc ρ hVn hV')).mpr fun d ↦
      ⟨fun _ ↦ mem_flatten_map_cyc ρ hV d, fun _ ↦ mem_flatten_map_cyc _ hF d⟩
  ne_nil f hf := by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hf
    exact cyc_ne_nil
  compat f hf r hr d hd hfd := by
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hf
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hr
    rw [formPerm_cyc hd, formPerm_cyc hfd, facePerm_apply]

end Ribbon
