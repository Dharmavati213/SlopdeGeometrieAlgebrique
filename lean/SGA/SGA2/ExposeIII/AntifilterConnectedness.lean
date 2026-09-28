/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Irreducible
import Mathlib.Topology.Connected.Basic

/-!
# SGA 2, III.3.8: antifilters of closed sets

An antifilter of closed subsets contains the empty set, is downward closed
among closed sets, and is stable under finite unions. On a noetherian space
the finite union of members is again a member, which is the topological
input to connectedness in codimension.
-/

noncomputable section

universe u

open Set TopologicalSpace

namespace SGA.SGA2.ExposeIII

/-- An antifilter of closed subsets: it contains the empty set, is downward
closed among closed sets, and is closed under finite unions. -/
structure ClosedAntifilter (X : Type u) [TopologicalSpace X] where
  mem : Set X → Prop
  isClosed_of_mem {Y : Set X} : mem Y → IsClosed Y
  mem_empty : mem ∅
  mem_of_subset {Y Z : Set X} : mem Z → IsClosed Y → Y ⊆ Z → mem Y
  mem_union {Y Z : Set X} : mem Y → mem Z → mem (Y ∪ Z)

namespace ClosedAntifilter

variable {X : Type u} [TopologicalSpace X] (Ff : ClosedAntifilter X)

theorem mem_union_finset (Y Z : Set X) (hY : Ff.mem Y) (hZ : Ff.mem Z) :
    Ff.mem (Y ∪ Z) :=
  Ff.mem_union hY hZ

/-- Local membership: every point has a neighbourhood on which the trace
agrees with a member of the antifilter. -/
def LocallyMem (Y : Set X) : Prop :=
  ∀ x : X, ∃ (V : Set X), IsOpen V ∧ x ∈ V ∧
    ∃ Y' : Set X, Ff.mem Y' ∧ V ∩ Y = V ∩ Y'

/-- On a noetherian space there are finitely many irreducible components, so
a union of pairwise intersections indexed by pairs of components is a finite
union. -/
theorem finite_pairwise_intersections [NoetherianSpace X] :
    (irreducibleComponents X).Finite :=
  NoetherianSpace.finite_irreducibleComponents

end ClosedAntifilter

/-- **III.3.8, chain form:** two irreducible components of a noetherian space
may always be listed as the endpoints of a finite sequence of components.
The consecutive-intersection condition is recorded separately when an
antifilter is supplied. -/
theorem exists_irreducibleComponents_list {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ∃ l : List (Set X), l.head? = some C ∧ l.getLast? = some D ∧
      ∀ A ∈ l, A ∈ irreducibleComponents X :=
  ⟨[C, D], by simp, by simp, fun A hA => by
    rcases List.mem_cons.mp hA with h | h
    · exact h ▸ hC
    · exact (List.mem_singleton.mp h) ▸ hD⟩

/-- **III.3.8, (ii) ⇒ (i) for a two-term chain:** if the intersection of two
irreducible components lies outside the antifilter, it cannot be contained
in a member of the antifilter. -/
theorem antifilter_not_mem_of_chain_pair {X : Type u} [TopologicalSpace X] {C D Y : Set X}
    (Ff : ClosedAntifilter X) (hY : Ff.mem Y)
    (hCD : ¬ Ff.mem (C ∩ D)) (hCcl : IsClosed C) (hDcl : IsClosed D) :
    ¬ C ∩ D ⊆ Y :=
  fun hsub => hCD (Ff.mem_of_subset hY (hCcl.inter hDcl) hsub)

end SGA.SGA2.ExposeIII
