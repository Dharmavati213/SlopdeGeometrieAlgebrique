/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.AntifilterConnectedness
import SGA.SGA2.ExposeIII.Equidimensionality
import Mathlib.Data.List.Chain
import Mathlib.Topology.Connected.Clopen

/-!
# SGA 2, III.3.8: dual graph of irreducible components

On a connected noetherian space any two irreducible components may be
joined by a finite chain with consecutive nonempty intersections. This is
the purely topological input to III.3.8 (ii).
-/

noncomputable section

universe u

open Set TopologicalSpace List Relation

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- Adjacent irreducible components. -/
def ComponentsAdjacent {X : Type u} [TopologicalSpace X] (C D : Set X) : Prop :=
  C ∈ irreducibleComponents X ∧ D ∈ irreducibleComponents X ∧ (C ∩ D).Nonempty

/-- Vertices of an adjacency chain are irreducible components, given the head. -/
theorem isChain_componentsAdjacent_mem {X : Type u} [TopologicalSpace X]
    {l : List (Set X)} (h : IsChain ComponentsAdjacent l) {C : Set X}
    (hC : l.head? = some C) (hCmem : C ∈ irreducibleComponents X) :
    ∀ A ∈ l, A ∈ irreducibleComponents X := by
  induction h generalizing C with
  | nil => intro A hA; cases hA
  | singleton A =>
    intro B hB
    have hA : A = C := Option.some.inj (by simpa using hC)
    have : B = A := List.mem_singleton.mp hB
    exact this ▸ hA ▸ hCmem
  | cons_cons hab rest ih =>
    intro E hE
    rcases List.mem_cons.mp hE with h | h
    · exact h ▸ hab.1
    · exact ih (by simp) hab.2.1 E h

/-- On a connected noetherian space, any two irreducible components are
joined by a chain of components with consecutive nonempty intersections. -/
theorem exists_irreducibleComponents_connected_chain {X : Type u}
    [TopologicalSpace X] [NoetherianSpace X] [ConnectedSpace X]
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ReflTransGen ComponentsAdjacent C D := by
  let S : Set (Set X) :=
    {E | E ∈ irreducibleComponents X ∧ ReflTransGen ComponentsAdjacent C E}
  have hCmem : C ∈ S := ⟨hC, ReflTransGen.refl⟩
  have hSfin : S.Finite :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).subset fun _ h => h.1
  have hTfin : (irreducibleComponents X \ S).Finite :=
    (NoetherianSpace.finite_irreducibleComponents (α := X)).subset fun _ h => h.1
  let Y := ⋃₀ S
  let Z := ⋃₀ (irreducibleComponents X \ S)
  have hYcl : IsClosed Y := by
    simpa [Y, sUnion_eq_biUnion] using
      hSfin.isClosed_biUnion fun E hE => isClosed_of_mem_irreducibleComponents E hE.1
  have hZcl : IsClosed Z := by
    simpa [Z, sUnion_eq_biUnion] using
      hTfin.isClosed_biUnion fun E hE => isClosed_of_mem_irreducibleComponents E hE.1
  have hcover : Y ∪ Z = univ := by
    ext x
    constructor
    · intro; exact mem_univ _
    · intro
      have hx : x ∈ ⋃₀ irreducibleComponents X := by
        rw [sUnion_irreducibleComponents]; exact mem_univ _
      obtain ⟨E, hE, hxE⟩ := mem_sUnion.mp hx
      by_cases hS' : E ∈ S
      · exact Or.inl (mem_sUnion.mpr ⟨E, hS', hxE⟩)
      · exact Or.inr (mem_sUnion.mpr ⟨E, ⟨hE, hS'⟩, hxE⟩)
  have hdisj : Disjoint Y Z := by
    rw [disjoint_iff_inter_eq_empty]
    ext x
    constructor
    · intro hx
      obtain ⟨E, hE, hxE⟩ := mem_sUnion.mp hx.1
      obtain ⟨F, hF, hxF⟩ := mem_sUnion.mp hx.2
      have hinter : (E ∩ F).Nonempty := ⟨x, hxE, hxF⟩
      have hFreach : ReflTransGen ComponentsAdjacent C F :=
        ReflTransGen.tail hE.2 ⟨hE.1, hF.1, hinter⟩
      exact (hF.2 ⟨hF.1, hFreach⟩).elim
    · intro hx; exact hx.elim
  have hYne : Y.Nonempty :=
    ⟨hC.1.nonempty.some, mem_sUnion.mpr ⟨C, hCmem, hC.1.nonempty.some_mem⟩⟩
  have hYopen : IsOpen Y := by
    have : Y = Zᶜ := by
      ext x
      constructor
      · intro hx hxZ
        exact hdisj.le_bot ⟨hx, hxZ⟩
      · intro hx
        have : x ∈ Y ∪ Z := by rw [hcover]; exact mem_univ _
        exact this.resolve_right hx
    simpa [this] using hZcl.isOpen_compl
  have hYuniv : Y = univ :=
    (isClopen_iff.mp ⟨hYcl, hYopen⟩).resolve_left hYne.ne_empty
  have hDmem : D ∈ S := by
    obtain ⟨x, hxD⟩ := hD.1.nonempty
    have hxY : x ∈ Y := by rw [hYuniv]; exact mem_univ _
    obtain ⟨E, hE, hxE⟩ := mem_sUnion.mp hxY
    have hinter : (E ∩ D).Nonempty := ⟨x, hxE, hxD⟩
    exact ⟨hD, ReflTransGen.tail hE.2 ⟨hE.1, hD, hinter⟩⟩
  exact hDmem.2

/-- Adjacency outside an antifilter: components meet in a set not in `Ff`. -/
def ComponentsAdjacentOutside {X : Type u} [TopologicalSpace X]
    (Ff : ClosedAntifilter X) (C D : Set X) : Prop :=
  ComponentsAdjacent C D ∧ ¬ Ff.mem (C ∩ D)

/-- A nonempty open trace of an irreducible set is irreducible. -/
theorem isIrreducible_inter_isOpen {X : Type u} [TopologicalSpace X]
    {C U : Set X} (hC : IsIrreducible C) (hU : IsOpen U)
    (hne : (C ∩ U).Nonempty) : IsIrreducible (C ∩ U) := by
  have := Subtype.irreducibleSpace hC
  let V : Set C := Subtype.val ⁻¹' U
  have hVopen : IsOpen V := hU.preimage continuous_subtype_val
  have hVpre : IsPreirreducible V :=
    (IrreducibleSpace.isIrreducible_univ (C : Type u)).isPreirreducible.open_subset
      hVopen (subset_univ _)
  have hVne : V.Nonempty := by
    obtain ⟨x, hx⟩ := hne
    exact ⟨⟨x, hx.1⟩, hx.2⟩
  have hVirr : IsIrreducible V := ⟨hVne, hVpre⟩
  have himg : IsIrreducible (Subtype.val '' V) :=
    hVirr.image Subtype.val (continuous_subtype_val.continuousOn.mono (subset_univ _))
  have hVU : Subtype.val '' V = C ∩ U := by
    ext z
    simp [V]
  exact hVU ▸ himg

/-- **III.3.8, (ii) ⇒ (i):** if every pair of components is joinable by a
chain whose consecutive intersections lie outside the antifilter, then
the complement of every member is connected. -/
theorem III_3_8_ii_implies_i {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    (Ff : ClosedAntifilter X)
    (hii : ∀ {C D : Set X}, C ∈ irreducibleComponents X → D ∈ irreducibleComponents X →
      ReflTransGen (ComponentsAdjacentOutside Ff) C D)
    {Y : Set X} (hY : Ff.mem Y) :
    IsPreconnected (Yᶜ : Set X) := by
  have hYcl : IsClosed Y := Ff.isClosed_of_mem hY
  refine isPreconnected_of_forall_pair ?_
  intro x hx y hy
  let Cx := irreducibleComponent x
  let Cy := irreducibleComponent y
  have hCx : Cx ∈ irreducibleComponents X :=
    irreducibleComponent_mem_irreducibleComponents x
  have hCy : Cy ∈ irreducibleComponents X :=
    irreducibleComponent_mem_irreducibleComponents y
  have hchain := hii hCx hCy
  have hCyne : (Cy ∩ Yᶜ).Nonempty := ⟨y, mem_irreducibleComponent, hy⟩
  have htrace :
      (Cx ∩ Yᶜ).Nonempty ∧
        ∃ S ⊆ (Yᶜ : Set X), IsConnected S ∧ Cx ∩ Yᶜ ⊆ S ∧ Cy ∩ Yᶜ ⊆ S := by
    refine ReflTransGen.head_induction_on hchain ?refl ?head
    · exact ⟨hCyne, Cy ∩ Yᶜ, inter_subset_right,
        (isIrreducible_inter_isOpen hCy.1 hYcl.isOpen_compl hCyne).isConnected,
        subset_rfl, subset_rfl⟩
    · intro A E hAE hEtoCy ih
      obtain ⟨hEne, S, hSU, hSconn, hES, hCyS⟩ := ih
      have hAcomp : A ∈ irreducibleComponents X := hAE.1.1
      have hEcomp : E ∈ irreducibleComponents X := hAE.1.2.1
      have hmeet : (A ∩ E ∩ Yᶜ).Nonempty :=
        not_subset.mp (antifilter_not_mem_of_chain_pair Ff hY hAE.2
          (isClosed_of_mem_irreducibleComponents A hAcomp)
          (isClosed_of_mem_irreducibleComponents E hEcomp))
      have hAne : (A ∩ Yᶜ).Nonempty :=
        hmeet.mono fun z hz => ⟨hz.1.1, hz.2⟩
      have hAconn : IsConnected (A ∩ Yᶜ) :=
        (isIrreducible_inter_isOpen hAcomp.1 hYcl.isOpen_compl hAne).isConnected
      let S' := (A ∩ Yᶜ) ∪ S
      have hmeet' : ((A ∩ Yᶜ) ∩ S).Nonempty := by
        obtain ⟨z, hzAE, hzU⟩ := hmeet
        exact ⟨z, ⟨⟨hzAE.1, hzU⟩, hES ⟨hzAE.2, hzU⟩⟩⟩
      refine ⟨hAne, S', ?_, hAconn.union hmeet' hSconn, subset_union_left,
        hCyS.trans subset_union_right⟩
      intro z hz
      rcases hz with hz | hz
      · exact hz.2
      · exact hSU hz
  obtain ⟨_, S, hSU, hSconn, hxS, hyS⟩ := htrace
  exact ⟨S, hSU, hxS ⟨mem_irreducibleComponent, hx⟩,
    hyS ⟨mem_irreducibleComponent, hy⟩, hSconn.isPreconnected⟩

/-- If the complement is nonempty, (ii) ⇒ (i) gives a connected complement. -/
theorem III_3_8_ii_implies_i_connected {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    (Ff : ClosedAntifilter X)
    (hii : ∀ {C D : Set X}, C ∈ irreducibleComponents X → D ∈ irreducibleComponents X →
      ReflTransGen (ComponentsAdjacentOutside Ff) C D)
    {Y : Set X} (hY : Ff.mem Y) (hYne : (Yᶜ : Set X).Nonempty) :
    IsConnected (Yᶜ : Set X) :=
  ⟨hYne, III_3_8_ii_implies_i Ff hii hY⟩

end SGA.SGA2.ExposeIII

