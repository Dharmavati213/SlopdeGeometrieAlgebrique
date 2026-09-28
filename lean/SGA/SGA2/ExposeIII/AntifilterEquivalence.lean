/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AntifilterConnectedness
import SGA.SGA2.ExposeIII.Equidimensionality
import SGA.SGA2.ExposeIII.LocallyNoetherianComponents
import Mathlib.Data.List.Chain
import Mathlib.Topology.Connected.Clopen

/-!
# SGA 2, III.3.8: the antifilter component-chain criterion

For a local antifilter on a locally noetherian space, its members have
connected complements if and only if every pair of irreducible components
can be joined by a finite chain whose successive intersections lie outside
the antifilter. The proof uses local finiteness of the components and
does not assume that the whole space is noetherian.
-/

noncomputable section

universe u

open Set TopologicalSpace Topology List Relation

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
theorem III_3_8_ii_implies_i {X : Type u} [TopologicalSpace X]
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
theorem III_3_8_ii_implies_i_connected {X : Type u} [TopologicalSpace X]
    (Ff : ClosedAntifilter X)
    (hii : ∀ {C D : Set X}, C ∈ irreducibleComponents X → D ∈ irreducibleComponents X →
      ReflTransGen (ComponentsAdjacentOutside Ff) C D)
    {Y : Set X} (hY : Ff.mem Y) (hYne : (Yᶜ : Set X).Nonempty) :
    IsConnected (Yᶜ : Set X) :=
  ⟨hYne, III_3_8_ii_implies_i Ff hii hY⟩

/-- The local membership condition imposed on the antifilter in III.3.8. -/
def ClosedAntifilter.IsLocal {X : Type u} [TopologicalSpace X]
    (Ff : ClosedAntifilter X) : Prop :=
  ∀ Y : Set X, IsClosed Y → Ff.LocallyMem Y → Ff.mem Y

/-- A local antifilter contains every locally finite union of its members. -/
theorem ClosedAntifilter.mem_iUnion_of_locallyFinite {X : Type u} [TopologicalSpace X]
    (Ff : ClosedAntifilter X) (hlocal : Ff.IsLocal) {ι : Type*} (f : ι → Set X)
    (hf : LocallyFinite f) (hmem : ∀ i, Ff.mem (f i)) : Ff.mem (⋃ i, f i) := by
  apply hlocal _ (hf.isClosed_iUnion fun i => Ff.isClosed_of_mem (hmem i))
  intro x
  obtain ⟨t, hxt, ht⟩ := hf x
  obtain ⟨U, hUt, hU, hxU⟩ := mem_nhds_iff.mp hxt
  let S : Set ι := {i | (f i ∩ t).Nonempty}
  refine ⟨U, hU, hxU, ⋃₀ (f '' S), ?_, ?_⟩
  · exact Ff.mem_sUnion_finite (ht.image f) (by
      rintro _ ⟨i, _, rfl⟩
      exact hmem i)
  · ext z
    constructor
    · rintro ⟨hzU, hz⟩
      obtain ⟨i, hzi⟩ := mem_iUnion.mp hz
      exact ⟨hzU, mem_sUnion.mpr ⟨f i, mem_image_of_mem f ⟨z, hzi, hUt hzU⟩, hzi⟩⟩
    · rintro ⟨hzU, hz⟩
      obtain ⟨_, ⟨i, _, rfl⟩, hzi⟩ := mem_sUnion.mp hz
      exact ⟨hzU, mem_iUnion.mpr ⟨i, hzi⟩⟩

/-- Pairwise intersections of a locally finite family are locally finite. -/
theorem locallyFinite_pairwise_intersections {X : Type u} [TopologicalSpace X]
    {ι : Type*} {f : ι → Set X} (hf : LocallyFinite f) :
    LocallyFinite (fun p : ι × ι => f p.1 ∩ f p.2) := by
  intro x
  obtain ⟨U, hxU, hU⟩ := hf x
  refine ⟨U, hxU, (hU.prod hU).subset ?_⟩
  rintro p ⟨y, ⟨hy₁, hy₂⟩, hyU⟩
  exact ⟨⟨y, hy₁, hyU⟩, ⟨y, hy₂, hyU⟩⟩

/-- **III.3.8, (i) ⇒ (ii):** in a locally noetherian space, connectedness
of the complements of the members of a local antifilter forces every pair
of irreducible components to be joined outside that antifilter. -/
theorem III_3_8_i_implies_ii {X : Type u} [TopologicalSpace X]
    [LocallyNoetherianSpace X] (Ff : ClosedAntifilter X) (hlocal : Ff.IsLocal)
    (hi : ∀ Y : Set X, Ff.mem Y → IsPreconnected (Yᶜ : Set X))
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ReflTransGen (ComponentsAdjacentOutside Ff) C D := by
  classical
  let S : Set (Set X) := {E | E ∈ irreducibleComponents X ∧
    ReflTransGen (ComponentsAdjacentOutside Ff) C E}
  let T : Set (Set X) := irreducibleComponents X \ S
  have hS : S ⊆ irreducibleComponents X := fun _ h => h.1
  have hT : T ⊆ irreducibleComponents X := fun _ h => h.1
  have hCS : C ∈ S := ⟨hC, ReflTransGen.refl⟩
  by_contra hCD
  have hDT : D ∈ T := ⟨hD, fun h => hCD h.2⟩
  let A := ⋃₀ S
  let B := ⋃₀ T
  let f : S × T → Set X := fun p => p.1.1 ∩ p.2.1
  have hpair : ∀ p : S × T, Ff.mem (f p) := by
    intro ⟨E, G⟩
    by_contra hEG
    have hne : (E.1 ∩ G.1).Nonempty := by
      apply nonempty_iff_ne_empty.mpr
      intro he
      apply hEG
      change Ff.mem (E.1 ∩ G.1)
      rw [he]
      exact Ff.mem_empty
    exact G.2.2 ⟨G.2.1, E.2.2.tail ⟨⟨E.2.1, G.2.1, hne⟩, hEG⟩⟩
  let idx : S × T → irreducibleComponents X × irreducibleComponents X :=
    fun p => (⟨p.1.1, hS p.1.2⟩, ⟨p.2.1, hT p.2.2⟩)
  have hidx : Function.Injective idx := by
    intro p q h
    apply Prod.ext
    · exact Subtype.ext (congrArg (fun r => ((r.1 : irreducibleComponents X) : Set X)) h)
    · exact Subtype.ext (congrArg (fun r => ((r.2 : irreducibleComponents X) : Set X)) h)
  have hf : LocallyFinite f :=
    (locallyFinite_pairwise_intersections locallyFinite_irreducibleComponents).comp_injective hidx
  have hAB : (⋃ p, f p) = A ∩ B := by
    ext x
    constructor
    · intro hx
      obtain ⟨⟨E, G⟩, hxE, hxG⟩ := mem_iUnion.mp hx
      exact ⟨mem_sUnion.mpr ⟨E.1, E.2, hxE⟩, mem_sUnion.mpr ⟨G.1, G.2, hxG⟩⟩
    · rintro ⟨hxA, hxB⟩
      obtain ⟨E, hE, hxE⟩ := mem_sUnion.mp hxA
      obtain ⟨G, hG, hxG⟩ := mem_sUnion.mp hxB
      exact mem_iUnion.mpr ⟨(⟨E, hE⟩, ⟨G, hG⟩), hxE, hxG⟩
  have hY : Ff.mem (A ∩ B) :=
    hAB ▸ Ff.mem_iUnion_of_locallyFinite hlocal f hf hpair
  have hcover : A ∪ B = univ := by
    dsimp [A, B, T]
    rw [← sUnion_union, union_sdiff_self, union_eq_right.mpr hS,
      sUnion_irreducibleComponents]
  have hsep := isPreconnected_iff_subset_of_disjoint_closed.mp (hi _ hY)
    A B (isClosed_sUnion_irreducibleComponents hS)
    (isClosed_sUnion_irreducibleComponents hT)
    (hcover ▸ subset_univ _) (compl_inter_self _)
  obtain ⟨x, hxC, hxunique⟩ := exists_mem_irreducibleComponent_unique hC
  obtain ⟨y, hyD, hyunique⟩ := exists_mem_irreducibleComponent_unique hD
  have hxB : x ∉ B := by
    intro hx
    obtain ⟨E, hE, hxE⟩ := mem_sUnion.mp hx
    exact hE.2 (hxunique E hE.1 hxE ▸ hCS)
  have hyA : y ∉ A := by
    intro hy
    obtain ⟨E, hE, hyE⟩ := mem_sUnion.mp hy
    exact hDT.2 (hyunique E hE.1 hyE ▸ hE)
  rcases hsep with h | h
  · exact hyA (h fun hy => hyA hy.1)
  · exact hxB (h fun hx => hxB hx.2)

/-- **III.3.8:** the complement criterion and the finite component-chain
criterion are equivalent for a local antifilter on a locally noetherian
space. `IsPreconnected` uses the source's convention allowing the empty
space to be connected. -/
theorem III_3_8 {X : Type u} [TopologicalSpace X] [LocallyNoetherianSpace X]
    (Ff : ClosedAntifilter X) (hlocal : Ff.IsLocal) :
    (∀ Y : Set X, Ff.mem Y → IsPreconnected (Yᶜ : Set X)) ↔
      ∀ {C D : Set X}, C ∈ irreducibleComponents X → D ∈ irreducibleComponents X →
        ReflTransGen (ComponentsAdjacentOutside Ff) C D :=
  ⟨fun hi _ _ hC hD => III_3_8_i_implies_ii Ff hlocal hi hC hD,
    fun hii _ hY => III_3_8_ii_implies_i Ff hii hY⟩

/-- The finite list of components in III.3.8, with the actual intersection
condition on every consecutive pair. -/
theorem III_3_8_list {X : Type u} [TopologicalSpace X] [LocallyNoetherianSpace X]
    (Ff : ClosedAntifilter X) (hlocal : Ff.IsLocal)
    (hi : ∀ Y : Set X, Ff.mem Y → IsPreconnected (Yᶜ : Set X))
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ∃ l : List (Set X), l.head? = some C ∧ l.getLast? = some D ∧
      (∀ E ∈ l, E ∈ irreducibleComponents X) ∧
      l.IsChain (fun E G => ¬ Ff.mem (E ∩ G)) := by
  obtain ⟨l, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen
    (III_3_8_i_implies_ii Ff hlocal hi hC hD)
  refine ⟨C :: l, by simp, ?_, ?_, hchain.imp fun _ _ h => h.2⟩
  · rw [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _), hlast]
  · exact isChain_componentsAdjacent_mem (hchain.imp fun _ _ h => h.1) (by simp) hC

end SGA.SGA2.ExposeIII
