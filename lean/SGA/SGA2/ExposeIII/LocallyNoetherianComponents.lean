/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.LocallyFinite

/-!
# Irreducible components of locally noetherian spaces

The irreducible components of a locally noetherian space form a locally
finite family. Every component has a point lying on no other component.
These statements apply without quasi-compactness and provide the
topological input to SGA 2, III.3.8.
-/

noncomputable section

universe u

open Set TopologicalSpace Topology

namespace SGA.SGA2.ExposeIII

/-- Every point has an open noetherian neighborhood. -/
class LocallyNoetherianSpace (X : Type u) [TopologicalSpace X] : Prop where
  exists_open_noetherian (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ NoetherianSpace U

instance {X : Type u} [TopologicalSpace X] [NoetherianSpace X] :
    LocallyNoetherianSpace X where
  exists_open_noetherian x := ⟨univ, isOpen_univ, mem_univ x, inferInstance⟩

/-- Nonempty open traces determine an irreducible component. -/
theorem irreducibleComponent_eq_of_open_trace_eq {X : Type u} [TopologicalSpace X]
    {C D U : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) (hU : IsOpen U)
    (hCU : (C ∩ U).Nonempty) (hDU : (D ∩ U).Nonempty)
    (h : (Subtype.val : U → X) ⁻¹' C = Subtype.val ⁻¹' D) : C = D := by
  have hclosure (E : Set X) (hE : E ∈ irreducibleComponents X)
      (hEU : (E ∩ U).Nonempty) :
      closure ((Subtype.val : U → X) '' (Subtype.val ⁻¹' E)) = E := by
    apply closure_image_preimage_of_isPreirreducible _ hU.isOpenMap_subtype_val _
      _ hE.1.2 (isClosed_of_mem_irreducibleComponents _ hE)
    obtain ⟨x, hxE, hxU⟩ := hEU
    exact ⟨⟨x, hxU⟩, hxE⟩
  rw [← hclosure C hC hCU, ← hclosure D hD hDU, h]

/-- A noetherian open meets only finitely many global irreducible components. -/
theorem finite_irreducibleComponents_meeting_open {X : Type u} [TopologicalSpace X]
    {U : Set X} (hU : IsOpen U) [NoetherianSpace U] :
    {C ∈ irreducibleComponents X | (C ∩ U).Nonempty}.Finite := by
  refine (NoetherianSpace.finite_irreducibleComponents (α := U)).of_injOn
    (f := fun C : Set X => (Subtype.val : U → X) ⁻¹' C) ?_ ?_
  · intro C hC
    apply preimage_mem_irreducibleComponents hC.1 hU.isOpenEmbedding_subtypeVal
    simpa using hC.2
  · intro C hC D hD h
    exact irreducibleComponent_eq_of_open_trace_eq hC.1 hD.1 hU hC.2 hD.2 h

/-- The irreducible components of a locally noetherian space are locally finite. -/
theorem locallyFinite_irreducibleComponents {X : Type u} [TopologicalSpace X]
    [LocallyNoetherianSpace X] :
    LocallyFinite (fun C : irreducibleComponents X => (C : Set X)) := by
  intro x
  obtain ⟨U, hU, hxU, hnoeth⟩ := LocallyNoetherianSpace.exists_open_noetherian x
  let := hnoeth
  refine ⟨U, hU.mem_nhds hxU, ?_⟩
  refine Set.Finite.of_injOn (f := fun C : irreducibleComponents X => (C : Set X))
    ?_ Subtype.val_injective.injOn (finite_irreducibleComponents_meeting_open hU)
  intro C hC
  exact ⟨C.2, hC⟩

/-- Any subfamily of irreducible components of a locally noetherian space
has closed union. -/
theorem isClosed_sUnion_irreducibleComponents {X : Type u} [TopologicalSpace X]
    [LocallyNoetherianSpace X] {S : Set (Set X)} (hS : S ⊆ irreducibleComponents X) :
    IsClosed (⋃₀ S) := by
  let f : S → irreducibleComponents X := fun C => ⟨C.1, hS C.2⟩
  have hf : Function.Injective f := by
    intro C D h
    exact Subtype.ext (congrArg (fun E : irreducibleComponents X => (E : Set X)) h)
  have hfin := locallyFinite_irreducibleComponents.comp_injective hf
  have hclosed := hfin.isClosed_iUnion fun C =>
    isClosed_of_mem_irreducibleComponents C.1 (hS C.2)
  simpa only [Function.comp_def, f, iUnion_coe_set, sUnion_eq_biUnion] using hclosed

/-- Every irreducible component has a point belonging to no other component. -/
theorem exists_mem_irreducibleComponent_unique {X : Type u} [TopologicalSpace X]
    [LocallyNoetherianSpace X] {C : Set X} (hC : C ∈ irreducibleComponents X) :
    ∃ x ∈ C, ∀ D ∈ irreducibleComponents X, x ∈ D → D = C := by
  obtain ⟨x, hxC⟩ := hC.1.nonempty
  obtain ⟨U, hU, hxU, hnoeth⟩ := LocallyNoetherianSpace.exists_open_noetherian x
  let := hnoeth
  let T : Set U := Subtype.val ⁻¹' C
  have hT : T ∈ irreducibleComponents U :=
    preimage_mem_irreducibleComponents hC hU.isOpenEmbedding_subtypeVal
      (by simpa using (show (C ∩ U).Nonempty from ⟨x, hxC, hxU⟩))
  have hnot : ¬ T ⊆ ⋃₀ (irreducibleComponents U \ {T}) := by
    intro hsub
    have hmem := mem_of_subset_sUnion_irreducibleComponents T hT
      (irreducibleComponents U \ {T}) NoetherianSpace.finite_irreducibleComponents.sdiff
      sdiff_subset hsub
    exact hmem.2 (mem_singleton T)
  obtain ⟨y, hyT, hyothers⟩ := not_subset.mp hnot
  refine ⟨y.1, hyT, ?_⟩
  intro D hD hyD
  have hDU : (D ∩ U).Nonempty := ⟨y.1, hyD, y.2⟩
  have hDtrace : (Subtype.val : U → X) ⁻¹' D ∈ irreducibleComponents U :=
    preimage_mem_irreducibleComponents hD hU.isOpenEmbedding_subtypeVal (by simpa using hDU)
  have htrace : (Subtype.val : U → X) ⁻¹' D = T := by
    by_contra hne
    exact hyothers (mem_sUnion.mpr ⟨_, ⟨hDtrace, by simpa using hne⟩, hyD⟩)
  exact irreducibleComponent_eq_of_open_trace_eq hD hC hU hDU ⟨x, hxC, hxU⟩ htrace

end SGA.SGA2.ExposeIII
