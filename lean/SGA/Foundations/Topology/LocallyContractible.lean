/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Strongly locally contractible spaces: examples and local nature

* Real locally convex topological vector spaces (e.g. `ℂⁿ`) are strongly locally contractible
  (`LocallyConvexSpace.toStronglyLocallyContractibleSpace`).
* Strong local contractibility is a local property
  (`StronglyLocallyContractibleSpace.of_isOpen_cover`), so it passes to the source of a local
  homeomorphism (`IsLocalHomeomorph.stronglyLocallyContractibleSpace`).

Together with `StronglyLocallyContractibleSpace.semilocallySimplyConnectedSpace` and
`StronglyLocallyContractibleSpace.instLocallyPathConnectedSpace`, this shows that a space which is
locally homeomorphic to `ℂⁿ` (a complex manifold, e.g. the complex points of a smooth complex
variety) is locally path-connected and semilocally simply connected.
-/

open Topology Set Filter

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A real locally convex topological vector space is strongly locally contractible: convex
neighbourhoods are contractible. -/
instance (priority := 100) LocallyConvexSpace.toStronglyLocallyContractibleSpace
    {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [LocallyConvexSpace ℝ E] : StronglyLocallyContractibleSpace E :=
  .of_bases (fun x ↦ LocallyConvexSpace.convex_basis (𝕜 := ℝ) x)
    fun _ _ hs ↦ hs.2.contractibleSpace (nonempty_of_mem (mem_of_mem_nhds hs.1))

/-- A space in which every point has a strongly locally contractible open neighbourhood is
strongly locally contractible. -/
theorem StronglyLocallyContractibleSpace.of_isOpen_cover
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ StronglyLocallyContractibleSpace U) :
    StronglyLocallyContractibleSpace X where
  contractible_basis x := by
    obtain ⟨U, hU, hxU, _⟩ := h x
    rw [hasBasis_self]
    intro t ht
    have ht' : Subtype.val ⁻¹' t ∈ 𝓝 (⟨x, hxU⟩ : U) :=
      continuous_subtype_val.continuousAt.preimage_mem_nhds ht
    obtain ⟨s, ⟨hs, hsc⟩, hst⟩ := (contractible_basis (⟨x, hxU⟩ : U)).mem_iff.mp ht'
    exact ⟨Subtype.val '' s, hU.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hs,
      (IsEmbedding.subtypeVal.homeomorphImage s).symm.contractibleSpace,
      image_subset_iff.mpr hst⟩

/-- The source of a local homeomorphism to a strongly locally contractible space is strongly
locally contractible. -/
theorem IsLocalHomeomorph.stronglyLocallyContractibleSpace {f : Y → X}
    (hf : IsLocalHomeomorph f) [StronglyLocallyContractibleSpace X] :
    StronglyLocallyContractibleSpace Y :=
  .of_isOpen_cover fun y ↦ by
    obtain ⟨φ, hy, -⟩ := hf y
    have := φ.open_target.stronglyLocallyContractibleSpace
    exact ⟨φ.source, φ.open_source, hy,
      φ.toHomeomorphSourceTarget.isOpenEmbedding.stronglyLocallyContractibleSpace⟩
