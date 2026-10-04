/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.LocallyFinite
import SGA.Foundations.Topology.SemilocallySimplyConnected

/-!
# Local path-connectedness: covers, local homeomorphisms, local contractibility

* `LocallyPathConnectedSpace.of_isOpen_cover`: local path-connectedness is a local property.
* `IsLocalHomeomorph.locallyPathConnectedSpace`: the source of a local homeomorphism to a
  locally path-connected space is locally path-connected.
* `LocallyPathConnectedSpace.of_locallyFinite_isClosed_cover`,
  `LocallyPathConnectedSpace.of_finite_isClosed_cover`: a space covered by a locally finite
  (e.g. finite) family of closed subsets, each locally path-connected, is locally
  path-connected.
* `LocallyContractibleSpace.locallyPathConnectedSpace`: a locally contractible space in the
  classical (weak) sense of mathlib's `LocallyContractibleSpace` (every neighbourhood `U` of `x`
  contains a neighbourhood `V` of `x` whose inclusion into `U` is null-homotopic) is locally
  path-connected. This strengthens the corresponding result for
  `StronglyLocallyContractibleSpace`. Such a space is also semilocally simply connected
  (`LocallyContractibleSpace.semilocallySimplyConnectedSpace`, in
  `Foundations/Topology/SemilocallySimplyConnected.lean`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

open Set Topology Filter CategoryTheory

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A space in which every point has a locally path-connected open neighbourhood is locally
path-connected. -/
theorem LocallyPathConnectedSpace.of_isOpen_cover
    (h : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ LocallyPathConnectedSpace U) :
    LocallyPathConnectedSpace X := by
  refine locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr fun x u hu hxu ↦ ?_
  obtain ⟨U, hU, hxU, _⟩ := h x
  have hx' : (⟨x, hxU⟩ : U) ∈ Subtype.val ⁻¹' u := hxu
  have hN : pathComponentIn (Subtype.val ⁻¹' u) (⟨x, hxU⟩ : U) ∈ 𝓝 (⟨x, hxU⟩ : U) :=
    pathComponentIn_mem_nhds ((hu.preimage continuous_subtype_val).mem_nhds hx')
  refine mem_of_superset (hU.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hN) ?_
  exact ((isPathConnected_pathComponentIn hx').image continuous_subtype_val).subset_pathComponentIn
    ⟨_, mem_pathComponentIn_self hx', rfl⟩
    ((image_mono pathComponentIn_subset).trans (image_preimage_subset _ _))

/-- The source of a local homeomorphism to a locally path-connected space is locally
path-connected. -/
theorem IsLocalHomeomorph.locallyPathConnectedSpace {f : Y → X} (hf : IsLocalHomeomorph f)
    [LocallyPathConnectedSpace X] : LocallyPathConnectedSpace Y :=
  .of_isOpen_cover fun y ↦ by
    obtain ⟨φ, hy, -⟩ := hf y
    have := φ.open_target.locallyPathConnectedSpace
    exact ⟨φ.source, φ.open_source, hy, φ.toHomeomorphSourceTarget.symm.locallyPathConnectedSpace⟩

/-- A space covered by a locally finite family of closed subsets, each of which is locally
path-connected, is locally path-connected. -/
theorem LocallyPathConnectedSpace.of_locallyFinite_isClosed_cover {ι : Type*} {C : ι → Set X}
    (hlf : LocallyFinite C) (hC : ∀ i, IsClosed (C i)) (hcov : ∀ x, ∃ i, x ∈ C i)
    (h : ∀ i, LocallyPathConnectedSpace (C i)) : LocallyPathConnectedSpace X := by
  classical
  refine locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr fun x u hu hxu ↦ ?_
  -- the members of the cover not containing `x` stay away from `x`
  let D : ι → Set X := fun i ↦ if x ∈ C i then ∅ else C i
  have hD : IsClosed (⋃ i, D i) := by
    refine (hlf.subset fun i ↦ ?_).isClosed_iUnion fun i ↦ ?_
    · by_cases hi : x ∈ C i <;> simp [D, hi]
    · by_cases hi : x ∈ C i <;> simp [D, hi, hC i]
  have hxD : x ∈ (⋃ i, D i)ᶜ := by
    simp only [mem_compl_iff, mem_iUnion, not_exists]
    intro i
    by_cases hi : x ∈ C i <;> simp [D, hi]
  -- in each member `C i ∋ x`, the path component of `x` in `u` is a neighbourhood
  have hV : ∀ i, ∃ V ∈ 𝓝 x, ∀ hi : x ∈ C i, V ∩ C i ⊆
      Subtype.val '' pathComponentIn (Subtype.val ⁻¹' u : Set (C i)) ⟨x, hi⟩ := by
    intro i
    by_cases hi : x ∈ C i
    · have hx' : (⟨x, hi⟩ : C i) ∈ Subtype.val ⁻¹' u := hxu
      obtain ⟨V, hV, hVsub⟩ := mem_nhds_subtype _ _ _ |>.mp
        (pathComponentIn_mem_nhds ((hu.preimage continuous_subtype_val).mem_nhds hx'))
      refine ⟨V, hV, fun _ y ⟨hyV, hyC⟩ ↦ ⟨⟨y, hyC⟩, hVsub hyV, rfl⟩⟩
    · exact ⟨univ, univ_mem, fun hi' ↦ absurd hi' hi⟩
  choose V hVx hVsub using hV
  have hfin : {i | x ∈ C i}.Finite := hlf.point_finite x
  refine mem_of_superset (inter_mem (hD.isOpen_compl.mem_nhds hxD)
    ((biInter_mem hfin).mpr fun i _ ↦ hVx i)) ?_
  rintro y ⟨hyD, hyV⟩
  obtain ⟨i, hyi⟩ := hcov y
  have hi : x ∈ C i := by
    by_contra hi
    exact hyD (mem_iUnion.mpr ⟨i, by simpa [D, hi] using hyi⟩)
  have hx' : (⟨x, hi⟩ : C i) ∈ Subtype.val ⁻¹' u := hxu
  have hyV' : y ∈ V i := mem_iInter₂.mp hyV i hi
  refine ((isPathConnected_pathComponentIn hx').image continuous_subtype_val).subset_pathComponentIn
    ⟨_, mem_pathComponentIn_self hx', rfl⟩
    ((image_mono pathComponentIn_subset).trans (image_preimage_subset _ _))
    (hVsub i hi ⟨hyV', hyi⟩)

/-- A space covered by finitely many closed subsets, each of which is locally path-connected, is
locally path-connected. -/
theorem LocallyPathConnectedSpace.of_finite_isClosed_cover {ι : Type*} [Finite ι] {C : ι → Set X}
    (hC : ∀ i, IsClosed (C i)) (hcov : ∀ x, ∃ i, x ∈ C i)
    (h : ∀ i, LocallyPathConnectedSpace (C i)) : LocallyPathConnectedSpace X :=
  .of_locallyFinite_isClosed_cover (locallyFinite_of_finite C) hC hcov h

namespace LocallyContractibleSpace

/-- A locally contractible space (in the classical, weak sense) is locally path-connected. -/
theorem locallyPathConnectedSpace (h : LocallyContractibleSpace X) :
    LocallyPathConnectedSpace X := by
  refine locallyPathConnectedSpace_iff_pathComponentIn_mem_nhds.mpr fun x u hu hxu ↦ ?_
  obtain ⟨V, hVu, hV, c, ⟨F⟩⟩ := h x u (hu.mem_nhds hxu)
  -- every point of `V` is joined to `c` inside `u`
  have hj : ∀ v (hv : v ∈ V), JoinedIn u v c := fun v hv ↦
    ⟨(F.evalAt ⟨v, hv⟩).map continuous_subtype_val, fun t ↦ (F (t, ⟨v, hv⟩)).2⟩
  refine mem_of_superset hV fun v hv ↦ ?_
  exact (hj x (mem_of_mem_nhds hV)).trans (hj v hv).symm

end LocallyContractibleSpace
