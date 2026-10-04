/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Homotopy.LocallyContractible
import SGA.Foundations.Topology.PathConnectedHelpersBasic

/-!
# Semilocally simply connected spaces

A topological space `X` is *semilocally simply connected* if every point `x` has a neighbourhood
`U` such that every loop at `x` in `U` is null-homotopic in `X`, i.e. the map
`π₁(U, x) → π₁(X, x)` is trivial. Together with local path-connectedness this is the hypothesis
under which covering spaces of `X` are classified by the fundamental groupoid.

## Main definitions

* `SemilocallySimplyConnectedSpace X`: the class of semilocally simply connected spaces.
* `IsRelSimplyConnected s`: any two paths in `s` with the same endpoints are homotopic in `X`.

## Main results

* `exists_isRelSimplyConnected_subset`: in a locally path-connected, semilocally simply connected
  space, the open, path-connected, relatively simply connected sets form a basis of the topology.
* Simply connected spaces are semilocally simply connected, and so are locally contractible
  spaces in the classical (weak) sense of mathlib's `LocallyContractibleSpace`
  (`LocallyContractibleSpace.semilocallySimplyConnectedSpace`), in particular strongly locally
  contractible spaces (the instance
  `StronglyLocallyContractibleSpace.semilocallySimplyConnectedSpace`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
-/

open CategoryTheory Topology Set Filter

universe u

variable {X : Type*} [TopologicalSpace X]

/-- A topological space is *semilocally simply connected* if every point `x` has a neighbourhood
`U` such that every loop at `x` with values in `U` is null-homotopic in `X`. -/
class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where
  exists_nhds_homotopic_refl (x : X) :
    ∃ U ∈ 𝓝 x, ∀ γ : Path x x, range γ ⊆ U → γ.Homotopic (Path.refl x)

/-- A set `s` is *relatively simply connected* (in `X`) if any two paths with values in `s` and
the same endpoints are homotopic in `X`. -/
def IsRelSimplyConnected (s : Set X) : Prop :=
  ∀ ⦃x y : X⦄ (γ γ' : Path x y), range γ ⊆ s → range γ' ⊆ s → γ.Homotopic γ'

namespace IsRelSimplyConnected

variable {s t : Set X}

lemma mono (h : IsRelSimplyConnected t) (hst : s ⊆ t) : IsRelSimplyConnected s :=
  fun _ _ γ γ' hγ hγ' ↦ h γ γ' (hγ.trans hst) (hγ'.trans hst)

/-- The homotopy classes of two paths in a relatively simply connected set with the same
endpoints agree. -/
lemma mk_eq (h : IsRelSimplyConnected s) {x y : X} {γ γ' : Path x y} (hγ : range γ ⊆ s)
    (hγ' : range γ' ⊆ s) : Path.Homotopic.Quotient.mk γ = .mk γ' :=
  Path.Homotopic.Quotient.eq.mpr (h γ γ' hγ hγ')

/-- If all loops in the path-connected set `s` based at some point `x ∈ s` are null-homotopic
in `X`, then `s` is relatively simply connected. -/
lemma of_isPathConnected {x : X} (hs : IsPathConnected s) (hx : x ∈ s)
    (h : ∀ γ : Path x x, range γ ⊆ s → γ.Homotopic (Path.refl x)) : IsRelSimplyConnected s := by
  intro y z γ γ' hγ hγ'
  have hy : y ∈ s := hγ ⟨0, γ.source⟩
  let α := (hs.joinedIn x hx y hy).somePath
  have hα : range α ⊆ s := range_subset_iff.mpr (hs.joinedIn x hx y hy).somePath_mem
  have hloop := h ((α.trans γ).trans (α.trans γ').symm) (by
    simp only [Path.trans_range, Path.symm_range]
    exact union_subset (union_subset hα hγ) (union_subset hα hγ'))
  rw [← Path.Homotopic.Quotient.eq] at hloop ⊢
  let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y :=
    FundamentalGroupoid.fromPath (.mk α)
  let g : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z :=
    FundamentalGroupoid.fromPath (.mk γ)
  let g' : FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z :=
    FundamentalGroupoid.fromPath (.mk γ')
  have h : (a ≫ g) ≫ Groupoid.inv (a ≫ g') = 𝟙 _ := hloop
  rwa [Groupoid.inv_eq_inv, comp_inv_eq_id, cancel_epi] at h

end IsRelSimplyConnected

/-- In a locally path-connected, semilocally simply connected space, every neighbourhood of a
point contains an open, path-connected, relatively simply connected neighbourhood. -/
theorem exists_isRelSimplyConnected_subset [LocallyPathConnectedSpace X]
    [SemilocallySimplyConnectedSpace X] {x : X} {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ V ⊆ U, IsOpen V ∧ x ∈ V ∧ IsPathConnected V ∧ IsRelSimplyConnected V := by
  obtain ⟨W, hW, hWx⟩ := SemilocallySimplyConnectedSpace.exists_nhds_homotopic_refl x
  have hxi : x ∈ interior (U ∩ W) := mem_interior_iff_mem_nhds.mpr (inter_mem hU hW)
  set V := pathComponentIn (interior (U ∩ W)) x
  have hVUW : V ⊆ U ∩ W := pathComponentIn_subset.trans interior_subset
  refine ⟨V, hVUW.trans inter_subset_left, isOpen_interior.pathComponentIn x,
    mem_pathComponentIn_self hxi, isPathConnected_pathComponentIn hxi, ?_⟩
  exact .of_isPathConnected (isPathConnected_pathComponentIn hxi) (mem_pathComponentIn_self hxi)
    fun γ hγ ↦ hWx γ (hγ.trans (hVUW.trans inter_subset_right))

/-- A simply connected space is semilocally simply connected. -/
instance (priority := 100) SimplyConnectedSpace.semilocallySimplyConnectedSpace
    [SimplyConnectedSpace X] : SemilocallySimplyConnectedSpace X where
  exists_nhds_homotopic_refl _ :=
    ⟨univ, univ_mem, fun _ _ ↦ SimplyConnectedSpace.paths_homotopic _ _⟩

/-- A loop in a simply connected subspace is null-homotopic. -/
lemma Path.homotopic_refl_of_range_subset {s : Set X} (hs : IsSimplyConnected s) {x : X}
    (γ : Path x x) (hγ : range γ ⊆ s) : γ.Homotopic (Path.refl x) :=
  have := hs.simplyConnectedSpace
  Path.Homotopic.of_codRestrict (h := hγ) (h' := range_subset_iff.mpr fun _ ↦ hγ ⟨0, γ.source⟩)
    (SimplyConnectedSpace.paths_homotopic _ _)

/-- A locally contractible space (in the classical, weak sense of mathlib's
`LocallyContractibleSpace`: every neighbourhood `U` of `x` contains a neighbourhood `V` of `x` whose
inclusion into `U` is null-homotopic) is semilocally simply connected. -/
theorem LocallyContractibleSpace.semilocallySimplyConnectedSpace (h : LocallyContractibleSpace X) :
    SemilocallySimplyConnectedSpace X where
  exists_nhds_homotopic_refl x := by
    obtain ⟨V, hVu, hV, c, ⟨F⟩⟩ := h x univ univ_mem
    refine ⟨V, hV, fun γ hγ ↦ ?_⟩
    let j : C((univ : Set X), X) := ⟨Subtype.val, continuous_subtype_val⟩
    have key := (Path.Homotopic.map_trans_evalAt F (γ.codRestrict hγ)).map j
    rw [Path.map_trans, Path.map_trans] at key
    let δ := (F.evalAt ⟨x, mem_of_mem_nhds hV⟩).map j.continuous
    have e₁ : ((γ.codRestrict hγ).map (ContinuousMap.inclusion hVu).continuous).map j.continuous =
        γ := by
      ext; rfl
    have e₂ : ((γ.codRestrict hγ).map (ContinuousMap.const V c).continuous).map j.continuous =
        Path.refl (c : X) := by
      ext; rfl
    rw [e₁, e₂] at key
    rw [← Path.Homotopic.Quotient.eq] at key ⊢
    have key' : FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ) ≫
        FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk δ) =
        𝟙 _ ≫ FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk δ) := by
      rw [Category.id_comp]
      exact key.trans (Path.Homotopic.Quotient.eq.mpr (Path.Homotopic.trans_refl _))
    exact (cancel_mono _).mp key'

/-- A strongly locally contractible space is semilocally simply connected. -/
instance (priority := 100) StronglyLocallyContractibleSpace.semilocallySimplyConnectedSpace
    [StronglyLocallyContractibleSpace X] : SemilocallySimplyConnectedSpace X :=
  StronglyLocallyContractibleSpace.locallyContractible.semilocallySimplyConnectedSpace
