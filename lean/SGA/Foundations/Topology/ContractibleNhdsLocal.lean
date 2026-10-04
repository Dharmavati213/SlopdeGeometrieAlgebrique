/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.LocallyContractible
import SGA.Foundations.Topology.SemilocallySimplyConnected

/-!
# Semilocal simple connectedness and local contractibility are local

A space covered by open subsets which are semilocally simply connected is semilocally simply
connected (`SemilocallySimplyConnectedSpace.of_isOpenEmbedding_cover`); in particular the property
is invariant under homeomorphisms (`Homeomorph.semilocallySimplyConnectedSpace`). The key point is
`IsOpenEmbedding.exists_nhds_homotopic_refl`: a loop near `f y` lifts along the open embedding `f`.

The same holds for local contractibility in the classical sense (mathlib's
`LocallyContractibleSpace`: small neighbourhoods contract inside larger ones):
`LocallyContractibleSpace.of_isOpenEmbedding_cover`, `Homeomorph.locallyContractibleSpace`.

## References

* [A. Hatcher, *Algebraic topology*, §1.3][hatcher02]
-/

open Set Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]

/-- If `f : Y → X` is an open embedding and `Y` is semilocally simply connected, then small loops
at `f y` are null-homotopic in `X`. -/
theorem Topology.IsOpenEmbedding.exists_nhds_homotopic_refl [SemilocallySimplyConnectedSpace Y]
    {f : Y → X} (hf : IsOpenEmbedding f) (y : Y) :
    ∃ U ∈ 𝓝 (f y), ∀ γ : Path (f y) (f y), range γ ⊆ U → γ.Homotopic (Path.refl (f y)) := by
  obtain ⟨V, hV, hVγ⟩ := SemilocallySimplyConnectedSpace.exists_nhds_homotopic_refl y
  refine ⟨f '' V, hf.isOpenMap.image_mem_nhds hV, fun γ hγ ↦ ?_⟩
  set e := hf.isEmbedding.toHomeomorph
  have he (z : Y) : (e z : X) = f z := rfl
  have hr (t : unitInterval) : γ t ∈ range f := image_subset_range f V (hγ ⟨t, rfl⟩)
  have hlift (t : unitInterval) : f (e.symm ⟨γ t, hr t⟩) = γ t := by
    rw [← he, e.apply_symm_apply]
  -- the lifted loop
  let γ' : Path y y :=
    { toFun t := e.symm ⟨γ t, hr t⟩
      continuous_toFun := e.symm.continuous.comp (γ.continuous.subtype_mk _)
      source' := hf.isEmbedding.injective (by rw [hlift, γ.source])
      target' := hf.isEmbedding.injective (by rw [hlift, γ.target]) }
  have hγ'V : range γ' ⊆ V := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨v, hv, hvt⟩ := hγ ⟨t, rfl⟩
    have : e.symm ⟨γ t, hr t⟩ = v := hf.isEmbedding.injective (by rw [hlift, hvt])
    change e.symm ⟨γ t, hr t⟩ ∈ V
    rw [this]
    exact hv
  have hmap : γ'.map hf.continuous = γ := by
    ext t
    exact hlift t
  have hrefl : (Path.refl y).map hf.continuous = Path.refl (f y) := by
    ext
    rfl
  have := (hVγ γ' hγ'V).map ⟨f, hf.continuous⟩
  change (γ'.map hf.continuous).Homotopic ((Path.refl y).map hf.continuous) at this
  rwa [hmap, hrefl] at this

/-- A space covered by open embeddings of semilocally simply connected spaces is semilocally simply
connected. -/
theorem SemilocallySimplyConnectedSpace.of_isOpenEmbedding_cover
    (h : ∀ x : X, ∃ (Z : Type v) (_ : TopologicalSpace Z) (_ : SemilocallySimplyConnectedSpace Z)
      (f : Z → X), IsOpenEmbedding f ∧ x ∈ range f) :
    SemilocallySimplyConnectedSpace X where
  exists_nhds_homotopic_refl x := by
    obtain ⟨Z, _, _, f, hf, z, rfl⟩ := h x
    exact hf.exists_nhds_homotopic_refl z

/-- Semilocal simple connectedness is invariant under homeomorphisms. -/
theorem Homeomorph.semilocallySimplyConnectedSpace [SemilocallySimplyConnectedSpace Y]
    (e : Y ≃ₜ X) : SemilocallySimplyConnectedSpace X :=
  .of_isOpenEmbedding_cover fun x ↦ ⟨Y, inferInstance, inferInstance, e, e.isOpenEmbedding,
    e.surjective x⟩

/-- If `f : Y → X` is an open embedding and `Y` is locally contractible (in the classical sense),
then so is `X` at the points of the range of `f`. -/
theorem Topology.IsOpenEmbedding.exists_nullhomotopic_inclusion (hY : LocallyContractibleSpace Y)
    {f : Y → X} (hf : IsOpenEmbedding f) (y : Y) (U : Set X) (hU : U ∈ 𝓝 (f y)) :
    ∃ (V : Set X) (hVU : V ⊆ U), V ∈ 𝓝 (f y) ∧
      ContinuousMap.Nullhomotopic (ContinuousMap.inclusion hVU) := by
  obtain ⟨V', hV'U', hV', ⟨c, ⟨H'⟩⟩⟩ :=
    hY y (f ⁻¹' U) (hf.continuous.continuousAt.preimage_mem_nhds hU)
  have hVU : f '' V' ⊆ U := (image_mono hV'U').trans (image_preimage_subset f U)
  refine ⟨f '' V', hVU, hf.isOpenMap.image_mem_nhds hV', ⟨⟨f c, c.2⟩, ⟨?_⟩⟩⟩
  set e := hf.isEmbedding.toHomeomorph
  have hr (v : f '' V') : (v : X) ∈ range f := image_subset_range f V' v.2
  have hlift (v : f '' V') : f (e.symm ⟨v, hr v⟩) = v := by
    change (e (e.symm ⟨v, hr v⟩) : X) = v
    rw [e.apply_symm_apply]
  have hmem (v : f '' V') : e.symm ⟨v, hr v⟩ ∈ V' := by
    obtain ⟨w, hw, hwv⟩ := v.2
    have : e.symm ⟨v, hr v⟩ = w := hf.isEmbedding.injective (by rw [hlift, hwv])
    rw [this]
    exact hw
  let g : C(f '' V', V') := ⟨fun v ↦ ⟨e.symm ⟨v, hr v⟩, hmem v⟩,
    (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _⟩
  exact
    { toFun := fun q ↦ ⟨f (H' (q.1, g q.2)), (H' (q.1, g q.2)).2⟩
      continuous_toFun := (hf.continuous.comp (continuous_subtype_val.comp (H'.continuous.comp
        (continuous_fst.prodMk (g.continuous.comp continuous_snd))))).subtype_mk _
      map_zero_left := fun v ↦ by
        refine Subtype.ext ?_
        simp only [ContinuousMap.Homotopy.apply_zero, ContinuousMap.inclusion_apply_coe]
        exact hlift v
      map_one_left := fun v ↦ by
        refine Subtype.ext ?_
        simp }

/-- A space covered by open embeddings of locally contractible spaces (in the classical sense) is
locally contractible. -/
theorem LocallyContractibleSpace.of_isOpenEmbedding_cover
    (h : ∀ x : X, ∃ (Z : Type v) (_ : TopologicalSpace Z), LocallyContractibleSpace Z ∧
      ∃ f : Z → X, IsOpenEmbedding f ∧ x ∈ range f) :
    LocallyContractibleSpace X := by
  intro x U hU
  obtain ⟨Z, _, hZ, f, hf, z, rfl⟩ := h x
  exact hf.exists_nullhomotopic_inclusion hZ z U hU

/-- Local contractibility (in the classical sense) is invariant under homeomorphisms. -/
theorem Homeomorph.locallyContractibleSpace (hY : LocallyContractibleSpace Y) (e : Y ≃ₜ X) :
    LocallyContractibleSpace X :=
  .of_isOpenEmbedding_cover fun x ↦ ⟨Y, inferInstance, hY, e, e.isOpenEmbedding, e.surjective x⟩
