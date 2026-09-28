/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Properness is local on the target

A continuous map `f : X → Y` is proper as soon as every point of `Y` has an open neighbourhood
`V` over which the restriction `f⁻¹(V) → V` is proper. Used for XII.3.2 (v) on points.
-/

namespace SGA.SGA1.ExposeXII

open Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

theorem isProperMap_of_isProperMap_restrictPreimage (hf : Continuous f)
    (h : ∀ y, ∃ V : Set Y, IsOpen V ∧ y ∈ V ∧ IsProperMap (V.restrictPreimage f)) :
    IsProperMap f := by
  rw [isProperMap_iff_ultrafilter]
  refine ⟨hf, fun 𝒰 y hy ↦ ?_⟩
  obtain ⟨V, hV, hyV, hp⟩ := h y
  have hmem : f ⁻¹' V ∈ (𝒰 : Filter X) := hy (hV.mem_nhds hyV)
  have hrange : range ((↑) : f ⁻¹' V → X) ∈ (𝒰 : Filter X) := by
    rwa [Subtype.range_coe]
  let 𝒰' : Ultrafilter (f ⁻¹' V) := 𝒰.comap Subtype.val_injective hrange
  have hmap : Filter.map ((↑) : f ⁻¹' V → X) 𝒰' = 𝒰 := Filter.map_comap_of_mem hrange
  have hy' : Tendsto (V.restrictPreimage f) 𝒰' (𝓝 ⟨y, hyV⟩) := by
    rw [nhds_subtype, tendsto_comap_iff]
    change Tendsto (f ∘ ((↑) : f ⁻¹' V → X)) 𝒰' (𝓝 y)
    rw [← tendsto_map'_iff, hmap]
    exact hy
  obtain ⟨x, hx, hle⟩ := (isProperMap_iff_ultrafilter.mp hp).2 hy'
  refine ⟨x.1, congr_arg Subtype.val hx, ?_⟩
  rw [← hmap]
  exact (continuous_subtype_val.tendsto x).mono_left (map_mono hle)

end SGA.SGA1.ExposeXII
