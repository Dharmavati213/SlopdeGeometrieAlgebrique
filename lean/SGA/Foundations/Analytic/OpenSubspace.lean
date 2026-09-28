/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Presentation
import Mathlib.Geometry.RingedSpace.OpenImmersion

/-!
# Open subspaces of local models

For a local model `Z(D) ⊆ U ⊆ E` and an open subset `U' ⊆ E`, the local model `D|_{U'}`
(`LocalModelData.restrictU`: same equations, domain `U ∩ U'`) has zero set `Z(D) ∩ U'`, and the
inclusion `Z(D) ∩ U' → Z(D)` is an open immersion of locally ringed spaces
(`LocalModelData.isOpenImmersion_inclusion`): the open subspaces of local models of this form are
local models (`LocalModelData.restrictUIso`).
-/

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter Topology

namespace AnalyticGeometry

namespace LocalModelData

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  (D : LocalModelData 𝕜 E) (U' : Set E) (hU' : IsOpen U')

/-- The local model `Z(D) ∩ U'`: the same equations on the smaller domain `U ∩ U'`. -/
def restrictU : LocalModelData 𝕜 E where
  U := D.U ∩ U'
  isOpen_U := D.isOpen_U.inter hU'
  k := D.k
  f := D.f
  analyticAt_f i x hx := D.analyticAt_f i x hx.1

variable {D U' hU'}

omit [CompleteSpace 𝕜] in
lemma mem_zeroSet_restrictU {x : E} :
    x ∈ (D.restrictU U' hU').zeroSet ↔ x ∈ D.zeroSet ∧ x ∈ U' :=
  ⟨fun h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩

omit [CompleteSpace 𝕜] in
lemma zeroSet_restrictU_subset : (D.restrictU U' hU').zeroSet ⊆ D.zeroSet :=
  fun _ hx ↦ (mem_zeroSet_restrictU.mp hx).1

variable (D U' hU')

/-- The inclusion `Z(D) ∩ U' → Z(D)`. -/
def inclusionMap : AnalyticMap (D.restrictU U' hU') D where
  toFun := id
  analyticAt _ _ := analyticAt_id
  mapsTo _ hy := hy.1.1
  mem_ideal y i := by
    rw [stalkPullback_germOf]
    exact Ideal.subset_span ⟨i, rfl⟩

lemma inclusionMap_fiberMap_apply (y : (D.restrictU U' hU').zeroSet)
    (t : D.Fiber ((inclusionMap D U' hU').pointMap y)) :
    (inclusionMap D U' hU').fiberMap y t = t := by
  obtain ⟨G, hG, rfl⟩ := D.classOf_surjective _ t
  rw [AnalyticMap.fiberMap_classOf]
  rfl

lemma isOpenEmbedding_inclusion_base :
    IsOpenEmbedding (inclusionMap D U' hU').toHom.base := by
  have h : (⇑(inclusionMap D U' hU').toHom.base) = Set.inclusion zeroSet_restrictU_subset := rfl
  rw [h]
  refine ⟨IsEmbedding.inclusion _, ?_⟩
  have : Set.range (Set.inclusion (zeroSet_restrictU_subset (D := D) (U' := U') (hU' := hU'))) =
      Subtype.val ⁻¹' U' := by
    ext x
    refine ⟨?_, fun hx ↦ ⟨⟨x.1, mem_zeroSet_restrictU.mpr ⟨x.2, hx⟩⟩, rfl⟩⟩
    rintro ⟨y, rfl⟩
    exact (mem_zeroSet_restrictU.mp y.2).2
  rw [this]
  exact hU'.preimage continuous_subtype_val

instance isIso_stalkMap_inclusion (y : (D.restrictU U' hU').zeroSet) :
    IsIso ((inclusionMap D U' hU').toHom.stalkMap y) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  set Φ := inclusionMap D U' hU'
  have h : ∀ t, (D.restrictU U' hU').stalkIso y (Φ.toHom.stalkMap y t) =
      Φ.fiberMap y (D.stalkIso (Φ.pointMap y) t) := fun t ↦
    Φ.stalkToFiber_stalkMap y t
  refine ⟨fun t₁ t₂ ht ↦ ?_, fun s ↦ ?_⟩
  · have h₁ := congrArg ((D.restrictU U' hU').stalkIso y) ht
    rw [h, h, inclusionMap_fiberMap_apply, inclusionMap_fiberMap_apply] at h₁
    exact (D.stalkIso _).injective h₁
  · refine ⟨(D.stalkIso (Φ.pointMap y)).symm ((D.restrictU U' hU').stalkIso y s), ?_⟩
    apply ((D.restrictU U' hU').stalkIso y).injective
    refine (h _).trans ?_
    rw [inclusionMap_fiberMap_apply]
    exact RingEquiv.apply_symm_apply _ _

/-- The inclusion `Z(D) ∩ U' → Z(D)` is an open immersion. -/
theorem isOpenImmersion_inclusion :
    LocallyRingedSpace.IsOpenImmersion (inclusionMap D U' hU').toHom :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ (isOpenEmbedding_inclusion_base D U' hU')

/-- **Open subspaces of local models**: the open subspace `Z(D) ∩ U'` of `Z(D)` is the local model
`D|_{U'}`. -/
def restrictUIso :
    (D.restrictU U' hU').toLocallyRingedSpace ≅
      D.toLocallyRingedSpace.restrict (isOpenEmbedding_inclusion_base D U' hU') :=
  have := isOpenImmersion_inclusion D U' hU'
  LocallyRingedSpace.IsOpenImmersion.isoRestrict (inclusionMap D U' hU').toHom

end LocalModelData

end AnalyticGeometry
