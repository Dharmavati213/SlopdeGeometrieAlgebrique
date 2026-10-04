/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Sheaf
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Schwarz
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Bounded holomorphic functions on a Riemann surface, and Montel's theorem

Let `M` be a complex manifold of dimension one (`ChartedSpace ℂ M`, `IsManifold 𝓘(ℂ) 1 M`).

* `AnalyticGeometry.mdifferentiableAt_iff_differentiableAt_chart`: a function `f : M → ℂ` is
  holomorphic at `x` iff its expression `f ∘ φ⁻¹` in any chart `φ = extChartAt 𝓘(ℂ) p` whose
  source contains `x` is complex differentiable at `φ x`.
* `AnalyticGeometry.boundedHolomorphic W`: the bounded holomorphic functions on an open set
  `W ⊆ M`, a closed subspace of the bounded continuous functions on `W`
  (`isClosed_boundedHolomorphic`), hence a Banach space.
* `AnalyticGeometry.boundedHolomorphic.restrict`: restriction `𝒪ᵇ(W') → 𝒪ᵇ(W)` for `W ⊆ W'`.
* **Montel's theorem** in the form needed for Forster's finiteness proof:
  `AnalyticGeometry.boundedHolomorphic.isCompactOperator_restrict`: if `W'` is open and the closure
  of `W` is a compact subset of `W'`, the restriction `𝒪ᵇ(W') → 𝒪ᵇ(W)` is a compact operator.
  (Arzelà–Ascoli on `closure W`, with equicontinuity from the Schwarz lemma in charts.)

References: Forster, *Lectures on Riemann surfaces*, 14.4–14.5 (with sup norms instead of `L²`
norms); Remmert, *Classical topics in complex function theory*, ch. 7.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff BoundedContinuousFunction

namespace AnalyticGeometry


variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]

/-! ### Holomorphy in charts -/

section Charts

variable [IsManifold 𝓘(ℂ) 1 M]

/-- A function `f : M → ℂ` is holomorphic at `x` iff it is complex differentiable in a chart
around `x`. -/
theorem mdifferentiableAt_iff_differentiableAt_chart {f : M → ℂ} {p x : M}
    (hx : x ∈ (chartAt ℂ p).source) :
    MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f x ↔
      DifferentiableAt ℂ (f ∘ (extChartAt 𝓘(ℂ) p).symm) (extChartAt 𝓘(ℂ) p x) := by
  rw [mdifferentiableAt_iff_of_mem_source (I' := 𝓘(ℂ)) (y := f x) hx (by simp),
    extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  have hx' : x ∈ (extChartAt 𝓘(ℂ) p).source := by rwa [extChartAt_source]
  have hc := h.continuousAt.comp (continuousAt_extChartAt' hx')
  refine hc.congr ?_
  filter_upwards [extChartAt_source_mem_nhds' hx'] with y hy
  rw [Function.comp_apply, Function.comp_apply, (extChartAt 𝓘(ℂ) p).left_inv hy]

/-- A function holomorphic on an open set `W ⊆ M` is complex differentiable, in the chart
`φ = extChartAt 𝓘(ℂ) p`, on `φ.target ∩ φ⁻¹ W`. -/
theorem MDifferentiableOn.differentiableOn_chart {f : M → ℂ} {W : Set M} (hW : IsOpen W)
    (hf : MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) f W) (p : M) :
    DifferentiableOn ℂ (f ∘ (extChartAt 𝓘(ℂ) p).symm)
      ((extChartAt 𝓘(ℂ) p).target ∩ (extChartAt 𝓘(ℂ) p).symm ⁻¹' W) := by
  intro z ⟨hz, hzW⟩
  have hsrc : (extChartAt 𝓘(ℂ) p).symm z ∈ (chartAt ℂ p).source := by
    rw [← extChartAt_source (I := 𝓘(ℂ))]; exact (extChartAt 𝓘(ℂ) p).map_target hz
  have h := (mdifferentiableAt_iff_differentiableAt_chart hsrc).mp
    ((hf _ hzW).mdifferentiableAt (hW.mem_nhds hzW))
  rw [(extChartAt 𝓘(ℂ) p).right_inv hz] at h
  exact h.differentiableWithinAt

omit [IsManifold 𝓘(ℂ) 1 M] in
/-- The open set `φ.target ∩ φ⁻¹ W` of a chart `φ = extChartAt 𝓘(ℂ) p`, for `W` open. -/
theorem isOpen_extChartAt_target_inter_preimage {W : Set M} (hW : IsOpen W) (p : M) :
    IsOpen ((extChartAt 𝓘(ℂ) p).target ∩ (extChartAt 𝓘(ℂ) p).symm ⁻¹' W) :=
  (continuousOn_extChartAt_symm p).isOpen_inter_preimage (isOpen_extChartAt_target p) hW

end Charts

/-! ### Bounded holomorphic functions -/

section Bounded

/-- The bounded holomorphic functions on a subset `W ⊆ M` (holomorphic meaning: the extension by
zero is holomorphic on `W`), a subspace of the bounded continuous functions on `W`. -/
def boundedHolomorphic (W : Set M) : Submodule ℂ (W →ᵇ ℂ) where
  carrier := {g | MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (extendByZero g) W}
  add_mem' {g h} hg hh := (hg.add hh).congr fun x hx => by
    simp [extendByZero_of_mem _ hx]
  zero_mem' := (mdifferentiableOn_const (c := (0 : ℂ))).congr fun x hx => by
    simp [extendByZero_of_mem _ hx]
  smul_mem' c g hg := (hg.const_smul c).congr fun x hx => by
    simp [extendByZero_of_mem _ hx]

lemma mem_boundedHolomorphic {W : Set M} {g : W →ᵇ ℂ} :
    g ∈ boundedHolomorphic W ↔ MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (extendByZero g) W :=
  Iff.rfl

/-- Uniform limits of holomorphic functions are holomorphic: the bounded holomorphic functions on
an open set form a closed subspace. -/
theorem isClosed_boundedHolomorphic [IsManifold 𝓘(ℂ) 1 M] {W : Set M} (hW : IsOpen W) :
    IsClosed (boundedHolomorphic W : Set (W →ᵇ ℂ)) := by
  refine isClosed_of_closure_subset fun g hg => ?_
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hg
  rw [BoundedContinuousFunction.tendsto_iff_tendstoUniformly] at hlim
  intro x hx
  refine MDifferentiableAt.mdifferentiableWithinAt ?_
  set φ := extChartAt 𝓘(ℂ) x
  set O := φ.target ∩ φ.symm ⁻¹' W
  have hO : IsOpen O := isOpen_extChartAt_target_inter_preimage hW x
  have hxO : φ x ∈ O := ⟨mem_extChartAt_target x, by rwa [mem_preimage, extChartAt_to_inv]⟩
  have hunif : TendstoUniformlyOn (fun n => extendByZero (u n) ∘ φ.symm)
      (extendByZero g ∘ φ.symm) atTop O := by
    intro U hU
    filter_upwards [hlim U hU] with n hn z hz
    simp only [Function.comp_apply]
    rw [extendByZero_of_mem (y := φ.symm z) _ hz.2, extendByZero_of_mem (y := φ.symm z) _ hz.2]
    exact hn _
  have hdiff : DifferentiableOn ℂ (extendByZero g ∘ φ.symm) O :=
    hunif.tendstoLocallyUniformlyOn.differentiableOn
      (Eventually.of_forall fun n => MDifferentiableOn.differentiableOn_chart hW (hu n) x) hO
  exact (mdifferentiableAt_iff_differentiableAt_chart (mem_chart_source ℂ x)).mpr
    (hdiff.differentiableAt (hO.mem_nhds hxO))

instance [IsManifold 𝓘(ℂ) 1 M] {W : Set M} [Fact (IsOpen W)] :
    CompleteSpace (boundedHolomorphic W) :=
  (isClosed_boundedHolomorphic Fact.out).completeSpace_coe

omit [ChartedSpace ℂ M] in
lemma norm_extendByZero_le {W : Set M} (g : W →ᵇ ℂ) (x : M) : ‖extendByZero g x‖ ≤ ‖g‖ := by
  by_cases hx : x ∈ W
  · rw [extendByZero_of_mem _ hx]; exact g.norm_coe_le_norm _
  · rw [extendByZero_of_notMem _ hx, norm_zero]; exact norm_nonneg _

/-- Restriction of bounded holomorphic functions from `W'` to `W ⊆ W'`. -/
def boundedHolomorphic.restrict {W W' : Set M} (h : W ⊆ W') :
    boundedHolomorphic W' →L[ℂ] boundedHolomorphic W :=
  ((BoundedContinuousFunction.compContinuousCLM ℂ ℂ ⟨inclusion h, continuous_inclusion h⟩).comp
    (boundedHolomorphic W').subtypeL).codRestrict _ fun g =>
      (g.2.mono h).congr fun x hx => by
        simp [extendByZero_of_mem _ hx, extendByZero_of_mem _ (h hx)]

@[simp]
lemma boundedHolomorphic.restrict_apply {W W' : Set M} (h : W ⊆ W')
    (g : boundedHolomorphic W') (x : W) :
    (restrict h g : W →ᵇ ℂ) x = (g : W' →ᵇ ℂ) (inclusion h x) :=
  rfl

lemma boundedHolomorphic.extendByZero_restrict {W W' : Set M} (h : W ⊆ W')
    (g : boundedHolomorphic W') {x : M} (hx : x ∈ W) :
    extendByZero (restrict h g : W →ᵇ ℂ) x = extendByZero (g : W' →ᵇ ℂ) x := by
  rw [extendByZero_of_mem _ hx, extendByZero_of_mem _ (h hx)]
  rfl

/-- **Montel's theorem**: if `W'` is open and the closure of `W` is a compact subset of `W'`, the
restriction of bounded holomorphic functions from `W'` to `W` is a compact operator. -/
theorem boundedHolomorphic.isCompactOperator_restrict [IsManifold 𝓘(ℂ) 1 M] {W W' : Set M}
    (hW : IsOpen W)
    (hW' : IsOpen W') (hc : IsCompact (closure W)) (hcl : closure W ⊆ W') :
    IsCompactOperator (restrict (subset_closure.trans hcl)) := by
  set K := closure W
  have : CompactSpace K := isCompact_iff_compactSpace.mp hc
  -- restriction to `K` and from `K` to `W`
  let RK : boundedHolomorphic W' →L[ℂ] (K →ᵇ ℂ) :=
    (BoundedContinuousFunction.compContinuousCLM ℂ ℂ ⟨inclusion hcl, continuous_inclusion hcl⟩).comp
      (boundedHolomorphic W').subtypeL
  let jW : (K →ᵇ ℂ) →L[ℂ] (W →ᵇ ℂ) := BoundedContinuousFunction.compContinuousCLM ℂ ℂ
    ⟨inclusion subset_closure, continuous_inclusion subset_closure⟩
  set A := RK '' closedBall 0 1
  -- equicontinuity of `A`, from the Schwarz lemma in charts
  have hequi : Equicontinuous ((↑) : A → K → ℂ) := by
    intro k
    rw [Metric.equicontinuousAt_iff_right]
    intro ε hε
    set φ := extChartAt 𝓘(ℂ) (k : M)
    set c := φ k
    have hO : IsOpen (φ.target ∩ φ.symm ⁻¹' W') := isOpen_extChartAt_target_inter_preimage hW' _
    have hcO : c ∈ φ.target ∩ φ.symm ⁻¹' W' :=
      ⟨mem_extChartAt_target _, by rw [mem_preimage, extChartAt_to_inv]; exact hcl k.2⟩
    obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO c hcO
    -- the Schwarz bound for each function of the unit ball
    have hbound : ∀ g ∈ closedBall (0 : boundedHolomorphic W') 1, ∀ z ∈ ball c R,
        dist (extendByZero (g : W' →ᵇ ℂ) (φ.symm z)) (extendByZero (g : W' →ᵇ ℂ) (φ.symm c))
          ≤ 2 / R * dist z c := by
      intro g hg z hz
      have hg1 : ‖(g : W' →ᵇ ℂ)‖ ≤ 1 := (mem_closedBall_zero_iff.mp hg :)
      have hd : DifferentiableOn ℂ (extendByZero (g : W' →ᵇ ℂ) ∘ φ.symm) (ball c R) :=
        (MDifferentiableOn.differentiableOn_chart hW' g.2 _).mono hRO
      refine Complex.dist_le_div_mul_dist_of_mapsTo_ball hd (fun w _ => ?_) hz
      rw [mem_closedBall, dist_eq_norm]
      refine (norm_sub_le _ _).trans ?_
      have h1 := (norm_extendByZero_le (g : W' →ᵇ ℂ) (φ.symm w)).trans hg1
      have h2 := (norm_extendByZero_le (g : W' →ᵇ ℂ) (φ.symm c)).trans hg1
      simp only [Function.comp_apply]
      linarith
    set δ := min R (ε * R / 4)
    have hδ : 0 < δ := lt_min hR (by positivity)
    have hnhds : ∀ᶠ k' : K in 𝓝 k, (k' : M) ∈ φ.source ∧ φ k' ∈ ball c δ := by
      have h1 : φ.source ∈ 𝓝 (k : M) := extChartAt_source_mem_nhds _
      have h2 : φ ⁻¹' ball c δ ∈ 𝓝 (k : M) :=
        (continuousAt_extChartAt (k : M)).preimage_mem_nhds (ball_mem_nhds c hδ)
      exact (continuous_subtype_val.continuousAt.preimage_mem_nhds (inter_mem h1 h2))
    filter_upwards [hnhds] with k' ⟨hk's, hk'b⟩
    rintro ⟨_, g, hg, rfl⟩
    have hval : ∀ y : K, (y : M) ∈ φ.source →
        (RK g : K →ᵇ ℂ) y = extendByZero (g : W' →ᵇ ℂ) (φ.symm (φ y)) := fun y hy => by
      rw [φ.left_inv hy, extendByZero_of_mem _ (hcl y.2)]
      rfl
    simp only
    rw [hval k (mem_extChartAt_source _), hval k' hk's, dist_comm]
    have hz : φ k' ∈ ball c R := ball_subset_ball (min_le_left _ _) hk'b
    refine (hbound g hg _ hz).trans_lt ?_
    have : dist (φ k') c < ε * R / 4 := hk'b.trans_le (min_le_right _ _)
    calc 2 / R * dist (φ k') c ≤ 2 / R * (ε * R / 4) := by gcongr
      _ = ε / 2 := by field_simp; ring
      _ < ε := by linarith
  have hA : IsCompact (closure A) := BoundedContinuousFunction.arzela_ascoli (closedBall (0 : ℂ) 1)
    (isCompact_closedBall _ _) A (by
      rintro _ y ⟨g, hg, rfl⟩
      rw [mem_closedBall, dist_zero_right]
      have hg1 : ‖(g : W' →ᵇ ℂ)‖ ≤ 1 := (mem_closedBall_zero_iff.mp hg :)
      exact ((g : W' →ᵇ ℂ).norm_coe_le_norm _).trans hg1) hequi
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  refine ⟨closedBall 0 1, closedBall_mem_nhds _ one_pos,
    Subtype.val ⁻¹' (jW '' closure A), ?_, ?_⟩
  · exact (isClosed_boundedHolomorphic hW).isClosedEmbedding_subtypeVal.isCompact_preimage
      (hA.image jW.continuous)
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨RK g, subset_closure ⟨g, hg, rfl⟩, rfl⟩

end Bounded

end AnalyticGeometry
