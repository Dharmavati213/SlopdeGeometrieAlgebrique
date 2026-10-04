/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Dolbeault
import SGA.Foundations.Analytic.RiemannSurfaceCech
import SGA.Foundations.Analytic.RiemannSurfaceDisc

/-!
# Refining cocycles on a compact Riemann surface (the `∂̄`-step of Forster 14.9)

Let `M` be a compact Riemann surface and `Dᵢ` finitely many disc charts whose discs of relative
radius `s` cover `M`; let `s < s' < 1`. Then every bounded holomorphic `1`-cocycle `ζ` on the
discs of radius `s` is, up to a bounded holomorphic coboundary, the restriction of a bounded
holomorphic cocycle on the discs of radius `s'`
(`AnalyticGeometry.DiscChart.exists_eq_cechRestrict_add_cechδ`). This is the surjectivity
hypothesis of Forster's finiteness criterion `cofg_range_cechδ`.

Proof (Forster, *Lectures on Riemann surfaces*, 14.9 and 13.4): glue `ζ` with a smooth partition
of unity `χ` subordinate to the cover into smooth functions `hᵢ = ∑ₖ χₖ ζₖᵢ` with
`ζᵢⱼ = hⱼ - hᵢ` (`partitionGlue_sub`). In each chart the `∂/∂z̄` of the `hᵢ` agree
(`dbar_partitionGlue_eq`), giving smooth data `w` on each chart (`dbarData`); by Dolbeault's
lemma on a disc (`exists_contDiff_dbar_eq_on_ball`) there are smooth `uᵢ` on the discs of radius
`s'` with `∂uᵢ/∂z̄ = w`. Then `ξᵢⱼ = uⱼ - uᵢ` and `ηᵢ = hᵢ - uᵢ` are holomorphic and
`ζ = ξ|_U + δη`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff BoundedContinuousFunction

namespace AnalyticGeometry

/-- `∂/∂z̄` of a smooth function is smooth. -/
theorem contDiffAt_dbar {f : ℂ → ℂ} {z : ℂ} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (dbar f) z := by
  have : dbar f = fun z => dbarCLM (fderiv ℝ f z) := funext (dbar_eq_dbarCLM f)
  rw [this]
  exact dbarCLM.contDiff.contDiffAt.comp z (hf.fderiv_right (by simp))

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) ω M]
  {ι : Type*} [Fintype ι]

/-! ### Gluing a cocycle with a partition of unity -/

section Glue

variable {U : ι → Set M} (χ : ι → M → ℝ) (ζ : cocycles U)

/-- The functions `hᵢ = ∑ₖ χₖ ζₖᵢ` obtained by gluing the cocycle `ζ` with `χ`. -/
def partitionGlue (i : ι) (x : M) : ℂ := ∑ k, (χ k x : ℂ) * Cech1.eval U ζ k i x

variable {χ}

omit [IsManifold 𝓘(ℂ) ω M] in
/-- `ζᵢⱼ = hⱼ - hᵢ` on `Uᵢ ∩ Uⱼ`. -/
theorem partitionGlue_sub (hsupp : ∀ k, tsupport (χ k) ⊆ U k) (hsum : ∀ x, ∑ k, χ k x = 1)
    {i j : ι} {x : M} (hx : x ∈ U i ∩ U j) :
    partitionGlue χ ζ j x - partitionGlue χ ζ i x = Cech1.eval U ζ i j x := by
  have hterm : ∀ k, (χ k x : ℂ) * Cech1.eval U ζ k j x - (χ k x : ℂ) * Cech1.eval U ζ k i x =
      (χ k x : ℂ) * Cech1.eval U ζ i j x := fun k => by
    by_cases hk : x ∈ U k
    · rw [ζ.2 k i j x ⟨⟨hk, hx.1⟩, hx.2⟩]
      ring
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hk (hsupp k h))]
      simp
  simp only [partitionGlue, ← Finset.sum_sub_distrib, hterm, ← Finset.sum_mul, ← Complex.ofReal_sum,
    hsum, Complex.ofReal_one, one_mul]

variable [IsManifold 𝓘(ℝ, ℂ) ∞ M]

/-- The glued functions are smooth in every chart. -/
theorem contDiffAt_partitionGlue_chart (hU : ∀ i, IsOpen (U i)) (hsupp : ∀ k, tsupport (χ k) ⊆ U k)
    (hsmooth : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (χ k)) (i : ι) (p : M) {z : ℂ}
    (hz : z ∈ (extChartAt 𝓘(ℂ) p).target) (hzi : (extChartAt 𝓘(ℂ) p).symm z ∈ U i) :
    ContDiffAt ℝ ∞ (partitionGlue χ ζ i ∘ (extChartAt 𝓘(ℂ) p).symm) z := by
  set φ := extChartAt 𝓘(ℂ) p
  have hfun : partitionGlue χ ζ i ∘ φ.symm =
      fun z => ∑ k, (χ k (φ.symm z) : ℂ) * Cech1.eval U ζ k i (φ.symm z) := rfl
  rw [hfun]
  refine ContDiffAt.sum fun k _ => ?_
  by_cases hk : φ.symm z ∈ U k
  · have h1 : ContDiffAt ℝ ∞ (fun z => (χ k (φ.symm z) : ℂ)) z :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp z (contDiffAt_chart_of_contMDiff (hsmooth k) p hz)
    have h2 : ContDiffAt ℝ ∞ (Cech1.eval U ζ k i ∘ φ.symm) z :=
      contDiffAt_chart_of_mdifferentiableOn ((hU k).inter (hU i)) (ζ.1 k i).2 p hz ⟨hk, hzi⟩
    exact h1.mul h2
  · have hev : ∀ᶠ z' in 𝓝 z, χ k (φ.symm z') = 0 := by
      have : (tsupport (χ k))ᶜ ∈ 𝓝 (φ.symm z) :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds fun h => hk (hsupp k h)
      filter_upwards [(continuousAt_extChartAt_symm'' hz).preimage_mem_nhds this] with z' hz'
      exact image_eq_zero_of_notMem_tsupport hz'
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with z' hz'
    simp [hz']

/-- In every chart, the `∂/∂z̄` of the glued functions `hᵢ` and `hⱼ` agree on `Uᵢ ∩ Uⱼ`. -/
theorem dbar_partitionGlue_eq (hU : ∀ i, IsOpen (U i)) (hsupp : ∀ k, tsupport (χ k) ⊆ U k)
    (hsum : ∀ x, ∑ k, χ k x = 1) (hsmooth : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (χ k))
    (p : M) {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ) p).target) {i j : ι}
    (hzij : (extChartAt 𝓘(ℂ) p).symm z ∈ U i ∩ U j) :
    dbar (partitionGlue χ ζ i ∘ (extChartAt 𝓘(ℂ) p).symm) z =
      dbar (partitionGlue χ ζ j ∘ (extChartAt 𝓘(ℂ) p).symm) z := by
  set φ := extChartAt 𝓘(ℂ) p
  have hi := (contDiffAt_partitionGlue_chart ζ hU hsupp hsmooth i p hz hzij.1).differentiableAt
    (by simp)
  have hj := (contDiffAt_partitionGlue_chart ζ hU hsupp hsmooth j p hz hzij.2).differentiableAt
    (by simp)
  have hev : (partitionGlue χ ζ j ∘ φ.symm) - (partitionGlue χ ζ i ∘ φ.symm) =ᶠ[𝓝 z]
      Cech1.eval U ζ i j ∘ φ.symm := by
    filter_upwards [(continuousAt_extChartAt_symm'' hz).preimage_mem_nhds
      (((hU i).inter (hU j)).mem_nhds hzij)] with z' hz'
    exact partitionGlue_sub ζ hsupp hsum hz'
  have hhol : DifferentiableAt ℂ (Cech1.eval U ζ i j ∘ φ.symm) z :=
    differentiableAt_chart_of_mdifferentiableOn ((hU i).inter (hU j)) (ζ.1 i j).2 p hz hzij
  have h0 : dbar ((partitionGlue χ ζ j ∘ φ.symm) - (partitionGlue χ ζ i ∘ φ.symm)) z = 0 := by
    rw [dbar_congr hev]
    exact (dbar_eq_zero_iff (hhol.restrictScalars ℝ)).mpr hhol
  rw [dbar_sub hj hi, sub_eq_zero] at h0
  exact h0.symm

variable (hcov : ∀ x : M, ∃ i, x ∈ U i)

variable (χ) in
include hcov in
/-- The common value, in the chart `extChartAt 𝓘(ℂ) p`, of the `∂/∂z̄` of the glued functions:
the coefficient of the global `(0, 1)`-form `∂̄hᵢ`. -/
def dbarData (p : M) (z : ℂ) : ℂ :=
  dbar (partitionGlue χ ζ (hcov ((extChartAt 𝓘(ℂ) p).symm z)).choose ∘ (extChartAt 𝓘(ℂ) p).symm) z

theorem dbarData_eq (hU : ∀ i, IsOpen (U i)) (hsupp : ∀ k, tsupport (χ k) ⊆ U k)
    (hsum : ∀ x, ∑ k, χ k x = 1) (hsmooth : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (χ k))
    (p : M) {z : ℂ} (hz : z ∈ (extChartAt 𝓘(ℂ) p).target) {i : ι}
    (hzi : (extChartAt 𝓘(ℂ) p).symm z ∈ U i) :
    dbarData χ ζ hcov p z = dbar (partitionGlue χ ζ i ∘ (extChartAt 𝓘(ℂ) p).symm) z :=
  dbar_partitionGlue_eq ζ hU hsupp hsum hsmooth p hz ⟨(hcov _).choose_spec, hzi⟩

theorem contDiffOn_dbarData (hU : ∀ i, IsOpen (U i)) (hsupp : ∀ k, tsupport (χ k) ⊆ U k)
    (hsum : ∀ x, ∑ k, χ k x = 1) (hsmooth : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (χ k)) (p : M) :
    ContDiffOn ℝ ∞ (dbarData χ ζ hcov p) (extChartAt 𝓘(ℂ) p).target := by
  intro z hz
  set φ := extChartAt 𝓘(ℂ) p
  set i := (hcov (φ.symm z)).choose
  have hi : φ.symm z ∈ U i := (hcov _).choose_spec
  have hev : dbarData χ ζ hcov p =ᶠ[𝓝 z] dbar (partitionGlue χ ζ i ∘ φ.symm) := by
    filter_upwards [(isOpen_extChartAt_target p).mem_nhds hz,
      (continuousAt_extChartAt_symm'' hz).preimage_mem_nhds ((hU i).mem_nhds hi)] with z' hz' hz''
    exact dbarData_eq ζ hcov hU hsupp hsum hsmooth p hz' hz''
  exact (contDiffAt_dbar (contDiffAt_partitionGlue_chart ζ hU hsupp hsmooth i p hz hi)
    ).congr_of_eventuallyEq hev |>.contDiffWithinAt

end Glue

/-! ### The refinement step -/

section Refinement

variable [T2Space M] [SigmaCompactSpace M] (D : ι → DiscChart M) {s s' : ℝ}

-- `[Fintype ι]` gives the normed structure on the cochain spaces used in the proof (see
-- `cofg_range_cechδ`).
set_option linter.unusedFintypeInType false in
/-- **The `∂̄`-step of Forster 14.9**: let `Dᵢ` be finitely many disc charts on a Riemann surface
whose discs of relative radius `s` cover `M`, and `s < s' < 1`. Then every bounded holomorphic
cocycle `ζ` on the discs of radius `s` is `ξ|_U + δη` for a bounded holomorphic cocycle `ξ` on the
discs of radius `s'` and a bounded holomorphic `0`-cochain `η` on the discs of radius `s`. -/
theorem DiscChart.exists_eq_cechRestrict_add_cechδ (hs : 0 < s) (hss' : s < s') (hs' : s' < 1)
    (hcov : ∀ x : M, ∃ i, x ∈ (D i).disc s) (ζ : cocycles fun i => (D i).disc s) :
    ∃ (ξ : cocycles fun i => (D i).disc s') (η : Cech0 fun i => (D i).disc s),
      ζ = cechRestrict (U := fun i => (D i).disc s) (U' := fun i => (D i).disc s')
        (fun i => (D i).disc_mono hss'.le) ξ + cechδ _ η := by
  classical
  set U : ι → Set M := fun i => (D i).disc s with hUdef
  set U' : ι → Set M := fun i => (D i).disc s' with hU'def
  have hU : ∀ i, IsOpen (U i) := fun i => (D i).isOpen_disc s
  have hUU' : ∀ i, U i ⊆ U' i := fun i => (D i).disc_mono hss'.le
  have := isManifold_real_of_complex M
  obtain ⟨χ, hχ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ) isClosed_univ U hU
    (fun x _ => mem_iUnion.mpr (hcov x))
  have hsupp : ∀ k, tsupport (χ k) ⊆ U k := hχ
  have hsum : ∀ x, ∑ k, χ k x = 1 := fun x => by
    rw [← finsum_eq_sum_of_fintype]; exact χ.sum_eq_one (mem_univ x)
  have hsmooth : ∀ k, ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (χ k) := fun k => (χ k).contMDiff
  -- Dolbeault's lemma on each disc
  have hW : ∀ m, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (dbarData (fun k => χ k) ζ hcov (D m).center)
      (ball (D m).c (D m).radius) := fun m =>
    (contDiffOn_dbarData ζ hcov hU hsupp hsum hsmooth _).mono
      (by simpa only [one_mul] using (D m).ball_subset_target (le_refl (1 : ℝ)))
  choose v hv hdv using fun m => exists_contDiff_dbar_eq_on_ball (n := ⊤) le_top
    (mul_pos (hs.trans hss') (D m).radius_pos)
    (by nlinarith [(D m).radius_pos] : s' * (D m).radius < (D m).radius) (hW m)
  set u : ι → M → ℂ := fun m x => v m ((D m).chart x) with hudef
  -- `uₘ - hᵢ` is holomorphic on the disc of radius `s'` of `Dₘ`, over `Uᵢ`
  have hkey : ∀ m i x, x ∈ U' m → x ∈ U i →
      MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (fun y => u m y - partitionGlue (fun k => χ k) ζ i y) x := by
    intro m i x hxm hxi
    set φ := (D m).chart
    have hxs : x ∈ (chartAt ℂ (D m).center).source := by
      rw [← extChartAt_source (I := 𝓘(ℂ))]; exact hxm.1
    rw [mdifferentiableAt_iff_differentiableAt_chart hxs]
    have hz : φ x ∈ φ.target := φ.map_source hxm.1
    have hzi : φ.symm (φ x) ∈ U i := by rw [φ.left_inv hxm.1]; exact hxi
    have hgd := (contDiffAt_partitionGlue_chart ζ hU hsupp hsmooth i (D m).center hz hzi
      ).differentiableAt (by simp)
    have hvd : DifferentiableAt ℝ (v m) (φ x) :=
      ((hv m).differentiable (by simp)).differentiableAt
    have heq : dbar (v m) (φ x) = dbar (partitionGlue (fun k => χ k) ζ i ∘ φ.symm) (φ x) := by
      rw [hdv m _ hxm.2, dbarData_eq ζ hcov hU hsupp hsum hsmooth _ hz hzi]
    refine (differentiableAt_sub_of_dbar_eq hvd hgd heq).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_extChartAt_target _).mem_nhds hz] with z' hz'
    simp only [Function.comp_apply, Pi.sub_apply, hudef]
    rw [show (D m).chart ((extChartAt 𝓘(ℂ) (D m).center).symm z') = z' from
      (extChartAt 𝓘(ℂ) (D m).center).right_inv hz']
  -- bounds for the `uₘ`
  have hbd : ∀ m, ∃ C, ∀ x ∈ U' m, ‖u m x‖ ≤ C := fun m => by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (D m).c (s' * (D m).radius)
      ).exists_bound_of_continuousOn (hv m).continuous.continuousOn
    exact ⟨C, fun x hx => hC _ (ball_subset_closedBall hx.2)⟩
  choose B hB using hbd
  -- the cocycle `ξ` on the discs of radius `s'`
  have hξhol : ∀ i j, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ) (fun y => u j y - u i y) (U' i ∩ U' j) :=
    fun i j x hx => by
      obtain ⟨l, hl⟩ := hcov x
      have h := (hkey j l x hx.2 hl).sub (hkey i l x hx.1 hl)
      refine MDifferentiableAt.mdifferentiableWithinAt ?_
      convert h using 1
      funext y
      simp only [Pi.sub_apply]
      ring
  have hξbd : ∀ i j, ∃ C, ∀ x ∈ U' i ∩ U' j, ‖u j x - u i x‖ ≤ C := fun i j =>
    ⟨B j + B i, fun x hx => (norm_sub_le _ _).trans (add_le_add (hB j x hx.2) (hB i x hx.1))⟩
  let ξ₁ : Cech1 U' := fun i j =>
    boundedHolomorphic.mk (fun y => u j y - u i y) (hξhol i j) (hξbd i j)
  have hξeval : ∀ i j, ∀ x ∈ U' i ∩ U' j, Cech1.eval U' ξ₁ i j x = u j x - u i x :=
    fun i j x hx => boundedHolomorphic.extendByZero_mk _ _ _ hx
  have hξcoc : ξ₁ ∈ cocycles U' := fun i j k x hx => by
    rw [hξeval i k x ⟨hx.1.1, hx.2⟩, hξeval i j x hx.1, hξeval j k x ⟨hx.1.2, hx.2⟩]
    ring
  -- the cochain `η` on the discs of radius `s`
  have hηhol : ∀ i, MDifferentiableOn 𝓘(ℂ) 𝓘(ℂ)
      (fun y => partitionGlue (fun k => χ k) ζ i y - u i y) (U i) := fun i x hx => by
    have h := (hkey i i x (hUU' i hx) hx).neg
    refine MDifferentiableAt.mdifferentiableWithinAt ?_
    convert h using 1
    funext y
    simp only [Pi.neg_apply]
    ring
  have hglue_bd : ∀ i x, ‖partitionGlue (fun k => χ k) ζ i x‖ ≤
      ∑ k, ‖(((ζ : Cech1 U) k i : boundedHolomorphic (U k ∩ U i)) : (U k ∩ U i : Set M) →ᵇ ℂ)‖ :=
    fun i x => by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (χ.nonneg k x)]
      exact (mul_le_of_le_one_left (norm_nonneg _) (χ.le_one k x)).trans
        (norm_extendByZero_le _ _)
  have hηbd : ∀ i, ∃ C, ∀ x ∈ U i, ‖partitionGlue (fun k => χ k) ζ i x - u i x‖ ≤ C := fun i =>
    ⟨_ + B i, fun x hx => (norm_sub_le _ _).trans (add_le_add (hglue_bd i x) (hB i x (hUU' i hx)))⟩
  let η : Cech0 U := fun i =>
    boundedHolomorphic.mk (fun y => partitionGlue (fun k => χ k) ζ i y - u i y) (hηhol i) (hηbd i)
  refine ⟨⟨ξ₁, hξcoc⟩, η, ?_⟩
  apply Subtype.ext
  have hcoe : ((cechRestrict hUU' ⟨ξ₁, hξcoc⟩ + cechδ U η : cocycles U) : Cech1 U) =
      cechRestrict₁ hUU' ξ₁ + cechδ₁ U η := rfl
  rw [hcoe]
  refine Cech1.ext_eval U fun i j x hx => ?_
  rw [Cech1.eval_add, cechRestrict₁_eval _ _ i j hx, cechδ₁_eval U η i j hx,
    hξeval i j x ⟨hUU' i hx.1, hUU' j hx.2⟩, boundedHolomorphic.extendByZero_mk _ _ _ hx.2,
    boundedHolomorphic.extendByZero_mk _ _ _ hx.1, ← partitionGlue_sub ζ hsupp hsum hx]
  ring

end Refinement

end AnalyticGeometry
