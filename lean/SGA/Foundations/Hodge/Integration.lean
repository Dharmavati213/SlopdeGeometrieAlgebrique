/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.DolbeaultCohomology
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Order

/-!
# Integration of top-degree forms on compact complex manifolds, and Stokes' theorem

Let `E` be a finite-dimensional complex normed space, `k = dim_ℝ E`, `μ` a Haar measure on `E` and
`b : Fin k → E` fixed vectors. For a `ℂ`-valued `k`-form `ρ` on an open set of `E` the integral of
`ρ` is `∫ ρ(y)(b) dμ(y)`; it depends on `(μ, b)` only through a real constant factor (the volume
of the parallelepiped spanned by `b`, with sign).

* `ContinuousAlternatingMap.map_comp_eq_det_mul`: a top-degree form satisfies
  `α (A ∘ v) = det A · α v`;
* `ContinuousLinearMap.det_restrictScalars_eq_normSq`: a complex linear map has real determinant
  `|det_ℂ|² ≥ 0`
  (so holomorphic changes of coordinates preserve orientation);
* `Hodge.integral_partDeriv_eq_zero`, `Hodge.integral_extDeriv_eq_zero`: **Stokes' theorem on `E`**,
  `∫ (∂̄τ)(b) = ∫ (∂τ)(b) = ∫ (dτ)(b) = 0` for `C¹` forms `τ` with compact support;
* `Hodge.setIntegral_localRep_eq`: on a complex manifold `M`, the integrals of the local
  representatives of a form supported in the domains of two charts agree (change of variables
  with Jacobian `|det_ℂ|² > 0`);
* `Hodge.ChartPartition`: a finite smooth partition of unity subordinate to charts (it exists on
  compact Hausdorff `M`: `Hodge.ChartPartition.nonempty`), and `Hodge.integralForm μ P b ρ`, the
  integral of a top-degree form over `M`;
* `Hodge.integralForm_eq_of_partition`: the integral does not depend on the partition of unity;
* `Hodge.integralForm_partForm_eq_zero`, `Hodge.integralForm_extDerivForm_eq_zero`: **Stokes'
  theorem on a compact complex manifold**, `∫_M ∂̄τ = ∫_M ∂τ = ∫_M dτ = 0`;
* `Hodge.integralForm_nonneg`, `Hodge.integralForm_pos`: if `ρ z b ≥ 0` for all `z` (read in the
  chart at `z`, in the order of `ℂ`), then `∫_M ρ ≥ 0`, and `> 0` if `ρ z₀ b > 0` somewhere
  (holomorphic changes of coordinates have `det = |det_ℂ|² > 0`).

Reference: J. M. Lee, *Introduction to smooth manifolds*, Ch. 16; R. O. Wells, *Differential
analysis on complex manifolds*, Ch. II.
-/

noncomputable section

open Set Filter Topology MeasureTheory ContinuousAlternatingMap
open scoped Manifold ContDiff ComplexOrder

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

section Linear

/-- A top-degree form satisfies `α (A v₁, …, A vₖ) = det A · α (v₁, …, vₖ)`. -/
lemma _root_.ContinuousAlternatingMap.map_comp_eq_det_mul [FiniteDimensional ℝ E]
    (hk : Module.finrank ℝ E = k)
    (α : E [⋀^Fin k]→L[ℝ] ℂ) (A : E →L[ℝ] E) (v : Fin k → E) :
    α (A ∘ v) = ((LinearMap.det (A : E →ₗ[ℝ] E) : ℝ) : ℂ) * α v := by
  let b := Module.finBasisOfFinrankEq ℝ E hk
  have key : ∀ φ : ℂ →L[ℝ] ℝ, φ (α (A ∘ v)) = LinearMap.det (A : E →ₗ[ℝ] E) * φ (α v) := by
    intro φ
    let f := (φ.compContinuousAlternatingMap α).toAlternatingMap
    have hf := f.eq_smul_basis_det b
    have h1 : f (A ∘ v) = φ (α (A ∘ v)) := rfl
    have h2 : f v = φ (α v) := rfl
    rw [← h1, ← h2, hf]
    simp only [AlternatingMap.smul_apply, smul_eq_mul]
    rw [show (A ∘ v) = (A : E →ₗ[ℝ] E) ∘ v from rfl, Module.Basis.det_comp]
    ring
  apply Complex.ext
  · have := key Complex.reCLM
    simpa using this
  · have := key Complex.imCLM
    simpa using this

/-- The real determinant of a complex linear map is the squared modulus of its complex
determinant. -/
lemma _root_.ContinuousLinearMap.det_restrictScalars_eq_normSq [FiniteDimensional ℂ E]
    (f : E →L[ℂ] E) :
    LinearMap.det ((f.restrictScalars ℝ : E →L[ℝ] E) : E →ₗ[ℝ] E) =
      Complex.normSq (LinearMap.det (f : E →ₗ[ℂ] E)) := by
  rw [← Algebra.norm_complex_apply, ← LinearMap.det_restrictScalars]
  rfl

end Linear

section Stokes

variable [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

lemma integral_fderiv_apply_eq_zero {g : E → ℂ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (w : E) : ∫ y, fderiv ℝ g y w ∂μ = 0 := by
  have hc : Continuous fun y ↦ fderiv ℝ g y w :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hs' : HasCompactSupport fun y ↦ fderiv ℝ g y w :=
    hs.fderiv_apply (𝕜 := ℝ) w
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := μ) (f := fun _ ↦ (1 : ℂ))
    (g := g) (v := w) (by simp) (by simpa using hc.integrable_of_hasCompactSupport hs')
    (by simpa using hg.continuous.integrable_of_hasCompactSupport hs)
    (fun x _ ↦ differentiableAt_const _) (fun x _ ↦ hg.differentiable one_ne_zero x)
  simpa using this

/-- **Stokes' theorem on a complex normed space** for `∂`, `∂̄` (and every `partDeriv ε`): the
integral of `partDeriv ε τ` (evaluated on any fixed vectors) vanishes for a `C¹` form `τ` with
compact support. -/
theorem integral_partDeriv_eq_zero (ε : ℂ) {m : ℕ} {τ : E → E [⋀^Fin m]→L[ℝ] ℂ}
    (hτ : ContDiff ℝ 1 τ) (hs : HasCompactSupport τ) (v : Fin (m + 1) → E) :
    ∫ y, partDeriv ε τ y v ∂μ = 0 := by
  have hg (u : Fin m → E) : ContDiff ℝ 1 fun y ↦ τ y u :=
    (ContinuousAlternatingMap.apply ℝ E ℂ u).contDiff.comp hτ
  have hgs (u : Fin m → E) : HasCompactSupport fun y ↦ τ y u :=
    hs.comp_left (g := fun α : E [⋀^Fin m]→L[ℝ] ℂ ↦ α u) (by simp)
  have hint (u : Fin m → E) (w : E) : Integrable (fun y ↦ fderiv ℝ (fun y ↦ τ y u) y w) μ :=
    (((hg u).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      ((hgs u).fderiv_apply (𝕜 := ℝ) w)
  have hpt : ∀ y, partDeriv ε τ y v = ∑ i : Fin (m + 1), ((-1 : ℂ) ^ i.val * 2⁻¹) *
      (fderiv ℝ (fun y ↦ τ y (i.removeNth v)) y (v i) +
        (ε * Complex.I) * fderiv ℝ (fun y ↦ τ y (i.removeNth v)) y (Complex.I • v i)) := by
    intro y
    have hd : DifferentiableAt ℝ τ y := hτ.differentiable one_ne_zero y
    rw [partDeriv_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [partCLM_apply, fderiv_continuousAlternatingMap_apply_const_apply hd,
      fderiv_continuousAlternatingMap_apply_const_apply hd]
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply,
      smul_eq_mul, zsmul_eq_mul]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_const_mul, integral_add (hint _ _) ((hint _ _).const_mul _), integral_const_mul,
      integral_fderiv_apply_eq_zero μ (hg _) (hgs _),
      integral_fderiv_apply_eq_zero μ (hg _) (hgs _)]
    simp
  · intro i _
    exact ((hint _ _).add ((hint _ _).const_mul _)).const_mul _

/-- **Stokes' theorem on a complex normed space** for the exterior derivative. -/
theorem integral_extDeriv_eq_zero {m : ℕ} {τ : E → E [⋀^Fin m]→L[ℝ] ℂ}
    (hτ : ContDiff ℝ 1 τ) (hs : HasCompactSupport τ) (v : Fin (m + 1) → E) :
    ∫ y, extDeriv τ y v ∂μ = 0 := by
  have hg (u : Fin m → E) : ContDiff ℝ 1 fun y ↦ τ y u :=
    (ContinuousAlternatingMap.apply ℝ E ℂ u).contDiff.comp hτ
  have hgs (u : Fin m → E) : HasCompactSupport fun y ↦ τ y u :=
    hs.comp_left (g := fun α : E [⋀^Fin m]→L[ℝ] ℂ ↦ α u) (by simp)
  have hint (u : Fin m → E) (w : E) : Integrable (fun y ↦ fderiv ℝ (fun y ↦ τ y u) y w) μ :=
    (((hg u).continuous_fderiv one_ne_zero).clm_apply
      continuous_const).integrable_of_hasCompactSupport
      ((hgs u).fderiv_apply (𝕜 := ℝ) w)
  have hpt : ∀ y, extDeriv τ y v = ∑ i : Fin (m + 1), (-1 : ℂ) ^ i.val *
      fderiv ℝ (fun y ↦ τ y (i.removeNth v)) y (v i) := by
    intro y
    have hd : DifferentiableAt ℝ τ y := hτ.differentiable one_ne_zero y
    rw [extDeriv_apply hd]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [fderiv_continuousAlternatingMap_apply_const_apply hd]
    simp [zsmul_eq_mul]
  simp_rw [hpt]
  rw [integral_finsetSum]
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [integral_const_mul, integral_fderiv_apply_eq_zero μ (hg _) (hgs _), mul_zero]
  · intro i _
    exact (hint _ _).const_mul _

end Stokes

section Charts

lemma extChartAt_target_eq (x : M) : (extChartAt 𝓘(ℂ, E) x).target = (chartAt E x).target := by
  simp

lemma extChartAt_source_eq (x : M) : (extChartAt 𝓘(ℂ, E) x).source = (chartAt E x).source := by
  simp

lemma extChartAt_real_eq (x : M) : extChartAt 𝓘(ℝ, E) x = extChartAt 𝓘(ℂ, E) x := by
  ext y
  · simp
  · simp
  · simp

/-- A complex manifold is a smooth real manifold, with the same charts. -/
theorem isManifold_real [IsManifold 𝓘(ℂ, E) ω M] : IsManifold 𝓘(ℝ, E) ∞ M :=
  isManifold_of_contDiffOn _ _ _ fun e e' he he' => by
    have h := HasGroupoid.compatible (G := contDiffGroupoid ω 𝓘(ℂ, E)) he he'
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
    have h1 := h.1
    simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      range_id, preimage_id_eq, id_eq, inter_univ, Function.id_comp, Function.comp_id] at h1 ⊢
    exact (h1.restrict_scalars ℝ).of_le le_top

variable [IsManifold 𝓘(ℂ, E) ω M]

theorem setIntegral_localRep_eq [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure] (hk : Module.finrank ℝ E = k) (b : Fin k → E)
    {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (x x' : M)
    (hsupp : ∀ z, ρ z ≠ 0 → z ∈ (chartAt E x).source ∩ (chartAt E x').source) :
    ∫ y in (extChartAt 𝓘(ℂ, E) x).target, localRep ρ x y b ∂μ =
      ∫ y in (extChartAt 𝓘(ℂ, E) x').target, localRep ρ x' y b ∂μ := by
  set e := extChartAt 𝓘(ℂ, E) x with he
  set e' := extChartAt 𝓘(ℂ, E) x' with he'
  let f : OpenPartialHomeomorph E E := (chartAt E x').symm.trans (chartAt E x)
  have hfs : f.source = e'.target ∩ e'.symm ⁻¹' e.source := by
    simp [f, he, he']
  have hft : f.target = e.target ∩ e.symm ⁻¹' e'.source := by
    simp [f, he, he']
  have hfeq : ∀ y, f y = transition x' x y := fun y ↦ by simp [f, transition]
  have h1 : ∫ y in e.target, localRep ρ x y b ∂μ = ∫ y in f.target, localRep ρ x y b ∂μ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_extChartAt_target x).measurableSet (by rw [hft]; exact inter_subset_left) ?_
    rintro y ⟨hy, hyf⟩
    have hns : e.symm y ∉ e'.source := fun h ↦ hyf (by rw [hft]; exact ⟨hy, h⟩)
    have hρ : ρ (e.symm y) = 0 := by
      by_contra hne
      exact hns (by rw [he', extChartAt_source_eq]; exact (hsupp _ hne).2)
    simp only [localRep, ← he]
    rw [hρ]
    simp
  have h4 : ∫ y in e'.target, localRep ρ x' y b ∂μ =
      ∫ y in f.source, localRep ρ x' y b ∂μ := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (isOpen_extChartAt_target x').measurableSet (by rw [hfs]; exact inter_subset_left) ?_
    rintro y ⟨hy, hyf⟩
    have hns : e'.symm y ∉ e.source := fun h ↦ hyf (by rw [hfs]; exact ⟨hy, h⟩)
    have hρ : ρ (e'.symm y) = 0 := by
      by_contra hne
      exact hns (by rw [he, extChartAt_source_eq]; exact (hsupp _ hne).1)
    simp only [localRep, ← he']
    rw [hρ]
    simp
  let f' : E → E →L[ℝ] E := fun y ↦
    (tangentCoordChange 𝓘(ℂ, E) x' x (e'.symm y)).restrictScalars ℝ
  have hf' : ∀ y ∈ f.source, HasFDerivAt f (f' y) y := by
    intro y hy
    rw [hfs] at hy
    have := (hasFDerivAt_transition (x₀ := x') (w := x) hy.1 hy.2).restrictScalars ℝ
    have hfun : (f : E → E) = transition x' x := funext hfeq
    rw [hfun]
    exact this
  rw [h1, h4, integral_target_eq_integral_abs_det_fderiv_smul μ hf']
  refine setIntegral_congr_fun f.open_source.measurableSet fun y hy ↦ ?_
  rw [hfs] at hy
  have hev := localRep_eventuallyEq_pullbackForm_of_mem ρ (x₀ := x') (w := x)
    (show e'.symm y ∈ (extChartAt 𝓘(ℂ, E) x').source from e'.map_target hy.1) hy.2
  rw [show extChartAt 𝓘(ℂ, E) x' (e'.symm y) = y from PartialEquiv.right_inv _ hy.1] at hev
  have hdet : (f' y).det = Complex.normSq (LinearMap.det
      ((tangentCoordChange 𝓘(ℂ, E) x' x (e'.symm y) : E →L[ℂ] E) : E →ₗ[ℂ] E)) :=
    ContinuousLinearMap.det_restrictScalars_eq_normSq _
  rw [hev.eq_of_nhds, pullbackForm, fderiv_transition hy.1 hy.2, compContinuousLinearMap_apply,
    ContinuousAlternatingMap.map_comp_eq_det_mul hk, hfeq,
    ContinuousLinearMap.det_restrictScalars_eq_normSq, hdet,
    abs_of_nonneg (Complex.normSq_nonneg _), Complex.real_smul]

end Charts

variable (E M) in
/-- A finite smooth partition of unity on `M` subordinate to the domains of finitely many charts
of the atlas. -/
structure ChartPartition where
  /-- The number of charts. -/
  card : ℕ
  /-- The centres of the charts. -/
  center : Fin card → M
  /-- The functions of the partition of unity. -/
  fn : Fin card → M → ℝ
  contMDiff_fn : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fn i)
  fn_nonneg : ∀ i x, 0 ≤ fn i x
  sum_fn_eq_one : ∀ x, ∑ i, fn i x = 1
  tsupport_fn_subset : ∀ i, tsupport (fn i) ⊆ (chartAt E (center i)).source

variable [IsManifold 𝓘(ℂ, E) ω M]

/-- A compact Hausdorff complex manifold with finite-dimensional model admits a chart partition. -/
theorem ChartPartition.nonempty [FiniteDimensional ℂ E] [CompactSpace M] [T2Space M] :
    Nonempty (ChartPartition E M) := by
  have := isManifold_real (E := E) (M := M)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x : M ↦ (chartAt E x).source)
    (fun x ↦ (chartAt E x).open_source) (fun x _ ↦ mem_iUnion.2 ⟨x, mem_chart_source E x⟩)
  obtain ⟨f, hf⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, E) isClosed_univ
    (fun i : t ↦ (chartAt E (i : M)).source) (fun i ↦ (chartAt E _).open_source)
    (fun x _ ↦ by
      obtain ⟨i, hi, hx⟩ := mem_iUnion₂.1 (ht (mem_univ x))
      exact mem_iUnion.2 ⟨⟨i, hi⟩, hx⟩)
  let e := Fintype.equivFin t
  refine ⟨⟨Fintype.card t, fun i ↦ (e.symm i : M), fun i ↦ f (e.symm i),
    fun i ↦ (f _).contMDiff, fun i x ↦ f.nonneg _ x, fun x ↦ ?_, fun i ↦ hf _⟩⟩
  have h := f.sum_eq_one (mem_univ x)
  rw [finsum_eq_sum_of_fintype] at h
  rw [← h]
  exact e.symm.sum_comp (fun j ↦ f j x)

section SmoothFunctions

/-- The local representative of `φ • ρ` for a real function `φ`. -/
lemma localRep_smul_fun (φ : M → ℝ) (ρ : M → E [⋀^Fin k]→L[ℝ] ℂ) (x : M) (y : E) :
    localRep (fun z ↦ φ z • ρ z) x y = φ ((extChartAt 𝓘(ℂ, E) x).symm y) • localRep ρ x y := by
  ext v
  simp [localRep]

/-- A smooth real function on `M` is smooth in every chart, on the whole chart. -/
lemma contDiffOn_comp_extChartAt_symm {φ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ) (x : M) :
    ContDiffOn ℝ ∞ (φ ∘ (extChartAt 𝓘(ℂ, E) x).symm) (extChartAt 𝓘(ℂ, E) x).target := by
  have := isManifold_real (E := E) (M := M)
  have h := ((contMDiff_iff.1 hφ).2 x (φ x))
  simp only [extChartAt_real_eq, extChartAt_model_space_eq_id, PartialEquiv.refl_source,
    preimage_univ, inter_univ, PartialEquiv.refl_coe, Function.id_comp] at h
  exact h

/-- `φ • ρ` is smooth for a smooth real function `φ` and a smooth form `ρ`. -/
lemma IsSmoothForm.smul_fun {φ : M → ℝ} (hφ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ φ)
    {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (hρ : IsSmoothForm ρ) : IsSmoothForm fun z ↦ φ z • ρ z := by
  intro x
  have hfun : localRep (fun z ↦ φ z • ρ z) x =
      fun y ↦ (φ ∘ (extChartAt 𝓘(ℂ, E) x).symm) y • localRep ρ x y := by
    ext1 y
    exact localRep_smul_fun φ ρ x y
  rw [hfun]
  exact ((contDiffOn_comp_extChartAt_symm hφ x).contDiffAt
    ((isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x))).smul (hρ x)

end SmoothFunctions

section Support

/-- The integrand of a form supported in a chart vanishes outside the image of its support. -/
lemma localRep_apply_eq_zero_of_not_mem {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} {x : M} {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℂ, E) x).target)
    (hK : y ∉ extChartAt 𝓘(ℂ, E) x '' tsupport ρ) : localRep ρ x y = 0 := by
  have : ρ ((extChartAt 𝓘(ℂ, E) x).symm y) = 0 := by
    by_contra h
    exact hK ⟨_, subset_tsupport _ h, PartialEquiv.right_inv _ hy⟩
  simp only [localRep]
  rw [this]
  ext v
  simp

lemma localRep_finsetSum {ι : Type*} (s : Finset ι) (ρ : ι → M → E [⋀^Fin k]→L[ℝ] ℂ) (x : M) :
    localRep (∑ i ∈ s, ρ i) x = ∑ i ∈ s, localRep (ρ i) x := by
  ext y v
  simp [localRep, Finset.sum_apply]

/-- `∂`, `∂̄` are local: `partForm ε σ` vanishes outside the support of `σ`. -/
lemma partForm_eq_zero_of_notMem_tsupport {m : ℕ} (ε : ℂ) {σ : M → E [⋀^Fin m]→L[ℝ] ℂ} {x : M}
    (hx : x ∉ tsupport σ) : partForm ε σ x = 0 := by
  have h0 : σ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 hx
  have h0' : ∀ᶠ z in 𝓝 ((extChartAt 𝓘(ℂ, E) x).symm (extChartAt 𝓘(ℂ, E) x x)), σ z = 0 := by
    rw [extChartAt_to_inv]
    exact h0
  have h1 : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, E) x x), σ ((extChartAt 𝓘(ℂ, E) x).symm y) = 0 :=
    (continuousAt_extChartAt_symm (I := 𝓘(ℂ, E)) x).eventually h0'
  have hloc : localRep σ x =ᶠ[𝓝 (extChartAt 𝓘(ℂ, E) x x)] 0 := by
    filter_upwards [h1] with y hy
    simp only [localRep]
    rw [hy]
    ext v
    simp
  rw [partForm, partDeriv_congr ε hloc]
  simp [partDeriv, ← alternatizeUncurryFinCLM_apply]

lemma tsupport_partForm_subset {m : ℕ} (ε : ℂ) (σ : M → E [⋀^Fin m]→L[ℝ] ℂ) :
    tsupport (partForm ε σ) ⊆ tsupport σ :=
  closure_minimal (fun x hx ↦ by
    by_contra h
    exact hx (partForm_eq_zero_of_notMem_tsupport ε h)) (isClosed_tsupport _)

lemma IsSmoothForm.finsetSum {m : ℕ} {ι : Type*} (s : Finset ι) {σ : ι → M → E [⋀^Fin m]→L[ℝ] ℂ}
    (hσ : ∀ i ∈ s, IsSmoothForm (σ i)) : IsSmoothForm (∑ i ∈ s, σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isSmoothForm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hσ a (Finset.mem_insert_self a s)).add
      (ih fun i hi ↦ hσ i (Finset.mem_insert_of_mem hi))

lemma partForm_finsetSum {m : ℕ} (ε : ℂ) {ι : Type*} (s : Finset ι)
    {σ : ι → M → E [⋀^Fin m]→L[ℝ] ℂ} (hσ : ∀ i ∈ s, IsSmoothForm (σ i)) :
    partForm ε (∑ i ∈ s, σ i) = ∑ i ∈ s, partForm ε (σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext1 x
    simp only [Finset.sum_empty, Pi.zero_apply]
    exact partForm_eq_zero_of_notMem_tsupport ε (by simp)
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, IsSmoothForm (σ i) := fun i hi ↦ hσ i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      partForm_add ε (hσ a (Finset.mem_insert_self a s)) (IsSmoothForm.finsetSum s hs), ih hs]

end Support

section Integral

variable [FiniteDimensional ℂ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
  [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℂ E] in
/-- A smooth form with compact support inside the domain of the chart at `x` has integrable local
representative on the chart. -/
lemma integrableOn_localRep {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (hρ : IsSmoothForm ρ) {x : M}
    (hc : IsCompact (tsupport ρ)) (hsupp : tsupport ρ ⊆ (chartAt E x).source) (b : Fin k → E) :
    IntegrableOn (fun y ↦ localRep ρ x y b) (extChartAt 𝓘(ℂ, E) x).target μ := by
  set K := extChartAt 𝓘(ℂ, E) x '' tsupport ρ
  have hsupp' : tsupport ρ ⊆ (extChartAt 𝓘(ℂ, E) x).source := by
    rwa [extChartAt_source_eq]
  have hKc : IsCompact K := hc.image_of_continuousOn ((continuousOn_extChartAt x).mono hsupp')
  have hKT : K ⊆ (extChartAt 𝓘(ℂ, E) x).target := by
    rintro _ ⟨z, hz, rfl⟩
    exact (extChartAt 𝓘(ℂ, E) x).map_source (hsupp' hz)
  have hcont : ContinuousOn (fun y ↦ localRep ρ x y b) (extChartAt 𝓘(ℂ, E) x).target := by
    intro y hy
    exact ((ContinuousAlternatingMap.apply ℝ E ℂ b).continuous.continuousAt.comp
      (hρ.contDiffAt_localRep x hy).continuousAt).continuousWithinAt
  have hKint : IntegrableOn (fun y ↦ localRep ρ x y b) K μ :=
    (hcont.mono hKT).integrableOn_compact hKc
  refine hKint.of_forall_sdiff_eq_zero (isOpen_extChartAt_target x).measurableSet ?_
  rintro y ⟨hy, hyK⟩
  rw [localRep_apply_eq_zero_of_not_mem hy hyK]
  rfl

/-- The integral over the chart at `x` of the local representative of `ρ`, evaluated on `b`. -/
def chartIntegral (b : Fin k → E) (ρ : M → E [⋀^Fin k]→L[ℝ] ℂ) (x : M) : ℂ :=
  ∫ y in (extChartAt 𝓘(ℂ, E) x).target, localRep ρ x y b ∂μ

lemma chartIntegral_eq (hk : Module.finrank ℝ E = k) (b : Fin k → E)
    {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} {x x' : M}
    (hsupp : ∀ z, ρ z ≠ 0 → z ∈ (chartAt E x).source ∩ (chartAt E x').source) :
    chartIntegral μ b ρ x = chartIntegral μ b ρ x' :=
  setIntegral_localRep_eq μ hk b x x' hsupp

omit [FiniteDimensional ℂ E] in
lemma chartIntegral_finsetSum {ι : Type*} (s : Finset ι) {ρ : ι → M → E [⋀^Fin k]→L[ℝ] ℂ}
    (hρ : ∀ i ∈ s, IsSmoothForm (ρ i)) (hc : ∀ i ∈ s, IsCompact (tsupport (ρ i))) {x : M}
    (hsupp : ∀ i ∈ s, tsupport (ρ i) ⊆ (chartAt E x).source) (b : Fin k → E) :
    chartIntegral μ b (∑ i ∈ s, ρ i) x = ∑ i ∈ s, chartIntegral μ b (ρ i) x := by
  rw [chartIntegral, localRep_finsetSum]
  simp only [ContinuousAlternatingMap.sum_apply, Finset.sum_apply]
  exact integral_finsetSum s fun i hi ↦ integrableOn_localRep μ (hρ i hi) (hc i hi) (hsupp i hi) b

/-- The **integral over `M`** of a top-degree form `ρ`, computed with the chart partition `P`, the
Haar measure `μ` on the model space and the vectors `b`: `Σᵢ ∫_{φᵢ(Uᵢ)} (χᵢ ρ)ᵢ(y)(b) dμ(y)`. It
does not depend on `P` (`Hodge.integralForm_eq_of_partition`). -/
def integralForm (P : ChartPartition E M) (b : Fin k → E) (ρ : M → E [⋀^Fin k]→L[ℝ] ℂ) : ℂ :=
  ∑ i, chartIntegral μ b (fun z ↦ P.fn i z • ρ z) (P.center i)

/-- The integral over `M` does not depend on the chart partition. -/
theorem integralForm_eq_of_partition [CompactSpace M] (hk : Module.finrank ℝ E = k)
    (b : Fin k → E) {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (hρ : IsSmoothForm ρ)
    (P Q : ChartPartition E M) : integralForm μ P b ρ = integralForm μ Q b ρ := by
  let σ : Fin P.card → Fin Q.card → M → E [⋀^Fin k]→L[ℝ] ℂ :=
    fun i j z ↦ Q.fn j z • P.fn i z • ρ z
  have hσ : ∀ i j, IsSmoothForm (σ i j) := fun i j ↦
    (hρ.smul_fun (P.contMDiff_fn i)).smul_fun (Q.contMDiff_fn j)
  have hσP : ∀ i j, tsupport (σ i j) ⊆ tsupport (P.fn i) := fun i j ↦
    (tsupport_smul_subset_right _ _).trans (tsupport_smul_subset_left _ _)
  have hσQ : ∀ i j, tsupport (σ i j) ⊆ tsupport (Q.fn j) := fun i j ↦
    tsupport_smul_subset_left _ _
  have hσc : ∀ i j, IsCompact (tsupport (σ i j)) := fun i j ↦ (isClosed_tsupport _).isCompact
  have hP : ∀ i, (fun z ↦ P.fn i z • ρ z) = ∑ j, σ i j := by
    intro i
    ext1 z
    simp only [σ, Finset.sum_apply, ← Finset.sum_smul, Q.sum_fn_eq_one, one_smul]
  have hQ : ∀ j, (fun z ↦ Q.fn j z • ρ z) = ∑ i, σ i j := by
    intro j
    ext1 z
    simp only [σ, Finset.sum_apply, ← Finset.smul_sum, ← Finset.sum_smul, P.sum_fn_eq_one,
      one_smul]
  have key : ∀ i j, chartIntegral μ b (σ i j) (P.center i) =
      chartIntegral μ b (σ i j) (Q.center j) := fun i j ↦
    chartIntegral_eq μ hk b fun z hz ↦
      ⟨P.tsupport_fn_subset i (hσP i j (subset_tsupport _ hz)),
        Q.tsupport_fn_subset j (hσQ i j (subset_tsupport _ hz))⟩
  unfold integralForm
  calc ∑ i, chartIntegral μ b (fun z ↦ P.fn i z • ρ z) (P.center i)
      = ∑ i, ∑ j, chartIntegral μ b (σ i j) (P.center i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hP i]
        exact chartIntegral_finsetSum μ _ (fun j _ ↦ hσ i j) (fun j _ ↦ hσc i j)
          (fun j _ ↦ (hσP i j).trans (P.tsupport_fn_subset i)) b
    _ = ∑ j, ∑ i, chartIntegral μ b (σ i j) (Q.center j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ key i j
    _ = ∑ j, chartIntegral μ b (fun z ↦ Q.fn j z • ρ z) (Q.center j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hQ j]
        exact (chartIntegral_finsetSum μ _ (fun i _ ↦ hσ i j) (fun i _ ↦ hσc i j)
          (fun i _ ↦ (hσQ i j).trans (Q.tsupport_fn_subset j)) b).symm

/-- **Stokes in a chart**: for a smooth form `σ` with compact support in the domain of the chart
at `x`, the integral of `∂σ`, `∂̄σ` over the chart vanishes. -/
theorem chartIntegral_partForm_eq_zero {m : ℕ} (b : Fin (m + 1) → E)
    {σ : M → E [⋀^Fin m]→L[ℝ] ℂ} (hσ : IsSmoothForm σ) {x : M} (hc : IsCompact (tsupport σ))
    (hsupp : tsupport σ ⊆ (chartAt E x).source) (ε : ℂ) :
    chartIntegral μ b (partForm ε σ) x = 0 := by
  set T := (extChartAt 𝓘(ℂ, E) x).target
  set K := extChartAt 𝓘(ℂ, E) x '' tsupport σ
  have hsupp' : tsupport σ ⊆ (extChartAt 𝓘(ℂ, E) x).source := by rwa [extChartAt_source_eq]
  have hKc : IsCompact K := hc.image_of_continuousOn ((continuousOn_extChartAt x).mono hsupp')
  have hKT : K ⊆ T := by
    rintro _ ⟨z, hz, rfl⟩
    exact (extChartAt 𝓘(ℂ, E) x).map_source (hsupp' hz)
  have hTo : IsOpen T := isOpen_extChartAt_target x
  classical
  let g : E → E [⋀^Fin m]→L[ℝ] ℂ := fun y ↦ if y ∈ T then localRep σ x y else 0
  have hgT : ∀ y ∈ T, g =ᶠ[𝓝 y] localRep σ x := fun y hy ↦
    Filter.eventuallyEq_of_mem (hTo.mem_nhds hy) fun y' hy' ↦ by simp [g, hy']
  have hgK : ∀ y ∉ K, g =ᶠ[𝓝 y] 0 := by
    intro y hy
    filter_upwards [hKc.isClosed.isOpen_compl.mem_nhds hy] with y' hy'
    by_cases h : y' ∈ T
    · simp only [g, h, ite_true, Pi.zero_apply]
      exact localRep_apply_eq_zero_of_not_mem h hy'
    · simp [g, h]
  have hg : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ T
    · exact ((hσ.contDiffAt_localRep x hy).of_le (by simp)).congr_of_eventuallyEq (hgT y hy)
    · exact contDiffAt_const.congr_of_eventuallyEq (hgK y fun h ↦ hy (hKT h))
  have hgc : HasCompactSupport g := by
    refine HasCompactSupport.intro hKc fun y hy ↦ ?_
    exact (hgK y hy).self_of_nhds
  have hpart : ∀ y ∈ T, localRep (partForm ε σ) x y = partDeriv ε g y := fun y hy ↦ by
    rw [localRep_partForm hσ ε x hy, partDeriv_congr ε (hgT y hy)]
  have hout : ∀ y ∉ T, partDeriv ε g y b = 0 := by
    intro y hy
    rw [partDeriv_congr ε (hgK y fun h ↦ hy (hKT h))]
    simp [partDeriv, ← alternatizeUncurryFinCLM_apply]
  rw [chartIntegral, setIntegral_congr_fun hTo.measurableSet fun y hy ↦ by
    rw [hpart y hy], setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  exact integral_partDeriv_eq_zero μ ε hg hgc b

/-- **Stokes' theorem on a compact complex manifold** for `∂`, `∂̄` (any `partForm ε`): the integral
over `M` of `partForm ε τ` vanishes for every smooth form `τ` of degree `dim_ℝ M - 1`. -/
theorem integralForm_partForm_eq_zero [CompactSpace M] {m : ℕ}
    (hk : Module.finrank ℝ E = m + 1) (b : Fin (m + 1) → E) (P : ChartPartition E M)
    {τ : M → E [⋀^Fin m]→L[ℝ] ℂ} (hτ : IsSmoothForm τ) (ε : ℂ) :
    integralForm μ P b (partForm ε τ) = 0 := by
  let σ : Fin P.card → M → E [⋀^Fin m]→L[ℝ] ℂ := fun j z ↦ P.fn j z • τ z
  have hσ : ∀ j, IsSmoothForm (σ j) := fun j ↦ hτ.smul_fun (P.contMDiff_fn j)
  have hτsum : τ = ∑ j, σ j := by
    ext1 z
    simp only [σ, Finset.sum_apply, ← Finset.sum_smul, P.sum_fn_eq_one, one_smul]
  have hpf : partForm ε τ = ∑ j, partForm ε (σ j) := by
    conv_lhs => rw [hτsum]
    exact partForm_finsetSum ε _ fun j _ ↦ hσ j
  let θ : Fin P.card → Fin P.card → M → E [⋀^Fin (m + 1)]→L[ℝ] ℂ :=
    fun i j z ↦ P.fn i z • partForm ε (σ j) z
  have hθ : ∀ i j, IsSmoothForm (θ i j) := fun i j ↦
    ((hσ j).partForm ε).smul_fun (P.contMDiff_fn i)
  have hθi : ∀ i j, tsupport (θ i j) ⊆ tsupport (P.fn i) := fun i j ↦
    tsupport_smul_subset_left _ _
  have hθj : ∀ i j, tsupport (θ i j) ⊆ tsupport (P.fn j) := fun i j ↦
    (tsupport_smul_subset_right _ _).trans
      ((tsupport_partForm_subset ε _).trans (tsupport_smul_subset_left _ _))
  have hθc : ∀ i j, IsCompact (tsupport (θ i j)) := fun _ _ ↦ (isClosed_tsupport _).isCompact
  have hrow : ∀ i, (fun z ↦ P.fn i z • partForm ε τ z) = ∑ j, θ i j := by
    intro i
    ext1 z
    rw [hpf]
    simp only [θ, Finset.sum_apply, Finset.smul_sum]
  have hcol : ∀ j, partForm ε (σ j) = ∑ i, θ i j := by
    intro j
    ext1 z
    simp only [θ, Finset.sum_apply, ← Finset.sum_smul, P.sum_fn_eq_one, one_smul]
  unfold integralForm
  calc ∑ i, chartIntegral μ b (fun z ↦ P.fn i z • partForm ε τ z) (P.center i)
      = ∑ i, ∑ j, chartIntegral μ b (θ i j) (P.center i) := by
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [hrow i]
        exact chartIntegral_finsetSum μ _ (fun j _ ↦ hθ i j) (fun j _ ↦ hθc i j)
          (fun j _ ↦ (hθi i j).trans (P.tsupport_fn_subset i)) b
    _ = ∑ j, ∑ i, chartIntegral μ b (θ i j) (P.center j) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦
          chartIntegral_eq μ hk b fun z hz ↦
            ⟨P.tsupport_fn_subset i (hθi i j (subset_tsupport _ hz)),
              P.tsupport_fn_subset j (hθj i j (subset_tsupport _ hz))⟩
    _ = ∑ j, chartIntegral μ b (partForm ε (σ j)) (P.center j) := by
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [hcol j]
        exact (chartIntegral_finsetSum μ _ (fun i _ ↦ hθ i j) (fun i _ ↦ hθc i j)
          (fun i _ ↦ (hθj i j).trans (P.tsupport_fn_subset j)) b).symm
    _ = 0 := Finset.sum_eq_zero fun j _ ↦
        chartIntegral_partForm_eq_zero μ b (hσ j) (isClosed_tsupport _).isCompact
          ((tsupport_smul_subset_left _ _).trans (P.tsupport_fn_subset j)) ε

omit [FiniteDimensional ℂ E] in
lemma integralForm_add [CompactSpace M] (P : ChartPartition E M) (b : Fin k → E)
    {ρ₁ ρ₂ : M → E [⋀^Fin k]→L[ℝ] ℂ} (h₁ : IsSmoothForm ρ₁) (h₂ : IsSmoothForm ρ₂) :
    integralForm μ P b (ρ₁ + ρ₂) = integralForm μ P b ρ₁ + integralForm μ P b ρ₂ := by
  unfold integralForm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hsum : (fun z ↦ P.fn i z • (ρ₁ + ρ₂) z) =
      ∑ j : Fin 2, ![fun z ↦ P.fn i z • ρ₁ z, fun z ↦ P.fn i z • ρ₂ z] j := by
    ext1 z
    simp [Fin.sum_univ_two, smul_add]
  rw [hsum, chartIntegral_finsetSum μ _ (by
      intro j _
      fin_cases j <;> simp [h₁.smul_fun (P.contMDiff_fn i), h₂.smul_fun (P.contMDiff_fn i)])
    (fun j _ ↦ (isClosed_tsupport _).isCompact)
    (by
      intro j _
      fin_cases j <;> exact (tsupport_smul_subset_left _ _).trans (P.tsupport_fn_subset i)) b]
  simp [Fin.sum_univ_two]

/-- **Stokes' theorem on a compact complex manifold**: `∫_M dτ = 0` for every smooth form `τ` of
degree `dim_ℝ M - 1`. -/
theorem integralForm_extDerivForm_eq_zero [CompactSpace M] {m : ℕ}
    (hk : Module.finrank ℝ E = m + 1) (b : Fin (m + 1) → E) (P : ChartPartition E M)
    {τ : M → E [⋀^Fin m]→L[ℝ] ℂ} (hτ : IsSmoothForm τ) :
    integralForm μ P b (extDerivForm τ) = 0 := by
  rw [extDerivForm_eq_add, integralForm_add μ P b (hτ.delForm) (hτ.dbarForm), delForm, dbarForm,
    integralForm_partForm_eq_zero μ hk b P hτ, integralForm_partForm_eq_zero μ hk b P hτ, add_zero]

end Integral

section Positivity

omit [IsManifold 𝓘(ℂ, E) ω M] in
/-- A set integral of a function with values in `[0, ∞) ⊆ ℂ` lies in `[0, ∞)`. -/
lemma _root_.MeasureTheory.setIntegral_nonneg_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {f : X → ℂ}
    {s : Set X} (hs : MeasurableSet s) (hf : ∀ y ∈ s, 0 ≤ f y) : 0 ≤ ∫ y in s, f y ∂μ := by
  have h : ∀ y ∈ s, f y = ((f y).re : ℂ) := fun y hy ↦
    Complex.ext (by simp) (by simp [← (Complex.nonneg_iff.1 (hf y hy)).2])
  rw [setIntegral_congr_fun hs h, integral_complex_ofReal]
  exact Complex.zero_le_real.2 (setIntegral_nonneg hs fun y hy ↦ (Complex.nonneg_iff.1 (hf y hy)).1)

variable [FiniteDimensional ℂ E]

/-- The value of a local representative of a top-degree form is `|det_ℂ|²` times the value of
the form, read in the chart at the point. -/
lemma localRep_apply_eq_normSq_det_mul (hk : Module.finrank ℝ E = k) (b : Fin k → E)
    (ρ : M → E [⋀^Fin k]→L[ℝ] ℂ) (x : M) (y : E) :
    localRep ρ x y b = (Complex.normSq (LinearMap.det
      ((tangentCoordChange 𝓘(ℂ, E) x ((extChartAt 𝓘(ℂ, E) x).symm y)
        ((extChartAt 𝓘(ℂ, E) x).symm y) : E →L[ℂ] E) : E →ₗ[ℂ] E)) : ℂ) *
      ρ ((extChartAt 𝓘(ℂ, E) x).symm y) b := by
  rw [localRep, compContinuousLinearMap_apply, ContinuousAlternatingMap.map_comp_eq_det_mul hk,
    ContinuousLinearMap.det_restrictScalars_eq_normSq]

omit [FiniteDimensional ℂ E] in
/-- The change of coordinates has nonzero determinant on the overlap of the charts. -/
lemma det_tangentCoordChange_ne_zero {x w : M} (hw : w ∈ (extChartAt 𝓘(ℂ, E) x).source) :
    LinearMap.det ((tangentCoordChange 𝓘(ℂ, E) x w w : E →L[ℂ] E) : E →ₗ[ℂ] E) ≠ 0 := by
  have h : (tangentCoordChange 𝓘(ℂ, E) w x w).comp (tangentCoordChange 𝓘(ℂ, E) x w w) =
      ContinuousLinearMap.id ℂ E := by
    ext v
    rw [ContinuousLinearMap.comp_apply, tangentCoordChange_comp
      ⟨⟨hw, mem_extChartAt_source w⟩, hw⟩, tangentCoordChange_self hw]
    rfl
  intro h0
  have := congrArg (fun f : E →L[ℂ] E ↦ LinearMap.det (f : E →ₗ[ℂ] E)) h
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id] at this
  change LinearMap.det (((tangentCoordChange 𝓘(ℂ, E) w x w : E →L[ℂ] E) : E →ₗ[ℂ] E).comp
    ((tangentCoordChange 𝓘(ℂ, E) x w w : E →L[ℂ] E) : E →ₗ[ℂ] E)) = 1 at this
  rw [LinearMap.det_comp, h0, mul_zero] at this
  exact zero_ne_one this

/-- The integrand of `integralForm` for a form taking nonnegative values on `b`. -/
lemma localRep_smul_fun_apply_nonneg (hk : Module.finrank ℝ E = k) (b : Fin k → E)
    {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (hpos : ∀ z, 0 ≤ ρ z b) {φ : M → ℝ} (hφ : ∀ z, 0 ≤ φ z)
    (x : M) (y : E) : 0 ≤ localRep (fun z ↦ φ z • ρ z) x y b := by
  rw [localRep_apply_eq_normSq_det_mul hk]
  simp only [ContinuousAlternatingMap.smul_apply, Complex.real_smul]
  exact mul_nonneg (Complex.zero_le_real.2 (Complex.normSq_nonneg _))
    (mul_nonneg (Complex.zero_le_real.2 (hφ _)) (hpos _))

variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

omit [μ.IsAddHaarMeasure] in
/-- **Positivity of the integral**: if `ρ z b ≥ 0` for every `z` (read in the chart at `z`), then
`∫_M ρ ≥ 0` (in the order of `ℂ`: real and nonnegative). -/
theorem integralForm_nonneg (hk : Module.finrank ℝ E = k) (b : Fin k → E)
    (P : ChartPartition E M) {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (hpos : ∀ z, 0 ≤ ρ z b) :
    0 ≤ integralForm μ P b ρ :=
  Finset.sum_nonneg fun i _ ↦ MeasureTheory.setIntegral_nonneg_complex μ
    (isOpen_extChartAt_target _).measurableSet fun y _ ↦
      localRep_smul_fun_apply_nonneg hk b hpos (P.fn_nonneg i) _ y

/-- **Strict positivity of the integral**: if the smooth top-degree form `ρ` satisfies
`ρ z b ≥ 0` for every `z` and `ρ z₀ b > 0` at some point, then `∫_M ρ > 0`. -/
theorem integralForm_pos [CompactSpace M] (hk : Module.finrank ℝ E = k) (b : Fin k → E)
    (P : ChartPartition E M) {ρ : M → E [⋀^Fin k]→L[ℝ] ℂ} (hρ : IsSmoothForm ρ)
    (hpos : ∀ z, 0 ≤ ρ z b) {z₀ : M} (hz₀ : 0 < ρ z₀ b) : 0 < integralForm μ P b ρ := by
  obtain ⟨i, -, hi⟩ : ∃ i ∈ Finset.univ, 0 < P.fn i z₀ := by
    by_contra h
    push Not at h
    have := P.sum_fn_eq_one z₀
    have h' : ∑ i, P.fn i z₀ ≤ 0 := Finset.sum_nonpos fun i hi ↦ h i hi
    linarith
  refine Finset.sum_pos' (fun j _ ↦ MeasureTheory.setIntegral_nonneg_complex μ
    (isOpen_extChartAt_target _).measurableSet fun y _ ↦
      localRep_smul_fun_apply_nonneg hk b hpos (P.fn_nonneg j) _ y) ⟨i, Finset.mem_univ _, ?_⟩
  -- the `i`-th chart integral is positive
  set x := P.center i
  set T := (extChartAt 𝓘(ℂ, E) x).target
  set σ : M → E [⋀^Fin k]→L[ℝ] ℂ := fun z ↦ P.fn i z • ρ z
  have hσ : IsSmoothForm σ := hρ.smul_fun (P.contMDiff_fn i)
  set g : E → ℝ := fun y ↦ (localRep σ x y b).re
  have hz₀x : z₀ ∈ (extChartAt 𝓘(ℂ, E) x).source := by
    rw [extChartAt_source_eq]
    exact P.tsupport_fn_subset i (subset_tsupport _ hi.ne')
  set y₀ := extChartAt 𝓘(ℂ, E) x z₀
  have hy₀ : y₀ ∈ T := (extChartAt 𝓘(ℂ, E) x).map_source hz₀x
  have hreal : ∀ y, localRep σ x y b = (g y : ℂ) := fun y ↦ by
    have h := Complex.nonneg_iff.1
      (localRep_smul_fun_apply_nonneg hk b hpos (P.fn_nonneg i) x y)
    exact Complex.ext (by simp [g]) (by simpa [g] using h.2.symm)
  have hgnn : ∀ y, 0 ≤ g y := fun y ↦
    (Complex.nonneg_iff.1 (localRep_smul_fun_apply_nonneg hk b hpos (P.fn_nonneg i) x y)).1
  have hgy₀ : 0 < g y₀ := by
    have h1 := localRep_apply_eq_normSq_det_mul hk b σ x y₀
    rw [PartialEquiv.left_inv _ hz₀x] at h1
    have hdet := det_tangentCoordChange_ne_zero hz₀x
    have h2 : 0 < localRep σ x y₀ b := by
      rw [h1]
      simp only [σ, ContinuousAlternatingMap.smul_apply, Complex.real_smul]
      exact mul_pos (Complex.zero_lt_real.2 (Complex.normSq_pos.2 hdet))
        (mul_pos (Complex.zero_lt_real.2 hi) hz₀)
    rw [hreal] at h2
    exact Complex.zero_lt_real.1 h2
  have hgc : ContinuousOn g T := fun y hy ↦
    (Complex.continuous_re.continuousAt.comp ((ContinuousAlternatingMap.apply ℝ E ℂ b).continuous
      |>.continuousAt.comp (hσ.contDiffAt_localRep x hy).continuousAt)).continuousWithinAt
  have hgint : IntegrableOn g T μ :=
    (integrableOn_localRep μ hσ (isClosed_tsupport _).isCompact
      ((tsupport_smul_subset_left _ _).trans (P.tsupport_fn_subset i)) b).re
  have hpos' : 0 < ∫ y in T, g y ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae (Eventually.of_forall hgnn) hgint]
    -- an open neighbourhood of `y₀` inside `T` where `g > 0`
    obtain ⟨U, hUo, hy₀U, hU⟩ : ∃ U, IsOpen U ∧ y₀ ∈ U ∧ U ⊆ {y | 0 < g y} ∩ T := by
      have := (hgc y₀ hy₀).preimage_mem_nhdsWithin (isOpen_Ioi.mem_nhds hgy₀)
      rw [mem_nhdsWithin] at this
      obtain ⟨U, hUo, hy₀U, hU⟩ := this
      exact ⟨U ∩ T, hUo.inter (isOpen_extChartAt_target x), ⟨hy₀U, hy₀⟩,
        fun y hy ↦ ⟨hU ⟨hy.1, hy.2⟩, hy.2⟩⟩
    refine lt_of_lt_of_le (hUo.measure_pos μ ⟨y₀, hy₀U⟩) (measure_mono fun y hy ↦ ?_)
    exact ⟨(hU hy).1.ne', (hU hy).2⟩
  change 0 < chartIntegral μ b σ x
  rw [chartIntegral, setIntegral_congr_fun (isOpen_extChartAt_target x).measurableSet
    (fun y _ ↦ hreal y), integral_complex_ofReal]
  exact Complex.zero_lt_real.2 hpos'

end Positivity

end Hodge
