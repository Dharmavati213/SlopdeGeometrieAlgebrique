/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.PowerSeriesExpansion
import Mathlib.Analysis.Analytic.Composition
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Taylor series and substitution of convergent power series

For a function `F : 𝕜^σ → 𝕜` analytic at `0`, `taylorSeries F` is the unique convergent power
series whose sum agrees with `F` near `0`. Composing with a germ of analytic map
`φ : (𝕜^τ, 0) → (𝕜^σ, 0)` gives the substitution homomorphism
`substAnalyticHom φ : 𝕜{X_σ} →ₐ[𝕜] 𝕜{X_τ}`, `f ↦ f ∘ φ`, which is functorial in `φ`. This covers
changes of coordinates, restriction to linear subspaces and substitution of convergent series
for variables ([Grauert–Remmert, *Analytische Stellenalgebren*, I §1]).
-/

open scoped NNReal ENNReal Topology
open Filter

noncomputable section

namespace MvPowerSeries

variable {σ τ υ : Type*} [Fintype σ] [Fintype τ] [Fintype υ]
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-! ### Taylor series -/

section Taylor

open Classical in
/-- The Taylor series at `0` of a function analytic at `0` (defined as `0` otherwise). -/
def taylorSeries (F : (σ → 𝕜) → 𝕜) : MvPowerSeries σ 𝕜 :=
  if h : AnalyticAt 𝕜 F 0 then (exists_convergent_eventuallyEq h).choose else 0

variable {F G : (σ → 𝕜) → 𝕜}

lemma taylorSeries_mem_convergent (F : (σ → 𝕜) → 𝕜) : taylorSeries F ∈ convergent σ 𝕜 := by
  rw [taylorSeries]
  split_ifs with h
  · exact (exists_convergent_eventuallyEq h).choose_spec.1
  · exact zero_mem _

lemma eventuallyEq_tsumEval_taylorSeries (hF : AnalyticAt 𝕜 F 0) :
    F =ᶠ[𝓝 0] tsumEval (taylorSeries F) := by
  rw [taylorSeries, dite_eq_left hF]
  exact (exists_convergent_eventuallyEq hF).choose_spec.2

/-- The Taylor series is characterized by its sum near `0`. -/
lemma taylorSeries_eq {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜)
    (h : F =ᶠ[𝓝 0] tsumEval f) : taylorSeries F = f := by
  have hF : AnalyticAt 𝕜 F 0 := (analyticAt_tsumEval hf).congr h.symm
  exact eq_of_tsumEval_eventuallyEq (taylorSeries_mem_convergent F) hf
    ((eventuallyEq_tsumEval_taylorSeries hF).symm.trans h)

@[simp] lemma taylorSeries_tsumEval {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) :
    taylorSeries (tsumEval f) = f :=
  taylorSeries_eq hf EventuallyEq.rfl

lemma taylorSeries_congr (h : F =ᶠ[𝓝 0] G) : taylorSeries F = taylorSeries G := by
  by_cases hF : AnalyticAt 𝕜 F 0
  · exact (taylorSeries_eq (taylorSeries_mem_convergent F)
      (h.symm.trans (eventuallyEq_tsumEval_taylorSeries hF))).symm
  · have hG : ¬ AnalyticAt 𝕜 G 0 := fun hG ↦ hF (hG.congr h.symm)
    rw [taylorSeries, taylorSeries, dite_eq_right hF, dite_eq_right hG]

lemma taylorSeries_const (c : 𝕜) : taylorSeries (fun _ : σ → 𝕜 ↦ c) = C c :=
  taylorSeries_eq (algebraMap_mem (convergent σ 𝕜) c) (Eventually.of_forall fun _ ↦ by simp)

lemma taylorSeries_add (hF : AnalyticAt 𝕜 F 0) (hG : AnalyticAt 𝕜 G 0) :
    taylorSeries (F + G) = taylorSeries F + taylorSeries G := by
  refine taylorSeries_eq (add_mem (taylorSeries_mem_convergent F) (taylorSeries_mem_convergent G))
    ?_
  filter_upwards [eventuallyEq_tsumEval_taylorSeries hF, eventuallyEq_tsumEval_taylorSeries hG,
    eventually_tsumEval_add_mul (taylorSeries_mem_convergent F)
      (taylorSeries_mem_convergent G)] with z h₁ h₂ h₃
  rw [Pi.add_apply, h₁, h₂, h₃.1]

lemma taylorSeries_mul (hF : AnalyticAt 𝕜 F 0) (hG : AnalyticAt 𝕜 G 0) :
    taylorSeries (F * G) = taylorSeries F * taylorSeries G := by
  refine taylorSeries_eq (mul_mem (taylorSeries_mem_convergent F) (taylorSeries_mem_convergent G))
    ?_
  filter_upwards [eventuallyEq_tsumEval_taylorSeries hF, eventuallyEq_tsumEval_taylorSeries hG,
    eventually_tsumEval_add_mul (taylorSeries_mem_convergent F)
      (taylorSeries_mem_convergent G)] with z h₁ h₂ h₃
  rw [Pi.mul_apply, h₁, h₂, h₃.2]

lemma taylorSeries_coord (i : σ) : taylorSeries (fun z : σ → 𝕜 ↦ z i) = X i :=
  taylorSeries_eq (X_mem_convergent i) (Eventually.of_forall fun z ↦ by simp)

end Taylor

/-! ### Substitution of analytic map germs -/

section Subst

variable {φ : (τ → 𝕜) → σ → 𝕜}

/-- The composition `f ∘ φ` of a power series with a map `φ : 𝕜^τ → 𝕜^σ`, as a power series
(meaningful when `f` is convergent, `φ` is analytic at `0` and `φ 0 = 0`). -/
def substAnalytic (φ : (τ → 𝕜) → σ → 𝕜) (f : MvPowerSeries σ 𝕜) : MvPowerSeries τ 𝕜 :=
  taylorSeries fun z ↦ tsumEval f (φ z)

omit [Fintype σ] in
lemma substAnalytic_mem_convergent (φ : (τ → 𝕜) → σ → 𝕜) (f : MvPowerSeries σ 𝕜) :
    substAnalytic φ f ∈ convergent τ 𝕜 :=
  taylorSeries_mem_convergent _

variable (hφ : AnalyticAt 𝕜 φ 0) (hφ0 : φ 0 = 0)
include hφ hφ0

lemma analyticAt_tsumEval_comp {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) :
    AnalyticAt 𝕜 (fun z ↦ tsumEval f (φ z)) 0 :=
  (analyticAt_tsumEval hf).comp_of_eq hφ hφ0

omit [CompleteSpace 𝕜] [Fintype υ] in
lemma tendsto_zero_of_analyticAt : Tendsto φ (𝓝 0) (𝓝 0) := by
  simpa [hφ0] using hφ.continuousAt.tendsto

/-- The defining property of `substAnalytic`: near `0`, its sum is `f ∘ φ`. -/
lemma tsumEval_substAnalytic {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) :
    (fun z ↦ tsumEval f (φ z)) =ᶠ[𝓝 0] tsumEval (substAnalytic φ f) :=
  eventuallyEq_tsumEval_taylorSeries (analyticAt_tsumEval_comp hφ hφ0 hf)

/-- Substitution of an analytic map germ `φ : (𝕜^τ, 0) → (𝕜^σ, 0)` into convergent power
series. -/
def substAnalyticHom : convergent σ 𝕜 →ₐ[𝕜] convergent τ 𝕜 where
  toFun f := ⟨substAnalytic φ f.1, substAnalytic_mem_convergent φ f.1⟩
  map_one' := Subtype.ext <| by
    refine taylorSeries_eq (one_mem _) (Eventually.of_forall fun z ↦ ?_)
    simp
  map_mul' f g := Subtype.ext <| by
    change substAnalytic φ (f.1 * g.1) = substAnalytic φ f.1 * substAnalytic φ g.1
    refine taylorSeries_eq (mul_mem (substAnalytic_mem_convergent φ f.1)
      (substAnalytic_mem_convergent φ g.1)) ?_
    filter_upwards [(tendsto_zero_of_analyticAt hφ hφ0).eventually
        (eventually_tsumEval_add_mul f.2 g.2), tsumEval_substAnalytic hφ hφ0 f.2,
      tsumEval_substAnalytic hφ hφ0 g.2, eventually_tsumEval_add_mul
        (substAnalytic_mem_convergent φ f.1) (substAnalytic_mem_convergent φ g.1)]
      with z h₁ h₂ h₃ h₄
    rw [h₁.2, h₄.2, h₂, h₃]
  map_zero' := Subtype.ext <| by
    refine taylorSeries_eq (zero_mem _) (Eventually.of_forall fun z ↦ ?_)
    simp [tsumEval]
  map_add' f g := Subtype.ext <| by
    change substAnalytic φ (f.1 + g.1) = substAnalytic φ f.1 + substAnalytic φ g.1
    refine taylorSeries_eq (add_mem (substAnalytic_mem_convergent φ f.1)
      (substAnalytic_mem_convergent φ g.1)) ?_
    filter_upwards [(tendsto_zero_of_analyticAt hφ hφ0).eventually
        (eventually_tsumEval_add_mul f.2 g.2), tsumEval_substAnalytic hφ hφ0 f.2,
      tsumEval_substAnalytic hφ hφ0 g.2, eventually_tsumEval_add_mul
        (substAnalytic_mem_convergent φ f.1) (substAnalytic_mem_convergent φ g.1)]
      with z h₁ h₂ h₃ h₄
    rw [h₁.1, h₄.1, h₂, h₃]
  commutes' c := Subtype.ext <| by
    refine taylorSeries_eq (algebraMap_mem _ c) (Eventually.of_forall fun z ↦ ?_)
    simp [MvPowerSeries.algebraMap_apply]

@[simp] lemma substAnalyticHom_apply (f : convergent σ 𝕜) :
    (substAnalyticHom hφ hφ0 f : MvPowerSeries τ 𝕜) = substAnalytic φ f.1 := rfl

omit hφ hφ0 in
lemma substAnalytic_id {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) :
    substAnalytic id f = f :=
  taylorSeries_tsumEval hf

/-- Functoriality of substitution. -/
lemma substAnalytic_substAnalytic {ψ : (υ → 𝕜) → τ → 𝕜} (hψ : AnalyticAt 𝕜 ψ 0)
    (hψ0 : ψ 0 = 0) {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) :
    substAnalytic ψ (substAnalytic φ f) = substAnalytic (φ ∘ ψ) f := by
  refine (taylorSeries_eq (substAnalytic_mem_convergent _ _) ?_).symm
  filter_upwards [(tendsto_zero_of_analyticAt hψ hψ0).eventually
      (tsumEval_substAnalytic hφ hφ0 hf),
    tsumEval_substAnalytic hψ hψ0 (substAnalytic_mem_convergent φ f)] with z h₁ h₂
  rw [← h₂, ← h₁]
  rfl

omit [Fintype σ] hφ hφ0 in
lemma substAnalytic_X (i : σ) :
    substAnalytic φ (X i) = taylorSeries fun z ↦ φ z i := by
  unfold substAnalytic
  simp only [tsumEval_X]

end Subst

/-! ### Units: `𝕜{X}` is a local ring -/

section Local

variable {ι : Type*} [Finite ι]

omit [CompleteSpace 𝕜] [Finite ι] in
lemma constantCoeff_ne_zero_of_isUnit {f : convergent ι 𝕜} (hf : IsUnit f) :
    constantCoeff f.1 ≠ 0 := by
  obtain ⟨g, hg⟩ := hf.exists_right_inv
  intro h
  have := congr_arg (fun x : convergent ι 𝕜 ↦ constantCoeff x.1) hg
  simp only [MulMemClass.coe_mul, map_mul, h, zero_mul, OneMemClass.coe_one, map_one] at this
  exact zero_ne_one this

omit [CompleteSpace 𝕜] [Finite ι] in
lemma tsumEval_zero_eq_constantCoeff (f : MvPowerSeries ι 𝕜) :
    tsumEval f 0 = constantCoeff f := by
  classical
  rw [tsumEval, tsum_eq_single 0]
  · simp
  · intro α hα
    obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
      by_contra! H
      exact hα (Finsupp.ext H)
    rw [monomialEval, Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.mpr hi)
      (by simp [hi]), mul_zero]

/-- A convergent power series is invertible in `𝕜{X}` if and only if its constant coefficient does
not vanish. -/
theorem isUnit_convergent_iff {f : convergent ι 𝕜} : IsUnit f ↔ constantCoeff f.1 ≠ 0 := by
  refine ⟨constantCoeff_ne_zero_of_isUnit, fun hf ↦ ?_⟩
  have := Fintype.ofFinite ι
  have h0 : tsumEval f.1 0 ≠ 0 := by rwa [tsumEval_zero_eq_constantCoeff]
  have hA : AnalyticAt 𝕜 (tsumEval f.1) 0 := analyticAt_tsumEval f.2
  let g : convergent ι 𝕜 := ⟨taylorSeries fun z ↦ (tsumEval f.1 z)⁻¹, taylorSeries_mem_convergent _⟩
  refine IsUnit.of_mul_eq_one g (Subtype.ext ?_)
  change f.1 * taylorSeries (fun z ↦ (tsumEval f.1 z)⁻¹) = 1
  have e1 : taylorSeries (tsumEval f.1 * fun z ↦ (tsumEval f.1 z)⁻¹) =
      f.1 * taylorSeries (fun z ↦ (tsumEval f.1 z)⁻¹) := by
    rw [taylorSeries_mul (G := fun z ↦ (tsumEval f.1 z)⁻¹) hA (hA.inv h0),
      taylorSeries_tsumEval f.2]
  have e2 : taylorSeries (tsumEval f.1 * fun z ↦ (tsumEval f.1 z)⁻¹) =
      taylorSeries (fun _ : ι → 𝕜 ↦ (1 : 𝕜)) := by
    apply taylorSeries_congr
    filter_upwards [hA.continuousAt.eventually_ne h0] with z hz
    simp [hz]
  rw [← e1, e2, taylorSeries_const, map_one]

instance isLocalRing_convergent : IsLocalRing (convergent ι 𝕜) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  rw [mem_nonunits_iff, isUnit_convergent_iff, not_not] at ha hb ⊢
  rw [AddMemClass.coe_add, map_add, ha, hb, add_zero]

theorem mem_maximalIdeal_convergent_iff {f : convergent ι 𝕜} :
    f ∈ IsLocalRing.maximalIdeal (convergent ι 𝕜) ↔ constantCoeff f.1 = 0 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_convergent_iff, not_not]

end Local

end MvPowerSeries
