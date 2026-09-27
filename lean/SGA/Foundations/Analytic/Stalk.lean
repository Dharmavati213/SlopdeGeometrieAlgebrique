/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.Sheaf
import SGA.Foundations.Analytic.Substitution
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# The stalks of the sheaf of analytic functions on `𝕜ⁿ`

The stalk at `x` of the sheaf `𝒪` of analytic functions on `𝕜^σ` (`σ` finite) is isomorphic to
the ring `𝕜{X}` of convergent power series, by sending a convergent series `f` to the germ of
`y ↦ f(y - x)` (`convergentStalkEquiv`). Consequently `𝕜{X}` is a local ring whose units are the
series with non-zero constant coefficient ([Grauert–Remmert, *Analytische Stellenalgebren*,
I §1]).
-/

universe u

open scoped NNReal ENNReal Topology
open Filter CategoryTheory MvPowerSeries

noncomputable section

namespace AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {σ : Type u} [Fintype σ]

omit [CompleteSpace 𝕜] [Fintype σ] in
lemma tendsto_sub_nhds_zero (x : σ → 𝕜) : Tendsto (fun y ↦ y - x) (𝓝 x) (𝓝 0) := by
  simpa using (continuous_sub_right x).tendsto x

omit [CompleteSpace 𝕜] [Fintype σ] in
lemma tendsto_add_nhds (x : σ → 𝕜) : Tendsto (fun y ↦ y + x) (𝓝 0) (𝓝 x) := by
  simpa using (continuous_add_const x).tendsto 0

lemma analyticAt_tsumEval_sub {f : MvPowerSeries σ 𝕜} (hf : f ∈ convergent σ 𝕜) (x : σ → 𝕜) :
    AnalyticAt 𝕜 (fun y ↦ tsumEval f (y - x)) x := by
  exact (analyticAt_tsumEval hf).comp_of_eq (f := fun y ↦ y - x)
    (analyticAt_id.sub analyticAt_const) (sub_self x)

/-- The germ at `x` of the function `y ↦ f(y - x)` defined by a convergent power series. -/
def convergentToStalk (x : σ → 𝕜) :
    convergent σ 𝕜 →+* (analyticPresheaf 𝕜 (σ → 𝕜)).stalk x where
  toFun f := germOf _ (analyticAt_tsumEval_sub f.2 x)
  map_one' := by
    rw [← germOf_one]
    exact germOf_congr _ (Eventually.of_forall fun y ↦ by simp)
  map_mul' f g := by
    rw [← germOf_mul]
    apply germOf_congr
    filter_upwards [(tendsto_sub_nhds_zero x).eventually
      (eventually_tsumEval_add_mul f.2 g.2)] with y hy
    exact hy.2
  map_zero' := by
    rw [← germOf_zero]
    exact germOf_congr _ (Eventually.of_forall fun y ↦ by simp [tsumEval])
  map_add' f g := by
    rw [← germOf_add]
    apply germOf_congr
    filter_upwards [(tendsto_sub_nhds_zero x).eventually
      (eventually_tsumEval_add_mul f.2 g.2)] with y hy
    exact hy.1

lemma convergentToStalk_apply (x : σ → 𝕜) (f : convergent σ 𝕜) :
    convergentToStalk x f = germOf _ (analyticAt_tsumEval_sub f.2 x) := rfl

lemma convergentToStalk_injective (x : σ → 𝕜) :
    Function.Injective (convergentToStalk (𝕜 := 𝕜) x) := by
  intro f g h
  rw [convergentToStalk_apply, convergentToStalk_apply, germOf_eq_germOf_iff] at h
  refine Subtype.ext (eq_of_tsumEval_eventuallyEq f.2 g.2 ?_)
  filter_upwards [(tendsto_add_nhds x).eventually h] with z hz
  simpa using hz

lemma convergentToStalk_surjective (x : σ → 𝕜) :
    Function.Surjective (convergentToStalk (𝕜 := 𝕜) x) := by
  intro s
  obtain ⟨F, hF, rfl⟩ := exists_germOf_eq s
  have hG : AnalyticAt 𝕜 (fun z ↦ F (z + x)) 0 :=
    hF.comp_of_eq (f := fun z ↦ z + x) (analyticAt_id.add analyticAt_const) (zero_add x)
  obtain ⟨f, hf, hfG⟩ := exists_convergent_eventuallyEq hG
  refine ⟨⟨f, hf⟩, ?_⟩
  rw [convergentToStalk_apply, germOf_eq_germOf_iff]
  filter_upwards [(tendsto_sub_nhds_zero x).eventually hfG] with y hy
  simpa using hy.symm

/-- The stalk at `x` of the sheaf of analytic functions on `𝕜^σ` is the ring of convergent
power series in the variables `σ` (centred at `x`). -/
def convergentStalkEquiv (x : σ → 𝕜) :
    convergent σ 𝕜 ≃+* (analyticPresheaf 𝕜 (σ → 𝕜)).stalk x :=
  RingEquiv.ofBijective (convergentToStalk x)
    ⟨convergentToStalk_injective x, convergentToStalk_surjective x⟩

@[simp] lemma convergentStalkEquiv_apply (x : σ → 𝕜) (f : convergent σ 𝕜) :
    convergentStalkEquiv x f = convergentToStalk x f := rfl

@[simp] lemma evalStalk_convergentToStalk (x : σ → 𝕜) (f : convergent σ 𝕜) :
    evalStalk x (convergentToStalk x f) = constantCoeff f.1 := by
  rw [convergentToStalk_apply, evalStalk_germOf, sub_self, tsumEval_zero_eq_constantCoeff]

end AnalyticGeometry

namespace MvPowerSeries

open AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {σ : Type u} [Fintype σ]

/-- The stalk of `𝒪_{𝕜^σ}` at `x` is a local ring isomorphic to `𝕜{X}`: under
`convergentStalkEquiv`, the maximal ideals correspond. -/
theorem convergentStalkEquiv_mem_maximalIdeal_iff (x : σ → 𝕜) (f : convergent σ 𝕜) :
    convergentStalkEquiv x f ∈ IsLocalRing.maximalIdeal _ ↔
      f ∈ IsLocalRing.maximalIdeal (convergent σ 𝕜) := by
  rw [mem_maximalIdeal_stalk_iff, convergentStalkEquiv_apply, evalStalk_convergentToStalk,
    mem_maximalIdeal_convergent_iff]

end MvPowerSeries
