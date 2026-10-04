/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaInduction
import SGA.Foundations.Analytic.Statements

/-!
# Oka's coherence theorem, germ form

`AnalyticGeometry.okaCoherence` proves `AnalyticGeometry.OkaCoherenceStatement`: for holomorphic
functions `f₁, …, f_p` on an open `U ⊆ ℂⁿ` and `x₀ ∈ U`, finitely many holomorphic relations
on a neighbourhood `V` of `x₀` generate the module of relations between the germs of the `fᵢ` at
every point of `V` ([Grauert–Remmert, *Coherent analytic sheaves*, 2.5]; [Gunning–Rossi, IV.C];
[Demailly, *Complex analytic and differential geometry*, II.3.19]). It is the case of one row of
`AnalyticGeometry.hasFiniteRelationsNear` (over any complete nontrivially normed field).

As a first consequence, `AnalyticGeometry.exists_relations_mod_ideal_of_analyticAt` gives the
coherence of the structure sheaf of a local model `𝒪_U/(g₁, …, g_r)` in germ form: the module of
`(aᵢ)` with `∑ aᵢ fᵢ ∈ (g₁, …, g_r)` is generated, near `x₀`, by finitely many analytic sections
(Grauert–Remmert, *Coherent analytic sheaves*, 2.5).
-/

noncomputable section

universe u

open TopologicalSpace Filter Set
open scoped Topology

namespace AnalyticGeometry

/-- **Oka's coherence theorem**, germ form (`OkaCoherenceStatement`). -/
theorem okaCoherence : OkaCoherenceStatement := by
  intro n p U hU f hf x₀ hx₀
  obtain ⟨V, hV, hxV, hA, m, g, hg, hgen⟩ :=
    hasFiniteRelationsNear (σ := Fin n) (κ := Unit) (fun _ ↦ f) x₀ fun _ i ↦ hf i x₀ hx₀
  refine ⟨V ∩ U, inter_mem (hV.mem_nhds hxV) (hU.mem_nhds hx₀), inter_subset_right, m, g,
    fun j i y hy ↦ hg j i y hy.1, fun j y hy ↦ ?_, fun y hy a ha ↦ ?_⟩
  · have hmem : (fun i ↦ germOf (g j i) (hg j i y hy.1)) ∈
        matrixRelationModule (fun (_ : Unit) i ↦ germOf (f i) (hA () i y hy.1)) := by
      rw [hgen y hy.1]
      exact Submodule.subset_span ⟨j, rfl⟩
    have h := congrArg (evalStalk y) (mem_matrixRelationModule.mp hmem ())
    simpa only [map_sum, map_mul, evalStalk_germOf, map_zero] using h
  · rw [← hgen y hy.1, mem_matrixRelationModule]
    exact fun _ ↦ ha

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {σ : Type u} [Fintype σ]

/-- **Coherence of the structure sheaf of a local model** (germ form): let `f₁, …, f_p` and
`g₁, …, g_r` be analytic at `x₀ ∈ 𝕜^σ`. There are an open neighbourhood `V` of `x₀` and finitely
many vectors `s_j` of functions analytic on `V` with `∑ᵢ s_{j i} fᵢ ∈ (g₁, …, g_r)` on `V` (as
germs), whose germs generate, at every `y ∈ V`, the module of germs `(aᵢ)` with
`∑ᵢ aᵢ fᵢ ∈ (g₁, …, g_r) 𝒪_y`. That is, the sheaf of relations of the images of the `fᵢ` in
`𝒪/(g₁, …, g_r)` is of finite type, so `𝒪/(g₁, …, g_r)` is a coherent `𝒪`-module. -/
theorem exists_relations_mod_ideal_of_analyticAt {p r : ℕ} {f : Fin p → (σ → 𝕜) → 𝕜}
    {g : Fin r → (σ → 𝕜) → 𝕜} {x₀ : σ → 𝕜} (hf : ∀ i, AnalyticAt 𝕜 (f i) x₀)
    (hg : ∀ l, AnalyticAt 𝕜 (g l) x₀) :
    ∃ V : Set (σ → 𝕜), IsOpen V ∧ x₀ ∈ V ∧
      ∃ (hfV : ∀ i, ∀ y ∈ V, AnalyticAt 𝕜 (f i) y) (hgV : ∀ l, ∀ y ∈ V, AnalyticAt 𝕜 (g l) y)
        (m : ℕ) (s : Fin m → Fin p → (σ → 𝕜) → 𝕜) (hs : ∀ j i, ∀ y ∈ V, AnalyticAt 𝕜 (s j i) y),
        (∀ j y (hy : y ∈ V), ∑ i, germOf (s j i) (hs j i y hy) * germOf (f i) (hfV i y hy) ∈
          Ideal.span (Set.range fun l ↦ germOf (g l) (hgV l y hy))) ∧
        ∀ y (hy : y ∈ V) (a : Fin p → (analyticPresheaf 𝕜 (σ → 𝕜)).stalk y),
          ∑ i, a i * germOf (f i) (hfV i y hy) ∈
              Ideal.span (Set.range fun l ↦ germOf (g l) (hgV l y hy)) →
            a ∈ Submodule.span ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk y)
              (Set.range fun j i ↦ germOf (s j i) (hs j i y hy)) := by
  classical
  -- relations between `f₁, …, f_p, g₁, …, g_r`
  let F : Fin p ⊕ Fin r → (σ → 𝕜) → 𝕜 := Sum.elim f g
  have hF : ∀ c, AnalyticAt 𝕜 (F c) x₀ := by
    rintro (i | l)
    exacts [hf i, hg l]
  obtain ⟨V, hV, hxV, hA, m, t, ht, hgen⟩ :=
    hasFiniteRelationsNear (σ := σ) (κ := Unit) (fun _ ↦ F) x₀ fun _ ↦ hF
  have hfV (i) (y) (hy : y ∈ V) : AnalyticAt 𝕜 (f i) y := hA () (Sum.inl i) y hy
  have hgV (l) (y) (hy : y ∈ V) : AnalyticAt 𝕜 (g l) y := hA () (Sum.inr l) y hy
  refine ⟨V, hV, hxV, hfV, hgV, m, fun j i ↦ t j (Sum.inl i), fun j i ↦ ht j (Sum.inl i),
    fun j y hy ↦ ?_, fun y hy a ha ↦ ?_⟩
  · have hmem : (fun c ↦ germOf (t j c) (ht j c y hy)) ∈
        matrixRelationModule (fun (_ : Unit) c ↦ germOf (F c) (hA () c y hy)) := by
      rw [hgen y hy]
      exact Submodule.subset_span ⟨j, rfl⟩
    have h := mem_matrixRelationModule.mp hmem ()
    rw [Fintype.sum_sum_type] at h
    have hmem' : -∑ l, germOf (t j (Sum.inr l)) (ht j _ y hy) *
        germOf (F (Sum.inr l)) (hA () _ y hy) ∈
          Ideal.span (Set.range fun l ↦ germOf (g l) (hgV l y hy)) :=
      neg_mem (Ideal.sum_mem _ fun l _ ↦
        Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨l, rfl⟩))
    rw [← eq_neg_of_add_eq_zero_left h] at hmem'
    exact hmem'
  · obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp ha
    -- `(a, -b)` is a relation between the `f` and the `g`
    have hrel : Sum.elim a (fun l ↦ -b l) ∈
        matrixRelationModule (fun (_ : Unit) c ↦ germOf (F c) (hA () c y hy)) := by
      rw [mem_matrixRelationModule]
      intro _
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, F, neg_mul, Finset.sum_neg_distrib]
      rw [← hb]
      simp only [smul_eq_mul]
      exact add_neg_cancel _
    rw [hgen y hy, Submodule.mem_span_range_iff_exists_fun] at hrel
    obtain ⟨c, hc⟩ := hrel
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨c, funext fun i ↦ ?_⟩
    have := congrFun hc (Sum.inl i)
    simpa only [Finset.sum_apply, Pi.smul_apply, Sum.elim_inl] using this

end AnalyticGeometry
