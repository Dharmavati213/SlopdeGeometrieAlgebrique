/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Syzygy
import SGA.Foundations.Analytic.OkaInduction

/-!
# Local finite free resolutions (the syzygy theorem for coherent sheaves)

Let `A` be a finite matrix of functions analytic near a point `x₀` of `𝕜^σ`. Its relation sheaf
`ℛ(A)` (the kernel of `𝒪^ι → 𝒪^κ`, `a ↦ (∑ᵢ aᵢ A_{k i})_k`; see
`AnalyticGeometry.matrixRelationModule`) has a free resolution of length `#σ + 1` near `x₀`
(`AnalyticGeometry.hasFreeResolutionNear_of_analyticAt`): there are matrices `g₁, g₂, …, g_N`
of functions analytic on one neighbourhood `V` of `x₀` such that, at every point `y ∈ V`, the
rows of `g₁` generate `ℛ(A)_y`, the rows of `g_{k+1}` generate the relations between the rows of
`g_k`, and the rows of `g_N` have no relations. That is, near `x₀` there is an exact sequence
`0 → 𝒪^{n_N} → ⋯ → 𝒪^{n_1} → 𝒪^ι → 𝒪^κ`. (The syzygy theorem; Grauert–Remmert, *Coherent
analytic sheaves*, Chapter 2; Hörmander, *An introduction to complex analysis in several
variables*, Chapter VI; Gunning–Rossi, Chapter VI.)

The proof combines Oka's theorem (`AnalyticGeometry.hasFiniteRelationsNear`) with Hilbert's
syzygy theorem for the regular local ring `𝒪_{x₀}`
(`AnalyticGeometry.hasProjectiveDimensionLE_stalk`): the `k`-th relation module at `x₀` has
projective dimension `≤ #σ + 1 - k`; when it reaches `0` the module at `x₀` is free, and a basis
at `x₀`, realized by analytic functions, generates the relation sheaf and has no relations on a
neighbourhood of `x₀`.
-/

noncomputable section

universe u

open TopologicalSpace Filter Set CategoryTheory
open scoped Topology

namespace AnalyticGeometry

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- `HasFreeResolutionNear x₀ N κ ι A`: the relation sheaf of the matrix `A : κ → ι → (E → 𝕜)` has a
free resolution of length `N` near `x₀`. For `N = 0` the relation sheaf vanishes near `x₀`; for
`N + 1`, finitely many analytic relations `g_m` generate it on a neighbourhood of `x₀`, and the
relation sheaf of the matrix `gᵀ` (the relations between the `g_m`) has a free resolution of
length `N` near `x₀`. -/
def HasFreeResolutionNear (x₀ : E) : ℕ → ∀ (κ ι : Type) [Fintype ι], (κ → ι → E → 𝕜) → Prop
  | 0 => fun _ _ _ A ↦ ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧
      ∃ hA : ∀ k i, ∀ y ∈ V, AnalyticAt 𝕜 (A k i) y,
        ∀ y (hy : y ∈ V), matrixRelationModule (fun k i ↦ germOf (A k i) (hA k i y hy)) = ⊥
  | N + 1 => fun _ ι _ A ↦ ∃ V : Set E, IsOpen V ∧ x₀ ∈ V ∧
      ∃ (hA : ∀ k i, ∀ y ∈ V, AnalyticAt 𝕜 (A k i) y) (n : ℕ) (g : Fin n → ι → E → 𝕜)
        (hg : ∀ m i, ∀ y ∈ V, AnalyticAt 𝕜 (g m i) y),
        (∀ y (hy : y ∈ V), matrixRelationModule (fun k i ↦ germOf (A k i) (hA k i y hy)) =
          Submodule.span _ (Set.range fun m i ↦ germOf (g m i) (hg m i y hy))) ∧
        HasFreeResolutionNear x₀ N ι (Fin n) (fun i m ↦ g m i)

variable {σ : Type u} [Fintype σ]

/-- The step `d = 0`: if the relation module of `A` at `x₀` has projective dimension `0`, a basis
at `x₀`, realized by analytic functions, generates the relation sheaf of `A` and has no relations
near `x₀`. -/
theorem hasFreeResolutionNear_one_of_hasProjectiveDimensionLE_zero {κ ι : Type} [Finite κ]
    [Fintype ι] {A : κ → ι → (σ → 𝕜) → 𝕜} {x₀ : σ → 𝕜} (hA : ∀ k i, AnalyticAt 𝕜 (A k i) x₀)
    (h : HasProjectiveDimensionLE (ModuleCat.of ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x₀)
      (matrixRelationModule fun k i ↦ germOf (A k i) (hA k i))) 0) :
    HasFreeResolutionNear x₀ 1 κ ι A := by
  classical
  have := Fintype.ofFinite κ
  set R := (analyticPresheaf 𝕜 (σ → 𝕜)).stalk x₀
  have : Module.Finite R (matrixRelationModule fun k i ↦ germOf (A k i) (hA k i)) :=
    Module.IsNoetherian.finite R _
  obtain ⟨r, b, hspan, hfree⟩ := exists_basis_of_hasProjectiveDimensionLE_zero _ h
  -- realize the basis by analytic functions
  let B : Fin r → ι → (σ → 𝕜) → 𝕜 := fun j i ↦ germRep (b j i)
  have hB (j i) : AnalyticAt 𝕜 (B j i) x₀ := analyticAt_germRep (b j i)
  have hBb (j i) : germOf (B j i) (hB j i) = b j i := germOf_germRep _
  -- Oka for `A`
  obtain ⟨V, hV, hxV, hAV, n, G, hG, hgen⟩ := hasFiniteRelationsNear A x₀ hA
  -- at `x₀`, the generators `G_m` are combinations of the basis
  have hGmem (m : Fin n) : (fun i ↦ germOf (G m i) (hG m i x₀ hxV)) ∈
      Submodule.span R (Set.range b) := by
    rw [← hspan, hgen x₀ hxV]
    exact Submodule.subset_span ⟨m, rfl⟩
  choose c hc using fun m ↦ (Submodule.mem_span_range_iff_exists_fun R).mp (hGmem m)
  let C : Fin n → Fin r → (σ → 𝕜) → 𝕜 := fun m j ↦ germRep (c m j)
  have hC (m j) : AnalyticAt 𝕜 (C m j) x₀ := analyticAt_germRep (c m j)
  -- the identities `G_m = ∑ⱼ c_{m j} B_j` and `∑ᵢ B_{j i} A_{k i} = 0` hold near `x₀`
  have hGC (m : Fin n) (i : ι) : G m i =ᶠ[𝓝 x₀] fun z ↦ ∑ j, C m j z * B j i z := by
    refine (germOf_eq_germOf_iff (hG m i x₀ hxV) (analyticAt_sum_mul (hC m) (hB · i))).mp ?_
    rw [germOf_sum_mul (hC m) (hB · i)]
    have := congrFun (hc m) i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
    rw [← this]
    exact Finset.sum_congr rfl fun j _ ↦ by rw [germOf_germRep, hBb]
  have hBrel (j : Fin r) (k : κ) : (fun z ↦ ∑ i, B j i z * A k i z) =ᶠ[𝓝 x₀] 0 := by
    rw [← germOf_eq_zero_iff (analyticAt_sum_mul (hB j) (hA k)), germOf_sum_mul (hB j) (hA k)]
    have hmem : b j ∈ matrixRelationModule fun k i ↦ germOf (A k i) (hA k i) := by
      rw [hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    rw [mem_matrixRelationModule] at hmem
    simpa only [hBb] using hmem k
  -- Oka for the basis: its relations vanish at `x₀`, hence near `x₀`
  obtain ⟨V', hV', hxV', hBV', n', H, hH, hgen'⟩ :=
    hasFiniteRelationsNear (fun i j ↦ B j i) x₀ fun i j ↦ hB j i
  have hH0 (t : Fin n') (j : Fin r) : H t j =ᶠ[𝓝 x₀] 0 := by
    rw [← germOf_eq_zero_iff (hH t j x₀ hxV')]
    have hmem : (fun j ↦ germOf (H t j) (hH t j x₀ hxV')) ∈
        matrixRelationModule fun i j ↦ germOf (B j i) (hBV' i j x₀ hxV') := by
      rw [hgen' x₀ hxV']
      exact Submodule.subset_span ⟨t, rfl⟩
    have hb : (matrixRelationModule fun i j ↦ germOf (B j i) (hBV' i j x₀ hxV')) = ⊥ := by
      simpa only [hBb] using hfree
    rw [hb, Submodule.mem_bot] at hmem
    exact congrFun hmem j
  -- the neighbourhood on which all these identities hold
  have hev : ∀ᶠ z in 𝓝 x₀, (∀ m i, AnalyticAt 𝕜 (C m i) z) ∧ (∀ j i, AnalyticAt 𝕜 (B j i) z) ∧
      (∀ m i, G m i =ᶠ[𝓝 z] fun z ↦ ∑ j, C m j z * B j i z) ∧
      (∀ j k, (fun z ↦ ∑ i, B j i z * A k i z) =ᶠ[𝓝 z] 0) ∧ (∀ t j, H t j =ᶠ[𝓝 z] 0) := by
    refine (eventually_all.mpr fun m ↦ eventually_all.mpr fun i ↦
      (hC m i).eventually_analyticAt).and ((eventually_all.mpr fun j ↦ eventually_all.mpr
        fun i ↦ (hB j i).eventually_analyticAt).and ((eventually_all.mpr fun m ↦
          eventually_all.mpr fun i ↦ (hGC m i).eventually_nhds).and
        ((eventually_all.mpr fun j ↦ eventually_all.mpr fun k ↦ (hBrel j k).eventually_nhds).and
          (eventually_all.mpr fun t ↦ eventually_all.mpr fun j ↦ (hH0 t j).eventually_nhds))))
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp hev
  let U := (V ∩ V') ∩ W
  have hU : IsOpen U := (hV.inter hV').inter hW
  have hxU : x₀ ∈ U := ⟨⟨hxV, hxV'⟩, hxW⟩
  refine ⟨U, hU, hxU, fun k i y hy ↦ hAV k i y hy.1.1, r, B,
    fun j i y hy ↦ (hWsub hy.2).2.1 j i, fun y hy ↦ ?_, ?_⟩
  · -- `ℛ(A)_y` is spanned by the basis
    have hy' := hWsub hy.2
    apply le_antisymm
    · rw [hgen y hy.1.1, Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      simp only [SetLike.mem_coe]
      rw [Submodule.mem_span_range_iff_exists_fun]
      refine ⟨fun j ↦ germOf (C m j) (hy'.1 m j), funext fun i ↦ ?_⟩
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [← germOf_sum_mul (fun j ↦ hy'.1 m j) (fun j ↦ hy'.2.1 j i)]
      exact (germOf_congr _ (hy'.2.2.1 m i)).symm
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      rw [SetLike.mem_coe, mem_matrixRelationModule]
      intro k
      rw [← germOf_sum_mul (fun i ↦ hy'.2.1 j i) (fun i ↦ hAV k i y hy.1.1)
        (analyticAt_sum_mul (fun i ↦ hy'.2.1 j i) (fun i ↦ hAV k i y hy.1.1)),
        germOf_eq_zero_iff]
      exact hy'.2.2.2.1 j k
  · -- the basis has no relations near `x₀`
    refine ⟨U, hU, hxU, fun i j y hy ↦ (hWsub hy.2).2.1 j i, fun y hy ↦ ?_⟩
    have hy' := hWsub hy.2
    rw [hgen' y hy.1.2]
    refine (Submodule.span_eq_bot.mpr ?_)
    rintro _ ⟨t, rfl⟩
    funext j
    exact (germOf_eq_zero_iff _).mpr (hy'.2.2.2.2 t j)

/-- **The syzygy step near a point**: if the relation module of `A` at `x₀` has projective
dimension `≤ d`, the relation sheaf of `A` has a free resolution of length `d + 1` near `x₀`. -/
theorem hasFreeResolutionNear_of_hasProjectiveDimensionLE (d : ℕ) :
    ∀ {κ ι : Type} [Finite κ] [Fintype ι] {A : κ → ι → (σ → 𝕜) → 𝕜} {x₀ : σ → 𝕜}
      (hA : ∀ k i, AnalyticAt 𝕜 (A k i) x₀),
      HasProjectiveDimensionLE (ModuleCat.of ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x₀)
        (matrixRelationModule fun k i ↦ germOf (A k i) (hA k i))) d →
      HasFreeResolutionNear x₀ (d + 1) κ ι A := by
  induction d with
  | zero => exact fun hA h ↦ hasFreeResolutionNear_one_of_hasProjectiveDimensionLE_zero hA h
  | succ d ih =>
    intro κ ι _ _ A x₀ hA h
    obtain ⟨V, hV, hxV, hAV, n, G, hG, hgen⟩ := hasFiniteRelationsNear A x₀ hA
    refine ⟨V, hV, hxV, hAV, n, G, hG, hgen, ?_⟩
    have hspan := hgen x₀ hxV
    have h' : HasProjectiveDimensionLE (ModuleCat.of ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x₀)
        (Submodule.span ((analyticPresheaf 𝕜 (σ → 𝕜)).stalk x₀)
        (Set.range fun m i ↦ germOf (G m i) (hG m i x₀ hxV)))) (d + 1) := by
      rw [← hspan]
      exact h
    exact ih (fun i m ↦ hG m i x₀ hxV) (hasProjectiveDimensionLE_relations _ d h')

/-- **The syzygy theorem** (local finite free resolutions, from Oka's theorem and Hilbert's
syzygy theorem for `𝒪_{x₀}`): the relation sheaf of every finite
matrix of functions analytic at a point `x₀` of `𝕜^σ` has a free resolution of length `#σ + 1`
near `x₀`. -/
theorem hasFreeResolutionNear_of_analyticAt {κ ι : Type} [Finite κ] [Fintype ι]
    (A : κ → ι → (σ → 𝕜) → 𝕜) (x₀ : σ → 𝕜) (hA : ∀ k i, AnalyticAt 𝕜 (A k i) x₀) :
    HasFreeResolutionNear x₀ (Fintype.card σ + 1) κ ι A :=
  hasFreeResolutionNear_of_hasProjectiveDimensionLE _ hA (hasProjectiveDimensionLE_stalk x₀ _)

end AnalyticGeometry
