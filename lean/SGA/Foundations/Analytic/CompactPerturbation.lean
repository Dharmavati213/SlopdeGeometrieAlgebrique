/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.RingTheory.Finiteness.Cofinite
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Compact perturbations of surjections have finite-codimensional range

**Theorem (L. Schwartz).** Let `E`, `F` be Banach spaces over `ℝ` or `ℂ`, `ψ : E → F` a surjective
continuous linear map and `φ : E → F` a compact operator. Then the range of `ψ - φ` has finite
codimension: there is a finite-dimensional subspace `V` with `range (ψ - φ) + V = F`
(`ContinuousLinearMap.exists_finiteDimensional_range_sub_sup_eq_top`), so
`(range (ψ - φ)).CoFG` (`ContinuousLinearMap.cofg_range_sub_of_surjective`).

This is the functional-analytic input of the finiteness of `H¹(X, 𝒪)` for a compact Riemann
surface `X` (Forster, *Lectures on Riemann surfaces*, 14.6–14.9).

The proof: by the open mapping theorem every `y` with `‖y‖ ≤ 1` is `ψ x` with `‖x‖ ≤ C`; the image
under `φ` of the ball of radius `C` is relatively compact, hence covered by finitely many balls of
radius `1/2` with centres `sᵢ`; with `V = span {sᵢ}`, the map `(x, v) ↦ (ψ - φ) x + v` on `E × V`
is surjective up to an error of half the norm, hence surjective by the iteration in the proof of
the open mapping theorem (`surjective_of_exists_approx_preimage`).

References: Forster, *Lectures on Riemann surfaces*, Theorem 14.6 (in Hilbert spaces); L. Schwartz,
*Homomorphismes et applications complètement continues*, C. R. Acad. Sci. Paris 236 (1953).
-/

noncomputable section

open Filter Topology Metric Set

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜]
  {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- A continuous linear map `f` from a Banach space such that every `y` is approximated up to
`‖y‖ / 2` by the image of some `x` with `‖x‖ ≤ C ‖y‖` is surjective. (The second step of the open
mapping theorem, `ContinuousLinearMap.exists_preimage_norm_le`.) -/
theorem surjective_of_exists_approx_preimage [CompleteSpace E] (f : E →L[𝕜] F) {C : ℝ}
    (hC : ∀ y, ∃ x, dist (f x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖) : Function.Surjective f := by
  choose g hg using hC
  let h y := y - f (g y)
  have hle : ∀ y, ‖h y‖ ≤ 1 / 2 * ‖y‖ := by
    intro y
    rw [← dist_eq_norm, dist_comm]
    exact (hg y).1
  intro y
  have hnle : ∀ n : ℕ, ‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n IH =>
      rw [Function.iterate_succ']
      apply le_trans (hle _) _
      rw [pow_succ', mul_assoc]
      gcongr
  let u n := g (h^[n] y)
  set C' := max C 0
  have ule : ∀ n, ‖u n‖ ≤ (1 / 2) ^ n * (C' * ‖y‖) := fun n ↦ by
    refine ((hg _).2.trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (norm_nonneg _))).trans ?_
    calc
      C' * ‖h^[n] y‖ ≤ C' * ((1 / 2) ^ n * ‖y‖) := by
        gcongr
        exact hnle n
      _ = (1 / 2) ^ n * (C' * ‖y‖) := by ring
  have sNu : Summable fun n => ‖u n‖ := by
    refine .of_nonneg_of_le (fun n => norm_nonneg _) ule ?_
    exact Summable.mul_right _ (summable_geometric_of_lt_one (by simp) (by norm_num))
  have su : Summable u := sNu.of_norm
  have fsumeq : ∀ n : ℕ, f (∑ i ∈ Finset.range n, u i) = y - h^[n] y := by
    intro n
    induction n with
    | zero => simp
    | succ n IH => rw [Finset.sum_range_succ, f.map_add, IH, Function.iterate_succ_apply', sub_add]
  have L₁ : Tendsto (fun n => f (∑ i ∈ Finset.range n, u i)) atTop (𝓝 (f (tsum u))) :=
    (f.continuous.tendsto _).comp su.hasSum.tendsto_sum_nat
  simp only [fsumeq] at L₁
  have L₂ : Tendsto (fun n => y - h^[n] y) atTop (𝓝 (y - 0)) := by
    refine tendsto_const_nhds.sub ?_
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp only [sub_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) hnle ?_
    rw [← zero_mul ‖y‖]
    refine (_root_.tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num
  exact ⟨tsum u, by simpa using tendsto_nhds_unique L₁ L₂⟩

variable [CompleteSpace E] [CompleteSpace F]

/-- **L. Schwartz's theorem**: if `ψ : E → F` is a surjective continuous linear map of Banach
spaces and `φ : E → F` is compact, there is a finite-dimensional subspace `V` of `F` with
`range (ψ - φ) + V = F`. -/
theorem exists_finiteDimensional_range_sub_sup_eq_top {ψ φ : E →L[𝕜] F}
    (hψ : Function.Surjective ψ) (hφ : IsCompactOperator φ) :
    ∃ V : Submodule 𝕜 F, FiniteDimensional 𝕜 V ∧ LinearMap.range (ψ - φ : E →ₗ[𝕜] F) ⊔ V = ⊤ := by
  obtain ⟨C, C0, hC⟩ := ψ.exists_preimage_norm_le hψ
  obtain ⟨t, hts, htf, hcov⟩ := exists_finite_cover_balls_of_isCompact_closure
    (hφ.isCompact_closure_image_closedBall C) (by norm_num : (0 : ℝ) < 1 / 2)
  let V : Submodule 𝕜 F := Submodule.span 𝕜 t
  have : FiniteDimensional 𝕜 V := FiniteDimensional.span_of_finite 𝕜 htf
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  refine ⟨V, inferInstance, ?_⟩
  -- the bound on the centres of the balls
  have hts' : ∀ s ∈ t, ‖s‖ ≤ ‖φ‖ * C := by
    intro s hs
    obtain ⟨x, hx, rfl⟩ := hts hs
    refine (φ.le_opNorm x).trans ?_
    gcongr
    simpa using hx
  let T : E × V →L[𝕜] F := (ψ - φ).coprod V.subtypeL
  have hT : Function.Surjective T := by
    refine T.surjective_of_exists_approx_preimage (C := C + ‖φ‖ * C) fun y => ?_
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, by simp⟩
    have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
    set a : 𝕜 := (‖y‖ : 𝕜) with ha
    have ha0 : a ≠ 0 := by simpa [ha] using hny.ne'
    obtain ⟨x, hx, hxC⟩ := hC (a⁻¹ • y)
    have hy' : ‖a⁻¹ • y‖ = 1 := by
      rw [norm_smul, norm_inv, ha, RCLike.norm_ofReal, abs_of_pos hny, inv_mul_cancel₀ hny.ne']
    rw [hy', mul_one] at hxC
    have hmem : φ x ∈ φ '' closedBall 0 C := ⟨x, by simpa using hxC, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (hcov hmem)
    refine ⟨a • (x, ⟨s, Submodule.subset_span hs⟩), ?_, ?_⟩
    · have : T (a • (x, ⟨s, Submodule.subset_span hs⟩)) - y = a • (s - φ x) := by
        simp only [T, map_smul, coprod_apply, sub_apply, Submodule.subtypeL_apply, hx,
          smul_sub, smul_add, smul_inv_smul₀ ha0]
        abel
      rw [dist_eq_norm, this, norm_smul, ha, RCLike.norm_ofReal, abs_of_pos hny, mul_comm,
        ← dist_eq_norm']
      exact mul_le_mul_of_nonneg_right (le_of_lt (by simpa [dist_comm] using hxs)) hny.le
    · rw [norm_smul, ha, RCLike.norm_ofReal, abs_of_pos hny, mul_comm]
      refine mul_le_mul_of_nonneg_right ?_ hny.le
      rw [Prod.norm_def]
      refine max_le (hxC.trans (le_add_of_nonneg_right (by positivity))) ?_
      exact (hts' s hs).trans (le_add_of_nonneg_left C0.le)
  rw [eq_top_iff]
  intro y _
  obtain ⟨⟨x, v⟩, rfl⟩ := hT y
  exact Submodule.add_mem_sup (LinearMap.mem_range_self _ x) v.2

/-- **L. Schwartz's theorem**: the range of `ψ - φ`, for `ψ` a surjection of Banach spaces and
`φ` compact, has finite codimension. -/
theorem cofg_range_sub_of_surjective {ψ φ : E →L[𝕜] F} (hψ : Function.Surjective ψ)
    (hφ : IsCompactOperator φ) : (LinearMap.range (ψ - φ : E →ₗ[𝕜] F)).CoFG := by
  obtain ⟨V, hV, hsup⟩ := exists_finiteDimensional_range_sub_sup_eq_top hψ hφ
  exact Submodule.FG.cofg_of_codisjoint (codisjoint_iff.mpr (by rw [sup_comm]; exact hsup))
    (Module.Finite.iff_fg.mp hV)

end ContinuousLinearMap
