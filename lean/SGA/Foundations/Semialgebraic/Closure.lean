/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.TarskiSeidenberg

/-!
# Closure and interior of semialgebraic sets

The closure, the interior and the frontier of a semialgebraic subset of `ℝ^ι`, `ι` finite, are
semialgebraic (`IsSemialgebraic.closure`, `IsSemialgebraic.interior`,
`IsSemialgebraic.frontier`). The closure is the first-order definable set
`{x | ∀ ε > 0, ∃ y ∈ S, ∀ i, |xᵢ - yᵢ| < ε}`, and the Tarski–Seidenberg theorem
(`IsSemialgebraic.exists_sumElim`, `IsSemialgebraic.forall_real`) eliminates the quantifiers.

## References

* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, Proposition 2.2.2][BCR]
-/

open Set MvPolynomial

variable {ι : Type*} [Finite ι]

namespace IsSemialgebraic

/-- The closure of a semialgebraic subset of `ℝ^ι`, `ι` finite, is semialgebraic. -/
protected theorem closure {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (closure S) := by
  have := Fintype.ofFinite ι
  -- `A = {(x, ε, y) | y ∈ S, ∀ i, |xᵢ - yᵢ| < ε}`
  let A : Set (Option ι ⊕ ι → ℝ) := (fun w ↦ w ∘ Sum.inr) ⁻¹' S ∩
    ⋂ i, ({w | eval w (X (Sum.inl (some i)) - X (Sum.inr i)) < eval w (X (Sum.inl none))} ∩
      {w | eval w (X (Sum.inr i) - X (Sum.inl (some i))) < eval w (X (Sum.inl none))})
  have hA : IsSemialgebraic A := (hS.preimage_comp Sum.inr).inter
    (IsSemialgebraic.iInter fun i ↦ (IsSemialgebraic.lt _ _).inter (IsSemialgebraic.lt _ _))
  -- `C = {(x, ε) | ε > 0 → ∃ y, (x, ε, y) ∈ A}`
  let C : Set (Option ι → ℝ) :=
    {v | eval v (X none) ≤ eval v 0} ∪ {v | ∃ y : ι → ℝ, Sum.elim v y ∈ A}
  have hC : IsSemialgebraic C := (IsSemialgebraic.le _ _).union hA.exists_sumElim
  convert hC.forall_real using 1
  ext x
  simp only [Metric.mem_closure_iff, C, A, mem_ofPred_eq, mem_union, mem_inter_iff,
    mem_preimage, mem_iInter, eval_X, map_sub, map_zero, Option.elim_none, Option.elim_some,
    Sum.elim_inl, Sum.elim_inr]
  refine forall_congr' fun ε ↦ ?_
  rw [← not_lt, ← imp_iff_not_or, gt_iff_lt]
  refine imp_congr_right fun hε ↦ ⟨fun ⟨y, hy, hxy⟩ ↦ ⟨y, hy, fun i ↦ ?_⟩, fun ⟨y, hy, h⟩ ↦
    ⟨y, hy, ?_⟩⟩
  · have := (dist_pi_lt_iff hε).mp hxy i
    rw [Real.dist_eq, abs_lt] at this
    exact ⟨by linarith [this.2], by linarith [this.1]⟩
  · refine (dist_pi_lt_iff hε).mpr fun i ↦ ?_
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [(h i).2], (h i).1⟩

/-- The interior of a semialgebraic subset of `ℝ^ι`, `ι` finite, is semialgebraic. -/
protected theorem interior {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (interior S) := by
  rw [← compl_compl (interior S), ← closure_compl]
  exact hS.compl.closure.compl

/-- The frontier of a semialgebraic subset of `ℝ^ι`, `ι` finite, is semialgebraic. -/
protected theorem frontier {S : Set (ι → ℝ)} (hS : IsSemialgebraic S) :
    IsSemialgebraic (frontier S) :=
  hS.closure.diff hS.interior

end IsSemialgebraic
