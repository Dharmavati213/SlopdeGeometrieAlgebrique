/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.Lojasiewicz
import SGA.Foundations.Topology.ContractibleNhdsLocal
import SGA.Foundations.Topology.PathConnectedHelpers

/-!
# Real algebraic sets are semilocally simply connected

For a finite type `σ` and a real polynomial `f` in the variables `σ`, the real algebraic set
`{x ∈ ℝ^σ | f x = 0}` is locally contractible in the classical sense
(`MvPolynomial.locallyContractibleSpace_setOf_eval_eq_zero`, via the Kurdyka–Łojasiewicz
inequality and gradient descent), hence semilocally simply connected
(`MvPolynomial.semilocallySimplyConnectedSpace_setOf_eval_eq_zero`) and locally path-connected.
These are the properties needed to classify the coverings of such a set by its fundamental group.

## References

* [S. Łojasiewicz, *Ensembles semi-analytiques*, IHES notes, 1965][Lojasiewicz1965]
* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, §9.3][BCR]
-/

open Set

namespace MvPolynomial

variable {σ : Type*} [Finite σ]

/-- Renaming the variables along `e : σ ≃ τ` identifies the zero sets. -/
def zeroSetHomeomorphRename {τ : Type*} (e : σ ≃ τ) (f : MvPolynomial σ ℝ) :
    {y : τ → ℝ | eval y (rename e f) = 0} ≃ₜ {x : σ → ℝ | eval x f = 0} where
  toFun y := ⟨fun i ↦ y.1 (e i), by
    have h : eval y.1 (rename e f) = 0 := y.2
    rwa [eval_rename] at h⟩
  invFun x := ⟨fun j ↦ x.1 (e.symm j), by
    have h : eval x.1 f = 0 := x.2
    change eval _ (rename e f) = 0
    rw [eval_rename]
    convert h using 3
    funext i
    simp⟩
  left_inv y := by ext; simp
  right_inv x := by ext; simp
  continuous_toFun := by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    exact (continuous_apply (e i)).comp continuous_subtype_val
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_pi fun j ↦ ?_) _
    exact (continuous_apply (e.symm j)).comp continuous_subtype_val

/-- **Real algebraic sets are locally contractible** (in the classical sense: small neighbourhoods
contract inside larger ones), for any finite set of variables. -/
theorem locallyContractibleSpace_setOf_eval_eq_zero' (f : MvPolynomial σ ℝ) :
    LocallyContractibleSpace {x : σ → ℝ | eval x f = 0} := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  exact (zeroSetHomeomorphRename e f).locallyContractibleSpace
    (locallyContractibleSpace_setOf_eval_eq_zero (rename e f))

/-- **Real algebraic sets are locally path-connected.** -/
theorem locallyPathConnectedSpace_setOf_eval_eq_zero (f : MvPolynomial σ ℝ) :
    LocallyPathConnectedSpace {x : σ → ℝ | eval x f = 0} := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have := (locallyContractibleSpace_setOf_eval_eq_zero (rename e f)).locallyPathConnectedSpace
  exact (zeroSetHomeomorphRename e f).locallyPathConnectedSpace

/-- **Real algebraic sets are semilocally simply connected.** -/
theorem semilocallySimplyConnectedSpace_setOf_eval_eq_zero (f : MvPolynomial σ ℝ) :
    SemilocallySimplyConnectedSpace {x : σ → ℝ | eval x f = 0} := by
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  have := (locallyContractibleSpace_setOf_eval_eq_zero (rename e f)).semilocallySimplyConnectedSpace
  exact (zeroSetHomeomorphRename e f).semilocallySimplyConnectedSpace

end MvPolynomial
