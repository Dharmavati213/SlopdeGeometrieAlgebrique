/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.ManifoldWedge
import SGA.Foundations.Hodge.Kahler

/-!
# Wedge powers of a `2`-form, and of a Kähler form

* `ContinuousAlternatingMap.wedgePow κ m = κᵐ`, the `m`-th wedge power of a `2`-form
  (`κ⁰ = 1`, `κᵐ⁺¹ = κᵐ ⋏ κ`), of degree `2 * m`;
* `Hodge.IsOfType.wedgePow`: `κᵐ` has type `(m, m)` if `κ` has type `(1, 1)`;
  `Hodge.conjForm_wedgePow`: `conj (κᵐ) = (conj κ)ᵐ`;
* on a complex manifold: `Hodge.IsSmoothForm.wedgePow` and `Hodge.partForm_wedgePow_eq_zero`
  (if `∂̄ κ = 0`, resp. `∂ κ = 0`, then the same holds for `κᵐ`); in particular the powers of a
  Kähler form are smooth, `∂`- and `∂̄`-closed and of type `(m, m)`
  (`Hodge.IsKahlerForm.dbarForm_wedgePow`, …).

Reference: D. Huybrechts, *Complex geometry*, §3.1.
-/

noncomputable section

open ContinuousAlternatingMap ComplexConjugate
open scoped Manifold ContDiff

namespace ContinuousAlternatingMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜]

/-- The `m`-th wedge power `κᵐ` of a `2`-form: `κ⁰ = 1`, `κᵐ⁺¹ = κᵐ ⋏ κ`. -/
def wedgePow (κ : E [⋀^Fin 2]→L[ℝ] 𝕜) : (m : ℕ) → E [⋀^Fin (2 * m)]→L[ℝ] 𝕜
  | 0 => constOfIsEmpty ℝ E (Fin 0) 1
  | m + 1 => wedgePow κ m ⋏ κ

@[simp]
lemma wedgePow_zero (κ : E [⋀^Fin 2]→L[ℝ] 𝕜) : wedgePow κ 0 = constOfIsEmpty ℝ E (Fin 0) 1 :=
  rfl

lemma wedgePow_succ (κ : E [⋀^Fin 2]→L[ℝ] 𝕜) (m : ℕ) : wedgePow κ (m + 1) = wedgePow κ m ⋏ κ :=
  rfl

lemma wedgePow_compContinuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (κ : E [⋀^Fin 2]→L[ℝ] 𝕜) (L : F →L[ℝ] E) (m : ℕ) :
    (wedgePow κ m).compContinuousLinearMap L = wedgePow (κ.compContinuousLinearMap L) m := by
  induction m with
  | zero =>
    ext v
    rfl
  | succ m ih => rw [wedgePow_succ, wedge_compContinuousLinearMap, ih, wedgePow_succ]

end ContinuousAlternatingMap

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- `κᵐ` has type `(m, m)` if `κ` has type `(1, 1)`. -/
theorem IsOfType.wedgePow {κ : E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsOfType 1 1 κ) (m : ℕ) :
    IsOfType m m (wedgePow κ m) := by
  induction m with
  | zero =>
    intro c v
    simp
  | succ m ih => exact ih.wedge hκ

/-- `conj (κᵐ) = (conj κ)ᵐ`. -/
theorem conjForm_wedgePow (κ : E [⋀^Fin 2]→L[ℝ] ℂ) (m : ℕ) :
    conjForm (wedgePow κ m) = wedgePow (conjForm κ) m := by
  induction m with
  | zero =>
    ext v
    simp
  | succ m ih => rw [wedgePow_succ, conjForm_wedge, ih, wedgePow_succ]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The local representatives of a constant `0`-form are constant. -/
lemma localRep_const_zero (c : E [⋀^Fin 0]→L[ℝ] ℂ) (x₀ : M) :
    localRep (fun _ : M ↦ c) x₀ = fun _ ↦ c := by
  ext y v
  simp only [localRep, compContinuousLinearMap_apply]
  congr 1
  exact Subsingleton.elim _ _

lemma isSmoothForm_const_zero (c : E [⋀^Fin 0]→L[ℝ] ℂ) : IsSmoothForm (fun _ : M ↦ c) := by
  intro x
  rw [localRep_const_zero]
  exact contDiffAt_const

lemma partForm_const_zero (ε : ℂ) (c : E [⋀^Fin 0]→L[ℝ] ℂ) : partForm ε (fun _ : M ↦ c) = 0 := by
  ext1 x
  rw [partForm, localRep_const_zero, partDeriv, fderiv_fun_const, Pi.zero_apply, _root_.map_zero,
    ← alternatizeUncurryFinCLM_apply, _root_.map_zero, Pi.zero_apply]

/-- The wedge powers of a smooth `2`-form are smooth. -/
theorem IsSmoothForm.wedgePow {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsSmoothForm κ) (m : ℕ) :
    IsSmoothForm fun x ↦ ContinuousAlternatingMap.wedgePow (κ x) m := by
  induction m with
  | zero => exact isSmoothForm_const_zero _
  | succ m ih => exact ih.wedge hκ

/-- If `partForm ε κ = 0` (e.g. `∂̄ κ = 0` or `∂ κ = 0`) for a smooth `2`-form `κ`, then the same
holds for all its wedge powers. -/
theorem partForm_wedgePow_eq_zero {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsSmoothForm κ) {ε : ℂ}
    (h : partForm ε κ = 0) (m : ℕ) :
    partForm ε (fun x ↦ ContinuousAlternatingMap.wedgePow (κ x) m) = 0 := by
  induction m with
  | zero => exact partForm_const_zero ε _
  | succ m ih => exact partForm_wedge_eq_zero (hκ.wedgePow m) hκ ih h

/-- The wedge powers of a Kähler form are smooth. -/
theorem IsKahlerForm.isSmoothForm_wedgePow {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (h : IsKahlerForm κ)
    (m : ℕ) : IsSmoothForm fun x ↦ ContinuousAlternatingMap.wedgePow (κ x) m :=
  h.isSmoothForm.wedgePow m

/-- The wedge powers of a Kähler form are `∂̄`-closed. -/
theorem IsKahlerForm.dbarForm_wedgePow {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (h : IsKahlerForm κ)
    (m : ℕ) : dbarForm (fun x ↦ ContinuousAlternatingMap.wedgePow (κ x) m) = 0 :=
  partForm_wedgePow_eq_zero h.isSmoothForm h.dbarForm_eq_zero m

/-- The wedge powers of a Kähler form are `∂`-closed. -/
theorem IsKahlerForm.delForm_wedgePow {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (h : IsKahlerForm κ)
    (m : ℕ) : delForm (fun x ↦ ContinuousAlternatingMap.wedgePow (κ x) m) = 0 :=
  partForm_wedgePow_eq_zero h.isSmoothForm h.delForm_eq_zero m

end Hodge
