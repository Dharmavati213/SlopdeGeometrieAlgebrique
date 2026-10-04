/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.DolbeaultCohomology

/-!
# Kähler forms

A **Kähler form** on a complex manifold `M` (modelled on `E`, `IsManifold 𝓘(ℂ, E) ω M`) is a smooth
real `(1, 1)`-form `ω` which is positive (`ω(v, i v) > 0` for every nonzero tangent vector `v`,
i.e. `g(v, w) = ω(v, i w)` is a Riemannian metric) and closed (`dω = 0`). `M` is a Kähler manifold
if it carries one; for instance every smooth projective complex variety, with the restriction of the
Fubini–Study form.

* `Hodge.IsKahlerForm ω`, with `ω x` read in the chart at `x` as usual
  (`Foundations/Hodge/ManifoldForms.lean`);
* `Hodge.IsKahlerForm.dbarForm_eq_zero`, `Hodge.IsKahlerForm.delForm_eq_zero`: a Kähler form is
  `∂`- and `∂̄`-closed (`dω = ∂ω + ∂̄ω` with `∂ω`, `∂̄ω` of types `(2, 1)`, `(1, 2)`).

Reference: D. Huybrechts, *Complex geometry*, §3.1; C. Voisin, *Hodge theory and complex algebraic
geometry I*, §3.1.
-/

noncomputable section

open ComplexConjugate
open scoped Manifold ContDiff

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- A `3`-form that is both of type `(2, 1)` and of type `(1, 2)` is zero. -/
lemma eq_zero_of_isOfType_two_one_of_isOfType_one_two {α : E [⋀^Fin 3]→L[ℝ] ℂ}
    (h₁ : IsOfType 2 1 α) (h₂ : IsOfType 1 2 α) : α = 0 := by
  ext v
  have e₁ := h₁ Complex.I v
  have e₂ := h₂ Complex.I v
  rw [e₁, Complex.conj_I] at e₂
  have : (2 * Complex.I) * α v = 0 := by
    linear_combination e₂ + (α v) * (Complex.I * Complex.I_sq) + α v * Complex.I_sq * Complex.I
  simpa [Complex.I_ne_zero] using this

/-- A **Kähler form** on the complex manifold `M`: a smooth `(1, 1)`-form `ω` which is real
(`ω̄ = ω`), positive (`Re ω(v, i v) > 0` for `v ≠ 0`, in the chart at each point; `ω(v, iv)` is
real since `ω` is) and closed (`dω = 0`). -/
structure IsKahlerForm (κ : M → E [⋀^Fin 2]→L[ℝ] ℂ) : Prop where
  isSmoothForm : IsSmoothForm κ
  isOfType : ∀ x, IsOfType 1 1 (κ x)
  conjForm_eq : ∀ x, conjForm (κ x) = κ x
  pos : ∀ x (v : E), v ≠ 0 → 0 < (κ x ![v, Complex.I • v]).re
  extDerivForm_eq_zero : extDerivForm κ = 0

/-- A Kähler form is `∂̄`-closed. -/
theorem IsKahlerForm.dbarForm_eq_zero {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (h : IsKahlerForm κ) :
    dbarForm κ = 0 := by
  ext1 x
  have hd := congrFun h.extDerivForm_eq_zero x
  rw [extDerivForm_eq_add, Pi.add_apply, Pi.zero_apply, add_eq_zero_iff_eq_neg] at hd
  have h₁ : IsOfType 2 1 (delForm κ x) := isOfType_delForm h.isOfType x
  have h₂ : IsOfType 1 2 (delForm κ x) := by
    rw [hd]
    exact (isOfType_dbarForm h.isOfType x).neg
  have h0 := eq_zero_of_isOfType_two_one_of_isOfType_one_two h₁ h₂
  rw [h0, zero_eq_neg] at hd
  exact hd

/-- A Kähler form is `∂`-closed. -/
theorem IsKahlerForm.delForm_eq_zero {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (h : IsKahlerForm κ) :
    delForm κ = 0 := by
  have hd := h.extDerivForm_eq_zero
  rw [extDerivForm_eq_add, h.dbarForm_eq_zero, add_zero] at hd
  exact hd

variable (E M) in
/-- `M` admits a Kähler form. -/
def IsKahlerManifold : Prop :=
  ∃ κ : M → E [⋀^Fin 2]→L[ℝ] ℂ, IsKahlerForm κ

end Hodge
