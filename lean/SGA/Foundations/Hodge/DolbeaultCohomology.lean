/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.ManifoldForms

/-!
# Dolbeault cohomology and holomorphic forms of a complex manifold

For a complex manifold `M` modelled on a complex normed space `E` (`ChartedSpace E M`,
`IsManifold 𝓘(ℂ, E) ω M`):

* `Hodge.smoothForms E M p q`: the complex vector space `A^{p,q}(M)` of smooth forms of type
  `(p, q)` on `M` (`Hodge.IsSmoothForm`, `Hodge.IsOfType`);
* `Hodge.dbarLinear E M p q : A^{p,q}(M) → A^{p,q+1}(M)`: the operator `∂̄`;
* `Hodge.dolbeaultCohomology E M p q`: `H^{p,q}_∂̄(M) = ker ∂̄ / im ∂̄`;
* `Hodge.holomorphicForms E M p`: the holomorphic `p`-forms, i.e. the smooth `(p, 0)`-forms `η`
  with `∂̄ η = 0` (= `H⁰(M, Ωᵖ)`); `H^{p,0}_∂̄(M)` is isomorphic to it
  (`Hodge.dolbeaultCohomologyZeroEquiv`);
* `Hodge.extDerivForm`: the exterior derivative of forms on `M`, `d = ∂ + ∂̄`
  (`Hodge.extDerivForm_eq_add`).

Reference: D. Huybrechts, *Complex geometry*, §2.6; R. O. Wells, *Differential analysis on complex
manifolds*, Ch. II.3.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap Filter Topology Set
open scoped Manifold ContDiff

namespace Hodge

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- The complex vector space `A^{p,q}(M)` of smooth `(p, q)`-forms on the complex manifold `M`. -/
def smoothForms (p q : ℕ) : Submodule ℂ (M → E [⋀^Fin (p + q)]→L[ℝ] ℂ) where
  carrier := {η | IsSmoothForm η ∧ ∀ x, IsOfType p q (η x)}
  add_mem' h₁ h₂ := ⟨h₁.1.add h₂.1, fun x ↦ (h₁.2 x).add (h₂.2 x)⟩
  zero_mem' := ⟨isSmoothForm_zero, fun _ ↦ isOfType_zero p q⟩
  smul_mem' c _ h := ⟨h.1.smul c, fun x ↦ (h.2 x).smul c⟩

variable {E M} in
lemma mem_smoothForms {p q : ℕ} {η : M → E [⋀^Fin (p + q)]→L[ℝ] ℂ} :
    η ∈ smoothForms E M p q ↔ IsSmoothForm η ∧ ∀ x, IsOfType p q (η x) :=
  Iff.rfl

/-- `∂̄ : A^{p,q}(M) → A^{p,q+1}(M)`. -/
def dbarLinear (p q : ℕ) : smoothForms E M p q →ₗ[ℂ] smoothForms E M p (q + 1) where
  toFun η := ⟨dbarForm η.1, η.2.1.dbarForm, isOfType_dbarForm η.2.2⟩
  map_add' η₁ η₂ := Subtype.ext (partForm_add 1 η₁.2.1 η₂.2.1)
  map_smul' c η := Subtype.ext (partForm_smul 1 c η.2.1)

@[simp]
lemma coe_dbarLinear (p q : ℕ) (η : smoothForms E M p q) :
    (dbarLinear E M p q η : M → E [⋀^Fin (p + (q + 1))]→L[ℝ] ℂ) = dbarForm η.1 :=
  rfl

lemma dbarLinear_comp_dbarLinear (p q : ℕ) :
    dbarLinear E M p (q + 1) ∘ₗ dbarLinear E M p q = 0 := by
  ext η : 2
  exact dbarForm_dbarForm η.2.1

/-- The `∂̄`-closed `(p, q)`-forms. -/
def dbarClosed (p q : ℕ) : Submodule ℂ (smoothForms E M p q) :=
  LinearMap.ker (dbarLinear E M p q)

/-- The `∂̄`-exact `(p, q)`-forms (`0` for `q = 0`). -/
def dbarExact : (p q : ℕ) → Submodule ℂ (smoothForms E M p q)
  | _, 0 => ⊥
  | p, q + 1 => LinearMap.range (dbarLinear E M p q)

lemma dbarExact_le_dbarClosed (p q : ℕ) : dbarExact E M p q ≤ dbarClosed E M p q := by
  cases q with
  | zero => exact bot_le
  | succ q =>
    rintro _ ⟨η, rfl⟩
    change dbarLinear E M p (q + 1) (dbarLinear E M p q η) = 0
    rw [← LinearMap.comp_apply, dbarLinear_comp_dbarLinear, LinearMap.zero_apply]

/-- **Dolbeault cohomology** `H^{p,q}_∂̄(M)`: `∂̄`-closed smooth `(p, q)`-forms modulo `∂̄`-exact
ones. -/
abbrev dolbeaultCohomology (p q : ℕ) : Type _ :=
  dbarClosed E M p q ⧸ (dbarExact E M p q).comap (dbarClosed E M p q).subtype

/-- The **holomorphic `p`-forms** on `M` (`H⁰(M, Ωᵖ)`): the smooth `(p, 0)`-forms `η` with
`∂̄ η = 0`. -/
abbrev holomorphicForms (p : ℕ) : Submodule ℂ (smoothForms E M p 0) :=
  dbarClosed E M p 0

/-- `H^{p,0}_∂̄(M)` is the space of holomorphic `p`-forms. -/
def dolbeaultCohomologyZeroEquiv (p : ℕ) :
    dolbeaultCohomology E M p 0 ≃ₗ[ℂ] holomorphicForms E M p :=
  Submodule.quotEquivOfEqBot _ (by simp [dbarExact])

variable {E M}

/-- The exterior derivative of forms on the complex manifold `M`, computed in the chart at each
point. -/
def extDerivForm {n : ℕ} (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x : M) : E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  extDeriv (localRep η x) (extChartAt 𝓘(ℂ, E) x x)

/-- `d = ∂ + ∂̄` on a complex manifold. -/
lemma extDerivForm_eq_add {n : ℕ} (η : M → E [⋀^Fin n]→L[ℝ] ℂ) :
    extDerivForm η = delForm η + dbarForm η := by
  ext1 x
  exact extDeriv_eq_delDeriv_add_dbarDeriv _ _

end Hodge
