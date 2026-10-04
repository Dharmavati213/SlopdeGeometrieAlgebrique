/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.KahlerHolomorphic

/-!
# Statement: the Hodge theorem for `∂̄` on `(0, q)`-forms

Let `M` be a compact Hausdorff complex manifold of dimension `n` (modelled on a finite-dimensional
complex normed space `E`) with a Kähler form `κ`. On smooth `(0, q)`-forms the Hermitian `L²`
product of the metric `κ` is, up to a positive constant,

  `⟨γ, h⟩ = ∫_M γ ∧ h̄ ∧ κⁿ⁻ᵍ`

(for `(0, q)`-forms this is the Hodge star; the positivity is
`Hodge.IsPositiveForm.wedge_conj_wedgePow_pos`). A smooth `(0, q + 1)`-form `h` is
**`∂̄`-harmonic** if `∂̄h = 0` and `h` is orthogonal to all `∂̄`-exact forms:
`∫_M ∂̄β ∧ h̄ ∧ κᵐ = 0` for every smooth `(0, q)`-form `β`, where `(q + 1) + m = n`
(`Hodge.IsDbarCoclosed`, i.e. `∂̄*h = 0` in the weak sense; `Hodge.IsDbarHarmonic`).

* `Hodge.DbarHodgeTheoremStatement` (statement only, registry row C24): there is a
  finite-dimensional space of `∂̄`-harmonic `(0, q + 1)`-forms such that every `∂̄`-closed smooth
  `(0, q + 1)`-form is the sum of one of them and a `∂̄`-exact form `∂̄β`, `β` smooth.

This is the Hodge theorem for the `∂̄`-Laplacian on `(0, q)`-forms (Hodge, Kodaira; Huybrechts,
*Complex geometry*, Thm. 4.1.13; Wells, *Differential analysis on complex manifolds*, Thm. IV.5.2;
Griffiths–Harris, p. 84). It holds for every Hermitian metric; we state it for a Kähler form,
which is the case used. Its proof needs Sobolev spaces on `M`, Gårding's inequality, Rellich's
lemma and elliptic regularity.

The quantifier over the Haar measure `μ` on `E` and the chart partition `P` in
`Hodge.IsDbarCoclosed` is harmless: `Hodge.integralForm` does not depend on `P`
(`Hodge.integralForm_eq_of_partition`) and Haar measures differ by a positive constant.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap MeasureTheory
open scoped Manifold ContDiff

universe u v

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-- `h` is **orthogonal to the `∂̄`-exact forms**, i.e. `∂̄* h = 0` weakly, for the `L²` product of
the Kähler form `κ` on `(0, q + 1)`-forms: `∫_M ∂̄β ∧ h̄ ∧ κᵐ = 0` for every smooth `(0, q)`-form
`β`, where `(q + 1) + m = dim_ℂ E`. The integral is computed with any Haar measure on `E` and any
chart partition (it does not depend on them up to a positive factor). -/
def IsDbarCoclosed (κ : M → E [⋀^Fin 2]→L[ℝ] ℂ) {q m : ℕ}
    (hm : (q + 1) + m = Module.finrank ℂ E) (h : M → E [⋀^Fin (0 + (q + 1))]→L[ℝ] ℂ) : Prop :=
  ∀ β ∈ smoothForms E M 0 q, ∀ [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (P : ChartPartition E M),
    integralForm μ P (stdFrame E (by omega))
      (fun x ↦ (dbarForm β x ⋏ conjForm (h x)) ⋏ wedgePow (κ x) m) = 0

/-- `h` is **`∂̄`-harmonic** for the Kähler form `κ`: `∂̄h = 0` and `∂̄*h = 0` (weakly,
`Hodge.IsDbarCoclosed`). -/
def IsDbarHarmonic (κ : M → E [⋀^Fin 2]→L[ℝ] ℂ) {q m : ℕ}
    (hm : (q + 1) + m = Module.finrank ℂ E) (h : M → E [⋀^Fin (0 + (q + 1))]→L[ℝ] ℂ) : Prop :=
  dbarForm h = 0 ∧ IsDbarCoclosed κ hm h

/-- **The Hodge theorem for `∂̄` on `(0, q)`-forms** (statement only; registry row C24): on a
compact Hausdorff complex manifold `M` modelled on a finite-dimensional complex normed space `E`,
with a Kähler form `κ`, for all `q`, `m` with `(q + 1) + m = dim_ℂ E` there is a
finite-dimensional space `H` of `∂̄`-harmonic smooth `(0, q + 1)`-forms such that every
`∂̄`-closed smooth `(0, q + 1)`-form `α` is `h + ∂̄β` with `h ∈ H` and `β` a smooth
`(0, q)`-form.

This is the part of the Hodge theorem (`A^{0,q} = ℋ^{0,q} ⊕ ∂̄A^{0,q-1} ⊕ ∂̄*A^{0,q+1}` with
`ℋ^{0,q}` finite-dimensional) that is used; `H` can be taken to be the whole space of harmonic
forms. Degrees `q + 1 > dim_ℂ E` are excluded: there all `(0, q + 1)`-forms vanish. -/
def DbarHodgeTheoremStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (M : Type v) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [CompactSpace M] [T2Space M] (κ : M → E [⋀^Fin 2]→L[ℝ] ℂ), IsKahlerForm κ →
    ∀ (q m : ℕ) (hm : (q + 1) + m = Module.finrank ℂ E),
      ∃ H : Submodule ℂ (smoothForms E M 0 (q + 1)), FiniteDimensional ℂ H ∧
        (∀ h ∈ H, IsDbarHarmonic κ hm (h : M → E [⋀^Fin (0 + (q + 1))]→L[ℝ] ℂ)) ∧
        ∀ α ∈ smoothForms E M 0 (q + 1), dbarForm α = 0 →
          ∃ h ∈ H, ∃ β ∈ smoothForms E M 0 q, α = (h : M → E [⋀^Fin (0 + (q + 1))]→L[ℝ] ℂ) +
            dbarForm β

end Hodge
