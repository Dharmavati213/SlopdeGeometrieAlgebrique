/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.WedgeDeriv
import SGA.Foundations.Hodge.DolbeaultCohomology

/-!
# Wedge products of forms on complex manifolds

For pointwise forms `α : M → E [⋀^Fin a]→L[ℝ] ℂ`, `β : M → E [⋀^Fin b]→L[ℝ] ℂ` on a complex
manifold `M` (values read in the chart at each point, `Foundations/Hodge/ManifoldForms.lean`), the
wedge product is taken pointwise, `x ↦ α x ⋏ β x`. Since the change of charts acts on values by a
linear pullback, and pullback is multiplicative, local representatives of a wedge product are wedge
products of local representatives (`Hodge.localRep_wedge`). Hence:

* `Hodge.IsSmoothForm.wedge`: the wedge product of smooth forms is smooth;
* `Hodge.partForm_wedge`: the **Leibniz rule** for `∂`, `∂̄` (any `partForm ε`) on `M`,
  `∂̄ (α ⋏ β) = ∂̄α ⋏ β + (-1)ᵃ α ⋏ ∂̄β` for smooth `α`, `β` (first term reindexed along
  `Fin ((a + 1) + b) = Fin ((a + b) + 1)`), and `Hodge.extDerivForm_wedge` for `d`;
* compatibility of `localRep`, smoothness, `∂`, `∂̄` with the reindexing `domDomCongr (finCongr h)`
  of the degree.

Reference: D. Huybrechts, *Complex geometry*, §1.3 and §2.6.
-/

noncomputable section

open ContinuousAlternatingMap Filter Topology Set
open scoped Manifold ContDiff

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M] {a b k k' : ℕ}

/-- Local representatives of a wedge product are wedge products of local representatives. -/
lemma localRep_wedge (α : M → E [⋀^Fin a]→L[ℝ] ℂ) (β : M → E [⋀^Fin b]→L[ℝ] ℂ) (x₀ : M) :
    localRep (fun x ↦ α x ⋏ β x) x₀ = fun y ↦ localRep α x₀ y ⋏ localRep β x₀ y := by
  ext1 y
  exact wedge_compContinuousLinearMap _ _ _

/-- The wedge product of smooth forms is smooth. -/
theorem IsSmoothForm.wedge {α : M → E [⋀^Fin a]→L[ℝ] ℂ} {β : M → E [⋀^Fin b]→L[ℝ] ℂ}
    (hα : IsSmoothForm α) (hβ : IsSmoothForm β) : IsSmoothForm fun x ↦ α x ⋏ β x := by
  intro x
  rw [localRep_wedge]
  exact contDiffAt_wedge (hα x) (hβ x)

/-- **Leibniz rule for `∂` and `∂̄` on a complex manifold** (any `partForm ε`), for smooth forms:
`∂̄ (α ⋏ β) = ∂̄α ⋏ β + (-1)ᵃ α ⋏ ∂̄β`, the first term reindexed along
`Fin ((a + 1) + b) = Fin ((a + b) + 1)`. -/
theorem partForm_wedge {α : M → E [⋀^Fin a]→L[ℝ] ℂ} {β : M → E [⋀^Fin b]→L[ℝ] ℂ}
    (hα : IsSmoothForm α) (hβ : IsSmoothForm β) (ε : ℂ) (x : M) :
    partForm ε (fun x ↦ α x ⋏ β x) x =
      (partForm ε α x ⋏ β x).domDomCongr (finCongr (Nat.succ_add a b)) +
        ((-1 : ℤ) ^ a) • (α x ⋏ partForm ε β x) := by
  rw [partForm, localRep_wedge, partDeriv_wedge ε ((hα x).differentiableAt (by simp))
    ((hβ x).differentiableAt (by simp)), localRep_self, localRep_self]
  rfl

/-- **Leibniz rule for `d` on a complex manifold**, for smooth forms. -/
theorem extDerivForm_wedge {α : M → E [⋀^Fin a]→L[ℝ] ℂ} {β : M → E [⋀^Fin b]→L[ℝ] ℂ}
    (hα : IsSmoothForm α) (hβ : IsSmoothForm β) (x : M) :
    extDerivForm (fun x ↦ α x ⋏ β x) x =
      (extDerivForm α x ⋏ β x).domDomCongr (finCongr (Nat.succ_add a b)) +
        ((-1 : ℤ) ^ a) • (α x ⋏ extDerivForm β x) := by
  rw [extDerivForm, localRep_wedge, extDeriv_wedge ((hα x).differentiableAt (by simp))
    ((hβ x).differentiableAt (by simp)), localRep_self, localRep_self]
  rfl

/-- If `∂̄ α = 0` and `∂̄ β = 0` (or `∂`, `d`: any `partForm ε`), then `∂̄ (α ⋏ β) = 0`. -/
theorem partForm_wedge_eq_zero {α : M → E [⋀^Fin a]→L[ℝ] ℂ} {β : M → E [⋀^Fin b]→L[ℝ] ℂ}
    (hα : IsSmoothForm α) (hβ : IsSmoothForm β) {ε : ℂ} (hα0 : partForm ε α = 0)
    (hβ0 : partForm ε β = 0) : partForm ε (fun x ↦ α x ⋏ β x) = 0 := by
  ext1 x
  rw [partForm_wedge hα hβ, hα0, hβ0]
  simp

/-! ### Reindexing the degree -/

lemma localRep_domDomCongr (η : M → E [⋀^Fin k]→L[ℝ] ℂ) (e : Fin k ≃ Fin k') (x₀ : M) :
    localRep (fun x ↦ (η x).domDomCongr e) x₀ = fun y ↦ (localRep η x₀ y).domDomCongr e := by
  ext1 y
  exact (domDomCongr_compContinuousLinearMap _ _ _)

theorem IsSmoothForm.domDomCongr {η : M → E [⋀^Fin k]→L[ℝ] ℂ} (h : IsSmoothForm η)
    (e : Fin k ≃ Fin k') : IsSmoothForm fun x ↦ (η x).domDomCongr e := by
  intro x
  rw [localRep_domDomCongr]
  let L : (E [⋀^Fin k]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin k']→L[ℝ] ℂ) :=
    { toFun := fun α ↦ α.domDomCongr e
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl
      cont := by
        refine (continuous_induced_rng.2 ?_)
        exact (ContinuousMultilinearMap.domDomCongrₗᵢ ℝ E ℂ e).continuous.comp
          continuous_induced_dom }
  exact L.contDiff.contDiffAt.comp _ (h x)

/-- `∂`, `∂̄` commute with the reindexing `Fin k = Fin k'` of the degree. -/
theorem partForm_domDomCongr_finCongr {η : M → E [⋀^Fin k]→L[ℝ] ℂ} (h : k = k') (ε : ℂ) (x : M) :
    partForm ε (fun x ↦ (η x).domDomCongr (finCongr h)) x =
      (partForm ε η x).domDomCongr (finCongr (congrArg (· + 1) h)) := by
  subst h
  simp only [finCongr_refl, domDomCongr_refl]

/-- `d` commutes with the reindexing `Fin k = Fin k'` of the degree. -/
theorem extDerivForm_domDomCongr_finCongr {η : M → E [⋀^Fin k]→L[ℝ] ℂ} (h : k = k') (x : M) :
    extDerivForm (fun x ↦ (η x).domDomCongr (finCongr h)) x =
      (extDerivForm η x).domDomCongr (finCongr (congrArg (· + 1) h)) := by
  subst h
  simp only [finCongr_refl, domDomCongr_refl]

end Hodge
