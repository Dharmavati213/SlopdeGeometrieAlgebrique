/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.DbarHodgeStatement
import SGA.Foundations.Hodge.Statements

/-!
# Hodge symmetry `h^{0,q} = h^{q,0}` from the Hodge theorem

On a compact Hausdorff complex manifold `M` with a Kähler form `κ`:

* `Hodge.finiteDimensional_holomorphicForms_zero`: holomorphic functions on `M` are locally
  constant (they are `∂`-closed by `Hodge.IsKahlerForm.delForm_eq_zero_of_dbarForm_eq_zero`), so
  they form a finite-dimensional space (`M` has finitely many connected components).
* `Hodge.DbarHarmonicClosedStatement` (statement only): every `∂̄`-harmonic `(0, q + 1)`-form
  (`Hodge.IsDbarHarmonic`) is `∂`-closed. This is the consequence of the Kähler identities used:
  `∂̄*h = 0` makes `∂h` primitive, and the Hodge–Riemann bilinear relations for primitive
  `(1, q + 1)`-forms together with Stokes' theorem give `∂h = 0`.
* `Hodge.compactKahlerHodgeSymmetry_of_dbarHodgeTheorem`: **`Hodge.DbarHodgeTheoremStatement`
  and `Hodge.DbarHarmonicClosedStatement` imply `Hodge.CompactKahlerHodgeSymmetryStatement`.**
  Every Dolbeault class has a harmonic representative `h`; `∂h = 0`, so `h̄` is a holomorphic
  form and `[h] = [conj h̄]`: the map `η ↦ [η̄]` (`Hodge.conjDolbeault`, injective by
  `Hodge.conjDolbeault_injective`) is onto.

Reference: D. Huybrechts, *Complex geometry*, Cor. 3.2.12; C. Voisin, *Hodge theory and complex
algebraic geometry I*, Thm. 6.11, Cor. 6.12.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

universe u v

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]

/-! ### Holomorphic functions on a compact Kähler manifold -/

/-- For `0`-forms the local representative is the value at the corresponding point. -/
lemma localRep_zero_degree (η : M → E [⋀^Fin 0]→L[ℝ] ℂ) (x₀ : M) (y : E) :
    localRep η x₀ y = η ((extChartAt 𝓘(ℂ, E) x₀).symm y) := by
  ext v
  simp only [localRep, compContinuousLinearMap_apply]
  congr 1
  exact Subsingleton.elim _ _

/-- A `0`-form valued map with vanishing exterior derivative has vanishing derivative. -/
lemma fderiv_eq_zero_of_extDeriv_eq_zero {f : E → E [⋀^Fin 0]→L[ℝ] ℂ} {y : E}
    (h : extDeriv f y = 0) : fderiv ℝ f y = 0 := by
  ext w v
  have := congrArg (fun α ↦ α ![w]) h
  simp only [extDeriv, alternatizeUncurryFin_apply] at this
  rw [Fin.sum_univ_one] at this
  rw [show v = Fin.removeNth 0 ![w] from Subsingleton.elim _ _]
  simpa using this

variable [FiniteDimensional ℂ E]

/-- On a compact Kähler manifold, a holomorphic function (a smooth `0`-form `η` with `∂̄η = 0`) is
locally constant. -/
theorem isLocallyConstant_of_holomorphicForms [CompactSpace M] [T2Space M]
    (hK : IsKahlerManifold E M) (η : holomorphicForms E M 0) :
    IsLocallyConstant (η : smoothForms E M 0 0).1 := by
  set f := (η : smoothForms E M 0 0).1
  have hs : IsSmoothForm f := η.1.2.1
  have hdb : dbarForm f = 0 := congrArg Subtype.val (show dbarLinear E M 0 0 η.1 = 0 from η.2)
  have hdel : delForm f = 0 := delForm_holomorphicForms hK η
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x₀
  set φ := extChartAt 𝓘(ℂ, E) x₀
  set g := localRep f x₀
  have hT := isOpen_extChartAt_target (I := 𝓘(ℂ, E)) x₀
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hT (φ x₀) (mem_extChartAt_target x₀)
  -- `g` has vanishing derivative on the chart
  have hg' : ∀ y ∈ φ.target, fderiv ℝ g y = 0 := by
    intro y hy
    apply fderiv_eq_zero_of_extDeriv_eq_zero
    rw [extDeriv_eq_delDeriv_add_dbarDeriv, delDeriv_def, dbarDeriv_def,
      ← localRep_partForm hs (-1) x₀ hy, ← localRep_partForm hs 1 x₀ hy,
      show partForm (-1) f = delForm f from rfl, show partForm 1 f = dbarForm f from rfl, hdel, hdb,
      localRep_zero]
    simp
  have hconst : ∀ y ∈ Metric.ball (φ x₀) r, g y = g (φ x₀) := by
    intro y hy
    refine (convex_ball (φ x₀) r).is_const_of_fderivWithin_eq_zero
      (fun z hz ↦ ((hs.contDiffAt_localRep x₀ (hball hz)).differentiableAt (by simp))
        |>.differentiableWithinAt) (fun z hz ↦ ?_) hy (Metric.mem_ball_self hr)
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hz]
    exact hg' z (hball hz)
  have hsrc : ∀ᶠ x in 𝓝 x₀, x ∈ φ.source := extChartAt_source_mem_nhds x₀
  have hnhds : ∀ᶠ x in 𝓝 x₀, x ∈ φ.source ∧ φ x ∈ Metric.ball (φ x₀) r :=
    hsrc.and ((continuousAt_extChartAt x₀).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  filter_upwards [hnhds] with x hx
  have h1 : f x = g (φ x) := by
    have := localRep_zero_degree (M := M) f x₀ (φ x)
    rw [PartialEquiv.left_inv _ hx.1] at this
    exact this.symm
  have h2 : f x₀ = g (φ x₀) := by
    have := localRep_zero_degree (M := M) f x₀ (φ x₀)
    rw [PartialEquiv.left_inv _ (mem_extChartAt_source x₀)] at this
    exact this.symm
  rw [h1, h2, hconst _ hx.2]

/-- **Holomorphic functions on a compact Kähler manifold form a finite-dimensional space**: they
are locally constant, and `M` has finitely many connected components. -/
theorem finiteDimensional_holomorphicForms_zero [CompactSpace M] [T2Space M]
    (hK : IsKahlerManifold E M) : FiniteDimensional ℂ (holomorphicForms E M 0) := by
  have : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace E M
  obtain ⟨xs, hxs⟩ := isCompact_univ.elim_finite_subcover (fun x : M ↦ connectedComponent x)
    (fun _ ↦ isOpen_connectedComponent) (fun x _ ↦ mem_iUnion.2 ⟨x, mem_connectedComponent⟩)
  let ev : holomorphicForms E M 0 →ₗ[ℂ] (xs → ℂ) :=
    { toFun := fun η x ↦ (η : smoothForms E M 0 0).1 x Fin.elim0
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  refine Module.Finite.of_injective ev fun η₁ η₂ h ↦ ?_
  rw [← sub_eq_zero]
  set η := η₁ - η₂
  have hη : ev η = 0 := by rw [map_sub, h, sub_self]
  have hlc := isLocallyConstant_of_holomorphicForms hK η
  ext1
  ext1
  funext y
  obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hxs (mem_univ y))
  have h1 : (η : smoothForms E M 0 0).1 y = (η : smoothForms E M 0 0).1 x :=
    hlc.apply_eq_of_isPreconnected isPreconnected_connectedComponent hyx mem_connectedComponent
  ext v
  have h2 := congrFun hη ⟨x, hx⟩
  have hv : v = Fin.elim0 := funext fun i ↦ i.elim0
  rw [hv, h1]
  exact h2

end Hodge
