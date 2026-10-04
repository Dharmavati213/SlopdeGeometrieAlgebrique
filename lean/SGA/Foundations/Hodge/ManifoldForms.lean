/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Dbar
import SGA.Foundations.Hodge.AlternatingSmooth
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-!
# Differential forms on complex manifolds, `∂` and `∂̄`

Let `M` be a complex manifold modelled on a complex normed space `E` (mathlib's `ChartedSpace E M`
with `IsManifold 𝓘(ℂ, E) ω M`). A *pointwise form* of degree `n` on `M` is a function
`η : M → E [⋀^Fin n]→L[ℝ] ℂ`, the value `η x` being read in the chart at `x` (mathlib's
convention for `TangentSpace 𝓘(ℂ, E) x = E`). Its **local representative** in the chart
`φ = extChartAt 𝓘(ℂ, E) x₀` is

  `Hodge.localRep η x₀ y = η (φ⁻¹ y) ∘ (D(φ_{w} ∘ φ⁻¹)(y), …)`, `w = φ⁻¹ y`,

the pullback of `η w` from the chart at `w` to the chart at `x₀` (`tangentCoordChange`). In two
charts the local representatives differ by pullback along the (holomorphic) change of
coordinates (`Hodge.localRep_eventuallyEq_pullbackForm`).

* `Hodge.IsSmoothForm η`: every local representative is `C^∞` at the centre of its chart;
  then it is `C^∞` on the whole chart (`Hodge.IsSmoothForm.contDiffAt_localRep`).
* `Hodge.partForm ε η x = partDeriv ε (localRep η x) (φₓ x)`, in particular
  `Hodge.dbarForm` (`∂̄`) and `Hodge.delForm` (`∂`). Their local representatives are `∂̄`, `∂` of
  the local representatives on the whole chart (`Hodge.localRep_partForm`), so for smooth `η`
  they are well defined (chart independent), smooth, and satisfy `∂̄² = 0`, `∂² = 0`,
  `∂∂̄ + ∂̄∂ = 0` (`Hodge.dbarForm_dbarForm`, …), shift types as expected, and
  `∂̄ η̄ = conj (∂ η)`.

The spaces of smooth `(p, q)`-forms, Dolbeault cohomology and holomorphic forms are in
`Foundations/Hodge/Dolbeault*.lean`.

Reference: R. O. Wells, *Differential analysis on complex manifolds*, Ch. II; D. Huybrechts,
*Complex geometry*, §2.6.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap Filter Topology Set
open scoped Manifold ContDiff

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n p q : ℕ}

section LocalRep

variable [IsManifold 𝓘(ℂ, E) ω M]

/-- The local representative of a pointwise form `η` (with `η x` read in the chart at `x`) in the
chart at `x₀`: at `y`, the pullback of `η w`, `w = φ_{x₀}⁻¹ y`, along the derivative of the change
of coordinates `φ_w ∘ φ_{x₀}⁻¹` at `y`. -/
def localRep (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x₀ : M) (y : E) : E [⋀^Fin n]→L[ℝ] ℂ :=
  (η ((extChartAt 𝓘(ℂ, E) x₀).symm y)).compContinuousLinearMap
    ((tangentCoordChange 𝓘(ℂ, E) x₀ ((extChartAt 𝓘(ℂ, E) x₀).symm y)
      ((extChartAt 𝓘(ℂ, E) x₀).symm y)).restrictScalars ℝ)

/-- The change of coordinates from the chart at `x₀` to the chart at `w`. -/
def transition (x₀ w : M) : E → E :=
  extChartAt 𝓘(ℂ, E) w ∘ (extChartAt 𝓘(ℂ, E) x₀).symm

/-- The local representative at the centre of the chart is the value itself. -/
lemma localRep_self (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x : M) :
    localRep η x (extChartAt 𝓘(ℂ, E) x x) = η x := by
  ext v
  simp only [localRep, extChartAt_to_inv, compContinuousLinearMap_apply,
    ContinuousLinearMap.coe_restrictScalars']
  congr 1
  ext i
  exact tangentCoordChange_self (mem_extChartAt_source x)

lemma localRep_add (η₁ η₂ : M → E [⋀^Fin n]→L[ℝ] ℂ) (x₀ : M) :
    localRep (η₁ + η₂) x₀ = localRep η₁ x₀ + localRep η₂ x₀ := by
  ext y v
  simp [localRep]

lemma localRep_smul (c : ℂ) (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x₀ : M) :
    localRep (c • η) x₀ = c • localRep η x₀ := by
  ext y v
  simp [localRep]

lemma localRep_zero (x₀ : M) : localRep (0 : M → E [⋀^Fin n]→L[ℝ] ℂ) x₀ = 0 := by
  ext y v
  simp [localRep]

lemma localRep_neg (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x₀ : M) :
    localRep (-η) x₀ = -localRep η x₀ := by
  ext y v
  simp [localRep]

lemma localRep_conjForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x₀ : M) :
    localRep (fun x ↦ conjForm (η x)) x₀ = fun y ↦ conjForm (localRep η x₀ y) :=
  rfl

/-- Local representatives of forms of type `(p, q)` are of type `(p, q)`. -/
lemma IsOfType.localRep {η : M → E [⋀^Fin n]→L[ℝ] ℂ} (h : ∀ x, IsOfType p q (η x)) (x₀ : M)
    (y : E) : IsOfType p q (localRep η x₀ y) :=
  (h _).compContinuousLinearMap _

/-- The derivative of the change of coordinates is `tangentCoordChange`. -/
lemma hasFDerivAt_transition {x₀ w : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target)
    (hw : (extChartAt 𝓘(ℂ, E) x₀).symm y ∈ (extChartAt 𝓘(ℂ, E) w).source) :
    HasFDerivAt (transition x₀ w)
      (tangentCoordChange 𝓘(ℂ, E) x₀ w ((extChartAt 𝓘(ℂ, E) x₀).symm y)) y := by
  have h := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℂ, E))
    (x := x₀) (y := w) (z := (extChartAt 𝓘(ℂ, E) x₀).symm y)
    ⟨(extChartAt 𝓘(ℂ, E) x₀).map_target hy, hw⟩
  rw [PartialEquiv.right_inv _ hy, modelWithCornersSelf_coe, range_id,
    hasFDerivWithinAt_univ] at h
  exact h

/-- The change of coordinates is complex analytic (`C^ω`) near every point of its domain. -/
lemma contDiffAt_transition {x₀ w : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target)
    (hw : (extChartAt 𝓘(ℂ, E) x₀).symm y ∈ (extChartAt 𝓘(ℂ, E) w).source) :
    ContDiffAt ℂ ω (transition x₀ w) y := by
  have hs : y ∈ ((extChartAt 𝓘(ℂ, E) x₀).symm ≫ extChartAt 𝓘(ℂ, E) w).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact ⟨hy, hw⟩
  have ho : IsOpen ((extChartAt 𝓘(ℂ, E) x₀).symm ≫ extChartAt 𝓘(ℂ, E) w).source := by
    rw [PartialEquiv.trans_source, PartialEquiv.symm_source]
    exact (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
      (isOpen_extChartAt_source w)
  exact (contDiffOn_ext_coord_change (I := 𝓘(ℂ, E)) (n := ω) w x₀).contDiffAt
    (ho.mem_nhds hs)

/-- The real derivative of the change of coordinates. -/
lemma fderiv_transition {x₀ w : M} {y : E} (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target)
    (hw : (extChartAt 𝓘(ℂ, E) x₀).symm y ∈ (extChartAt 𝓘(ℂ, E) w).source) :
    fderiv ℝ (transition x₀ w) y =
      (tangentCoordChange 𝓘(ℂ, E) x₀ w ((extChartAt 𝓘(ℂ, E) x₀).symm y)).restrictScalars ℝ :=
  ((hasFDerivAt_transition hy hw).restrictScalars ℝ).fderiv

/-- **Change of charts**: near `φ_{x₀}(z)`, for `z` in the chart domains at `x₀` and at `w`, the
local representative in the chart at `x₀` is the pullback of the local representative in the chart
at `w` along the change of coordinates. -/
theorem localRep_eventuallyEq_pullbackForm_of_mem (η : M → E [⋀^Fin n]→L[ℝ] ℂ) {x₀ w z : M}
    (hz : z ∈ (extChartAt 𝓘(ℂ, E) x₀).source) (hzw : z ∈ (extChartAt 𝓘(ℂ, E) w).source) :
    localRep η x₀ =ᶠ[𝓝 (extChartAt 𝓘(ℂ, E) x₀ z)]
      pullbackForm (transition x₀ w) (localRep η w) := by
  have hU : (extChartAt 𝓘(ℂ, E) x₀).target ∩
      (extChartAt 𝓘(ℂ, E) x₀).symm ⁻¹' (extChartAt 𝓘(ℂ, E) w).source ∈
        𝓝 (extChartAt 𝓘(ℂ, E) x₀ z) := by
    refine ((continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀)
      (isOpen_extChartAt_source w)).mem_nhds ⟨(extChartAt 𝓘(ℂ, E) x₀).map_source hz, ?_⟩
    rw [mem_preimage, PartialEquiv.left_inv _ hz]
    exact hzw
  filter_upwards [hU] with y ⟨hy, hyw⟩
  set w' := (extChartAt 𝓘(ℂ, E) x₀).symm y with hw'
  have hT : transition x₀ w y = extChartAt 𝓘(ℂ, E) w w' := rfl
  have hinv : (extChartAt 𝓘(ℂ, E) w).symm (extChartAt 𝓘(ℂ, E) w w') = w' :=
    PartialEquiv.left_inv _ hyw
  have hx₀ : w' ∈ (extChartAt 𝓘(ℂ, E) x₀).source := (extChartAt 𝓘(ℂ, E) x₀).map_target hy
  rw [pullbackForm, fderiv_transition hy hyw, hT, localRep, localRep, hinv]
  ext v
  simp only [compContinuousLinearMap_apply, ContinuousLinearMap.coe_restrictScalars']
  congr 1
  ext i
  exact (tangentCoordChange_comp (I := 𝓘(ℂ, E)) ⟨⟨hx₀, hyw⟩, mem_extChartAt_source w'⟩).symm

/-- **Change of charts**: near `φ_{x₀}(w)`, the local representative in the chart at `x₀` is the
pullback of the local representative in the chart at `w` along the change of coordinates. -/
theorem localRep_eventuallyEq_pullbackForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) {x₀ w : M}
    (hw : w ∈ (extChartAt 𝓘(ℂ, E) x₀).source) :
    localRep η x₀ =ᶠ[𝓝 (extChartAt 𝓘(ℂ, E) x₀ w)]
      pullbackForm (transition x₀ w) (localRep η w) :=
  localRep_eventuallyEq_pullbackForm_of_mem η hw (mem_extChartAt_source w)

/-- A pointwise form is **smooth** if each local representative is `C^∞` at the centre of its
chart (equivalently, on the whole chart: `Hodge.IsSmoothForm.contDiffAt_localRep`). -/
def IsSmoothForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) : Prop :=
  ∀ x, ContDiffAt ℝ ∞ (localRep η x) (extChartAt 𝓘(ℂ, E) x x)

/-- The pullback of a smooth local form along a change of coordinates is smooth. -/
lemma contDiffAt_pullbackForm_transition {x₀ w : M} {y : E} {ρ : E → E [⋀^Fin n]→L[ℝ] ℂ}
    (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target)
    (hw : (extChartAt 𝓘(ℂ, E) x₀).symm y ∈ (extChartAt 𝓘(ℂ, E) w).source)
    (hρ : ContDiffAt ℝ ∞ ρ (transition x₀ w y)) :
    ContDiffAt ℝ ∞ (pullbackForm (transition x₀ w) ρ) y := by
  have hT : ContDiffAt ℝ ω (transition x₀ w) y :=
    (contDiffAt_transition hy hw).restrict_scalars ℝ
  have hT' : ContDiffAt ℝ ∞ (transition x₀ w) y := hT.of_le le_top
  have hDT : ContDiffAt ℝ ∞ (fderiv ℝ (transition x₀ w)) y :=
    hT.fderiv_right (m := ∞) le_top
  exact (hρ.comp y hT').continuousAlternatingMapCompContinuousLinearMap hDT

/-- A smooth form has `C^∞` local representatives on the whole chart. -/
theorem IsSmoothForm.contDiffAt_localRep {η : M → E [⋀^Fin n]→L[ℝ] ℂ} (h : IsSmoothForm η)
    (x₀ : M) {y : E} (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target) :
    ContDiffAt ℝ ∞ (localRep η x₀) y := by
  set w := (extChartAt 𝓘(ℂ, E) x₀).symm y
  have hw : w ∈ (extChartAt 𝓘(ℂ, E) x₀).source := (extChartAt 𝓘(ℂ, E) x₀).map_target hy
  have hyw : extChartAt 𝓘(ℂ, E) x₀ w = y := PartialEquiv.right_inv _ hy
  have he := localRep_eventuallyEq_pullbackForm η hw
  rw [hyw] at he
  refine ContDiffAt.congr_of_eventuallyEq ?_ he
  exact contDiffAt_pullbackForm_transition hy (mem_extChartAt_source w) (h w)

end LocalRep

section Smooth

variable [IsManifold 𝓘(ℂ, E) ω M] {η η₁ η₂ : M → E [⋀^Fin n]→L[ℝ] ℂ}

lemma isSmoothForm_zero : IsSmoothForm (0 : M → E [⋀^Fin n]→L[ℝ] ℂ) := by
  intro x
  rw [localRep_zero]
  exact contDiffAt_const

lemma IsSmoothForm.add (h₁ : IsSmoothForm η₁) (h₂ : IsSmoothForm η₂) :
    IsSmoothForm (η₁ + η₂) := by
  intro x
  rw [localRep_add]
  exact (h₁ x).add (h₂ x)

lemma IsSmoothForm.smul (c : ℂ) (h : IsSmoothForm η) : IsSmoothForm (c • η) := by
  intro x
  rw [localRep_smul]
  exact (h x).const_smul c

lemma IsSmoothForm.neg (h : IsSmoothForm η) : IsSmoothForm (-η) := by
  intro x
  rw [localRep_neg]
  exact (h x).neg

lemma IsSmoothForm.conjForm (h : IsSmoothForm η) : IsSmoothForm fun x ↦ conjForm (η x) := by
  intro x
  rw [localRep_conjForm]
  exact (conjFormCLM E n).contDiff.contDiffAt.comp _ (h x)

end Smooth

section Operators

variable [IsManifold 𝓘(ℂ, E) ω M] {η η₁ η₂ : M → E [⋀^Fin n]→L[ℝ] ℂ}

/-- The operator `partDeriv ε` on pointwise forms on `M`, computed in the chart at each point. For
`ε = 1` it is `∂̄` (`Hodge.dbarForm`), for `ε = -1` it is `∂` (`Hodge.delForm`). -/
def partForm (ε : ℂ) (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x : M) : E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  partDeriv ε (localRep η x) (extChartAt 𝓘(ℂ, E) x x)

/-- `∂̄` on forms on a complex manifold. -/
def dbarForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) : M → E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  partForm 1 η

/-- `∂` on forms on a complex manifold. -/
def delForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) : M → E [⋀^Fin (n + 1)]→L[ℝ] ℂ :=
  partForm (-1) η

lemma partDeriv_congr (ε : ℂ) {ρ₁ ρ₂ : E → E [⋀^Fin n]→L[ℝ] ℂ} {y : E} (h : ρ₁ =ᶠ[𝓝 y] ρ₂) :
    partDeriv ε ρ₁ y = partDeriv ε ρ₂ y := by
  rw [partDeriv, partDeriv, h.fderiv_eq]

/-- **Chart independence of `∂`, `∂̄`**: on the whole chart at `x₀`, the local representative of
`partForm ε η` is `partDeriv ε` of the local representative of `η`. -/
theorem localRep_partForm (h : IsSmoothForm η) (ε : ℂ) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target) :
    localRep (partForm ε η) x₀ y = partDeriv ε (localRep η x₀) y := by
  set w := (extChartAt 𝓘(ℂ, E) x₀).symm y with hwdef
  have hw : w ∈ (extChartAt 𝓘(ℂ, E) x₀).source := (extChartAt 𝓘(ℂ, E) x₀).map_target hy
  have hyw : extChartAt 𝓘(ℂ, E) x₀ w = y := PartialEquiv.right_inv _ hy
  have he := localRep_eventuallyEq_pullbackForm η hw
  rw [hyw] at he
  have hT : ContDiffAt ℂ 2 (transition x₀ w) y :=
    (contDiffAt_transition hy (mem_extChartAt_source w)).of_le le_top
  have hρ : DifferentiableAt ℝ (localRep η w) (transition x₀ w y) :=
    (h w).differentiableAt (by simp)
  rw [partDeriv_congr ε he, partDeriv_pullbackForm ε hρ hT,
    fderiv_transition hy (mem_extChartAt_source w)]
  rfl

lemma localRep_partForm_eventuallyEq (h : IsSmoothForm η) (ε : ℂ) (x₀ : M) {y : E}
    (hy : y ∈ (extChartAt 𝓘(ℂ, E) x₀).target) :
    localRep (partForm ε η) x₀ =ᶠ[𝓝 y] partDeriv ε (localRep η x₀) := by
  filter_upwards [(isOpen_extChartAt_target x₀).mem_nhds hy] with y' hy'
  exact localRep_partForm h ε x₀ hy'

lemma contDiffAt_partDeriv (ε : ℂ) {ρ : E → E [⋀^Fin n]→L[ℝ] ℂ} {y : E}
    (hρ : ContDiffAt ℝ ∞ ρ y) : ContDiffAt ℝ ∞ (partDeriv ε ρ) y := by
  rw [partDeriv_eq_comp]
  exact (alternatizeUncurryFinCLM ℝ E ℂ ∘L partCLM E _ ε).contDiff.contDiffAt.comp y
    (hρ.fderiv_right (m := ∞) (by simp))

/-- `∂`, `∂̄` of a smooth form are smooth. -/
theorem IsSmoothForm.partForm (h : IsSmoothForm η) (ε : ℂ) : IsSmoothForm (partForm ε η) := by
  intro x
  exact (contDiffAt_partDeriv ε ((h x))).congr_of_eventuallyEq
    (localRep_partForm_eventuallyEq h ε x (mem_extChartAt_target x))

theorem IsSmoothForm.dbarForm (h : IsSmoothForm η) : IsSmoothForm (dbarForm η) :=
  h.partForm 1

theorem IsSmoothForm.delForm (h : IsSmoothForm η) : IsSmoothForm (delForm η) :=
  h.partForm (-1)

/-- Second derivatives on `M`: `P_ε P_δ η + P_δ P_ε η = 0` for smooth `η`. -/
theorem partForm_partForm_add (h : IsSmoothForm η) (ε δ : ℂ) (x : M) :
    partForm ε (partForm δ η) x + partForm δ (partForm ε η) x = 0 := by
  rw [partForm, partForm,
    partDeriv_congr ε (localRep_partForm_eventuallyEq h δ x (mem_extChartAt_target x)),
    partDeriv_congr δ (localRep_partForm_eventuallyEq h ε x (mem_extChartAt_target x))]
  exact partDeriv_partDeriv_add_partDeriv_partDeriv ε δ ((h x).of_le (by simp))

private lemma eq_zero_of_add_self' {V : Type*} [AddCommGroup V] [Module ℂ V] {a : V}
    (h : a + a = 0) : a = 0 := by
  rw [← two_smul ℂ a] at h
  exact (smul_eq_zero.mp h).resolve_left two_ne_zero

/-- `∂̄² = 0` on a complex manifold. -/
theorem dbarForm_dbarForm (h : IsSmoothForm η) : dbarForm (dbarForm η) = 0 := by
  ext1 x
  exact eq_zero_of_add_self' (partForm_partForm_add h 1 1 x)

/-- `∂² = 0` on a complex manifold. -/
theorem delForm_delForm (h : IsSmoothForm η) : delForm (delForm η) = 0 := by
  ext1 x
  exact eq_zero_of_add_self' (partForm_partForm_add h (-1) (-1) x)

/-- `∂∂̄ + ∂̄∂ = 0` on a complex manifold. -/
theorem delForm_dbarForm_add (h : IsSmoothForm η) :
    delForm (dbarForm η) + dbarForm (delForm η) = 0 := by
  ext1 x
  exact partForm_partForm_add h (-1) 1 x

/-- `∂̄` maps forms of type `(p, q)` to forms of type `(p, q + 1)`. -/
theorem isOfType_dbarForm (h : ∀ x, IsOfType p q (η x)) (x : M) :
    IsOfType p (q + 1) (dbarForm η x) :=
  isOfType_dbarDeriv (Eventually.of_forall (IsOfType.localRep h x))

/-- `∂` maps forms of type `(p, q)` to forms of type `(p + 1, q)`. -/
theorem isOfType_delForm (h : ∀ x, IsOfType p q (η x)) (x : M) :
    IsOfType (p + 1) q (delForm η x) :=
  isOfType_delDeriv (Eventually.of_forall (IsOfType.localRep h x))

/-- `∂̄ η̄ = conj (∂ η)` on a complex manifold. -/
theorem dbarForm_conjForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x : M) :
    dbarForm (fun x ↦ conjForm (η x)) x = conjForm (delForm η x) := by
  rw [dbarForm, partForm, localRep_conjForm]
  exact dbarDeriv_conjForm _ _

/-- `∂ η̄ = conj (∂̄ η)` on a complex manifold. -/
theorem delForm_conjForm (η : M → E [⋀^Fin n]→L[ℝ] ℂ) (x : M) :
    delForm (fun x ↦ conjForm (η x)) x = conjForm (dbarForm η x) := by
  rw [delForm, partForm, localRep_conjForm]
  exact delDeriv_conjForm _ _

lemma partForm_add (ε : ℂ) (h₁ : IsSmoothForm η₁) (h₂ : IsSmoothForm η₂) :
    partForm ε (η₁ + η₂) = partForm ε η₁ + partForm ε η₂ := by
  ext1 x
  rw [Pi.add_apply, partForm, partForm, partForm, localRep_add, partDeriv, partDeriv, partDeriv,
    fderiv_add ((h₁ x).differentiableAt (by simp)) ((h₂ x).differentiableAt (by simp)), map_add,
    alternatizeUncurryFin_add]

lemma partForm_smul (ε c : ℂ) (h : IsSmoothForm η) :
    partForm ε (c • η) = c • partForm ε η := by
  ext1 x
  have hd : DifferentiableAt ℝ (localRep η x) (extChartAt 𝓘(ℂ, E) x x) :=
    (h x).differentiableAt (by simp)
  have hf : fderiv ℝ (c • localRep η x) (extChartAt 𝓘(ℂ, E) x x) =
      c • fderiv ℝ (localRep η x) (extChartAt 𝓘(ℂ, E) x x) :=
    fderiv_const_smul hd c
  rw [Pi.smul_apply, partForm, partForm, localRep_smul, partDeriv, partDeriv, hf, partCLM_smul,
    alternatizeUncurryFin_smul]

end Operators

end Hodge
