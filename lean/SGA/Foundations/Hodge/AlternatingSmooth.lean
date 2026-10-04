/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Normed.Module.Multilinear.Curry
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial

/-!
# Smoothness of pullbacks of alternating maps

mathlib proves that `(ρ, g) ↦ ρ.compContinuousLinearMap g` (the pullback of an alternating map
`ρ` along a linear map `g`) is differentiable
(`DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap`) but not that it is `Cᵐ`.
This file proves it, through the alternatization of continuous multilinear maps, which is a left
inverse (up to `n!`) of the embedding of alternating maps into multilinear maps:

* `ContinuousMultilinearMap.alternatizationCLM`: `ContinuousMultilinearMap.alternatization` as a
  continuous linear map (bound `n!`);
* `ContinuousMultilinearMap.alternatizationCLM_toContinuousMultilinearMap`: on alternating maps it
  is `n! • id`;
* `ContinuousAlternatingMap.contDiffAt_of_toContinuousMultilinearMap`: a map into alternating maps
  is `Cᵐ` if its composite with the embedding into multilinear maps is;
* `ContDiffAt.continuousAlternatingMapCompContinuousLinearMap`:
  `y ↦ (ρ y).compContinuousLinearMap (g y)` is `Cᵐ` where `ρ` and `g` are (the `Cᵐ` analogue of
  mathlib's `DifferentiableAt.continuousAlternatingMapCompContinuousLinearMap`).

All over `ℝ` (the alternatization needs `n!` to be invertible).

Reference: standard multilinear algebra; mathlib's `Mathlib/Topology/Algebra/Module/Alternating`.
-/

noncomputable section

variable {E F G X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup X]
  [NormedSpace ℝ X] {n : ℕ}

namespace ContinuousMultilinearMap

variable (E F n) in
/-- `ContinuousMultilinearMap.alternatization` (`f ↦ Σ_σ sign σ • f ∘ σ`) as a continuous linear
map, of norm at most `n!`. -/
def alternatizationCLM :
    ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F →L[ℝ] E [⋀^Fin n]→L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := ContinuousMultilinearMap.alternatization
      map_add' := map_add _
      map_smul' := by
        intro c f
        ext v
        simp [ContinuousMultilinearMap.alternatization_apply_apply, Finset.smul_sum,
          smul_comm c] }
    (Fintype.card (Equiv.Perm (Fin n)))
    (by
      intro f
      rw [← ContinuousAlternatingMap.norm_toContinuousMultilinearMap]
      simp only [LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousMultilinearMap.alternatization_apply_toContinuousMultilinearMap]
      refine (norm_sum_le _ _).trans ?_
      have : ∀ σ : Equiv.Perm (Fin n), ‖Equiv.Perm.sign σ • f.domDomCongr σ‖ = ‖f‖ := by
        intro σ
        rw [Units.smul_def, ← Int.cast_smul_eq_zsmul ℝ, norm_smul,
          ContinuousMultilinearMap.norm_domDomCongr]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
      simp [this])

@[simp]
lemma alternatizationCLM_apply (f : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F) :
    alternatizationCLM E F n f = f.alternatization :=
  rfl

/-- Alternatizing an alternating map multiplies it by `n!`. -/
lemma alternatizationCLM_toContinuousMultilinearMap (α : E [⋀^Fin n]→L[ℝ] F) :
    alternatizationCLM E F n α.toContinuousMultilinearMap = (n.factorial : ℝ) • α := by
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  have := AlternatingMap.coe_alternatization α.toAlternatingMap
  simp only [Fintype.card_fin] at this
  simp only [alternatizationCLM, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousMultilinearMap.alternatization_apply_toAlternatingMap]
  rw [Nat.cast_smul_eq_nsmul]
  convert this using 1
  ext v
  simp

end ContinuousMultilinearMap

open ContinuousMultilinearMap in
/-- A map into alternating maps is `Cᵐ` as soon as its composite with the embedding into
multilinear maps is. -/
theorem ContinuousAlternatingMap.contDiffAt_of_toContinuousMultilinearMap
    {f : X → E [⋀^Fin n]→L[ℝ] F} {x : X} {m : WithTop ℕ∞}
    (h : ContDiffAt ℝ m (fun y ↦ (f y).toContinuousMultilinearMap) x) :
    ContDiffAt ℝ m f x := by
  have hf : f = fun y ↦ ((n.factorial : ℝ)⁻¹ • alternatizationCLM E F n)
      ((f y).toContinuousMultilinearMap) := by
    ext1 y
    rw [_root_.smul_apply, alternatizationCLM_toContinuousMultilinearMap, smul_smul,
      inv_mul_cancel₀ (by exact_mod_cast n.factorial_ne_zero), one_smul]
  rw [hf]
  exact ((n.factorial : ℝ)⁻¹ • alternatizationCLM E F n).contDiff.contDiffAt.comp x h

/-- Smoothness of the pullback `(ρ y) ∘ (g y, …, g y)` of a family of alternating maps along a
family of linear maps. -/
theorem ContDiffAt.continuousAlternatingMapCompContinuousLinearMap
    {ρ : X → G [⋀^Fin n]→L[ℝ] F} {g : X → E →L[ℝ] G} {x : X} {m : WithTop ℕ∞}
    (hρ : ContDiffAt ℝ m ρ x) (hg : ContDiffAt ℝ m g x) :
    ContDiffAt ℝ m (fun y ↦ (ρ y).compContinuousLinearMap (g y)) x := by
  apply ContinuousAlternatingMap.contDiffAt_of_toContinuousMultilinearMap
  have h1 : ContDiffAt ℝ m (fun y ↦ (ρ y).toContinuousMultilinearMap) x :=
    ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ (E := G) (F := F)
      (ι := Fin n)).contDiff.contDiffAt.comp x hρ :)
  have h2 : ContDiffAt ℝ m (fun y ↦
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear
        ℝ (fun _ : Fin n ↦ E) (fun _ ↦ G) F (fun _ ↦ g y)) x :=
    (ContinuousMultilinearMap.contDiff _).contDiffAt.comp x (contDiffAt_pi.2 fun _ ↦ hg)
  exact h2.clm_apply h1
