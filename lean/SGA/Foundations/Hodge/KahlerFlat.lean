/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Kahler
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# The flat Kähler form

For a complex inner product space `E`, the constant `2`-form `ω(v, w) = Im ⟪v, w⟫`
(`Hodge.flatKahler`) is a Kähler form on `E`, viewed as a complex manifold modelled on itself
(`Hodge.isKahlerForm_flatKahler`, `Hodge.isKahlerManifold_self`). In coordinates on `ℂⁿ` it is
`(i/2) Σⱼ dzⱼ ∧ dz̄ⱼ`. This shows that `Hodge.IsKahlerForm` is satisfiable, with the sign
conventions used there (`ω(v, i v) = ‖v‖² > 0`).

Also: `Hodge.localRep_modelSpace`, local representatives on the model space are the forms
themselves.
-/

noncomputable section
open ComplexConjugate ContinuousAlternatingMap
open scoped Manifold ContDiff InnerProductSpace

namespace Hodge
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- `(v, w) ↦ ½ Im ⟪v, w⟫`, as a continuous real bilinear map. -/
def flatAux : E →L[ℝ] E →L[ℝ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun v w ↦ (((⟪v, w⟫_ℂ).im / 2 : ℝ) : ℂ))
      (fun v v' w ↦ by simp [inner_add_left, add_div])
      (fun r v w ↦ by
        rw [← Complex.coe_smul, inner_smul_left, Complex.conj_ofReal, Complex.im_ofReal_mul,
          Complex.real_smul]
        push_cast
        ring)
      (fun v w w' ↦ by simp [inner_add_right, add_div])
      (fun r v w ↦ by
        rw [← Complex.coe_smul, inner_smul_right, Complex.im_ofReal_mul,
          Complex.real_smul]
        push_cast
        ring))
    (1 / 2) (fun v w ↦ by
      simp only [LinearMap.mk₂_apply, Complex.norm_real, Real.norm_eq_abs]
      calc |(⟪v, w⟫_ℂ).im / 2| = |(⟪v, w⟫_ℂ).im| / 2 := by rw [abs_div, abs_two]
        _ ≤ ‖⟪v, w⟫_ℂ‖ / 2 := by gcongr; exact Complex.abs_im_le_norm _
        _ ≤ ‖v‖ * ‖w‖ / 2 := by gcongr; exact norm_inner_le_norm v w
        _ = 1 / 2 * ‖v‖ * ‖w‖ := by ring)

lemma flatAux_apply (v w : E) : flatAux v w = (((⟪v, w⟫_ℂ).im / 2 : ℝ) : ℂ) := rfl

/-- The **flat Kähler form** `ω(v, w) = Im ⟪v, w⟫` of a complex inner product space. -/
def flatKahler : E [⋀^Fin 2]→L[ℝ] ℂ :=
  alternatizeUncurryFin
    ((ContinuousAlternatingMap.ofSubsingletonLIE (𝕜 := ℝ) (E := E) (F := ℂ)
      (0 : Fin 1)).toContinuousLinearEquiv.toContinuousLinearMap ∘L flatAux)

lemma flatKahler_apply (u : Fin 2 → E) : flatKahler u = (((⟪u 0, u 1⟫_ℂ).im : ℝ) : ℂ) := by
  have h : (⟪u 1, u 0⟫_ℂ).im = -(⟪u 0, u 1⟫_ℂ).im := by
    rw [← inner_conj_symm, Complex.conj_im]
  have ht : Fin.tail u 0 = u 1 := rfl
  rw [flatKahler, alternatizeUncurryFin_apply, Fin.sum_univ_two]
  simp [flatAux_apply, Fin.removeNth, ht, h]
  ring

/-- The flat form is of type `(1, 1)`. -/
lemma isOfType_flatKahler : IsOfType 1 1 (flatKahler : E [⋀^Fin 2]→L[ℝ] ℂ) := by
  intro c u
  rw [flatKahler_apply, flatKahler_apply]
  simp only [Pi.smul_apply, inner_smul_left, inner_smul_right]
  rw [← mul_assoc, Complex.mul_conj, Complex.im_ofReal_mul, pow_one, pow_one, Complex.mul_conj]
  push_cast
  ring

/-- The flat form is real. -/
lemma conjForm_flatKahler : conjForm (flatKahler : E [⋀^Fin 2]→L[ℝ] ℂ) = flatKahler := by
  ext u
  rw [conjForm_apply, flatKahler_apply, Complex.conj_ofReal]

/-- The flat form is positive: `ω(v, i v) = ‖v‖²`. -/
lemma flatKahler_apply_I_smul (v : E) :
    flatKahler ![v, Complex.I • v] = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
  rw [flatKahler_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, inner_smul_right, Complex.mul_im,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- On the model space, local representatives are the forms themselves. -/
lemma localRep_modelSpace {n : ℕ} (η : E → E [⋀^Fin n]→L[ℝ] ℂ) (x : E) :
    localRep η x = η := by
  ext1 y
  have h : tangentCoordChange 𝓘(ℂ, E) x y y = ContinuousLinearMap.id ℂ E := by
    rw [tangentCoordChange_def]
    simp [chartAt_self_eq]
  simp only [localRep, extChartAt_model_space_eq_id, PartialEquiv.refl_symm,
    PartialEquiv.refl_coe, id_eq, h]
  ext v
  simp

/-- A complex inner product space, as a complex manifold modelled on itself, is Kähler: the
constant form `ω(v, w) = Im ⟪v, w⟫` is a Kähler form. -/
theorem isKahlerForm_flatKahler :
    IsKahlerForm (M := E) (fun _ ↦ (flatKahler : E [⋀^Fin 2]→L[ℝ] ℂ)) where
  isSmoothForm x := by
    rw [localRep_modelSpace]
    exact contDiffAt_const
  isOfType _ := isOfType_flatKahler
  conjForm_eq _ := conjForm_flatKahler
  pos x v hv := by
    rw [flatKahler_apply_I_smul, Complex.ofReal_re]
    positivity
  extDerivForm_eq_zero := by
    ext1 x
    rw [extDerivForm, localRep_modelSpace]
    simp [extDeriv, ← alternatizeUncurryFinCLM_apply]

theorem isKahlerManifold_self : IsKahlerManifold E E :=
  ⟨_, isKahlerForm_flatKahler⟩

end Hodge
