/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Wedge
import Mathlib.LinearAlgebra.ExteriorAlgebra.OfAlternating
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Wedge products of `1`-forms, and the exterior algebra of `1`-forms

Let `E` be a real normed space and `𝕜` a normed field which is a normed `ℝ`-algebra. For
`1`-forms `φ₀, …, φ_{k-1} : E →L[ℝ] 𝕜`:

* `ContinuousAlternatingMap.detForm φ = φ₀ ⋏ ⋯ ⋏ φ_{k-1}`, defined as the alternatization of
  `v ↦ ∏ᵢ φᵢ (vᵢ)`; its value is the determinant `det (φⱼ (vᵢ))`
  (`ContinuousAlternatingMap.detForm_apply_eq_det`);
* `ContinuousAlternatingMap.detForm_append`: `detForm (φ ++ ψ) = detForm φ ⋏ detForm ψ`;
* `ContinuousAlternatingMap.detFormAlt`: `detForm` is `𝕜`-multilinear and alternating in `φ`;
* `ContinuousAlternatingMap.toForms`: the induced `𝕜`-linear map from the exterior algebra
  `ExteriorAlgebra 𝕜 (E →L[ℝ] 𝕜)` to forms of all degrees, `ιMulti φ ↦ detForm φ` in degree `k`;
  it is multiplicative on homogeneous elements (`ContinuousAlternatingMap.toForms_mul`). This lets
  one compute wedge products of forms in mathlib's exterior algebra.

Reference: N. Bourbaki, *Algebra I*, Ch. III, §7 and §11.
-/

noncomputable section

open Equiv Function ContinuousMultilinearMap

namespace ContinuousAlternatingMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜] {k a b : ℕ}

/-- The multilinear map `v ↦ ∏ᵢ φᵢ (vᵢ)`. -/
def prodFin (φ : Fin k → E →L[ℝ] 𝕜) : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ E) 𝕜 :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin k) 𝕜).compContinuousLinearMap φ

@[simp]
lemma prodFin_apply (φ : Fin k → E →L[ℝ] 𝕜) (v : Fin k → E) :
    prodFin φ v = ∏ i, φ i (v i) := by
  simp [prodFin]

/-- The wedge product `φ₀ ⋏ ⋯ ⋏ φ_{k-1}` of `k` one-forms: the alternatization of
`v ↦ ∏ᵢ φᵢ (vᵢ)`. -/
def detForm (φ : Fin k → E →L[ℝ] 𝕜) : E [⋀^Fin k]→L[ℝ] 𝕜 :=
  alternatization (prodFin φ)

lemma detForm_apply (φ : Fin k → E →L[ℝ] 𝕜) (v : Fin k → E) :
    detForm φ v = ∑ σ : Perm (Fin k), Perm.sign σ • ∏ i, φ i (v (σ i)) := by
  simp [detForm, alternatization_apply_apply]

/-- The value of `φ₀ ⋏ ⋯ ⋏ φ_{k-1}` on `v` is the determinant `det (φⱼ (vᵢ))`. -/
lemma detForm_apply_eq_det (φ : Fin k → E →L[ℝ] 𝕜) (v : Fin k → E) :
    detForm φ v = (Matrix.of fun i j ↦ φ j (v i)).det := by
  rw [detForm_apply, Matrix.det_apply]
  rfl

lemma prodFin_append (φ : Fin a → E →L[ℝ] 𝕜) (ψ : Fin b → E →L[ℝ] 𝕜) :
    prodFin (Fin.append φ ψ) = mulFin (prodFin φ) (prodFin ψ) := by
  refine ext_fin fun v ↦ ?_
  simp [Fin.prod_univ_add]

/-- `detForm (φ ++ ψ) = detForm φ ⋏ detForm ψ`. -/
theorem detForm_append (φ : Fin a → E →L[ℝ] 𝕜) (ψ : Fin b → E →L[ℝ] 𝕜) :
    detForm (Fin.append φ ψ) = detForm φ ⋏ detForm ψ := by
  rw [wedge_def, detForm, detForm, detForm, alternatization_mulFin_alternatization_left,
    alternatization_mulFin_alternatization_right, prodFin_append, ← Nat.cast_smul_eq_nsmul ℝ,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  have := a.factorial_pos
  have := b.factorial_pos
  rw [show ((a.factorial * b.factorial : ℕ) : ℝ)⁻¹ * a.factorial * b.factorial = 1 by
    push_cast; field_simp, one_smul]

/-- Permuting the factors multiplies `detForm` by the sign. -/
theorem detForm_comp_perm (φ : Fin k → E →L[ℝ] 𝕜) (σ : Perm (Fin k)) :
    detForm (φ ∘ σ) = Perm.sign σ • detForm φ := by
  have h : prodFin (φ ∘ σ) = (prodFin φ).domDomCongr σ.symm := by
    refine ext_fin fun v ↦ ?_
    simp only [prodFin_apply, comp_apply]
    exact Fintype.prod_equiv σ _ _ fun i ↦ by simp
  rw [detForm, h, alternatization_domDomCongr_perm, Perm.sign_symm, detForm]

/-- `detForm φ = 0` if two factors coincide. -/
theorem detForm_eq_zero_of_eq (φ : Fin k → E →L[ℝ] 𝕜) {i j : Fin k} (hij : i ≠ j)
    (h : φ i = φ j) : detForm φ = 0 := by
  have h1 : φ ∘ Equiv.swap i j = φ := by
    ext1 l
    simp only [comp_apply]
    rcases eq_or_ne l i with rfl | hli
    · rw [Equiv.swap_apply_left, h]
    · rcases eq_or_ne l j with rfl | hlj
      · rw [Equiv.swap_apply_right, h]
      · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]
  have h2 := detForm_comp_perm φ (Equiv.swap i j)
  rw [h1, Perm.sign_swap hij, Units.neg_smul, one_smul] at h2
  have h3 : (2 : ℝ) • detForm φ = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h2]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

private lemma prod_update_apply [DecidableEq (Fin k)] (φ : Fin k → E →L[ℝ] 𝕜) (i : Fin k)
    (χ : E →L[ℝ] 𝕜) (w : Fin k → E) :
    ∏ j, (update φ i χ j) (w j) = (MultilinearMap.mkPiAlgebra 𝕜 (Fin k) 𝕜)
      (update (fun j ↦ φ j (w j)) i (χ (w i))) := by
  rw [MultilinearMap.mkPiAlgebra_apply]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rcases eq_or_ne j i with rfl | hji
  · simp
  · simp [hji]

variable (E 𝕜 k) in
/-- `detForm` as a `𝕜`-multilinear alternating map of the `1`-forms. -/
def detFormAlt : (E →L[ℝ] 𝕜) [⋀^Fin k]→ₗ[𝕜] (E [⋀^Fin k]→L[ℝ] 𝕜) where
  toFun := detForm
  map_update_add' φ i ψ ψ' := by
    ext v
    simp only [detForm_apply, ContinuousAlternatingMap.add_apply, ← Finset.sum_add_distrib,
      ← smul_add]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    congr 1
    rw [prod_update_apply, prod_update_apply, prod_update_apply, _root_.add_apply,
      MultilinearMap.map_update_add]
  map_update_smul' φ i c ψ := by
    ext v
    simp only [detForm_apply, ContinuousAlternatingMap.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [prod_update_apply, prod_update_apply, _root_.smul_apply,
      MultilinearMap.map_update_smul, smul_comm]
  map_eq_zero_of_eq' φ i j h hij := detForm_eq_zero_of_eq φ hij h

@[simp]
lemma detFormAlt_apply (φ : Fin k → E →L[ℝ] 𝕜) : detFormAlt E 𝕜 k φ = detForm φ :=
  rfl

/-! ### The exterior algebra of `1`-forms -/

variable (E 𝕜) in
/-- The `𝕜`-linear map from the exterior algebra of `1`-forms to forms of all degrees, sending
`φ₀ ∧ ⋯ ∧ φ_{k-1}` to `detForm φ` in degree `k`. -/
def toForms : ExteriorAlgebra 𝕜 (E →L[ℝ] 𝕜) →ₗ[𝕜] ((l : ℕ) → E [⋀^Fin l]→L[ℝ] 𝕜) :=
  ExteriorAlgebra.liftAlternating fun l ↦
    (LinearMap.single 𝕜 (fun l ↦ E [⋀^Fin l]→L[ℝ] 𝕜) l).compAlternatingMap (detFormAlt E 𝕜 l)

lemma toForms_ιMulti (φ : Fin k → E →L[ℝ] 𝕜) :
    toForms E 𝕜 (ExteriorAlgebra.ιMulti 𝕜 k φ) = Pi.single k (detForm φ) := by
  rw [toForms, ExteriorAlgebra.liftAlternating_apply_ιMulti]
  rfl

@[simp]
lemma toForms_ιMulti_self (φ : Fin k → E →L[ℝ] 𝕜) :
    toForms E 𝕜 (ExteriorAlgebra.ιMulti 𝕜 k φ) k = detForm φ := by
  rw [toForms_ιMulti, Pi.single_eq_same]

/-- `toForms` vanishes outside the degree of a homogeneous element. -/
lemma toForms_of_mem_of_ne {x : ExteriorAlgebra 𝕜 (E →L[ℝ] 𝕜)}
    (hx : x ∈ ⋀[𝕜]^a (E →L[ℝ] 𝕜)) {l : ℕ} (hl : l ≠ a) : toForms E 𝕜 x l = 0 := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨φ, rfl⟩ := hy
    rw [toForms_ιMulti, Pi.single_eq_of_ne hl]
  | zero => simp
  | add y z _ _ hy hz => simp [hy, hz]
  | smul c y _ hy => simp [hy]

/-- **`toForms` is multiplicative on homogeneous elements.** -/
theorem toForms_mul {x y : ExteriorAlgebra 𝕜 (E →L[ℝ] 𝕜)} (hx : x ∈ ⋀[𝕜]^a (E →L[ℝ] 𝕜))
    (hy : y ∈ ⋀[𝕜]^b (E →L[ℝ] 𝕜)) :
    toForms E 𝕜 (x * y) (a + b) = toForms E 𝕜 x a ⋏ toForms E 𝕜 y b := by
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hx hy
  induction hx using Submodule.span_induction with
  | mem x' hx' =>
    obtain ⟨φ, rfl⟩ := hx'
    induction hy using Submodule.span_induction with
    | mem y' hy' =>
      obtain ⟨ψ, rfl⟩ := hy'
      rw [ExteriorAlgebra.ιMulti_mul_ιMulti, toForms_ιMulti_self, toForms_ιMulti_self,
        toForms_ιMulti_self, detForm_append]
    | zero => simp
    | add y z _ _ hy hz => simp [mul_add, hy, hz]
    | smul c y _ hy => simp [hy]
  | zero => simp
  | add x z _ _ hx hz => simp [add_mul, hx, hz]
  | smul c x _ hx => simp [hx]

lemma toForms_ι (φ : E →L[ℝ] 𝕜) :
    toForms E 𝕜 (ExteriorAlgebra.ι 𝕜 φ) 1 = detForm ![φ] := by
  have : ExteriorAlgebra.ι 𝕜 φ = ExteriorAlgebra.ιMulti 𝕜 1 ![φ] := by
    simp [ExteriorAlgebra.ιMulti_apply]
  rw [this, toForms_ιMulti_self]

end ContinuousAlternatingMap
