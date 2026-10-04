/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Kahler
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Positive `(1, 1)`-forms and unitary frames

A **positive real `(1, 1)`-form** on a complex vector space `E` (`Hodge.IsPositiveForm κ`) is a
`ℂ`-valued real alternating `2`-form `κ` of type `(1, 1)`, with real values (`κ̄ = κ`), such that
`κ (v, i v) > 0` for `v ≠ 0`; the value of a Kähler form at a point is one
(`Hodge.IsKahlerForm.isPositiveForm`). It defines the Hermitian inner product

  `h (v, w) = κ (v, i w) + i κ (v, w)` (`Hodge.hermForm`),

conjugate linear in `v` and linear in `w`. A **unitary frame** is a complex basis `u` of `E` which
is orthonormal for `h`, i.e. `κ (uⱼ, i uₖ) = δⱼₖ` and `κ (uⱼ, uₖ) = 0`; one exists when `E` is
finite-dimensional (`Hodge.IsPositiveForm.exists_unitary_basis`, Gram–Schmidt through mathlib's
`stdOrthonormalBasis`).

Reference: D. Huybrechts, *Complex geometry*, §1.2; C. Voisin, *Hodge theory and complex algebraic
geometry I*, §6.1.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap
open scoped Manifold ContDiff

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A **positive real `(1, 1)`-form**: type `(1, 1)`, real valued, and `Re κ (v, i v) > 0` for
`v ≠ 0`. -/
structure IsPositiveForm (κ : E [⋀^Fin 2]→L[ℝ] ℂ) : Prop where
  isOfType : IsOfType 1 1 κ
  conjForm_eq : conjForm κ = κ
  pos : ∀ v : E, v ≠ 0 → 0 < (κ ![v, Complex.I • v]).re

/-- The value of a Kähler form at a point is a positive real `(1, 1)`-form. -/
theorem IsKahlerForm.isPositiveForm {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
    [IsManifold 𝓘(ℂ, E) ω M] {κ : M → E [⋀^Fin 2]→L[ℝ] ℂ} (h : IsKahlerForm κ) (x : M) :
    IsPositiveForm (κ x) :=
  ⟨h.isOfType x, h.conjForm_eq x, h.pos x⟩

namespace IsPositiveForm

variable {κ : E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsPositiveForm κ)
include hκ

/-- A positive form has real values. -/
lemma conj_apply (v : Fin 2 → E) : conj (κ v) = κ v := by
  have := congrArg (· v) hκ.conjForm_eq
  simpa using this

lemma ofReal_re_apply (v : Fin 2 → E) : ((κ v).re : ℂ) = κ v :=
  Complex.conj_eq_iff_re.1 (hκ.conj_apply v)

omit hκ in
lemma apply_swap (v w : E) : κ ![w, v] = -κ ![v, w] := by
  have h := κ.toAlternatingMap.map_swap ![v, w] (i := 0) (j := 1) (by decide)
  have e : (![v, w] ∘ Equiv.swap 0 1 : Fin 2 → E) = ![w, v] := by
    ext i
    fin_cases i <;> rfl
  rw [e] at h
  exact h

omit hκ in
lemma apply_self (v : E) : κ ![v, v] = 0 :=
  κ.map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl (by decide)

omit hκ in
lemma apply_add_left (v v' w : E) : κ ![v + v', w] = κ ![v, w] + κ ![v', w] :=
  κ.toContinuousMultilinearMap.cons_add ![w] v v'

omit hκ in
lemma apply_smul_left (r : ℝ) (v w : E) : κ ![r • v, w] = r • κ ![v, w] :=
  κ.toContinuousMultilinearMap.cons_smul ![w] r v

omit hκ in
lemma apply_neg_left (v w : E) : κ ![-v, w] = -κ ![v, w] := by
  rw [← neg_one_smul ℝ v, apply_smul_left, neg_one_smul]

lemma apply_I_I (v w : E) : κ ![Complex.I • v, Complex.I • w] = κ ![v, w] := by
  have h := hκ.isOfType Complex.I ![v, w]
  have e : (Complex.I • ![v, w] : Fin 2 → E) = ![Complex.I • v, Complex.I • w] := by
    ext i
    fin_cases i <;> rfl
  rw [e, pow_one, pow_one, Complex.conj_I] at h
  rw [h]
  simp

lemma apply_I_left (v w : E) : κ ![Complex.I • v, w] = -κ ![v, Complex.I • w] := by
  rw [← hκ.apply_I_I (Complex.I • v) w, smul_smul, Complex.I_mul_I, neg_one_smul,
    apply_neg_left]

omit hκ in
lemma apply_complex_smul_left (c : ℂ) (v w : E) :
    κ ![c • v, w] = c.re • κ ![v, w] + c.im • κ ![Complex.I • v, w] := by
  rw [complex_smul_eq_re_smul_add_im_smul c v, apply_add_left, apply_smul_left, apply_smul_left]

end IsPositiveForm

/-- The Hermitian form `h (v, w) = κ (v, i w) + i κ (v, w)` of a `2`-form `κ`. -/
def hermForm (κ : E [⋀^Fin 2]→L[ℝ] ℂ) (v w : E) : ℂ :=
  κ ![v, Complex.I • w] + Complex.I * κ ![v, w]

namespace IsPositiveForm

variable {κ : E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsPositiveForm κ)
include hκ

lemma hermForm_conj_symm (v w : E) : conj (hermForm κ w v) = hermForm κ v w := by
  simp only [hermForm, map_add, map_mul, Complex.conj_I, hκ.conj_apply]
  rw [apply_swap, hκ.apply_I_left, apply_swap v w]
  ring

omit hκ in
lemma hermForm_add_left (v v' w : E) :
    hermForm κ (v + v') w = hermForm κ v w + hermForm κ v' w := by
  simp only [hermForm, apply_add_left]
  ring

lemma hermForm_smul_left (c : ℂ) (v w : E) :
    hermForm κ (c • v) w = conj c * hermForm κ v w := by
  simp only [hermForm, apply_complex_smul_left, hκ.apply_I_I, hκ.apply_I_left, Complex.real_smul]
  have hc : conj c = (c.re : ℂ) - c.im * Complex.I := by
    apply Complex.ext <;> simp
  rw [hc]
  linear_combination (c.im : ℂ) * κ ![v, w] * Complex.I_sq

omit hκ in
lemma hermForm_self (v : E) : hermForm κ v v = κ ![v, Complex.I • v] := by
  simp [hermForm, apply_self]

lemma re_hermForm_self_nonneg (v : E) : 0 ≤ (hermForm κ v v).re := by
  rw [hermForm_self]
  rcases eq_or_ne v 0 with rfl | hv
  · simp [apply_self]
  · exact (hκ.pos v hv).le

lemma hermForm_self_eq_zero {v : E} (h : hermForm κ v v = 0) : v = 0 := by
  by_contra hv
  have := hκ.pos v hv
  rw [← hermForm_self, h] at this
  simp at this

end IsPositiveForm

/-- `E`, as the carrier of the Hermitian inner product defined by `κ`. -/
def HermSpace (_κ : E [⋀^Fin 2]→L[ℝ] ℂ) : Type _ := E

namespace HermSpace

variable (κ : E [⋀^Fin 2]→L[ℝ] ℂ)

instance : AddCommGroup (HermSpace κ) := inferInstanceAs (AddCommGroup E)
instance : Module ℂ (HermSpace κ) := inferInstanceAs (Module ℂ E)

end HermSpace

/-- The inner product space structure (core) on `E` defined by a positive `(1, 1)`-form. -/
@[reducible]
def IsPositiveForm.hermCore {κ : E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsPositiveForm κ) :
    InnerProductSpace.Core ℂ (HermSpace κ) where
  inner v w := hermForm κ v w
  conj_inner_symm v w := hκ.hermForm_conj_symm v w
  re_inner_nonneg v := hκ.re_hermForm_self_nonneg v
  add_left v v' w := IsPositiveForm.hermForm_add_left (E := E) (κ := κ) v v' w
  smul_left v w c := hκ.hermForm_smul_left c v w
  definite _ h := hκ.hermForm_self_eq_zero h

/-- **Unitary frames**: a positive `(1, 1)`-form on a finite-dimensional complex space admits a
complex basis `u` with `κ (uⱼ, i uₖ) = δⱼₖ` and `κ (uⱼ, uₖ) = 0`. -/
theorem IsPositiveForm.exists_unitary_basis [FiniteDimensional ℂ E]
    {κ : E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsPositiveForm κ) :
    ∃ u : Module.Basis (Fin (Module.finrank ℂ E)) ℂ E, ∀ j k,
      κ ![u j, Complex.I • u k] = (if j = k then 1 else 0) ∧ κ ![u j, u k] = 0 := by
  let _ : InnerProductSpace.Core ℂ (HermSpace κ) := hκ.hermCore
  let _ : NormedAddCommGroup (HermSpace κ) := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℂ)
  let _ : InnerProductSpace ℂ (HermSpace κ) :=
    InnerProductSpace.ofCore hκ.hermCore.toCore
  have : FiniteDimensional ℂ (HermSpace κ) := inferInstanceAs (FiniteDimensional ℂ E)
  let b := stdOrthonormalBasis ℂ (HermSpace κ)
  refine ⟨b.toBasis, fun j k ↦ ?_⟩
  have key : hermForm κ (b j) (b k) = if j = k then 1 else 0 := by
    by_cases hjk : j = k
    · subst hjk
      simp only [ite_true]
      have h1 : inner ℂ (b j) (b j) = (1 : ℂ) := by
        rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
        simp
      exact h1
    · simp only [hjk, ite_false]
      exact b.orthonormal.2 hjk
  change κ ![b j, Complex.I • b k] + Complex.I * κ ![b j, b k] = _ at key
  rw [← hκ.ofReal_re_apply ![b j, Complex.I • b k],
    ← hκ.ofReal_re_apply ![b j, b k]] at key
  have hre := congrArg Complex.re key
  have him := congrArg Complex.im key
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    one_mul, zero_add] at hre him
  refine ⟨?_, ?_⟩
  · change κ ![b j, Complex.I • b k] = _
    rw [← hκ.ofReal_re_apply, hre]
    split_ifs <;> simp
  · change κ ![b j, b k] = _
    rw [← hκ.ofReal_re_apply, him]
    split_ifs <;> simp

end Hodge
