/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Calculus.DifferentialForm.Basic
import Mathlib.Analysis.Complex.Basic

/-!
# Forms of type `(p, q)` on a complex vector space

Let `E` be a complex normed space. A *complex-valued `k`-form* on `E` is a real alternating
`k`-linear map `E [⋀^Fin k]→L[ℝ] ℂ` (`E` viewed as a real vector space). Such a form `α` is
**of type `(p, q)`** (`Hodge.IsOfType p q α`) if

  `α (c v₁, …, c vₖ) = cᵖ c̄ᵠ α (v₁, …, vₖ)` for every `c ∈ ℂ`.

For `α = φ₁ ∧ ⋯ ∧ φₚ ∧ ψ₁ ∧ ⋯ ∧ ψ_q` with `φᵢ` complex linear and `ψⱼ` complex antilinear this
holds, and the forms of type `(p, q)` with `p + q = k` are exactly the classical `Λ^{p,q}` (the
characters `c ↦ cᵖ c̄ᵠ`, `p + q = k`, of `ℂ^×` are distinct). This basis-free definition is the
one used throughout `Foundations/Hodge`. A nonzero form of type `(p, q)` has degree `p + q`
(`Hodge.IsOfType.eq_zero_of_add_ne`).

Main definitions:
* `Hodge.IsOfType p q α`, and the submodule `Hodge.typeSubmodule E k p q`;
* `Hodge.conjForm α = ᾱ`, the complex conjugate of a form, which exchanges the types `(p, q)` and
  `(q, p)` (`Hodge.IsOfType.conjForm`).

Reference: D. Huybrechts, *Complex geometry*, §1.2; R. O. Wells, *Differential analysis on complex
manifolds*, Ch. I.3.
-/

noncomputable section

open ComplexConjugate

namespace Hodge

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F]
  [NormedSpace ℂ F] {k p q : ℕ}

/-- A `ℂ`-valued real alternating `k`-form `α` on a complex vector space `E` is **of type
`(p, q)`** if `α (c v₁, …, c vₖ) = cᵖ c̄ᵠ α (v₁, …, vₖ)` for all `c ∈ ℂ` and `vᵢ ∈ E`. -/
def IsOfType (p q : ℕ) (α : E [⋀^Fin k]→L[ℝ] ℂ) : Prop :=
  ∀ (c : ℂ) (v : Fin k → E), α (c • v) = c ^ p * conj c ^ q * α v

lemma isOfType_zero (p q : ℕ) : IsOfType p q (0 : E [⋀^Fin k]→L[ℝ] ℂ) := by
  intro c v
  simp

namespace IsOfType

variable {α β : E [⋀^Fin k]→L[ℝ] ℂ}

lemma add (hα : IsOfType p q α) (hβ : IsOfType p q β) : IsOfType p q (α + β) := by
  intro c v
  simp [hα c v, hβ c v, mul_add]

lemma smul (a : ℂ) (hα : IsOfType p q α) : IsOfType p q (a • α) := by
  intro c v
  simp only [ContinuousAlternatingMap.smul_apply, hα c v, smul_eq_mul]
  ring

lemma neg (hα : IsOfType p q α) : IsOfType p q (-α) := by
  intro c v
  simp [hα c v]

lemma sub (hα : IsOfType p q α) (hβ : IsOfType p q β) : IsOfType p q (α - β) := by
  intro c v
  simp [hα c v, hβ c v, mul_sub]

lemma sum {ι : Type*} (s : Finset ι) {α : ι → E [⋀^Fin k]→L[ℝ] ℂ}
    (h : ∀ i ∈ s, IsOfType p q (α i)) : IsOfType p q (∑ i ∈ s, α i) := by
  intro c v
  simp only [ContinuousAlternatingMap.sum_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i hi ↦ h i hi c v

/-- The pullback of a form of type `(p, q)` by a complex linear map is of type `(p, q)`. -/
lemma compContinuousLinearMap (hα : IsOfType p q α) (g : F →L[ℂ] E) :
    IsOfType p q (α.compContinuousLinearMap (g.restrictScalars ℝ)) := by
  intro c v
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  rw [← hα c]
  congr 1
  ext i
  simp

/-- A nonzero form of type `(p, q)` has degree `p + q`. -/
lemma eq_zero_of_add_ne (hα : IsOfType p q α) (h : p + q ≠ k) : α = 0 := by
  ext v
  have h1 := hα 2 v
  have h2 : α ((2 : ℂ) • v) = (2 : ℂ) ^ k * α v := by
    have : ((2 : ℂ) • v) = fun i ↦ (2 : ℝ) • v i := by
      ext i
      rw [Pi.smul_apply, ← Complex.coe_smul]
      norm_num
    rw [this, ContinuousAlternatingMap.map_smul_univ (f := α) (fun _ ↦ (2 : ℝ)) v]
    simp [Finset.prod_const, Complex.real_smul]
  rw [h2] at h1
  have hconj : conj (2 : ℂ) = 2 := map_ofNat (starRingEnd ℂ) 2
  rw [hconj, ← pow_add] at h1
  have hne : (2 : ℂ) ^ k ≠ 2 ^ (p + q) := by
    intro he
    have : (2 : ℝ) ^ k = 2 ^ (p + q) := by exact_mod_cast he
    exact h ((pow_right_injective₀ (by norm_num) (by norm_num) this).symm)
  have : ((2 : ℂ) ^ k - 2 ^ (p + q)) * α v = 0 := by rw [sub_mul, h1, sub_self]
  simpa [sub_ne_zero.mpr hne] using this

end IsOfType

variable (E) in
/-- The complex subspace of `ℂ`-valued real alternating `k`-forms of type `(p, q)`. -/
def typeSubmodule (k p q : ℕ) : Submodule ℂ (E [⋀^Fin k]→L[ℝ] ℂ) where
  carrier := {α | IsOfType p q α}
  add_mem' := IsOfType.add
  zero_mem' := isOfType_zero p q
  smul_mem' c _ h := h.smul c

@[simp]
lemma mem_typeSubmodule {α : E [⋀^Fin k]→L[ℝ] ℂ} :
    α ∈ typeSubmodule E k p q ↔ IsOfType p q α :=
  Iff.rfl

/-- The complex conjugate `ᾱ` of a `ℂ`-valued form, `ᾱ (v) = conj (α v)`. -/
def conjForm (α : E [⋀^Fin k]→L[ℝ] ℂ) : E [⋀^Fin k]→L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.compContinuousAlternatingMap α

/-- Complex conjugation of forms, as a real continuous linear map. -/
def conjFormCLM (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] (k : ℕ) :
    (E [⋀^Fin k]→L[ℝ] ℂ) →L[ℝ] (E [⋀^Fin k]→L[ℝ] ℂ) :=
  ContinuousLinearMap.compContinuousAlternatingMapCLM ℝ E ℂ ℂ (Fin k)
    Complex.conjCLE.toContinuousLinearMap

@[simp]
lemma conjForm_apply (α : E [⋀^Fin k]→L[ℝ] ℂ) (v : Fin k → E) :
    conjForm α v = conj (α v) :=
  rfl

@[simp]
lemma conjFormCLM_apply (α : E [⋀^Fin k]→L[ℝ] ℂ) : conjFormCLM E k α = conjForm α := by
  ext v
  simp [conjFormCLM]

@[simp]
lemma conjForm_conjForm (α : E [⋀^Fin k]→L[ℝ] ℂ) : conjForm (conjForm α) = α := by
  ext v
  simp

@[simp]
lemma conjForm_add (α β : E [⋀^Fin k]→L[ℝ] ℂ) : conjForm (α + β) = conjForm α + conjForm β := by
  ext v
  simp

@[simp]
lemma conjForm_smul (c : ℂ) (α : E [⋀^Fin k]→L[ℝ] ℂ) :
    conjForm (c • α) = conj c • conjForm α := by
  ext v
  simp

@[simp]
lemma conjForm_zero : conjForm (0 : E [⋀^Fin k]→L[ℝ] ℂ) = 0 := by
  ext v
  simp

@[simp]
lemma conjForm_neg (α : E [⋀^Fin k]→L[ℝ] ℂ) : conjForm (-α) = -conjForm α := by
  ext v
  simp

@[simp]
lemma conjForm_sub (α β : E [⋀^Fin k]→L[ℝ] ℂ) : conjForm (α - β) = conjForm α - conjForm β := by
  ext v
  simp

lemma conjForm_injective : Function.Injective (conjForm : (E [⋀^Fin k]→L[ℝ] ℂ) → _) :=
  Function.LeftInverse.injective conjForm_conjForm

lemma conjForm_compContinuousLinearMap (α : E [⋀^Fin k]→L[ℝ] ℂ) (g : F →L[ℝ] E) :
    conjForm (α.compContinuousLinearMap g) = (conjForm α).compContinuousLinearMap g :=
  rfl

/-- Conjugation exchanges the types `(p, q)` and `(q, p)`. -/
lemma IsOfType.conjForm {α : E [⋀^Fin k]→L[ℝ] ℂ} (hα : IsOfType p q α) :
    IsOfType q p (conjForm α) := by
  intro c v
  simp only [conjForm_apply, hα c v, map_mul, map_pow, Complex.conj_conj]
  ring

lemma isOfType_conjForm_iff {α : E [⋀^Fin k]→L[ℝ] ℂ} :
    IsOfType q p (conjForm α) ↔ IsOfType p q α :=
  ⟨fun h ↦ by simpa using h.conjForm, fun h ↦ h.conjForm⟩

end Hodge
