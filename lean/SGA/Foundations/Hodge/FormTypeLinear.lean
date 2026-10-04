/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Dbar
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Forms of type `(p, 0)` are complex multilinear

A `ℂ`-valued real alternating `p`-form `α` on a complex vector space `E` is of type `(p, 0)`
(`Hodge.IsOfType p 0 α`) if `α (c v₁, …, c vₚ) = cᵖ α (v₁, …, vₚ)` for all `c ∈ ℂ`, i.e. the
scaling is by all arguments at once. This file proves that such a form is complex linear in each
argument separately (`Hodge.IsOfType.map_update_smul`), hence is a complex alternating map
(`Hodge.IsOfType.toAlternatingMap`).

The proof uses "types" with integer exponents: `Hodge.IsOfZType a b α` means
`α (c • v) = cᵃ c̄ᵇ α v` for `c ≠ 0` (`a, b ∈ ℤ`). If `b < 0` then `α = 0`
(`Hodge.IsOfZType.eq_zero_of_neg`), by induction on the degree: split the first argument of `α`
into its complex linear and antilinear parts (`Hodge.partCLM`), which have types `(a - 1, b)` and
`(a, b - 1)` in the remaining arguments; in degree `0`, `cᵃ c̄ᵇ = 1` for all `c ≠ 0` forces
`(a, b) = 0`. For `α` of type `(p, 0)` the antilinear part of the first argument has type
`(p, -1)`, so it vanishes.

Reference: D. Huybrechts, *Complex geometry*, §1.2 (the decomposition `Λᵏ = ⊕ Λ^{p,q}`).
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k p : ℕ}

/-- `α` has "type `(a, b)`" with integer exponents: `α (c • v) = cᵃ c̄ᵇ α v` for every `c ≠ 0`. -/
def IsOfZType (a b : ℤ) (α : E [⋀^Fin k]→L[ℝ] ℂ) : Prop :=
  ∀ c : ℂ, c ≠ 0 → ∀ v : Fin k → E, α (c • v) = c ^ a * conj c ^ b * α v

lemma IsOfType.isOfZType {q : ℕ} {α : E [⋀^Fin k]→L[ℝ] ℂ} (h : IsOfType p q α) :
    IsOfZType p q α := by
  intro c _ v
  rw [h c v, zpow_natCast, zpow_natCast]

/-- For every `a ≥ 1` there is `c ≠ 0` with `cᵃ ≠ c̄ᵃ`: `c = exp (π i / 2a)`, with `cᵃ = i`. -/
lemma exists_pow_ne_conj_pow {a : ℕ} (ha : 0 < a) : ∃ c : ℂ, c ≠ 0 ∧ c ^ a ≠ conj c ^ a := by
  refine ⟨Complex.exp (Real.pi / (2 * a) * Complex.I), Complex.exp_ne_zero _, ?_⟩
  have h1 : Complex.exp (Real.pi / (2 * a) * Complex.I) ^ a = Complex.I := by
    rw [← Complex.exp_nat_mul]
    have : (a : ℂ) * (Real.pi / (2 * a) * Complex.I) = (Real.pi / 2 : ℝ) * Complex.I := by
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
      push_cast
      field_simp
    rw [this, Complex.exp_mul_I]
    simp
  rw [← map_pow, h1, Complex.conj_I]
  intro h
  have := congrArg Complex.im h
  simp at this
  norm_num at this

/-- In degree `0`, a nonzero constant has type `(a, b)` only for `(a, b) = (0, 0)`; we only need:
`b < 0` forces it to vanish. -/
private lemma eq_zero_of_mul_eq {a b : ℤ} (hb : b < 0) {z : ℂ}
    (h : ∀ c : ℂ, c ≠ 0 → z = c ^ a * conj c ^ b * z) : z = 0 := by
  by_cases hab : a + b = 0
  · obtain ⟨c, hc0, hc⟩ := exists_pow_ne_conj_pow (a := a.toNat) (by omega)
    have hcc : conj c ≠ 0 := (map_ne_zero _).2 hc0
    have ha : a = (a.toNat : ℤ) := by omega
    have hb' : b = -(a.toNat : ℤ) := by omega
    have h1 := h c hc0
    rw [ha, hb', zpow_natCast, zpow_neg, zpow_natCast] at h1
    by_contra hz
    have : c ^ a.toNat * (conj c ^ a.toNat)⁻¹ = 1 := by
      have := mul_right_cancel₀ hz (h1.symm.trans (one_mul z).symm)
      exact this
    rw [mul_inv_eq_one₀ (pow_ne_zero _ hcc)] at this
    exact hc this
  · have h1 := h 2 two_ne_zero
    have h2 : conj (2 : ℂ) = 2 := map_ofNat _ 2
    rw [h2, ← zpow_add₀ two_ne_zero] at h1
    have h3 : (2 : ℂ) ^ (a + b) ≠ 1 := by
      intro h4
      have h5 : (((2 : ℝ) ^ (a + b) : ℝ) : ℂ) = 1 := by
        rw [Complex.ofReal_zpow, Complex.ofReal_ofNat]
        exact h4
      have : ((2 : ℝ) ^ (a + b) : ℝ) = 1 := by exact_mod_cast h5
      exact hab ((zpow_eq_one_iff_right₀ (by norm_num) (by norm_num)).1 this)
    by_contra hz
    exact h3 (mul_right_cancel₀ hz (h1.symm.trans (one_mul z).symm))

private lemma smul_vecCons (c : ℂ) (x : E) (w : Fin k → E) :
    c • (Matrix.vecCons x w : Fin (k + 1) → E) = Matrix.vecCons (c • x) (c • w) := by
  ext i
  cases i using Fin.cases <;> rfl

/-- The linear and antilinear parts of the first argument of a form of type `(a, b)`. -/
private lemma isOfZType_partCLM {a b : ℤ} {α : E [⋀^Fin (k + 1)]→L[ℝ] ℂ} (h : IsOfZType a b α)
    (ε : ℂ) (c : ℂ) (hc : c ≠ 0) (x : E) (w : Fin k → E) :
    partCLM E _ ε α.curryLeft (c • x) (c • w) = c ^ a * conj c ^ b *
      partCLM E _ ε α.curryLeft x w := by
  have key : ∀ y : E, α.curryLeft (c • y) (c • w) = c ^ a * conj c ^ b * α.curryLeft y w := by
    intro y
    simp only [curryLeft_apply_apply]
    rw [← smul_vecCons, h c hc]
  simp only [partCLM_apply, ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.add_apply]
  rw [smul_comm Complex.I c x, key, key, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- **A form of type `(a, b)` with `b < 0` vanishes.** -/
theorem IsOfZType.eq_zero_of_neg {a b : ℤ} {α : E [⋀^Fin k]→L[ℝ] ℂ} (h : IsOfZType a b α)
    (hb : b < 0) : α = 0 := by
  induction k generalizing a b with
  | zero =>
    ext v
    refine eq_zero_of_mul_eq (a := a) hb fun c hc ↦ ?_
    rw [← h c hc v]
    congr 1
    exact Subsingleton.elim _ _
  | succ k ih =>
    have hL : ∀ x : E, α.curryLeft x = 0 := by
      intro x
      have h1 : partCLM E _ 1 α.curryLeft x = 0 := by
        refine ih (a := a) (b := b - 1) (fun c hc w ↦ ?_) (by omega)
        have := isOfZType_partCLM h 1 c hc x w
        rw [partCLM_one_apply_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at this
        have hcc : conj c ≠ 0 := (map_ne_zero _).2 hc
        rw [zpow_sub_one₀ hcc]
        field_simp
        linear_combination this
      have h2 : partCLM E _ (-1) α.curryLeft x = 0 := by
        refine ih (a := a - 1) (b := b) (fun c hc w ↦ ?_) hb
        have := isOfZType_partCLM h (-1) c hc x w
        rw [partCLM_neg_one_apply_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at this
        rw [zpow_sub_one₀ hc]
        field_simp
        linear_combination this
      have := congrArg (· x) (partCLM_one_add_partCLM_neg_one α.curryLeft)
      simp only [_root_.add_apply] at this
      rw [← this, h1, h2, add_zero]
    ext v
    rw [← Fin.cons_self_tail v]
    exact congrArg (· (Fin.tail v)) (hL (v 0))

/-- A form of type `(k + 1, 0)` is complex linear in its first argument. -/
theorem IsOfType.map_vecCons_smul {α : E [⋀^Fin (k + 1)]→L[ℝ] ℂ} (h : IsOfType (k + 1) 0 α)
    (c : ℂ) (x : E) (w : Fin k → E) :
    α (Matrix.vecCons (c • x) w) = c * α (Matrix.vecCons x w) := by
  have h1 : partCLM E _ 1 α.curryLeft = 0 := by
    ext1 x
    refine IsOfZType.eq_zero_of_neg (a := k + 1) (b := -1) (fun c hc w ↦ ?_) (by omega)
    have := isOfZType_partCLM h.isOfZType 1 c hc x w
    rw [partCLM_one_apply_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul] at this
    have hcc : conj c ≠ 0 := (map_ne_zero _).2 hc
    rw [show ((0 : ℕ) : ℤ) = 0 from rfl, zpow_zero] at this
    push_cast at this ⊢
    rw [zpow_neg_one]
    field_simp
    linear_combination this
  have hL : α.curryLeft = partCLM E _ (-1) α.curryLeft := by
    have := partCLM_one_add_partCLM_neg_one α.curryLeft
    rw [h1, zero_add] at this
    exact this.symm
  calc α (Matrix.vecCons (c • x) w) = α.curryLeft (c • x) w := rfl
    _ = partCLM E _ (-1) α.curryLeft (c • x) w := congrArg (fun L ↦ L (c • x) w) hL
    _ = c * partCLM E _ (-1) α.curryLeft x w := by
      rw [partCLM_neg_one_apply_smul, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    _ = c * α (Matrix.vecCons x w) := by
      rw [← hL]
      rfl

/-- **A form of type `(p, 0)` is complex linear in each argument.** -/
theorem IsOfType.map_update_smul {α : E [⋀^Fin p]→L[ℝ] ℂ} (h : IsOfType p 0 α)
    (v : Fin p → E) (i : Fin p) (c : ℂ) (x : E) :
    α (Function.update v i (c • x)) = c * α (Function.update v i x) := by
  obtain _ | k := p
  · exact i.elim0
  have h0 : ∀ (w : Fin (k + 1) → E) (y : E),
      α (Function.update w 0 (c • y)) = c * α (Function.update w 0 y) := by
    intro w y
    rw [← Fin.cons_self_tail w, Fin.update_cons_zero, Fin.update_cons_zero]
    exact h.map_vecCons_smul c y (Fin.tail w)
  by_cases hi : i = 0
  · subst hi
    exact h0 v x
  · have hs : ∀ y : E, Function.update v i y ∘ Equiv.swap 0 i =
        Function.update (v ∘ Equiv.swap 0 i) 0 y := by
      intro y
      ext j
      simp only [Function.comp_apply, Function.update_apply]
      by_cases hj : j = 0
      · subst hj
        simp
      · by_cases hj' : j = i
        · subst hj'
          simp [hj, Ne.symm hj, Equiv.swap_apply_right]
        · simp [hj, hj', Equiv.swap_apply_of_ne_of_ne hj hj']
    have e : ∀ y : E, α (Function.update v i y) =
        -α (Function.update (v ∘ Equiv.swap 0 i) 0 y) := by
      intro y
      rw [← hs y]
      exact (α.toAlternatingMap.map_swap (Function.update v i y) (Ne.symm hi)).symm ▸ by
        rw [neg_neg]
        rfl
    rw [e, e, h0, mul_neg]

/-- A form of type `(p, 0)`, as a complex alternating map. -/
def IsOfType.toAlternatingMap {α : E [⋀^Fin p]→L[ℝ] ℂ} (h : IsOfType p 0 α) :
    E [⋀^Fin p]→ₗ[ℂ] ℂ where
  toFun := α
  map_update_add' v i x y := α.map_update_add v i x y
  map_update_smul' v i c x := by
    rw [smul_eq_mul]
    convert h.map_update_smul v i c x
  map_eq_zero_of_eq' v i j hv hij := α.map_eq_zero_of_eq v hv hij

@[simp]
lemma IsOfType.toAlternatingMap_apply {α : E [⋀^Fin p]→L[ℝ] ℂ} (h : IsOfType p 0 α)
    (v : Fin p → E) : h.toAlternatingMap v = α v :=
  rfl

end Hodge
