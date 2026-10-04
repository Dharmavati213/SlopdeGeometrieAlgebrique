/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.HermitianFrame
import SGA.Foundations.Hodge.DetForm
import SGA.Foundations.Hodge.FormTypeLinear
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Coordinates attached to a complex basis

Let `u` be a basis of the finite-dimensional complex vector space `E`, indexed by `Fin n`.

* `Hodge.coordForm u j = ζⱼ` (the `j`-th complex coordinate, a complex linear `1`-form) and
  `Hodge.conjCoordForm u j = ζ̄ⱼ`, as real `1`-forms with complex values;
* `Hodge.basisFrame u = (u₀, …, u_{n-1}, i u₀, …, i u_{n-1})`, a real basis of `E`;
* `Hodge.IsPositiveForm.eq_sum_of_unitary`: in a unitary frame `u` of a positive `(1, 1)`-form
  `κ` (`Hodge.IsPositiveForm.exists_unitary_basis`), `κ = (i / 2) ∑ⱼ ζⱼ ⋏ ζ̄ⱼ`;
* `Hodge.IsOfType.eq_sum_detForm`: a form `θ` of type `(p, 0)` expands as
  `θ = ∑_{J} θ (u_J) ζ_J` over the subsets `J ⊆ {0, …, n-1}` of cardinality `p`
  (`Set.powersetCard (Fin n) p`), where `u_J`, `ζ_J` list the `uⱼ`, `ζⱼ`, `j ∈ J`, in increasing
  order. The proof goes through mathlib's basis `Module.Basis.exteriorPower` of `⋀ᵖ E` and its
  coordinate forms `exteriorPower.ιMultiDual`;
* `Hodge.conjForm_detForm`: `conj (φ₀ ⋏ ⋯ ⋏ φ_{k-1}) = φ̄₀ ⋏ ⋯ ⋏ φ̄_{k-1}`.

Reference: D. Huybrechts, *Complex geometry*, §1.2.
-/

noncomputable section

open ComplexConjugate ContinuousAlternatingMap

namespace Hodge

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {n : ℕ}
  (u : Module.Basis (Fin n) ℂ E)

/-- The `j`-th complex coordinate `ζⱼ` of the basis `u`, as a real `1`-form. -/
def coordForm (j : Fin n) : E →L[ℝ] ℂ :=
  ((u.coord j).toContinuousLinearMap : E →L[ℂ] ℂ).restrictScalars ℝ

/-- The conjugate `ζ̄ⱼ` of the `j`-th complex coordinate. -/
def conjCoordForm (j : Fin n) : E →L[ℝ] ℂ :=
  Complex.conjCLE.toContinuousLinearMap.comp (coordForm u j)

@[simp]
lemma coordForm_apply (j : Fin n) (v : E) : coordForm u j v = u.coord j v :=
  rfl

@[simp]
lemma conjCoordForm_apply (j : Fin n) (v : E) : conjCoordForm u j v = conj (u.coord j v) :=
  rfl

omit [FiniteDimensional ℂ E] in
lemma coord_basis (j k : Fin n) : u.coord j (u k) = if k = j then 1 else 0 := by
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

omit [FiniteDimensional ℂ E] in
lemma coord_I_basis (j k : Fin n) :
    u.coord j (Complex.I • u k) = if k = j then Complex.I else 0 := by
  rw [map_smul, coord_basis, smul_eq_mul]
  split_ifs <;> simp

/-- The real frame `(u₀, …, u_{n-1}, i u₀, …, i u_{n-1})`. -/
def basisFrame : Fin (n + n) → E :=
  Fin.append u fun j ↦ Complex.I • u j

/-- A complex linear map carries the frame of a basis to the frame of the image basis. -/
lemma basisFrame_map (w : Module.Basis (Fin n) ℂ E) :
    basisFrame w = (((u.equiv w (Equiv.refl _)).toContinuousLinearEquiv : E →L[ℂ] E).restrictScalars
      ℝ) ∘ basisFrame u := by
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp only [basisFrame, Fin.append_left, Function.comp_apply]
    simp
  · simp only [basisFrame, Fin.append_right, Function.comp_apply]
    simp

/-- **A positive `(1, 1)`-form in a unitary frame**: `κ = (i / 2) ∑ⱼ ζⱼ ⋏ ζ̄ⱼ`. -/
theorem IsPositiveForm.eq_sum_of_unitary {κ : E [⋀^Fin 2]→L[ℝ] ℂ} (hκ : IsPositiveForm κ)
    (hu : ∀ j k, κ ![u j, Complex.I • u k] = (if j = k then 1 else 0) ∧ κ ![u j, u k] = 0) :
    κ = (Complex.I / 2) • ∑ j, detForm ![coordForm u j, conjCoordForm u j] := by
  -- the real basis `(1 • uⱼ, i • uⱼ)` of `E`
  let e : Module.Basis (Fin 2 × Fin n) ℝ E := Complex.basisOneI.smulTower u
  have he : ∀ a j, e (a, j) = (Complex.basisOneI a : ℂ) • u j := fun a j ↦ by
    simp [e, Module.Basis.smulTower_apply]
  have hc : ∀ (c : ℂ) (j l : Fin n), u.coord l (c • u j) = if j = l then c else 0 := by
    intro c j l
    rw [map_smul, coord_basis, smul_eq_mul]
    split_ifs <;> simp
  -- the left hand side on `(c uⱼ, c' uₖ)`
  have hL : ∀ (c c' : ℂ) (j k : Fin n),
      κ ![c • u j, c' • u k] = if j = k then ((conj c * c').im : ℂ) else 0 := by
    intro c c' j k
    have h1 : ∀ v w : E, κ ![v, w] = ((hermForm κ v w).im : ℂ) := by
      intro v w
      rw [hermForm, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
        zero_add, ← hκ.ofReal_re_apply ![v, Complex.I • w], Complex.ofReal_im, zero_add]
      exact (hκ.ofReal_re_apply ![v, w]).symm
    have h2 : hermForm κ (u j) (u k) = if j = k then 1 else 0 := by
      rw [hermForm, (hu j k).1, (hu j k).2, mul_zero, add_zero]
    have h3 : ∀ (c' : ℂ) (v w : E), hermForm κ v (c' • w) = c' * hermForm κ v w := by
      intro c' v w
      rw [← hκ.hermForm_conj_symm, hκ.hermForm_smul_left, map_mul, Complex.conj_conj,
        hκ.hermForm_conj_symm]
    rw [h1, hκ.hermForm_smul_left, h3, h2]
    split_ifs <;> simp
  -- the right hand side on two vectors
  have hR : ∀ v w : E, ((Complex.I / 2) • ∑ j, detForm ![coordForm u j, conjCoordForm u j])
      ![v, w] = (Complex.I / 2) * ∑ j, (u.coord j v * conj (u.coord j w) -
        conj (u.coord j v) * u.coord j w) := by
    intro v w
    simp only [ContinuousAlternatingMap.smul_apply, ContinuousAlternatingMap.sum_apply,
      detForm_apply_eq_det, Matrix.det_fin_two, Matrix.of_apply, smul_eq_mul]
    simp
  have hR' : ∀ (c c' : ℂ) (j k : Fin n),
      ((Complex.I / 2) • ∑ j, detForm ![coordForm u j, conjCoordForm u j]) ![c • u j, c' • u k] =
        if j = k then ((conj c * c').im : ℂ) else 0 := by
    intro c c' j k
    rw [hR]
    simp only [hc]
    by_cases hjk : j = k
    · subst hjk
      rw [Finset.sum_eq_single j (fun l _ hl ↦ by simp [Ne.symm hl]) (by simp)]
      simp only [ite_true]
      have : ((conj c * c').im : ℂ) = (conj c * c' - conj (conj c * c')) / (2 * Complex.I) := by
        rw [Complex.sub_conj]
        field_simp
        push_cast
        ring
      rw [this, map_mul, Complex.conj_conj]
      field_simp
      ring_nf
      rw [Complex.I_sq]
      ring
    · rw [Finset.sum_eq_zero fun l _ ↦ ?_]
      · simp [hjk]
      · by_cases hl : j = l
        · subst hl
          simp [Ne.symm hjk]
        · simp [hl]
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  refine e.ext_alternating fun v _ ↦ ?_
  have hv : (fun i ↦ e (v i)) = ![e (v 0), e (v 1)] := by
    ext i
    fin_cases i <;> rfl
  simp only [coe_toAlternatingMap]
  rw [hv]
  obtain ⟨⟨a, j⟩, ha⟩ : ∃ x, v 0 = x := ⟨_, rfl⟩
  obtain ⟨⟨b, k⟩, hb⟩ : ∃ y, v 1 = y := ⟨_, rfl⟩
  rw [ha, hb, he, he, hL, hR']

/-! ### Expansion of forms of type `(p, 0)` -/

/-- The complex coordinates `ζ_J = (ζ_{j₀}, …, ζ_{j_{p-1}})` of a subset `J` (in increasing
order). -/
def coordFormsOf {p : ℕ} (J : Set.powersetCard (Fin n) p) : Fin p → E →L[ℝ] ℂ :=
  fun i ↦ coordForm u (Set.powersetCard.ofFinEmbEquiv.symm J i)

/-- The conjugate coordinates `ζ̄_J`. -/
def conjCoordFormsOf {p : ℕ} (J : Set.powersetCard (Fin n) p) : Fin p → E →L[ℝ] ℂ :=
  fun i ↦ conjCoordForm u (Set.powersetCard.ofFinEmbEquiv.symm J i)

/-- The basis vectors `u_J = (u_{j₀}, …, u_{j_{p-1}})` of a subset `J` (in increasing order). -/
def basisOf {p : ℕ} (J : Set.powersetCard (Fin n) p) : Fin p → E :=
  fun i ↦ u (Set.powersetCard.ofFinEmbEquiv.symm J i)

/-- **Expansion of a form of type `(p, 0)`** in the coordinates of a complex basis:
`θ = ∑_{|J| = p} θ (u_J) ζ_J`. -/
theorem IsOfType.eq_sum_detForm {p : ℕ} {θ : E [⋀^Fin p]→L[ℝ] ℂ} (hθ : IsOfType p 0 θ) :
    θ = ∑ J : Set.powersetCard (Fin n) p, θ (basisOf u J) • detForm (coordFormsOf u J) := by
  let F : Module.Dual ℂ (⋀[ℂ]^p E) := exteriorPower.alternatingMapLinearEquiv hθ.toAlternatingMap
  let B := u.exteriorPower p
  have hF := B.sum_dual_apply_smul_coord F
  ext v
  have h1 := congrArg (fun G : Module.Dual ℂ (⋀[ℂ]^p E) ↦ G (exteriorPower.ιMulti ℂ p v)) hF
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h1
  rw [ContinuousAlternatingMap.sum_apply]
  simp only [ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  have hFv : F (exteriorPower.ιMulti ℂ p v) = θ v := by
    simp [F, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rw [← hFv, ← h1]
  refine Finset.sum_congr rfl fun J _ ↦ ?_
  congr 1
  · simp [F, B, exteriorPower.basis_apply, exteriorPower.ιMulti_family,
      exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, Function.comp_def]
    rfl
  · rw [exteriorPower.basis_coord, exteriorPower.ιMultiDual_apply_ιMulti, detForm_apply_eq_det]
    rfl

/-! ### Conjugation of wedge products of `1`-forms -/

/-- `conj (φ₀ ⋏ ⋯ ⋏ φ_{k-1}) = φ̄₀ ⋏ ⋯ ⋏ φ̄_{k-1}`. -/
theorem conjForm_detForm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k : ℕ}
    (φ : Fin k → E →L[ℝ] ℂ) :
    conjForm (detForm φ) =
      detForm fun i ↦ Complex.conjCLE.toContinuousLinearMap.comp (φ i) := by
  ext v
  simp [conjForm_apply, detForm_apply, _root_.map_sum, map_prod]

lemma conjForm_detForm_coordFormsOf {p : ℕ} (J : Set.powersetCard (Fin n) p) :
    conjForm (detForm (coordFormsOf u J)) = detForm (conjCoordFormsOf u J) := by
  rw [conjForm_detForm]
  rfl

end Hodge
