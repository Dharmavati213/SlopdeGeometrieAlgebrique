/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Wedge
import SGA.Foundations.Hodge.Dbar

/-!
# The Leibniz rule for the wedge product

For differential forms `α : E → E [⋀^Fin a]→L[ℝ] 𝕜`, `β : E → E [⋀^Fin b]→L[ℝ] 𝕜` on a real
normed space `E`, differentiable at `x`:

  `d (α ⋏ β) = dα ⋏ β + (-1)ᵃ α ⋏ dβ` (`ContinuousAlternatingMap.extDeriv_wedge`),

the first term reindexed along `Fin ((a + 1) + b) = Fin ((a + b) + 1)`. On a complex normed space
the same holds for `∂` and `∂̄` (`Hodge.partDeriv_wedge`, any `partDeriv ε`).

The algebraic content is two identities for mathlib's `alternatizeUncurryFin` (the alternation
`f ↦ Σᵢ (-1)ⁱ f (vᵢ) (v̂ᵢ)` that defines `d` from the derivative):

* `ContinuousAlternatingMap.alternatizeUncurryFin_eq_alternatization`:
  `alternatizeUncurryFin f = (n!)⁻¹ • Alt (uncurryFin f)` where `uncurryFin f v = f (v 0) (tail v)`;
* `ContinuousAlternatingMap.alternatizeUncurryFin_wedge_left`,
  `ContinuousAlternatingMap.alternatizeUncurryFin_wedge_right`: alternating `u ↦ f u ⋏ β` gives
  `alternatizeUncurryFin f ⋏ β`, alternating `u ↦ α ⋏ g u` gives
  `(-1)ᵃ α ⋏ alternatizeUncurryFin g`.

Both are proved by letting `Alt` absorb the inner alternations
(`ContinuousMultilinearMap.alternatization_domDomCongr_perm`); the sign `(-1)ᵃ` is the sign of a
`Fin.cycleRange`.

Reference: F. Warner, *Foundations of differentiable manifolds and Lie groups*, 2.23;
D. Huybrechts, *Complex geometry*, §1.3.
-/

noncomputable section

open Equiv Function ContinuousMultilinearMap

namespace ContinuousAlternatingMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜] {n a b : ℕ}

/-- The multilinear map `v ↦ f (v 0) (tail v)` attached to a linear map into alternating maps. -/
def uncurryFin (f : E →L[ℝ] E [⋀^Fin n]→L[ℝ] 𝕜) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) 𝕜 :=
  ContinuousLinearMap.uncurryLeft
    (Ei := fun _ : Fin (n + 1) ↦ E) ((toContinuousMultilinearMapCLM ℝ).comp f)

@[simp]
lemma uncurryFin_apply (f : E →L[ℝ] E [⋀^Fin n]→L[ℝ] 𝕜) (v : Fin (n + 1) → E) :
    uncurryFin f v = f (v 0) (Fin.tail v) :=
  rfl

/-- `alternatizeUncurryFin f`, as a multilinear map, is a signed sum of reindexings of
`uncurryFin f` along the cycles `Fin.cycleRange p`. -/
lemma toContinuousMultilinearMap_alternatizeUncurryFin (f : E →L[ℝ] E [⋀^Fin n]→L[ℝ] 𝕜) :
    (alternatizeUncurryFin f).toContinuousMultilinearMap =
      ∑ p : Fin (n + 1), ((-1 : ℤ) ^ (p : ℕ)) •
        (uncurryFin f).domDomCongr p.cycleRange.symm := by
  refine ContinuousMultilinearMap.ext fun (v : Fin (n + 1) → E) ↦ ?_
  rw [coe_toContinuousMultilinearMap, alternatizeUncurryFin_apply,
    _root_.sum_apply]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [_root_.smul_apply, ContinuousMultilinearMap.domDomCongr_apply]
  have h : (fun i ↦ v (p.cycleRange.symm i)) = Fin.cons (v p) (p.removeNth v) :=
    (Fin.cons_removeNth_eq_comp_cycleRange_symm v p).symm
  rw [h, uncurryFin_apply, Fin.cons_zero, Fin.tail_cons]

private lemma neg_one_pow_smul_units_smul {V : Type*} [AddCommGroup V] (k : ℕ) (x : V) :
    ((-1 : ℤ) ^ k) • (((-1 : ℤˣ) ^ k) • x) = x := by
  rw [Units.smul_def, smul_smul, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one,
    ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]

/-- `alternatizeUncurryFin f = (n!)⁻¹ • Alt (uncurryFin f)`. -/
theorem alternatizeUncurryFin_eq_alternatization (f : E →L[ℝ] E [⋀^Fin n]→L[ℝ] 𝕜) :
    alternatizeUncurryFin f = ((n.factorial : ℝ)⁻¹) • alternatization (uncurryFin f) := by
  have h1 := alternatization_toContinuousMultilinearMap (alternatizeUncurryFin f)
  rw [toContinuousMultilinearMap_alternatizeUncurryFin, _root_.map_sum] at h1
  have h3 : ∀ p : Fin (n + 1), alternatization (((-1 : ℤ) ^ (p : ℕ)) •
      (uncurryFin f).domDomCongr p.cycleRange.symm) = alternatization (uncurryFin f) := by
    intro p
    rw [map_zsmul, alternatization_domDomCongr_perm, Perm.sign_symm, Fin.sign_cycleRange,
      neg_one_pow_smul_units_smul]
  simp only [h3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Fintype.card_perm,
    Nat.factorial_succ] at h1
  rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ] at h1
  have hn : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [eq_inv_smul_iff₀ hf]
  apply smul_right_injective _ hn
  simp only
  rw [h1, smul_smul]
  push_cast
  ring_nf

/-- The permutation of `Fin (n + 1)` fixing `0` and acting by `τ` on the other places. -/
def permSucc (τ : Perm (Fin n)) : Perm (Fin (n + 1)) :=
  Perm.decomposeFin.symm (0, τ)

@[simp]
lemma permSucc_zero (τ : Perm (Fin n)) : permSucc τ 0 = 0 := by
  simp [permSucc]

@[simp]
lemma permSucc_succ (τ : Perm (Fin n)) (i : Fin n) : permSucc τ i.succ = (τ i).succ := by
  simp [permSucc]

@[simp]
lemma sign_permSucc (τ : Perm (Fin n)) : Perm.sign (permSucc τ) = Perm.sign τ := by
  simp [permSucc]

/-- `Alt` of a multilinear map in `n + 1` variables whose last `n` variables are alternated by
`τ ↦ sign τ • h ∘ permSucc τ` is `n!` times `Alt h`. -/
lemma alternatization_sum_permSucc (h : ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) ↦ E) 𝕜) :
    alternatization (∑ τ : Perm (Fin n), Perm.sign τ • h.domDomCongr (permSucc τ)) =
      n.factorial • alternatization h := by
  rw [_root_.map_sum]
  simp_rw [map_zsmul_unit, alternatization_domDomCongr_perm, sign_permSucc, smul_smul,
    Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- `uncurryFin` of `u ↦ f u ⋏ β`. -/
private lemma uncurryFin_wedge_left_apply (f : E →L[ℝ] E [⋀^Fin a]→L[ℝ] 𝕜)
    (β : E [⋀^Fin b]→L[ℝ] 𝕜) (v : Fin (a + b + 1) → E) :
    uncurryFin ((wedgeL E 𝕜 a b).flip β ∘L f) v =
      (((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) • ∑ τ : Perm (Fin (a + b)), Perm.sign τ •
        (f (v 0) (fun i ↦ v (τ (Fin.castAdd b i)).succ) *
          β (fun j ↦ v (τ (Fin.natAdd a j)).succ)) := by
  rw [uncurryFin_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    wedgeL_apply, wedge_apply]
  rfl

/-- `uncurryFin` of `u ↦ α ⋏ g u`. -/
private lemma uncurryFin_wedge_right_apply (α : E [⋀^Fin a]→L[ℝ] 𝕜)
    (g : E →L[ℝ] E [⋀^Fin b]→L[ℝ] 𝕜) (v : Fin (a + b + 1) → E) :
    uncurryFin (wedgeL E 𝕜 a b α ∘L g) v =
      (((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) • ∑ τ : Perm (Fin (a + b)), Perm.sign τ •
        (α (fun i ↦ v (τ (Fin.castAdd b i)).succ) *
          g (v 0) (fun j ↦ v (τ (Fin.natAdd a j)).succ)) := by
  rw [uncurryFin_apply, ContinuousLinearMap.comp_apply, wedgeL_apply, wedge_apply]
  rfl

/-- **Leibniz, left factor**: alternating `u ↦ f u ⋏ β` gives `alternatizeUncurryFin f ⋏ β`,
reindexed along `Fin ((a + 1) + b) = Fin ((a + b) + 1)`. -/
theorem alternatizeUncurryFin_wedge_left (f : E →L[ℝ] E [⋀^Fin a]→L[ℝ] 𝕜)
    (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    alternatizeUncurryFin ((wedgeL E 𝕜 a b).flip β ∘L f) =
      (alternatizeUncurryFin f ⋏ β).domDomCongr (finCongr (Nat.succ_add a b)) := by
  set U₀ : ContinuousMultilinearMap ℝ (fun _ : Fin (a + b + 1) ↦ E) 𝕜 :=
    (mulFin (uncurryFin f) β.toContinuousMultilinearMap).domDomCongr
      (finCongr (Nat.succ_add a b)) with hU₀
  have hU₀v : ∀ w : Fin (a + b + 1) → E, U₀ w =
      f (w 0) (fun i ↦ w (Fin.castAdd b i).succ) * β (fun j ↦ w (Fin.natAdd a j).succ) := by
    intro w
    rw [hU₀, ContinuousMultilinearMap.domDomCongr_apply, mulFin_apply, uncurryFin_apply,
      coe_toContinuousMultilinearMap]
    have e0 : (finCongr (Nat.succ_add a b) (Fin.castAdd b 0) : Fin (a + b + 1)) = 0 :=
      Fin.ext (by simp)
    have e1 : ∀ i : Fin a, (finCongr (Nat.succ_add a b) (Fin.castAdd b i.succ) :
        Fin (a + b + 1)) = (Fin.castAdd b i).succ := fun i ↦ Fin.ext (by simp)
    have e2 : ∀ j : Fin b, (finCongr (Nat.succ_add a b) (Fin.natAdd (a + 1) j) :
        Fin (a + b + 1)) = (Fin.natAdd a j).succ := fun j ↦ Fin.ext (by simp; omega)
    have et : (Fin.tail fun i ↦ w (finCongr (Nat.succ_add a b) (Fin.castAdd b i))) =
        fun i ↦ w (Fin.castAdd b i).succ := funext fun i ↦ congrArg w (e1 i)
    simp only [e0, e2, et]
  have hU : uncurryFin ((wedgeL E 𝕜 a b).flip β ∘L f) =
      (((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) •
        ∑ τ : Perm (Fin (a + b)), Perm.sign τ • U₀.domDomCongr (permSucc τ) := by
    refine ContinuousMultilinearMap.ext fun (v : Fin (a + b + 1) → E) ↦ ?_
    rw [uncurryFin_wedge_left_apply, _root_.smul_apply,
      _root_.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [_root_.smul_apply, ContinuousMultilinearMap.domDomCongr_apply, hU₀v]
    simp only [permSucc_zero, permSucc_succ]
  rw [alternatizeUncurryFin_eq_alternatization, hU, alternatization_smul,
    alternatization_sum_permSucc, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul]
  rw [wedge_def, alternatizeUncurryFin_eq_alternatization, toContinuousMultilinearMap_smul,
    mulFin_smul_left', alternatization_smul, alternatization_mulFin_alternatization_left,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, domDomCongr_smul,
    ← alternatization_domDomCongr, ← hU₀]
  congr 1
  have := (a + b).factorial_pos
  have := a.factorial_pos
  have := b.factorial_pos
  rw [Nat.factorial_succ]
  push_cast
  field_simp

/-- **Leibniz, right factor**: alternating `u ↦ α ⋏ g u` gives
`(-1)ᵃ α ⋏ alternatizeUncurryFin g`. -/
theorem alternatizeUncurryFin_wedge_right (α : E [⋀^Fin a]→L[ℝ] 𝕜)
    (g : E →L[ℝ] E [⋀^Fin b]→L[ℝ] 𝕜) :
    alternatizeUncurryFin (wedgeL E 𝕜 a b α ∘L g) =
      ((-1 : ℤ) ^ a) • (α ⋏ alternatizeUncurryFin g) := by
  set π : Perm (Fin (a + b + 1)) := Fin.cycleRange ⟨a, by omega⟩ with hπ
  set V₀ : ContinuousMultilinearMap ℝ (fun _ : Fin (a + b + 1) ↦ E) 𝕜 :=
    (mulFin α.toContinuousMultilinearMap (uncurryFin g)).domDomCongr π with hV₀
  have hV₀v : ∀ w : Fin (a + b + 1) → E, V₀ w =
      α (fun i ↦ w (Fin.castAdd b i).succ) * g (w 0) (fun j ↦ w (Fin.natAdd a j).succ) := by
    intro w
    rw [hV₀, ContinuousMultilinearMap.domDomCongr_apply, mulFin_apply, uncurryFin_apply,
      coe_toContinuousMultilinearMap]
    have e1 : ∀ i : Fin a, π (Fin.castAdd (b + 1) i) = (Fin.castAdd b i).succ := by
      intro i
      refine Fin.ext ?_
      rw [hπ, Fin.coe_cycleRange_of_lt (by simp [Fin.lt_def])]
      simp
    have e0 : π (Fin.natAdd a (0 : Fin (b + 1))) = 0 := by
      rw [hπ]
      exact Fin.cycleRange_of_eq (Fin.ext (by simp))
    have e2 : ∀ j : Fin b, π (Fin.natAdd a j.succ) = (Fin.natAdd a j).succ := by
      intro j
      rw [hπ, Fin.cycleRange_of_gt (by simp [Fin.lt_def])]
      exact Fin.ext (by simp; omega)
    have et : (Fin.tail fun j ↦ w (π (Fin.natAdd a j))) = fun j ↦ w (Fin.natAdd a j).succ :=
      funext fun j ↦ congrArg w (e2 j)
    simp only [e0, e1, et]
  have hV : uncurryFin (wedgeL E 𝕜 a b α ∘L g) =
      (((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) •
        ∑ τ : Perm (Fin (a + b)), Perm.sign τ • V₀.domDomCongr (permSucc τ) := by
    refine ContinuousMultilinearMap.ext fun (v : Fin (a + b + 1) → E) ↦ ?_
    rw [uncurryFin_wedge_right_apply, _root_.smul_apply,
      _root_.sum_apply]
    congr 1
    refine Finset.sum_congr rfl fun τ _ ↦ ?_
    rw [_root_.smul_apply, ContinuousMultilinearMap.domDomCongr_apply, hV₀v]
    simp only [permSucc_zero, permSucc_succ]
  have hsign : alternatization V₀ =
      ((-1 : ℝ) ^ a) • alternatization (mulFin α.toContinuousMultilinearMap (uncurryFin g)) := by
    rw [hV₀, alternatization_domDomCongr_perm, hπ, Fin.sign_cycleRange, Units.smul_def,
      Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← Int.cast_smul_eq_zsmul ℝ]
    push_cast
    rfl
  rw [← Int.cast_smul_eq_zsmul ℝ, alternatizeUncurryFin_eq_alternatization, hV,
    alternatization_smul, alternatization_sum_permSucc, hsign, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, smul_smul, smul_smul]
  rw [wedge_def, alternatizeUncurryFin_eq_alternatization, toContinuousMultilinearMap_smul,
    mulFin_smul_right', alternatization_smul, alternatization_mulFin_alternatization_right,
    ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, smul_smul, smul_smul]
  congr 1
  have := (a + b).factorial_pos
  have := a.factorial_pos
  have := b.factorial_pos
  rw [Nat.factorial_succ]
  push_cast
  field_simp

end ContinuousAlternatingMap

namespace ContinuousAlternatingMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜] {a b : ℕ}

/-- The derivative of `y ↦ α y ⋏ β y` (product rule). -/
theorem fderiv_wedge {α : E → E [⋀^Fin a]→L[ℝ] 𝕜} {β : E → E [⋀^Fin b]→L[ℝ] 𝕜} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    fderiv ℝ (fun y ↦ α y ⋏ β y) x =
      (wedgeL E 𝕜 a b).flip (β x) ∘L fderiv ℝ α x + wedgeL E 𝕜 a b (α x) ∘L fderiv ℝ β x := by
  rw [show (fun y ↦ α y ⋏ β y) = fun y ↦ wedgeL E 𝕜 a b (α y) (β y) from rfl,
    (wedgeL E 𝕜 a b).fderiv_of_bilinear hα hβ]
  ext1 u
  simp only [_root_.add_apply]
  exact add_comm _ _

theorem differentiableAt_wedge {α : E → E [⋀^Fin a]→L[ℝ] 𝕜} {β : E → E [⋀^Fin b]→L[ℝ] 𝕜}
    {x : E} (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    DifferentiableAt ℝ (fun y ↦ α y ⋏ β y) x :=
  ((wedgeL E 𝕜 a b).hasFDerivAt_of_bilinear hα.hasFDerivAt hβ.hasFDerivAt).differentiableAt

theorem contDiffAt_wedge {α : E → E [⋀^Fin a]→L[ℝ] 𝕜} {β : E → E [⋀^Fin b]→L[ℝ] 𝕜}
    {x : E} {m : WithTop ℕ∞} (hα : ContDiffAt ℝ m α x) (hβ : ContDiffAt ℝ m β x) :
    ContDiffAt ℝ m (fun y ↦ α y ⋏ β y) x :=
  ((wedgeL E 𝕜 a b).contDiff.contDiffAt.comp x hα).clm_apply hβ

/-- **Leibniz rule for the exterior derivative**:
`d (α ⋏ β) = dα ⋏ β + (-1)ᵃ α ⋏ dβ`, the first term reindexed along
`Fin ((a + 1) + b) = Fin ((a + b) + 1)`. -/
theorem extDeriv_wedge {α : E → E [⋀^Fin a]→L[ℝ] 𝕜} {β : E → E [⋀^Fin b]→L[ℝ] 𝕜} {x : E}
    (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    extDeriv (fun y ↦ α y ⋏ β y) x =
      (extDeriv α x ⋏ β x).domDomCongr (finCongr (Nat.succ_add a b)) +
        ((-1 : ℤ) ^ a) • (α x ⋏ extDeriv β x) := by
  rw [extDeriv, fderiv_wedge hα hβ, alternatizeUncurryFin_add, alternatizeUncurryFin_wedge_left,
    alternatizeUncurryFin_wedge_right]
  rfl

end ContinuousAlternatingMap

namespace Hodge

open ContinuousAlternatingMap ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a b p q p' q' : ℕ}

/-- **Leibniz rule for `∂` and `∂̄`** (any `partDeriv ε`):
`∂̄ (α ⋏ β) = ∂̄α ⋏ β + (-1)ᵃ α ⋏ ∂̄β`, the first term reindexed along
`Fin ((a + 1) + b) = Fin ((a + b) + 1)`. -/
theorem partDeriv_wedge (ε : ℂ) {α : E → E [⋀^Fin a]→L[ℝ] ℂ} {β : E → E [⋀^Fin b]→L[ℝ] ℂ}
    {x : E} (hα : DifferentiableAt ℝ α x) (hβ : DifferentiableAt ℝ β x) :
    partDeriv ε (fun y ↦ α y ⋏ β y) x =
      (partDeriv ε α x ⋏ β x).domDomCongr (finCongr (Nat.succ_add a b)) +
        ((-1 : ℤ) ^ a) • (α x ⋏ partDeriv ε β x) := by
  have hA : ∀ (c : ℂ) (ω : E [⋀^Fin a]→L[ℝ] ℂ),
      (wedgeL E ℂ a b).flip (β x) (c • ω) = c • (wedgeL E ℂ a b).flip (β x) ω := fun c ω ↦
    wedge_smul_left c ω (β x)
  have hB : ∀ (c : ℂ) (ω : E [⋀^Fin b]→L[ℝ] ℂ),
      wedgeL E ℂ a b (α x) (c • ω) = c • wedgeL E ℂ a b (α x) ω := fun c ω ↦
    wedge_smul_right c (α x) ω
  rw [partDeriv, fderiv_wedge hα hβ, map_add, partCLM_postcomp ε _ hA, partCLM_postcomp ε _ hB,
    alternatizeUncurryFin_add, alternatizeUncurryFin_wedge_left,
    alternatizeUncurryFin_wedge_right]
  rfl

/-- The wedge product of forms of types `(p, q)` and `(p', q')` has type `(p + p', q + q')`. -/
theorem IsOfType.wedge {α : E [⋀^Fin a]→L[ℝ] ℂ} {β : E [⋀^Fin b]→L[ℝ] ℂ} (hα : IsOfType p q α)
    (hβ : IsOfType p' q' β) : IsOfType (p + p') (q + q') (α ⋏ β) := by
  intro c v
  have key : ∀ σ : Perm (Fin (a + b)), (α fun i ↦ (c • v) (σ (Fin.castAdd b i))) *
      β (fun j ↦ (c • v) (σ (Fin.natAdd a j))) = (c ^ (p + p') * conj c ^ (q + q')) *
        ((α fun i ↦ v (σ (Fin.castAdd b i))) * β (fun j ↦ v (σ (Fin.natAdd a j)))) := by
    intro σ
    rw [show (fun i ↦ (c • v) (σ (Fin.castAdd b i))) = c • fun i ↦ v (σ (Fin.castAdd b i))
      from rfl, show (fun j ↦ (c • v) (σ (Fin.natAdd a j))) = c • fun j ↦ v (σ (Fin.natAdd a j))
      from rfl, hα, hβ]
    ring
  rw [wedge_apply, wedge_apply]
  simp only [key]
  simp only [Units.smul_def, zsmul_eq_mul, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun σ _ ↦ by ring

/-- Complex conjugation is multiplicative for the wedge product. -/
theorem conjForm_wedge (α : E [⋀^Fin a]→L[ℝ] ℂ) (β : E [⋀^Fin b]→L[ℝ] ℂ) :
    conjForm (α ⋏ β) = conjForm α ⋏ conjForm β :=
  compContinuousAlternatingMap_wedge _ (fun x y ↦ map_mul (starRingEnd ℂ) x y) α β

lemma conjForm_domDomCongr {k k' : ℕ} (e : Fin k ≃ Fin k') (α : E [⋀^Fin k]→L[ℝ] ℂ) :
    conjForm (α.domDomCongr e) = (conjForm α).domDomCongr e :=
  rfl

lemma IsOfType.domDomCongr {k k' : ℕ} {α : E [⋀^Fin k]→L[ℝ] ℂ} (hα : IsOfType p q α)
    (e : Fin k ≃ Fin k') : IsOfType p q (α.domDomCongr e) := fun c _ ↦ hα c _

end Hodge
