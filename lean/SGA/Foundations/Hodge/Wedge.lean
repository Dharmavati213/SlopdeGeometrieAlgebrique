/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.AlternatingSmooth
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# The wedge product of continuous alternating maps

Let `E` be a real normed space and `𝕜` a normed field which is a normed `ℝ`-algebra (for us
`𝕜 = ℂ`). For continuous alternating maps `α : E [⋀^Fin a]→L[ℝ] 𝕜` and
`β : E [⋀^Fin b]→L[ℝ] 𝕜` the **wedge product** is

  `α ⋏ β = (a! b!)⁻¹ • Alt (α ⊗ β)`, i.e.
  `(α ⋏ β) v = (a! b!)⁻¹ Σ_{σ ∈ S_{a+b}} sign σ · α (v_{σ 0}, …) · β (…, v_{σ (a+b-1)})`,

where `α ⊗ β = ContinuousMultilinearMap.mulFin α β` is the multilinear map
`v ↦ α (v ∘ castAdd b) * β (v ∘ natAdd a)` and `Alt` is `ContinuousMultilinearMap.alternatization`.
With this normalisation the wedge of two `1`-forms is `φ ⊗ ψ - ψ ⊗ φ`.

Main results:
* `ContinuousAlternatingMap.wedgeL`: the wedge product as a continuous bilinear map;
* `ContinuousAlternatingMap.wedge_smul_left`, `wedge_smul_right`: it is `𝕜`-bilinear;
* `ContinuousAlternatingMap.wedge_assoc`: associativity (up to the cast
  `Fin ((a + b) + c) ≃ Fin (a + (b + c))`);
* `ContinuousAlternatingMap.wedge_comm_domDomCongr`: `β ⋏ α` is `α ⋏ β` with the arguments
  rotated by `finAddFlip`; `ContinuousAlternatingMap.wedge_comm`: graded commutativity
  `β ⋏ α = (-1)^{ab} α ⋏ β` (up to the cast `Fin (a + b) ≃ Fin (b + a)`);
* `ContinuousAlternatingMap.wedge_compContinuousLinearMap`: pullback along a linear map is
  multiplicative.

The key tool is `ContinuousMultilinearMap.alternatization_domDomCongr_perm`:
`Alt (f ∘ σ) = sign σ • Alt f`, which lets `Alt` absorb partial alternations
(`ContinuousMultilinearMap.alternatization_mulFin_alternatization_left`, `…_right`).

Reference: N. Bourbaki, *Algebra I*, Ch. III, §7 and §11; F. Warner, *Foundations of
differentiable manifolds and Lie groups*, §2.10.
-/

noncomputable section

open Equiv Function

/-! ### `domDomCongr` for continuous alternating maps -/

namespace ContinuousAlternatingMap

variable {R M N ι ι' : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [TopologicalSpace M]
  [AddCommMonoid N] [Module R N] [TopologicalSpace N]

/-- Reindexing the arguments of a continuous alternating map along an equivalence `e : ι ≃ ι'`:
`(f.domDomCongr e) v = f (v ∘ e)`. -/
def domDomCongr (e : ι ≃ ι') (f : M [⋀^ι]→L[R] N) : M [⋀^ι']→L[R] N where
  toContinuousMultilinearMap := f.toContinuousMultilinearMap.domDomCongr e
  map_eq_zero_of_eq' v i j hv hij := by
    change f (fun k ↦ v (e k)) = 0
    exact f.map_eq_zero_of_eq _ (i := e.symm i) (j := e.symm j) (by simpa using hv)
      (by simpa using hij)

@[simp]
lemma domDomCongr_apply (e : ι ≃ ι') (f : M [⋀^ι]→L[R] N) (v : ι' → M) :
    f.domDomCongr e v = f (fun k ↦ v (e k)) :=
  rfl

@[simp]
lemma toContinuousMultilinearMap_domDomCongr (e : ι ≃ ι') (f : M [⋀^ι]→L[R] N) :
    (f.domDomCongr e).toContinuousMultilinearMap = f.toContinuousMultilinearMap.domDomCongr e :=
  rfl

@[simp]
lemma domDomCongr_refl (f : M [⋀^ι]→L[R] N) : f.domDomCongr (Equiv.refl ι) = f := by
  ext v
  rfl

lemma domDomCongr_trans {ι'' : Type*} (e : ι ≃ ι') (e' : ι' ≃ ι'') (f : M [⋀^ι]→L[R] N) :
    f.domDomCongr (e.trans e') = (f.domDomCongr e).domDomCongr e' := by
  ext v
  rfl

@[simp]
lemma domDomCongr_symm_domDomCongr (e : ι ≃ ι') (f : M [⋀^ι]→L[R] N) :
    (f.domDomCongr e).domDomCongr e.symm = f := by
  ext v
  simp

@[simp]
lemma domDomCongr_domDomCongr_symm (e : ι ≃ ι') (f : M [⋀^ι']→L[R] N) :
    (f.domDomCongr e.symm).domDomCongr e = f := by
  ext v
  simp

lemma domDomCongr_injective (e : ι ≃ ι') :
    Function.Injective (domDomCongr e : (M [⋀^ι]→L[R] N) → M [⋀^ι']→L[R] N) := fun f g h ↦ by
  simpa using congrArg (domDomCongr e.symm) h

@[simp]
lemma domDomCongr_add [ContinuousAdd N] (e : ι ≃ ι') (f g : M [⋀^ι]→L[R] N) :
    (f + g).domDomCongr e = f.domDomCongr e + g.domDomCongr e := by
  ext v
  rfl

@[simp]
lemma domDomCongr_zero (e : ι ≃ ι') : (0 : M [⋀^ι]→L[R] N).domDomCongr e = 0 := by
  ext v
  rfl

@[simp]
lemma domDomCongr_smul {S : Type*} [Monoid S] [DistribMulAction S N] [ContinuousConstSMul S N]
    [SMulCommClass R S N] [ContinuousAdd N] (c : S) (e : ι ≃ ι') (f : M [⋀^ι]→L[R] N) :
    (c • f).domDomCongr e = c • f.domDomCongr e := by
  ext v
  rfl

/-- Reindexing an alternating map along a permutation multiplies it by the sign. -/
lemma domDomCongr_perm {N : Type*} [AddCommGroup N] [Module R N] [TopologicalSpace N]
    [IsTopologicalAddGroup N] [Fintype ι] [DecidableEq ι] (σ : Perm ι) (f : M [⋀^ι]→L[R] N) :
    f.domDomCongr σ = ((Perm.sign σ : ℤ) • f) := by
  ext v
  rw [domDomCongr_apply, ContinuousAlternatingMap.smul_apply]
  exact (f.toAlternatingMap.map_perm v σ).trans (Units.smul_def _ _)

lemma domDomCongr_compContinuousLinearMap {M' : Type*} [AddCommMonoid M'] [Module R M']
    [TopologicalSpace M'] (e : ι ≃ ι') (f : M [⋀^ι]→L[R] N) (g : M' →L[R] M) :
    (f.domDomCongr e).compContinuousLinearMap g = (f.compContinuousLinearMap g).domDomCongr e := by
  ext v
  rfl

end ContinuousAlternatingMap

/-! ### Alternatization and permutations -/

namespace ContinuousMultilinearMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜]

section Alternatization

variable {M N ι ι' : Type*} [AddCommMonoid M] [Module ℝ M] [TopologicalSpace M]
  [AddCommGroup N] [Module ℝ N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- **Alternatization absorbs permutations**: `Alt (f ∘ σ) = sign σ • Alt f`. -/
theorem alternatization_domDomCongr_perm (f : ContinuousMultilinearMap ℝ (fun _ : ι ↦ M) N)
    (σ : Perm ι) : alternatization (f.domDomCongr σ) = Perm.sign σ • alternatization f := by
  ext v
  simp only [alternatization_apply_apply, domDomCongr_apply, ContinuousAlternatingMap.smul_apply,
    Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight σ) _ _ fun τ ↦ ?_
  simp only [Equiv.coe_mulRight, Perm.sign_mul, smul_smul, Function.comp_def, Perm.coe_mul]
  congr 1
  rw [mul_comm (Perm.sign τ), ← mul_assoc, Int.units_mul_self, one_mul]

/-- Alternatization commutes with reindexing along an equivalence. -/
theorem alternatization_domDomCongr (e : ι ≃ ι')
    (f : ContinuousMultilinearMap ℝ (fun _ : ι ↦ M) N) :
    alternatization (f.domDomCongr e) = (alternatization f).domDomCongr e := by
  ext v
  simp only [alternatization_apply_apply, domDomCongr_apply,
    ContinuousAlternatingMap.domDomCongr_apply]
  refine Fintype.sum_equiv e.permCongr.symm _ _ fun τ ↦ ?_
  simp [Function.comp_def, Perm.sign_permCongr, Equiv.permCongr_apply]

lemma alternatization_smul {S : Type*} [Monoid S] [DistribMulAction S N] [ContinuousConstSMul S N]
    [SMulCommClass ℝ S N] (r : S) (f : ContinuousMultilinearMap ℝ (fun _ : ι ↦ M) N) :
    alternatization (r • f) = r • alternatization f := by
  ext v
  simp only [alternatization_apply_apply, smul_apply, ContinuousAlternatingMap.smul_apply,
    Finset.smul_sum, smul_comm r]

/-- Alternatizing an alternating map multiplies it by `card (Perm ι)`. -/
lemma alternatization_toContinuousMultilinearMap (f : M [⋀^ι]→L[ℝ] N) :
    alternatization f.toContinuousMultilinearMap = Fintype.card (Perm ι) • f := by
  ext v
  simp only [alternatization_apply_apply, ContinuousAlternatingMap.coe_toContinuousMultilinearMap,
    ContinuousAlternatingMap.smul_apply]
  rw [← Finset.card_univ, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun σ _ ↦ ?_
  have h := f.toAlternatingMap.map_perm v σ
  simp only [ContinuousAlternatingMap.coe_toAlternatingMap] at h
  rw [h, smul_smul, Int.units_mul_self, one_smul]

end Alternatization

/-! ### The external product of multilinear maps -/

section MulFin

variable {a b c : ℕ}

/-- Extensionality for continuous multilinear maps in `Fin n` variables with a non-dependent
argument `v : Fin n → E` (`ext` produces a dependent one, under which `simp` cannot rewrite). -/
lemma ext_fin {n : ℕ} {f g : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) 𝕜}
    (h : ∀ v : Fin n → E, f v = g v) : f = g :=
  ContinuousMultilinearMap.ext h

/-- The external product `(f ⊗ g) v = f (v ∘ castAdd b) * g (v ∘ natAdd a)` of two continuous
multilinear maps, as a continuous multilinear map in `a + b` variables. -/
def mulFin (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    ContinuousMultilinearMap ℝ (fun _ : Fin (a + b) ↦ E) 𝕜 :=
  (((ContinuousLinearMap.lsmul ℝ 𝕜).flip g).compContinuousMultilinearMap f).uncurrySum.domDomCongr
    finSumFinEquiv

@[simp]
lemma mulFin_apply (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) (v : Fin (a + b) → E) :
    mulFin f g v = f (fun i ↦ v (Fin.castAdd b i)) * g (fun j ↦ v (Fin.natAdd a j)) := by
  simp [mulFin, Function.comp_def]

lemma norm_mulFin_le (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) : ‖mulFin f g‖ ≤ ‖f‖ * ‖g‖ := by
  refine opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [mulFin_apply, norm_mul, Fin.prod_univ_add]
  calc ‖f (fun i ↦ v (Fin.castAdd b i))‖ * ‖g (fun j ↦ v (Fin.natAdd a j))‖
      ≤ (‖f‖ * ∏ i, ‖v (Fin.castAdd b i)‖) * (‖g‖ * ∏ j, ‖v (Fin.natAdd a j)‖) :=
        mul_le_mul (f.le_opNorm _) (g.le_opNorm _) (norm_nonneg _) (by positivity)
    _ = ‖f‖ * ‖g‖ * ((∏ i, ‖v (Fin.castAdd b i)‖) * ∏ j, ‖v (Fin.natAdd a j)‖) := by ring

variable (E 𝕜 a b) in
/-- The external product as a continuous bilinear map. -/
def mulFinL : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜 →L[ℝ]
    ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜 →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin (a + b) ↦ E) 𝕜 :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ mulFin
      (fun f f' g ↦ ext_fin fun v ↦ by simp [add_mul])
      (fun r f g ↦ ext_fin fun v ↦ by simp)
      (fun f g g' ↦ ext_fin fun v ↦ by simp [mul_add])
      (fun r f g ↦ ext_fin fun v ↦ by simp))
    1 fun f g ↦ by simpa using norm_mulFin_le f g

@[simp]
lemma mulFinL_apply (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) : mulFinL E 𝕜 a b f g = mulFin f g :=
  rfl

lemma mulFin_smul_left (r : 𝕜) (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin (r • f) g = r • mulFin f g := by
  refine ext_fin fun v ↦ ?_
  simp [mul_assoc]

lemma mulFin_smul_right (r : 𝕜) (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin f (r • g) = r • mulFin f g := by
  refine ext_fin fun v ↦ ?_
  simp only [mulFin_apply, smul_apply, smul_eq_mul]
  ring

lemma mulFin_smul_left' (r : ℝ) (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin (r • f) g = r • mulFin f g := by
  exact map_smul ((mulFinL E 𝕜 a b).flip g) r f

lemma mulFin_smul_right' (r : ℝ) (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin f (r • g) = r • mulFin f g := by
  simp only [← mulFinL_apply, map_smul]

/-- The permutation of `Fin (a + b)` acting by `σ` on the first `a` places. -/
def permLeft (σ : Perm (Fin a)) : Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongr (σ.sumCongr (Equiv.refl _))

/-- The permutation of `Fin (a + b)` acting by `σ` on the last `b` places. -/
def permRight (σ : Perm (Fin b)) : Perm (Fin (a + b)) :=
  finSumFinEquiv.permCongr ((Equiv.refl _).sumCongr σ)

@[simp]
lemma sign_permLeft (σ : Perm (Fin a)) : Perm.sign (permLeft (b := b) σ) = Perm.sign σ := by
  simp [permLeft, Perm.sign_permCongr, Perm.sign_sumCongr]

@[simp]
lemma sign_permRight (σ : Perm (Fin b)) : Perm.sign (permRight (a := a) σ) = Perm.sign σ := by
  simp [permRight, Perm.sign_permCongr, Perm.sign_sumCongr]

@[simp]
lemma permLeft_castAdd (σ : Perm (Fin a)) (i : Fin a) :
    permLeft (b := b) σ (Fin.castAdd b i) = Fin.castAdd b (σ i) := by
  simp [permLeft, Equiv.permCongr_apply]

@[simp]
lemma permLeft_natAdd (σ : Perm (Fin a)) (j : Fin b) :
    permLeft σ (Fin.natAdd a j) = Fin.natAdd a j := by
  simp [permLeft, Equiv.permCongr_apply]

@[simp]
lemma permRight_castAdd (σ : Perm (Fin b)) (i : Fin a) :
    permRight σ (Fin.castAdd b i) = Fin.castAdd b i := by
  simp [permRight, Equiv.permCongr_apply]

@[simp]
lemma permRight_natAdd (σ : Perm (Fin b)) (j : Fin b) :
    permRight (a := a) σ (Fin.natAdd a j) = Fin.natAdd a (σ j) := by
  simp [permRight, Equiv.permCongr_apply]

lemma mulFin_domDomCongr_left (σ : Perm (Fin a))
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin (f.domDomCongr σ) g = (mulFin f g).domDomCongr (permLeft σ) := by
  refine ext_fin fun v ↦ ?_
  simp

lemma mulFin_domDomCongr_right (σ : Perm (Fin b))
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin f (g.domDomCongr σ) = (mulFin f g).domDomCongr (permRight σ) := by
  refine ext_fin fun v ↦ ?_
  simp

/-- `Alt` absorbs an alternation of the left factor. -/
theorem alternatization_mulFin_alternatization_left
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    alternatization (mulFin (alternatization f).toContinuousMultilinearMap g) =
      a.factorial • alternatization (mulFin f g) := by
  rw [alternatization_apply_toContinuousMultilinearMap]
  have h : mulFin (∑ σ : Perm (Fin a), Perm.sign σ • f.domDomCongr σ) g =
      ∑ σ : Perm (Fin a), Perm.sign σ • (mulFin f g).domDomCongr (permLeft σ) := by
    have e : ∀ f', mulFin f' g = (mulFinL E 𝕜 a b).flip g f' := fun _ ↦ rfl
    rw [e, _root_.map_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [map_zsmul_unit, ← e, mulFin_domDomCongr_left]
  rw [h, _root_.map_sum]
  simp_rw [map_zsmul_unit, alternatization_domDomCongr_perm, sign_permLeft, smul_smul,
    Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- `Alt` absorbs an alternation of the right factor. -/
theorem alternatization_mulFin_alternatization_right
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    alternatization (mulFin f (alternatization g).toContinuousMultilinearMap) =
      b.factorial • alternatization (mulFin f g) := by
  rw [alternatization_apply_toContinuousMultilinearMap]
  have h : mulFin f (∑ σ : Perm (Fin b), Perm.sign σ • g.domDomCongr σ) =
      ∑ σ : Perm (Fin b), Perm.sign σ • (mulFin f g).domDomCongr (permRight σ) := by
    rw [← mulFinL_apply, _root_.map_sum]
    refine Finset.sum_congr rfl fun σ _ ↦ ?_
    rw [map_zsmul_unit, mulFinL_apply, mulFin_domDomCongr_right]
  rw [h, _root_.map_sum]
  simp_rw [map_zsmul_unit, alternatization_domDomCongr_perm, sign_permRight, smul_smul,
    Int.units_mul_self, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    Fintype.card_fin]

/-- Associativity of the external product, up to `Fin ((a + b) + c) ≃ Fin (a + (b + c))`. -/
lemma mulFin_assoc (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜)
    (h : ContinuousMultilinearMap ℝ (fun _ : Fin c ↦ E) 𝕜) :
    mulFin (mulFin f g) h =
      (mulFin f (mulFin g h)).domDomCongr (finCongr (Nat.add_assoc a b c).symm) := by
  refine ext_fin fun v ↦ ?_
  simp only [mulFin_apply, domDomCongr_apply, finCongr_apply, mul_assoc]
  congr 3
  all_goals ext i; congr 1; ext; simp [Nat.add_assoc]

/-- Commutativity of the external product, up to `finAddFlip`. -/
lemma mulFin_comm (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) :
    mulFin g f = (mulFin f g).domDomCongr finAddFlip := by
  refine ext_fin fun v ↦ ?_
  simp [mul_comm]

lemma mulFin_compContinuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin a ↦ E) 𝕜)
    (g : ContinuousMultilinearMap ℝ (fun _ : Fin b ↦ E) 𝕜) (L : F →L[ℝ] E) :
    (mulFin f g).compContinuousLinearMap (fun _ ↦ L) =
      mulFin (f.compContinuousLinearMap fun _ ↦ L) (g.compContinuousLinearMap fun _ ↦ L) := by
  refine ContinuousMultilinearMap.ext fun (v : Fin (a + b) → F) ↦ ?_
  simp

end MulFin

end ContinuousMultilinearMap

/-! ### The wedge product -/

namespace ContinuousAlternatingMap

open ContinuousMultilinearMap

variable {E 𝕜 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedField 𝕜]
  [NormedAlgebra ℝ 𝕜] {a b c : ℕ}

variable (E 𝕜 a b) in
/-- The **wedge product** `(α, β) ↦ α ⋏ β = (a! b!)⁻¹ • Alt (α ⊗ β)` of continuous alternating
maps, as a continuous bilinear map. -/
def wedgeL : (E [⋀^Fin a]→L[ℝ] 𝕜) →L[ℝ] (E [⋀^Fin b]→L[ℝ] 𝕜) →L[ℝ]
    (E [⋀^Fin (a + b)]→L[ℝ] 𝕜) :=
  (ContinuousLinearMap.compL ℝ _ _ _
      ((((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) • alternatizationCLM E 𝕜 (a + b))).comp
    ((mulFinL E 𝕜 a b).bilinearComp (toContinuousMultilinearMapCLM ℝ)
      (toContinuousMultilinearMapCLM ℝ))

/-- The **wedge product** of continuous alternating maps, `α ⋏ β = (a! b!)⁻¹ • Alt (α ⊗ β)`. -/
def wedge (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) : E [⋀^Fin (a + b)]→L[ℝ] 𝕜 :=
  wedgeL E 𝕜 a b α β

@[inherit_doc] scoped infixr:70 " ⋏ " => ContinuousAlternatingMap.wedge

@[simp]
lemma wedgeL_apply (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    wedgeL E 𝕜 a b α β = α ⋏ β :=
  rfl

lemma wedge_def (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α ⋏ β = (((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) •
      alternatization (mulFin α.toContinuousMultilinearMap β.toContinuousMultilinearMap) :=
  rfl

lemma wedge_apply (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) (v : Fin (a + b) → E) :
    (α ⋏ β) v = (((a.factorial * b.factorial : ℕ) : ℝ)⁻¹) •
      ∑ σ : Perm (Fin (a + b)), Perm.sign σ •
        (α (fun i ↦ v (σ (Fin.castAdd b i))) * β (fun j ↦ v (σ (Fin.natAdd a j)))) := by
  rw [wedge_def, smul_apply, alternatization_apply_apply]
  simp [Function.comp_def]

@[simp]
lemma wedge_add_left (α α' : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    (α + α') ⋏ β = α ⋏ β + α' ⋏ β := by
  rw [← wedgeL_apply, _root_.map_add]
  rfl

@[simp]
lemma wedge_add_right (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β β' : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α ⋏ (β + β') = α ⋏ β + α ⋏ β' := by
  rw [← wedgeL_apply, _root_.map_add]
  rfl

@[simp]
lemma wedge_zero_left (β : E [⋀^Fin b]→L[ℝ] 𝕜) : (0 : E [⋀^Fin a]→L[ℝ] 𝕜) ⋏ β = 0 := by
  rw [← wedgeL_apply, _root_.map_zero]
  rfl

@[simp]
lemma wedge_zero_right (α : E [⋀^Fin a]→L[ℝ] 𝕜) : α ⋏ (0 : E [⋀^Fin b]→L[ℝ] 𝕜) = 0 := by
  rw [← wedgeL_apply, _root_.map_zero]

@[simp]
lemma wedge_neg_left (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    (-α) ⋏ β = -(α ⋏ β) := by
  rw [← wedgeL_apply, _root_.map_neg]
  rfl

@[simp]
lemma wedge_neg_right (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α ⋏ (-β) = -(α ⋏ β) := by
  rw [← wedgeL_apply, _root_.map_neg]
  rfl

@[simp]
lemma wedge_sub_left (α α' : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    (α - α') ⋏ β = α ⋏ β - α' ⋏ β := by
  rw [sub_eq_add_neg, wedge_add_left, wedge_neg_left, ← sub_eq_add_neg]

@[simp]
lemma wedge_sub_right (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β β' : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α ⋏ (β - β') = α ⋏ β - α ⋏ β' := by
  rw [sub_eq_add_neg, wedge_add_right, wedge_neg_right, ← sub_eq_add_neg]

lemma wedge_sum_left {ι : Type*} (s : Finset ι) (α : ι → E [⋀^Fin a]→L[ℝ] 𝕜)
    (β : E [⋀^Fin b]→L[ℝ] 𝕜) : (∑ i ∈ s, α i) ⋏ β = ∑ i ∈ s, α i ⋏ β :=
  _root_.map_sum ((wedgeL E 𝕜 a b).flip β) α s

lemma wedge_sum_right {ι : Type*} (s : Finset ι) (α : E [⋀^Fin a]→L[ℝ] 𝕜)
    (β : ι → E [⋀^Fin b]→L[ℝ] 𝕜) : α ⋏ (∑ i ∈ s, β i) = ∑ i ∈ s, α ⋏ β i :=
  _root_.map_sum (wedgeL E 𝕜 a b α) β s

@[simp]
lemma wedge_smul_left (r : 𝕜) (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    (r • α) ⋏ β = r • (α ⋏ β) := by
  rw [wedge_def, wedge_def, toContinuousMultilinearMap_smul, mulFin_smul_left,
    alternatization_smul, smul_comm]

@[simp]
lemma wedge_smul_right (r : 𝕜) (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α ⋏ (r • β) = r • (α ⋏ β) := by
  rw [wedge_def, wedge_def, toContinuousMultilinearMap_smul, mulFin_smul_right,
    alternatization_smul, smul_comm]

@[simp]
lemma wedge_real_smul_left (r : ℝ) (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    (r • α) ⋏ β = r • (α ⋏ β) :=
  map_smul ((wedgeL E 𝕜 a b).flip β) r α

@[simp]
lemma wedge_real_smul_right (r : ℝ) (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    α ⋏ (r • β) = r • (α ⋏ β) :=
  map_smul (wedgeL E 𝕜 a b α) r β

/-- Pullback along a linear map is multiplicative. -/
lemma wedge_compContinuousLinearMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) (L : F →L[ℝ] E) :
    (α ⋏ β).compContinuousLinearMap L =
      α.compContinuousLinearMap L ⋏ β.compContinuousLinearMap L := by
  ext v
  simp [wedge_apply, Function.comp_def]

/-- Postcomposition with a multiplicative continuous `ℝ`-linear map (e.g. complex conjugation)
commutes with the wedge product. -/
lemma compContinuousAlternatingMap_wedge (T : 𝕜 →L[ℝ] 𝕜) (hT : ∀ x y, T (x * y) = T x * T y)
    (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    T.compContinuousAlternatingMap (α ⋏ β) =
      T.compContinuousAlternatingMap α ⋏ T.compContinuousAlternatingMap β := by
  ext v
  simp only [ContinuousLinearMap.compContinuousAlternatingMap_coe, Function.comp_apply,
    wedge_apply, map_smul, _root_.map_sum, map_zsmul_unit, hT]

/-! #### Associativity -/

/-- **Associativity of the wedge product**, up to the reindexing
`Fin (a + (b + c)) ≃ Fin ((a + b) + c)`. -/
theorem wedge_assoc (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜)
    (γ : E [⋀^Fin c]→L[ℝ] 𝕜) :
    (α ⋏ β) ⋏ γ = (α ⋏ (β ⋏ γ)).domDomCongr (finCongr (Nat.add_assoc a b c).symm) := by
  have h1 : (α ⋏ β) ⋏ γ = (((a.factorial * b.factorial * c.factorial : ℕ) : ℝ)⁻¹) •
      alternatization (mulFin (mulFin α.toContinuousMultilinearMap β.toContinuousMultilinearMap)
        γ.toContinuousMultilinearMap) := by
    rw [wedge_def (α ⋏ β), wedge_def α β, toContinuousMultilinearMap_smul, mulFin_smul_left',
      alternatization_smul, alternatization_mulFin_alternatization_left, smul_smul,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    have := (a + b).factorial_pos
    have := a.factorial_pos
    have := b.factorial_pos
    have := c.factorial_pos
    push_cast
    field_simp
  have h2 : α ⋏ (β ⋏ γ) = (((a.factorial * b.factorial * c.factorial : ℕ) : ℝ)⁻¹) •
      alternatization (mulFin α.toContinuousMultilinearMap
        (mulFin β.toContinuousMultilinearMap γ.toContinuousMultilinearMap)) := by
    rw [wedge_def α (β ⋏ γ), wedge_def β γ, toContinuousMultilinearMap_smul, mulFin_smul_right',
      alternatization_smul, alternatization_mulFin_alternatization_right, smul_smul,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    have := (b + c).factorial_pos
    have := a.factorial_pos
    have := b.factorial_pos
    have := c.factorial_pos
    push_cast
    field_simp
  rw [h1, h2, domDomCongr_smul, ← alternatization_domDomCongr, mulFin_assoc]

/-! #### Graded commutativity -/

/-- `β ⋏ α` is `α ⋏ β` with its arguments rotated by `finAddFlip`. -/
theorem wedge_comm_domDomCongr (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    β ⋏ α = (α ⋏ β).domDomCongr finAddFlip := by
  rw [wedge_def, wedge_def, mulFin_comm, alternatization_domDomCongr, domDomCongr_smul, mul_comm]

/-- The block rotation of `Fin (a + b)`: `i ↦ i + b` modulo `a + b` (`finAddFlip` followed by
the cast `Fin (b + a) = Fin (a + b)`). -/
def flipPerm (a b : ℕ) : Perm (Fin (a + b)) :=
  finAddFlip.trans (finCongr (Nat.add_comm b a))

lemma val_finRotate_pow_apply (n b : ℕ) (i : Fin n) :
    (((finRotate n) ^ b) i : ℕ) = (i + b) % n := by
  induction b with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ b ih =>
    rw [pow_succ', Perm.mul_apply]
    set j := ((finRotate n) ^ b) i
    have := j.neZero
    rw [finRotate_apply, Fin.val_add, ih, Fin.val_one', Nat.add_mod_mod, Nat.mod_add_mod,
      Nat.add_assoc]

lemma flipPerm_eq_pow (a b : ℕ) : flipPerm a b = (finRotate (a + b)) ^ b := by
  ext i
  rw [val_finRotate_pow_apply]
  refine Fin.addCases (fun k ↦ ?_) (fun k ↦ ?_) i
  · simp only [flipPerm, Equiv.trans_apply, finAddFlip_apply_castAdd, finCongr_apply,
      Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [flipPerm, Equiv.trans_apply, finAddFlip_apply_natAdd, finCongr_apply,
      Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
    rw [show a + k + b = k + (a + b) by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

lemma sign_flipPerm (a b : ℕ) : Perm.sign (flipPerm a b) = (-1) ^ (a * b) := by
  rw [flipPerm_eq_pow, map_pow, sign_finRotate]
  rcases b with _ | c
  · simp
  · rw [← pow_mul, show a + (c + 1) - 1 = a + c by omega,
      show (a + c) * (c + 1) = a * (c + 1) + c * (c + 1) by ring, pow_add,
      (Nat.even_mul_succ_self c).neg_one_pow, mul_one]

/-- **Graded commutativity of the wedge product**: `β ⋏ α = (-1)^{ab} α ⋏ β`, up to the
reindexing `Fin (a + b) = Fin (b + a)`. -/
theorem wedge_comm (α : E [⋀^Fin a]→L[ℝ] 𝕜) (β : E [⋀^Fin b]→L[ℝ] 𝕜) :
    β ⋏ α = ((-1 : ℤ) ^ (a * b)) • (α ⋏ β).domDomCongr (finCongr (Nat.add_comm a b)) := by
  have h : (finAddFlip : Fin (a + b) ≃ Fin (b + a)) =
      (flipPerm a b).trans (finCongr (Nat.add_comm a b)) := by
    ext i
    simp [flipPerm]
  rw [wedge_comm_domDomCongr, h, domDomCongr_trans, domDomCongr_perm, sign_flipPerm,
    domDomCongr_smul]
  push_cast
  rfl

/-- Two `1`-forms anticommute. -/
theorem wedge_comm_one (φ ψ : E [⋀^Fin 1]→L[ℝ] 𝕜) : ψ ⋏ φ = -(φ ⋏ ψ) := by
  rw [wedge_comm]
  ext v
  simp

/-- The wedge square of a `1`-form vanishes. -/
theorem wedge_self_one (φ : E [⋀^Fin 1]→L[ℝ] 𝕜) : φ ⋏ φ = 0 := by
  have h := wedge_comm_one φ φ
  have h2 : (2 : ℝ) • (φ ⋏ φ) = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    exact neg_add_cancel _
  exact (smul_eq_zero.mp h2).resolve_left two_ne_zero

end ContinuousAlternatingMap
