/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.MaximalRegular

/-!
# Boundary cases for SGA 2, Exposé III

The unit ideal has infinite depth, and the zero ideal has depth zero on a
nonzero finite module. These cases check SGA's convention about regular
sequences whose final quotient is zero and the value `∞` in the depth
definition. The module `ℤ` has depth one along `(2)`.
-/

noncomputable section

universe u

open CategoryTheory Abelian Limits RingTheory.Sequence
open scoped Pointwise

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- Units give regular sequences of arbitrary length in SGA's convention. -/
theorem isWeaklyRegular_replicate_one (M : ModuleCat.{u} R) (n : ℕ) :
    IsWeaklyRegular M (List.replicate n (1 : R)) := by
  induction n generalizing M with
  | zero => exact IsWeaklyRegular.nil R M
  | succ n ih =>
    rw [List.replicate_succ]
    exact (ih (ModuleCat.of R (QuotSMulTop (1 : R) M))).cons
      (by intro x y h; simpa using h)

/-- The empty support has infinite depth, even when the coefficient module is nonzero. -/
@[simp]
theorem depth_top (M : ModuleCat.{u} R) : depth (⊤ : Ideal R) M = ⊤ := by
  apply (depth_eq_top_iff _ M).mpr
  intro n
  have h := length_le_depth (⊤ : Ideal R) M (List.replicate n 1)
    (by simp) (isWeaklyRegular_replicate_one M n)
  exact (le_depth_iff _ M n).mp (by simpa using h)

/-- The finite-depth qualification in III.2.6 cannot be dropped. -/
theorem no_maximalRegularSequence_top [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (rs : List R) :
    ¬ IsMaximalRegularSequence (⊤ : Ideal R) M rs := by
  intro h
  have hlen := depth_eq_length_of_maximal (⊤ : Ideal R) M rs h
  simp at hlen

/-- The full support has depth zero on a nonzero finite module. -/
@[simp]
theorem depth_bot (M : ModuleCat.{u} R) [Module.Finite R M] [Nontrivial M] :
    depth (⊥ : Ideal R) M = 0 := by
  apply le_antisymm _ bot_le
  by_contra h
  have hpos : (1 : ℕ∞) ≤ depth (⊥ : Ideal R) M :=
    Order.one_le_iff_pos.mpr (lt_of_not_ge h)
  have hExt := (le_depth_iff (⊥ : Ideal R) M 1).mp hpos M inferInstance
    ⟨1, by simp⟩ 0 (by omega)
  have : Subsingleton (M ⟶ M) := Abelian.Ext.addEquiv₀.subsingleton_congr.mp hExt
  have hz : (𝟙 M : M ⟶ M) = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  exact hx (by simpa using congrArg (fun g : M ⟶ M ↦ g x) hz)

/-- An explicit depth-one calculation over the integers. -/
theorem depth_int_two :
    depth (Ideal.span ({2} : Set ℤ)) (ModuleCat.of ℤ ℤ) = 1 := by
  let I : Ideal ℤ := Ideal.span ({2} : Set ℤ)
  let M := ModuleCat.of ℤ ℤ
  have hreg : IsSMulRegular M (2 : ℤ) := by
    intro x y h
    change (2 : ℤ) * x = 2 * y at h
    exact mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0) h
  have hquot : depth I (ModuleCat.of ℤ (QuotSMulTop (2 : ℤ) M)) = 0 := by
    apply le_antisymm _ bot_le
    by_contra h
    have hpos : (1 : ℕ∞) ≤ depth I (ModuleCat.of ℤ (QuotSMulTop (2 : ℤ) M)) :=
      Order.one_le_iff_pos.mpr (lt_of_not_ge h)
    have hExt := ((le_depth_iff I _ 1).mp hpos).quotient 0 (by omega)
    have : Subsingleton ((ℤ ⧸ I) →ₗ[ℤ] QuotSMulTop (2 : ℤ) M) :=
      (Abelian.Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp hExt
    have hI : I = (2 : ℤ) • (⊤ : Submodule ℤ ℤ) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
    let e : (ℤ ⧸ I) ≃ₗ[ℤ] QuotSMulTop (2 : ℤ) M := Submodule.quotEquivOfEq _ _ hI
    have hz := LinearMap.congr_fun (Subsingleton.elim e.toLinearMap 0) (1 : ℤ ⧸ I)
    have h10 : (1 : ℤ ⧸ I) = 0 := e.injective (by simpa using hz)
    have hmem : (1 : ℤ) ∈ I := (Ideal.Quotient.eq_zero_iff_mem).mp h10
    have hdvd : (2 : ℤ) ∣ 1 := Ideal.mem_span_singleton.mp hmem
    norm_num at hdvd
  simpa [hquot] using III_2_5 I M (Ideal.subset_span (by simp)) hreg

end SGA.SGA2.ExposeIII
