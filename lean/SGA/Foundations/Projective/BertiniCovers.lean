/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Topology.Sober
import Mathlib.RingTheory.TensorProduct.Nontrivial

/-!
# Algebraic and topological lemmas for étale covers of a hyperplane section

These are used to show that the generic hyperplane section of SGA 1 X.2.10 stays geometrically
connected after pulling back along a connected finite étale cover.

* `Bertini.isField_ratFunc_tensor`: for a field `L` and a finite field extension `B ⊇ L`,
  `L(s) ⊗_L B` is a field (it is a localization of the domain `L[s] ⊗_L B ≅ B[s]`, finite over
  `L(s)`);
* `isField_of_isReduced_of_subsingleton`: a reduced ring with exactly one prime ideal is a field;
* `IsOpenMap.exists_specializes_of_finite_preimage`: generizations lift along an open map with
  finite fibres.

## References

* [Stacks Project, Tag 0EKA](https://stacks.math.columbia.edu/tag/0EKA)
-/

open TensorProduct Polynomial

namespace Bertini

section ClearDenominators

variable {R P F B : Type*} [CommRing R] [CommRing P] [IsDomain P] [Field F] [Algebra R P]
  [Algebra P F] [Algebra R F] [IsScalarTower R P F] [IsFractionRing P F] [CommRing B]
  [Algebra R B]

/-- Every element of `B ⊗_R F` (`F` the fraction field of `P`) becomes, after multiplication by
`1 ⊗ s` for some nonzero `s ∈ P`, the image of an element of `B ⊗_R P`. -/
lemma exists_mul_mem_range_map_tensor (c : B ⊗[R] F) :
    ∃ s ∈ nonZeroDivisors P, (1 ⊗ₜ algebraMap P F s) * c ∈
      Set.range (Algebra.TensorProduct.map (AlgHom.id R B) (IsScalarTower.toAlgHom R P F)) := by
  let ι := Algebra.TensorProduct.map (AlgHom.id R B) (IsScalarTower.toAlgHom R P F)
  induction c using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | tmul b q =>
    obtain ⟨p, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := P) q
    refine ⟨t, ht, b ⊗ₜ p, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    rw [mul_div_cancel₀]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  | add c c' hc hc' =>
    obtain ⟨s, hs, w, hw⟩ := hc
    obtain ⟨s', hs', w', hw'⟩ := hc'
    refine ⟨s * s', mul_mem hs hs', (1 ⊗ₜ s') * w + (1 ⊗ₜ s) * w', ?_⟩
    rw [map_add, map_mul, map_mul, hw, hw', mul_add]
    simp only [Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom', map_mul]
    rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    rw [mul_comm (algebraMap P F s'), mul_one]

/-- If `B ⊗_R P` is a domain and `B` is flat over `R`, so is `B ⊗_R F` for the fraction field `F`
of `P`. -/
lemma isDomain_tensor_fractionRing [Module.Flat R B] [IsDomain (B ⊗[R] P)] [Nontrivial (B ⊗[R] F)] :
    IsDomain (B ⊗[R] F) := by
  let ι := Algebra.TensorProduct.map (AlgHom.id R B) (IsScalarTower.toAlgHom R P F)
  have hι : Function.Injective ι := by
    have : Function.Injective (LinearMap.lTensor B
        (IsScalarTower.toAlgHom R P F).toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective P F)
    exact this
  have hu (t : P) (ht : t ∈ nonZeroDivisors P) : IsUnit ((1 : B) ⊗ₜ[R] algebraMap P F t) := by
    have ht' : algebraMap P F t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
    have h1 : ((1 : B) ⊗ₜ[R] algebraMap P F t) * (1 ⊗ₜ (algebraMap P F t)⁻¹) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ ht',
        Algebra.TensorProduct.one_def]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {u v} huv ↦ ?_⟩
  obtain ⟨s, hs, u₀, hu₀⟩ := exists_mul_mem_range_map_tensor (P := P) (B := B) u
  obtain ⟨s', hs', v₀, hv₀⟩ := exists_mul_mem_range_map_tensor (P := P) (B := B) v
  have h0 : ι (u₀ * v₀) = 0 := by
    rw [map_mul, hu₀, hv₀]
    calc _ = (1 ⊗ₜ algebraMap P F s) * (1 ⊗ₜ algebraMap P F s') * (u * v) := by ring
      _ = 0 := by rw [huv, mul_zero]
  rw [← map_zero ι] at h0
  rcases mul_eq_zero.mp (hι h0) with h | h
  · left
    rw [h, map_zero] at hu₀
    exact (hu s hs).mul_right_eq_zero.mp hu₀.symm
  · right
    rw [h, map_zero] at hv₀
    exact (hu s' hs').mul_right_eq_zero.mp hv₀.symm

end ClearDenominators

/-- **`L(s) ⊗_L B` is a field** for a finite field extension `B` of `L`: it is a domain (a
localization of `L[s] ⊗_L B ≅ B[s]`) and finite-dimensional over `L(s)`. -/
theorem isField_ratFunc_tensor (L B : Type*) [Field L] [Field B] [Algebra L B]
    [Module.Finite L B] : IsField (RatFunc L ⊗[L] B) := by
  have : IsDomain (B ⊗[L] L[X]) := (polyEquivTensor L B).symm.toMulEquiv.isDomain
  have : Nontrivial (B ⊗[L] RatFunc L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain L B (RatFunc L)
      (algebraMap L B).injective (algebraMap L (RatFunc L)).injective
  have : IsDomain (B ⊗[L] RatFunc L) := isDomain_tensor_fractionRing (R := L) (P := L[X])
  have : IsDomain (RatFunc L ⊗[L] B) :=
    (Algebra.TensorProduct.comm L (RatFunc L) B).toMulEquiv.isDomain
  have : IsArtinianRing (RatFunc L ⊗[L] B) := IsArtinianRing.of_finite (RatFunc L) _
  exact IsArtinianRing.isField_of_isDomain _

end Bertini

/-- A reduced ring with a single prime ideal is a field. -/
theorem isField_of_isReduced_of_subsingleton {A : Type*} [CommRing A] [Nontrivial A]
    [IsReduced A] (h : Subsingleton (PrimeSpectrum A)) : IsField A := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  have hbot : (⊥ : Ideal A) = M := by
    have hnil : nilradical A = ⊥ := nilradical_eq_zero A
    rw [← hnil, nilradical_eq_sInf]
    refine le_antisymm (sInf_le hM.isPrime) (le_sInf fun P hP ↦ ?_)
    have := congrArg PrimeSpectrum.asIdeal
      (Subsingleton.elim (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ⟨P, hP⟩)
    exact this.le
  rw [← hbot] at hM
  exact Ring.isField_iff_maximal_bot.mpr hM

/-- **Generizations lift along an open map with finite fibres**: if `f` is open, `f ⁻¹' {y}` is
finite and `y ⤳ f x`, then `x` is a specialization of a point of `f ⁻¹' {y}`. -/
theorem IsOpenMap.exists_specializes_of_finite_preimage {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : IsOpenMap f) {y : Y} (hfin : (f ⁻¹' {y}).Finite)
    {x : X} (h : y ⤳ f x) : ∃ x' ∈ f ⁻¹' {y}, x' ⤳ x := by
  have hcl : x ∈ closure (f ⁻¹' {y}) := by
    rw [mem_closure_iff]
    intro U hU hxU
    obtain ⟨x', hx'U, hx'⟩ := (specializes_iff_forall_open.mp h) (f '' U) (hf U hU) ⟨x, hxU, rfl⟩
    exact ⟨x', hx'U, hx'⟩
  have : x ∈ ⋃ x' ∈ f ⁻¹' {y}, closure {x'} := by
    rw [← hfin.closure_biUnion, Set.biUnion_of_singleton]
    exact hcl
  obtain ⟨x', hx', hxx'⟩ := Set.mem_iUnion₂.mp this
  exact ⟨x', hx', specializes_iff_mem_closure.mpr hxx'⟩
