/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.OkaRelations
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Finite coefficient equations for polynomial relations

Relations of bounded degree among finitely many polynomials are the kernel of a map
between finite free modules over the coefficient ring. This is the finite system of
linear equations used to descend the Oka coherence argument by one variable after
Weierstrass reduction (Demailly, *Complex Analytic and Differential Geometry*, II.3.19).
The construction is algebraic and is valid over an arbitrary commutative ring.
-/

noncomputable section

open Finset
open scoped Polynomial

namespace Polynomial

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]

open Classical in
/-- The polynomial combination encoded by a finite array of coefficient vectors. -/
def boundedRelationCombination (P : ι → R[X]) (d : ℕ) :
    (ι → Fin (d + 1) → R) →ₗ[R] R[X] where
  toFun a := ∑ i, ofFn (d + 1) (a i) * P i
  map_add' a b := by
    simp only [Pi.add_apply, map_add, add_mul, sum_add_distrib]
  map_smul' r a := by
    simp only [Pi.smul_apply, map_smul, smul_mul_assoc, smul_sum, RingHom.id_apply]

open Classical in
/-- The finite coefficient equations for a bounded-degree polynomial relation. -/
def boundedRelationEquations (P : ι → R[X]) (d μ : ℕ) :
    (ι → Fin (d + 1) → R) →ₗ[R] (Fin (d + μ + 1) → R) :=
  (toFn (d + μ + 1)).comp (boundedRelationCombination P d)

@[simp]
lemma boundedRelationEquations_apply (P : ι → R[X]) (d μ : ℕ)
    (a : ι → Fin (d + 1) → R) (j : Fin (d + μ + 1)) :
    boundedRelationEquations P d μ a j = (boundedRelationCombination P d a).coeff j := rfl

lemma natDegree_boundedRelationCombination_le (P : ι → R[X]) (d μ : ℕ)
    (hP : ∀ i, (P i).natDegree ≤ μ) (a : ι → Fin (d + 1) → R) :
    (boundedRelationCombination P d a).natDegree ≤ d + μ := by
  classical
  apply natDegree_sum_le_of_forall_le
  intro i hi
  exact natDegree_mul_le_of_le (Nat.le_of_lt_succ (ofFn_natDegree_lt (by omega) (a i))) (hP i)

/-- All polynomial relation equations are detected by finitely many coefficients. -/
theorem boundedRelationEquations_eq_zero_iff (P : ι → R[X]) (d μ : ℕ)
    (hP : ∀ i, (P i).natDegree ≤ μ) (a : ι → Fin (d + 1) → R) :
    boundedRelationEquations P d μ a = 0 ↔ boundedRelationCombination P d a = 0 := by
  constructor
  · intro h
    ext j
    by_cases hj : j < d + μ + 1
    · exact congrFun h ⟨j, hj⟩
    · rw [coeff_eq_zero_of_natDegree_lt
        ((natDegree_boundedRelationCombination_le P d μ hP a).trans_lt (by omega)), coeff_zero]
  · intro h
    ext j
    rw [boundedRelationEquations_apply, h, coeff_zero]
    rfl

open Classical in
/-- In vector form, bounded-degree polynomial relations are exactly the kernel of the
finite coefficient-equation map. -/
theorem mem_ker_boundedRelationEquations_iff (P : ι → R[X]) (d μ : ℕ)
    (hP : ∀ i, (P i).natDegree ≤ μ) (a : ι → Fin (d + 1) → R) :
    a ∈ (boundedRelationEquations P d μ).ker ↔
      (fun i ↦ ofFn (d + 1) (a i)) ∈ AnalyticGeometry.relationModule P :=
  boundedRelationEquations_eq_zero_iff P d μ hP a

open Classical in
/-- The polynomial encoded by a finite vector commutes with a coefficient homomorphism. -/
lemma map_ofFn {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ) (a : Fin n → R) :
    (ofFn n a).map φ = ofFn n (fun i ↦ φ (a i)) := by
  ext j
  by_cases hj : j < n
  · simp [hj]
  · simp [Nat.le_of_not_gt hj]

/-- The bounded relation combination commutes with a coefficient homomorphism. -/
lemma boundedRelationCombination_map {S : Type*} [CommRing S] (φ : R →+* S)
    (P : ι → R[X]) (d : ℕ) (a : ι → Fin (d + 1) → R) :
    (boundedRelationCombination P d a).map φ =
      boundedRelationCombination (fun i ↦ (P i).map φ) d (fun i l ↦ φ (a i l)) := by
  classical
  simp only [boundedRelationCombination, LinearMap.coe_mk, AddHom.coe_mk,
    Polynomial.map_sum, Polynomial.map_mul, map_ofFn]

/-- The finite coefficient equations commute with restriction or any other coefficient
homomorphism. This is the compatibility needed for their use as a sheaf morphism. -/
lemma boundedRelationEquations_map {S : Type*} [CommRing S] (φ : R →+* S)
    (P : ι → R[X]) (d μ : ℕ) (a : ι → Fin (d + 1) → R) (j : Fin (d + μ + 1)) :
    φ (boundedRelationEquations P d μ a j) =
      boundedRelationEquations (fun i ↦ (P i).map φ) d μ (fun i l ↦ φ (a i l)) j := by
  rw [boundedRelationEquations_apply, boundedRelationEquations_apply,
    ← Polynomial.coeff_map, boundedRelationCombination_map]

open Classical in
/-- Generators of the finite coefficient-equation kernel generate every bounded-degree
polynomial relation, even after evaluation in a larger coefficient ring. -/
theorem eval_relation_mem_span_of_coefficient_generators
    {S : Type*} [CommRing S] (φ : R[X] →+* S)
    (P : ι → R[X]) (d μ : ℕ) (hP : ∀ i, (P i).natDegree ≤ μ)
    {κ : Type*} [Finite κ] (B : κ → ι → Fin (d + 1) → R)
    (hB : (boundedRelationEquations P d μ).ker = Submodule.span R (Set.range B))
    (Q : ι → R[X]) (hQ : ∀ i, (Q i).natDegree ≤ d)
    (hrel : Q ∈ AnalyticGeometry.relationModule P) :
    (fun i ↦ φ (Q i)) ∈ Submodule.span S
      (Set.range (fun k i ↦ φ (ofFn (d + 1) (B k i)))) := by
  classical
  let := Fintype.ofFinite κ
  let c : ι → Fin (d + 1) → R := fun i ↦ toFn (d + 1) (Q i)
  have hc (i : ι) : ofFn (d + 1) (c i) = Q i :=
    ofFn_comp_toFn_eq_id_of_natDegree_lt (Nat.lt_succ_of_le (hQ i))
  have hker : c ∈ (boundedRelationEquations P d μ).ker := by
    rw [mem_ker_boundedRelationEquations_iff P d μ hP]
    simpa only [hc] using hrel
  rw [hB, Submodule.mem_span_range_iff_exists_fun] at hker
  obtain ⟨t, ht⟩ := hker
  rw [Submodule.mem_span_range_iff_exists_fun]
  refine ⟨fun k ↦ φ (C (t k)), ?_⟩
  funext i
  have hi := congrArg (fun z : ι → Fin (d + 1) → R ↦ ofFn (d + 1) (z i)) ht
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, hc] at hi
  have hφ := congrArg φ hi
  simp only [map_sum, smul_eq_C_mul, map_mul] at hφ
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hφ

end Polynomial
