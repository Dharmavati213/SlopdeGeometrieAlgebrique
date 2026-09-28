/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Discriminants of étale algebras (for XI.1.1)

An étale algebra `B` over a ring `R`, free with basis `e`, has invertible discriminant
`disc_R(e)` (its trace form is perfect); this is the algebraic form of "an étale covering is
unramified". We prove what is used for `π₁(ℙ¹) = 1`:

* `Algebra.discr_baseChange`: the discriminant is compatible with base change;
* `discr_ne_zero_of_isSepClosed`: over a separably closed field `k`, an étale algebra is
  `k × ⋯ × k`, so its discriminant in any basis is nonzero;
* `exists_discr_eq_C`: over `k[X]`, `k` any field, the discriminant of a finite free étale algebra
  is a nonzero constant (it has no zero in an algebraic closure, since the fibres are étale).
-/

open Polynomial TensorProduct

namespace SGA.SGA1.ExposeXI

section BaseChange

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The trace is compatible with base change. -/
lemma trace_baseChange_tmul [Module.Free R B] [Module.Finite R B] (b : B) :
    Algebra.trace A (A ⊗[R] B) (1 ⊗ₜ b) = algebraMap R A (Algebra.trace R B b) := by
  have h : Algebra.lmul A (A ⊗[R] B) (1 ⊗ₜ b) =
      (Algebra.lmul R B b).baseChange A := by
    refine TensorProduct.AlgebraTensorModule.ext fun a b' ↦ ?_
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange, Algebra.trace_apply]

/-- The discriminant is compatible with base change. -/
lemma discr_baseChange {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι R B) :
    Algebra.discr A (Algebra.TensorProduct.basis A e) = algebraMap R A (Algebra.discr R e) := by
  have : Module.Free R B := Module.Free.of_basis e
  have : Module.Finite R B := Module.Finite.of_basis e
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, trace_baseChange_tmul]

end BaseChange

section Field

variable (k : Type*) [Field k]

lemma trace_pi_apply (P : Type*) [Fintype P] (y : P → k) :
    Algebra.trace k (P → k) y = ∑ p, y p := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun k P), Matrix.trace]
  refine Finset.sum_congr rfl fun p _ ↦ ?_
  rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, Pi.basisFun_repr, Pi.basisFun_apply,
    Pi.mul_apply, Pi.single_eq_same, mul_one]

lemma trace_pi_single_mul (P : Type*) [Finite P] [DecidableEq P] (x : P → k) (p : P) :
    Algebra.trace k (P → k) (Pi.single p 1 * x) = x p := by
  have := Fintype.ofFinite P
  rw [trace_pi_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [Pi.single_eq_of_ne hq]
  · simp

lemma traceForm_pi_nondegenerate (P : Type*) [Finite P] :
    (Algebra.traceForm k (P → k)).Nondegenerate := by
  classical
  refine ⟨fun x hx ↦ funext fun p ↦ ?_, fun x hx ↦ funext fun p ↦ ?_⟩
  · have := hx (Pi.single p 1)
    rwa [Algebra.traceForm_apply, mul_comm, trace_pi_single_mul] at this
  · have := hx (Pi.single p 1)
    rwa [Algebra.traceForm_apply, trace_pi_single_mul] at this

variable {k}

/-- Over a separably closed field, the discriminant of an étale algebra is nonzero in any
basis. -/
theorem discr_ne_zero_of_isSepClosed [IsSepClosed k] {B : Type*} [CommRing B] [Algebra k B]
    [Algebra.Etale k B] {ι : Type*} [Fintype ι] [DecidableEq ι] (v : Module.Basis ι k B) :
    Algebra.discr k v ≠ 0 := by
  have : Module.Finite k B := Module.Finite.of_basis v
  have : IsArtinianRing B := isArtinian_of_tower k inferInstance
  let f := Algebra.FormallyEtale.equivPiOfIsSepClosed k B
  have : Fintype (PrimeSpectrum B) := Fintype.ofFinite _
  classical
  rw [Algebra.discr_eq_discr_of_algEquiv v f]
  have hv : ⇑f ∘ ⇑v = ⇑(v.map f.toLinearEquiv) := by
    funext i
    simp
  rw [hv, Algebra.discr_def, Algebra.traceMatrix_of_basis,
    ← LinearMap.BilinForm.nondegenerate_iff_det_ne_zero]
  exact traceForm_pi_nondegenerate k _

/-- Over `k[X]` (`k` any field), the discriminant of a finite free étale algebra is a nonzero
constant: its value at a point `a` of an algebraic closure of `k` is the discriminant of the fibre
at `X = a`, an étale algebra over an algebraically closed field. -/
theorem exists_discr_eq_C {B : Type*} [CommRing B] [Algebra k[X] B]
    [Algebra.Etale k[X] B] {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Module.Basis ι k[X] B) :
    ∃ c : k, c ≠ 0 ∧ Algebra.discr k[X] e = Polynomial.C c := by
  let K := AlgebraicClosure k
  have heval : ∀ a : K, (Algebra.discr k[X] e).eval₂ (algebraMap k K) a ≠ 0 := by
    intro a
    let _ : Algebra k[X] K := (Polynomial.eval₂RingHom (algebraMap k K) a).toAlgebra
    have h := discr_baseChange (A := K) e
    rw [← show algebraMap k[X] K (Algebra.discr k[X] e) =
      (Algebra.discr k[X] e).eval₂ (algebraMap k K) a from rfl, ← h]
    exact discr_ne_zero_of_isSepClosed _
  have hne : Algebra.discr k[X] e ≠ 0 := fun h ↦ heval 0 (by rw [h, eval₂_zero])
  have hdeg : (Algebra.discr k[X] e).degree = 0 := by
    by_contra hd
    obtain ⟨a, ha⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective (algebraMap k K)
      (algebraMap k K).injective _ hd
    exact heval a ha
  refine ⟨(Algebra.discr k[X] e).coeff 0, fun h0 ↦ hne ?_, eq_C_of_degree_eq_zero hdeg⟩
  rw [eq_C_of_degree_eq_zero hdeg, h0, map_zero]

end Field

end SGA.SGA1.ExposeXI
