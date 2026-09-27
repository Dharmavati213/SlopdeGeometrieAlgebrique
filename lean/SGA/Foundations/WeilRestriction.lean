/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Weil restriction along a finite free algebra

Let `T` be an `A`-algebra which is free of finite rank as an `A`-module, with basis `b`, and let
`B = A[x_σ]/(r_τ)` be a finitely presented `A`-algebra. The functor
`C ↦ Hom_A(B, C ⊗_A T)` on `A`-algebras is represented by the finitely presented `A`-algebra
`Algebra.WeilRestriction b r = A[x_{a,i} | a ∈ σ, i ∈ ι]/(coordinates of r(∑ᵢ x_{a,i} ⊗ bᵢ))`:
it is the Weil restriction along `Spec T → Spec A` of `Spec (T ⊗_A B)`
(Bosch–Lütkebohmert–Raynaud, *Néron models*, 7.6). If `B` is formally étale, so is its Weil
restriction, since `C ⊗_A T → (C/I) ⊗_A T` has square-zero kernel when `I` does.

## Main definitions

* `Algebra.WeilRestriction b r`: the representing algebra;
* `Algebra.WeilRestriction.homEquiv`: `(WeilRestriction b r →ₐ[A] C) ≃ (B →ₐ[A] C ⊗[A] T)`,
  natural in `C` (`Algebra.WeilRestriction.homEquiv_comp`);
* `Algebra.WeilRestriction.formallyEtale`, `Algebra.WeilRestriction.etale`.
-/

open TensorProduct MvPolynomial

noncomputable section

namespace Algebra

variable {A T : Type*} [CommRing A] [CommRing T] [Algebra A T]

section Basis

variable {ι : Type*} (b : Module.Basis ι A T)

/-- The coordinates of an element of `C ⊗[A] T` in the basis `1 ⊗ b` are natural in `C`. -/
lemma TensorProduct.basis_repr_map {C C' : Type*} [CommRing C] [CommRing C'] [Algebra A C]
    [Algebra A C'] (g : C →ₐ[A] C') (z : C ⊗[A] T) (j : ι) :
    (TensorProduct.basis C' b).repr (TensorProduct.map g (AlgHom.id A T) z) j =
      g ((TensorProduct.basis C b).repr z j) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul c t =>
    simp only [TensorProduct.map_tmul, AlgHom.coe_id, id_eq, TensorProduct.basis_repr_tmul,
      Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, map_mul, AlgHom.commutes]
  | add x y hx hy => simp [hx, hy]

end Basis

section QuotientHom

variable {σ τ : Type*} (r : τ → MvPolynomial σ A)

/-- Maps out of `A[x_σ]/(r_τ)` are the solutions of the equations `r`. -/
def quotientHomEquiv (D : Type*) [CommRing D] [Algebra A D] :
    (MvPolynomial σ A ⧸ Ideal.span (Set.range r) →ₐ[A] D) ≃
      {y : σ → D // ∀ l, aeval y (r l) = 0} where
  toFun φ := ⟨fun a ↦ φ (Ideal.Quotient.mk _ (X a)), fun l ↦ by
    have h : aeval (fun a ↦ φ (Ideal.Quotient.mk _ (X a))) =
        φ.comp (Ideal.Quotient.mkₐ A (Ideal.span (Set.range r))) :=
      MvPolynomial.algHom_ext fun a ↦ by simp
    rw [h, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self l)), map_zero]⟩
  invFun y := Ideal.Quotient.liftₐ _ (aeval y.1) fun p hp ↦ by
    refine Submodule.span_induction ?_ (by simp) (fun _ _ _ _ h₁ h₂ ↦ by simp [h₁, h₂])
      (fun a _ _ h ↦ by simp [h]) hp
    rintro _ ⟨l, rfl⟩
    exact y.2 l
  left_inv φ := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro a
    exact aeval_X _ a
  right_inv y := by
    ext a
    exact aeval_X _ a

end QuotientHom

namespace WeilRestriction

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι A T) {σ τ : Type*}
  (r : τ → MvPolynomial σ A)

/-- The universal family `(∑ᵢ x_{a,i} ⊗ bᵢ)_{a ∈ σ}` of elements of `A[x_{σ × ι}] ⊗[A] T`. -/
def universalElt (a : σ) : MvPolynomial (σ × ι) A ⊗[A] T :=
  ∑ i, X (a, i) ⊗ₜ b i

/-- The equations of the Weil restriction: the coordinates of `r(∑ᵢ x_{a,i} ⊗ bᵢ)`. -/
def equations (lj : τ × ι) : MvPolynomial (σ × ι) A :=
  (TensorProduct.basis (MvPolynomial (σ × ι) A) b).repr (aeval (universalElt b) (r lj.1)) lj.2

variable {C : Type*} [CommRing C] [Algebra A C]

/-- The family `(∑ᵢ c_{a,i} ⊗ bᵢ)_{a ∈ σ}` of elements of `C ⊗[A] T`. -/
def elt (c : σ × ι → C) (a : σ) : C ⊗[A] T :=
  ∑ i, c (a, i) ⊗ₜ b i

lemma map_universalElt (c : σ × ι → C) (a : σ) :
    TensorProduct.map (aeval c) (AlgHom.id A T) (universalElt b a) = elt b c a := by
  simp [universalElt, elt, map_sum]

lemma aeval_equations (c : σ × ι → C) (l : τ) (j : ι) :
    aeval c (equations b r (l, j)) =
      (TensorProduct.basis C b).repr (aeval (elt b c) (r l)) j := by
  rw [equations, ← TensorProduct.basis_repr_map, comp_aeval_apply]
  simp only [map_universalElt]

lemma elt_eq_sum_smul (c : σ × ι → C) (a : σ) :
    elt b c a = ∑ i, c (a, i) • TensorProduct.basis C b i := by
  simp only [elt, TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

lemma repr_elt (c : σ × ι → C) (a : σ) (i : ι) :
    (TensorProduct.basis C b).repr (elt b c a) i = c (a, i) := by
  rw [elt_eq_sum_smul, Module.Basis.repr_sum_self]

lemma elt_repr (y : σ → C ⊗[A] T) :
    elt b (fun ai ↦ (TensorProduct.basis C b).repr (y ai.1) ai.2) = y := by
  funext a
  rw [elt_eq_sum_smul]
  exact (TensorProduct.basis C b).sum_repr (y a)

variable (C) in
/-- The solutions of the equations of the Weil restriction in `C` are the solutions of `r` in
`C ⊗[A] T`. -/
def solutionsEquiv :
    {c : σ × ι → C // ∀ lj, aeval c (equations b r lj) = 0} ≃
      {y : σ → C ⊗[A] T // ∀ l, aeval y (r l) = 0} where
  toFun c := ⟨elt b c.1, fun l ↦ (TensorProduct.basis C b).repr.injective <| by
    ext j
    rw [← aeval_equations, c.2, map_zero, Finsupp.zero_apply]⟩
  invFun y := ⟨fun ai ↦ (TensorProduct.basis C b).repr (y.1 ai.1) ai.2, fun lj ↦ by
    rw [aeval_equations, elt_repr, y.2, map_zero, Finsupp.zero_apply]⟩
  left_inv c := by
    ext ai
    exact repr_elt b c.1 ai.1 ai.2
  right_inv y := Subtype.ext (elt_repr b y.1)

end WeilRestriction

variable {ι : Type*} [Fintype ι] (b : Module.Basis ι A T) {σ τ : Type*}
  (r : τ → MvPolynomial σ A)

/-- The Weil restriction along `A → T` (free with basis `b`) of `T ⊗[A] A[x_σ]/(r)`: it represents
the functor `C ↦ Hom_A(A[x_σ]/(r), C ⊗[A] T)` (`Algebra.WeilRestriction.homEquiv`). -/
def WeilRestriction : Type _ :=
  MvPolynomial (σ × ι) A ⧸ Ideal.span (Set.range (WeilRestriction.equations b r))

namespace WeilRestriction

instance : CommRing (WeilRestriction b r) :=
  inferInstanceAs (CommRing (MvPolynomial (σ × ι) A ⧸ Ideal.span _))

instance : Algebra A (WeilRestriction b r) :=
  inferInstanceAs (Algebra A (MvPolynomial (σ × ι) A ⧸ Ideal.span _))

variable (C : Type*) [CommRing C] [Algebra A C]

/-- The universal property of the Weil restriction. -/
def homEquiv : (WeilRestriction b r →ₐ[A] C) ≃
    (MvPolynomial σ A ⧸ Ideal.span (Set.range r) →ₐ[A] C ⊗[A] T) :=
  (quotientHomEquiv (equations b r) C).trans
    ((solutionsEquiv b r C).trans (quotientHomEquiv r (C ⊗[A] T)).symm)

variable {C} in
lemma homEquiv_apply_mk_X (ψ : WeilRestriction b r →ₐ[A] C) (a : σ) :
    homEquiv b r C ψ (Ideal.Quotient.mk _ (X a)) =
      ∑ i, ψ (Ideal.Quotient.mk _ (X (a, i))) ⊗ₜ b i :=
  aeval_X _ a

/-- Naturality of `homEquiv`. -/
lemma homEquiv_comp {C' : Type*} [CommRing C'] [Algebra A C'] (g : C →ₐ[A] C')
    (ψ : WeilRestriction b r →ₐ[A] C) :
    homEquiv b r C' (g.comp ψ) =
      (TensorProduct.map g (AlgHom.id A T)).comp (homEquiv b r C ψ) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [homEquiv_apply_mk_X, homEquiv_apply_mk_X, map_sum]
  simp
  rfl

variable [Finite σ] [Finite τ]

instance finitePresentation : FinitePresentation A (WeilRestriction b r) :=
  FinitePresentation.quotient (Submodule.fg_span (Set.finite_range _))

/-- The Weil restriction of a formally étale algebra is formally étale. -/
instance formallyEtale [FormallyEtale A (MvPolynomial σ A ⧸ Ideal.span (Set.range r))] :
    FormallyEtale A (WeilRestriction b r) := by
  rw [FormallyEtale.iff_comp_bijective]
  intro C _ _ I hI
  let S := C ⊗[A] T
  let J : Ideal S := I.map (algebraMap C S)
  have hJ : J ^ 2 = ⊥ := by rw [← Ideal.map_pow, hI, Ideal.map_bot]
  let e : (C ⧸ I) ⊗[A] T ≃ₐ[A] S ⧸ J :=
    TensorProduct.quotientTensorEquiv (R := A) A T C I
  let π : S →ₐ[A] (C ⧸ I) ⊗[A] T := TensorProduct.map (Ideal.Quotient.mkₐ A I) (AlgHom.id A T)
  have he : (e : _ →ₐ[A] _).comp π = Ideal.Quotient.mkₐ A J := by
    ext <;> rfl
  have key : Function.Bijective
      (fun φ : MvPolynomial σ A ⧸ Ideal.span (Set.range r) →ₐ[A] S ↦ π.comp φ) := by
    have h₁ := FormallyEtale.comp_bijective A (MvPolynomial σ A ⧸ Ideal.span (Set.range r)) J hJ
    have h₂ : Function.Bijective
        (fun ψ : MvPolynomial σ A ⧸ Ideal.span (Set.range r) →ₐ[A] S ⧸ J ↦
          (e.symm : S ⧸ J →ₐ[A] (C ⧸ I) ⊗[A] T).comp ψ) := by
      refine ⟨fun ψ₁ ψ₂ h ↦ AlgHom.ext fun x ↦ e.symm.injective ?_,
        fun ψ ↦ ⟨(e : (C ⧸ I) ⊗[A] T →ₐ[A] S ⧸ J).comp ψ, AlgHom.ext fun x ↦ by simp⟩⟩
      exact DFunLike.congr_fun h x
    convert h₂.comp h₁ using 1
    funext φ
    ext x
    simp [← he]
  have hsq : (homEquiv b r (C ⧸ I)) ∘ (Ideal.Quotient.mkₐ A I).comp =
      (fun φ ↦ π.comp φ) ∘ (homEquiv b r C) :=
    funext fun ψ ↦ homEquiv_comp b r C _ ψ
  rw [← (homEquiv b r (C ⧸ I)).bijective.of_comp_iff', hsq]
  exact key.comp (homEquiv b r C).bijective

instance etale [FormallyEtale A (MvPolynomial σ A ⧸ Ideal.span (Set.range r))] :
    Etale A (WeilRestriction b r) where

end WeilRestriction

end Algebra
