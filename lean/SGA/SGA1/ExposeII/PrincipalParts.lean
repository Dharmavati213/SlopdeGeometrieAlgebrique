/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# SGA 1, Exposé II, remarks II.4.18: principal parts along a section

The sheaves of principal parts `𝒫ⁿ_{X/S} = 𝒪_{X ×_S X}/𝓘^{n+1}` (Exposé I, §1; on affines
`(S ⊗_R S)/I^{n+1}` with `I = KaehlerDifferential.ideal R S`) are `𝒪_X`-algebras through the
first projection. SGA's
formula (4.4) computes their pull-back along a section `s` of `X` over `S` with ideal `𝒥`:
`s^*(𝒫ⁿ_{X/S}) = 𝒪_X/𝒥^{n+1}`. We prove it in the affine case.

The characterisation "smooth = flat + differentially smooth", and that of differential smoothness
by `𝒫^∞ ≅ 𝒪_X[[t₁,…,tₙ]]` (affine form, for global generators of the ideal of the diagonal), are
in `SGA.SGA1.ExposeII.DifferentiallySmooth`. Not formalized: the sheaves `𝒫ⁿ`, `𝒫^∞` themselves,
the characterisation through `S(Ω¹) ≅ gr(𝒫^∞)`, the second algebra structure `dⁿ` and
differential operators.
-/

universe u

open TensorProduct

namespace SGA.SGA1.ExposeII

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (σ : S →ₐ[R] R)

/-- The kernel of the diagonal is sent onto the ideal of the section `σ` by
`a ⊗ b ↦ σ(a) b`. -/
lemma map_diagonal_eq_ker (ψ : S ⊗[R] S →+* S)
    (hψ : ∀ a b, ψ (a ⊗ₜ b) = algebraMap R S (σ a) * b) :
    (KaehlerDifferential.ideal R S).map ψ = RingHom.ker σ := by
  rw [← KaehlerDifferential.span_range_eq_ideal, Ideal.map_span, ← Set.range_comp]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨a, rfl⟩
    simp [hψ, RingHom.mem_ker]
  · intro j hj
    have : j = (ψ ∘ fun s : S ↦ (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) j := by
      simp [hψ, (RingHom.mem_ker).mp hj]
    rw [this]
    exact Ideal.subset_span ⟨j, rfl⟩


/-- Formula (4.4) of the remarks II.4.18: for a section `s` of `X = Spec S` over `Spec R`, given
by `σ : S → R`, with ideal `J = ker σ`, one has `s^*(𝒫ⁿ_{X/S}) ≅ 𝒪_X/J^{n+1}`, i.e.
`R ⊗_S Pⁿ ≅ S ⧸ J^{n+1}` where `Pⁿ = (S ⊗_R S)/I^{n+1}` is an `S`-algebra through the first
factor. For `R = k` a field and `σ` a rational point `x`, this is (4.5):
`𝒫ⁿ(x) ≅ 𝒪_x/𝔪_x^{n+1}`, which justifies the name *sheaf of principal parts*. -/
theorem nonempty_principalParts_baseChange_section (n : ℕ) :
    letI := σ.toRingHom.toAlgebra
    Nonempty (R ⊗[S] ((S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (n + 1)) ≃ₐ[R]
      S ⧸ RingHom.ker σ ^ (n + 1)) := by
  let := σ.toRingHom.toAlgebra
  have : IsScalarTower R S R := .of_algebraMap_eq fun r ↦ (σ.commutes r).symm
  set I := KaehlerDifferential.ideal R S
  let g : S ⊗[R] S →ₐ[S] (S ⊗[R] S) ⧸ KaehlerDifferential.ideal R S ^ (n + 1) :=
    Ideal.Quotient.mkₐ S _
  have hg : Function.Surjective g := Ideal.Quotient.mkₐ_surjective S _
  let φ := Algebra.TensorProduct.map (AlgHom.id R R) g
  have hφ : Function.Surjective φ := Algebra.TensorProduct.map_surjective _ _
    Function.surjective_id hg
  let ι : S ⊗[R] S →+* R ⊗[S] (S ⊗[R] S) :=
    (Algebra.TensorProduct.includeRight : S ⊗[R] S →ₐ[S] R ⊗[S] (S ⊗[R] S)).toRingHom
  have hker : RingHom.ker φ = (I ^ (n + 1)).map ι := by
    change RingHom.ker (Algebra.TensorProduct.map (AlgHom.id S R) g) = _
    rw [Algebra.TensorProduct.lTensor_ker _ hg]
    congr 1
    exact Ideal.mk_ker
  let e : R ⊗[S] (S ⊗[R] S) ≃ₐ[R] S :=
    (Algebra.TensorProduct.cancelBaseChange R S R R S).trans (Algebra.TensorProduct.lid R S)
  have he (a b : S) : e (1 ⊗ₜ (a ⊗ₜ b)) = algebraMap R S (σ a) * b := by
    simp [e, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let e' : R ⊗[S] (S ⊗[R] S) →+* S := e.toRingEquiv.toRingHom
  have hJ : RingHom.ker σ ^ (n + 1) = (RingHom.ker φ).map e' := by
    rw [hker, Ideal.map_map, Ideal.map_pow]
    congr 1
    exact (map_diagonal_eq_ker σ (e'.comp ι) fun a b ↦ he a b).symm
  exact ⟨(Ideal.quotientKerAlgEquivOfSurjective hφ).symm.trans
    (Ideal.quotientEquivAlg _ _ e hJ)⟩

end SGA.SGA1.ExposeII
