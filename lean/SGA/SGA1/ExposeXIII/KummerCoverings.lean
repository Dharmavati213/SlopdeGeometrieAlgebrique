/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Extension.Presentation.Submersive
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# SGA 1, Exposé XIII, Appendix I: Kummer coverings

The coverings of Appendix I are the *Kummer coverings*
`U' = U[T₁, …, T_r]/(T₁^{n₁} - f₁, …, T_r^{n_r} - f_r)`. Here `U = Spec B` is affine and
`KummerAlgebra n f` is the ring `B[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. We prove:

* XIII.5.1 (étale part, via I.7.4): if the `fᵢ` and the `nᵢ` are units, `U' → U` is étale;
  the Jacobian of the presentation is `∏ nᵢ Tᵢ^{nᵢ-1}`. The one-variable version
  `etale_adjoinRoot_X_pow_sub_C` holds more generally for any monic separable polynomial.
* XIII.5.3.0: `μ_{n₁} × ⋯ × μ_{n_r}` acts on `U'` by `Tᵢ ↦ ξᵢ Tᵢ`, and this is the whole
  automorphism group when `U'` is connected (a domain) and `B` contains primitive `nᵢ`-th roots
  of unity (as it does in SGA, `U` being the complement of a divisor in a strictly local scheme
  and the `nᵢ` prime to the residue characteristic).
* XIII.5.2 for Kummer coverings: if `V = U[Sᵢ]/(Sᵢ^{eᵢ} - fᵢ)` with `eᵢ mᵢ = nᵢ`, then over
  `U'`, where `fᵢ = Tᵢ^{nᵢ}` with `Tᵢ` invertible, `V'` is isomorphic to the restriction of
  `X'[Wᵢ]/(Wᵢ^{eᵢ} - 1)`, which is étale over `X'` as soon as the `eᵢ` are invertible: the
  covering `V'` of `U'` extends to an étale covering of `X'`.
* the base change of `B[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` along `B → A` is `A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`, so that
  SGA's `U' = U ×_X X'` is again a Kummer covering.
-/

universe u v w

namespace SGA.SGA1.ExposeXIII

section AdjoinRoot

open Polynomial

variable {R : Type u} [CommRing R]

/-- I.7.4, as used in XIII.5.1: `R[T]/(f)` is étale over `R` when `f` is monic and separable
(`f` and `f'` generate the unit ideal). -/
theorem etale_adjoinRoot_of_separable {f : R[X]} (hm : f.Monic) (hs : f.Separable) :
    Algebra.Etale R (AdjoinRoot f) := by
  obtain ⟨a, b, hab⟩ := hs
  let P : StandardEtalePair R :=
    { f := f, monic_f := hm, g := 1, cond := ⟨b, a, 0, by rw [pow_zero]; linear_combination hab⟩ }
  have hunit : Submonoid.powers (AdjoinRoot.mk f 1) ≤ IsUnit.submonoid (AdjoinRoot f) := by
    rw [map_one, Submonoid.powers_one]
    exact bot_le
  let e : AdjoinRoot f ≃ₐ[R] Localization.Away (AdjoinRoot.mk f 1) :=
    (IsLocalization.atUnits (AdjoinRoot f) _ hunit).restrictScalars R
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans e.symm)

/-- XIII.5.1, étale part, one variable: `R[T]/(Tⁿ - u)` is étale over `R` when `n` and `u` are
units of `R`. -/
theorem etale_adjoinRoot_X_pow_sub_C {n : ℕ} (hn : IsUnit (n : R)) (u : Rˣ) :
    Algebra.Etale R (AdjoinRoot (X ^ n - C (u : R))) := by
  refine etale_adjoinRoot_of_separable ?_ (separable_X_pow_sub_C_unit u hn)
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · have : Subsingleton R := subsingleton_of_zero_eq_one (by simpa using hn)
    exact monic_of_subsingleton _
  · exact monic_X_pow_sub_C _ hpos.ne'

open scoped KummerExtension in
/-- XIII.5.3.0 for `r = 1` at the generic point (mathlib): if `K` contains a primitive `n`-th root
of unity and `Tⁿ - a` is irreducible, the automorphism group of `K[ⁿ√a]` is `μ_n(K)`. -/
noncomputable def rootsOfUnityEquivAutAdjoinRoot {K : Type u} [Field K] {n : ℕ} [NeZero n]
    (hζ : (primitiveRoots n K).Nonempty) {a : K} (H : Irreducible (X ^ n - C a)) :
    rootsOfUnity n K ≃* (K[n√a] ≃ₐ[K] K[n√a]) :=
  autAdjoinRootXPowSubCEquiv hζ H

end AdjoinRoot

open MvPolynomial
open scoped TensorProduct

variable {B : Type u} [CommRing B] {ι : Type v}

/-- The ring `B[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` of the Kummer covering `U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` of
`U = Spec B` (XIII.5.1, XIII.5.3.0). -/
abbrev KummerAlgebra (n : ι → ℕ) (f : ι → B) : Type (max u v) :=
  MvPolynomial ι B ⧸ Ideal.span (Set.range fun i ↦ (X i ^ n i - C (f i) : MvPolynomial ι B))

namespace KummerAlgebra

variable (n : ι → ℕ) (f : ι → B)

/-- The class of `Tᵢ`. -/
noncomputable def T (i : ι) : KummerAlgebra n f := Ideal.Quotient.mk _ (X i)

theorem T_pow (i : ι) : T n f i ^ n i = algebraMap B _ (f i) := by
  rw [T, ← map_pow, ← sub_eq_zero, IsScalarTower.algebraMap_apply B (MvPolynomial ι B),
    Ideal.Quotient.algebraMap_eq, ← map_sub, MvPolynomial.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨i, rfl⟩

variable {n f} in
theorem algHom_ext {A : Type*} [Semiring A] [Algebra B A] {φ ψ : KummerAlgebra n f →ₐ[B] A}
    (h : ∀ i, φ (T n f i) = ψ (T n f i)) : φ = ψ :=
  Ideal.Quotient.algHom_ext _ (MvPolynomial.algHom_ext h)

variable {n f} in
/-- The `B`-algebra map out of `B[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` sending `Tᵢ` to `xᵢ`, when `xᵢ^{nᵢ} = fᵢ`. -/
noncomputable def lift {A : Type*} [CommRing A] [Algebra B A] (x : ι → A)
    (hx : ∀ i, x i ^ n i = algebraMap B A (f i)) : KummerAlgebra n f →ₐ[B] A :=
  Ideal.Quotient.liftₐ _ (aeval x) fun a ha ↦ by
    induction ha using Submodule.span_induction with
    | mem _ h => obtain ⟨i, rfl⟩ := h; simp [hx]
    | zero => simp
    | add _ _ _ _ h₁ h₂ => simp [h₁, h₂]
    | smul c _ _ h => simp [h]

@[simp]
theorem lift_T {A : Type*} [CommRing A] [Algebra B A] (x : ι → A)
    (hx : ∀ i, x i ^ n i = algebraMap B A (f i)) (i : ι) : lift x hx (T n f i) = x i := by
  change aeval x (X i) = x i
  simp

theorem isUnit_T {n : ι → ℕ} {f : ι → B} {i : ι} (hn : 0 < n i) (hf : IsUnit (f i)) :
    IsUnit (T n f i) :=
  (isUnit_pow_iff hn.ne').mp (T_pow n f i ▸ hf.map _)

/-- XIII.5.3.0: `ξ` acts by `Tᵢ ↦ ξᵢ Tᵢ`. -/
noncomputable def scale (ξ : ∀ i, rootsOfUnity (n i) B) :
    KummerAlgebra n f →ₐ[B] KummerAlgebra n f :=
  lift (fun i ↦ algebraMap B _ ((ξ i : Bˣ) : B) * T n f i) fun i ↦ by
    have h : ((ξ i : Bˣ) : B) ^ n i = 1 := by
      rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).mp (ξ i).2, Units.val_one]
    rw [mul_pow, ← map_pow, h, map_one, one_mul, T_pow]

@[simp]
theorem scale_T (ξ : ∀ i, rootsOfUnity (n i) B) (i : ι) :
    scale n f ξ (T n f i) = algebraMap B _ ((ξ i : Bˣ) : B) * T n f i :=
  lift_T _ _ _ _ i

/-- XIII.5.3.0: the action of `μ_{n₁} × ⋯ × μ_{n_r}` on `U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. -/
noncomputable def scaleHom :
    (∀ i, rootsOfUnity (n i) B) →* (KummerAlgebra n f →ₐ[B] KummerAlgebra n f) where
  toFun := scale n f
  map_one' := algHom_ext fun i ↦ by simp
  map_mul' ξ η := algHom_ext fun i ↦ by
    simp only [scale_T, AlgHom.mul_apply, map_mul, AlgHom.commutes, Pi.mul_apply,
      Subgroup.coe_mul, Units.val_mul]
    ring

/-- XIII.5.3.0: `μ_{n₁} × ⋯ × μ_{n_r}` acts on `U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` by automorphisms. -/
noncomputable def rootsOfUnityToAlgEquiv :
    (∀ i, rootsOfUnity (n i) B) →* (KummerAlgebra n f ≃ₐ[B] KummerAlgebra n f) :=
  (AlgEquiv.algHomUnitsEquiv B _).toMonoidHom.comp (scaleHom n f).toHomUnits

@[simp]
theorem rootsOfUnityToAlgEquiv_apply (ξ : ∀ i, rootsOfUnity (n i) B) (x : KummerAlgebra n f) :
    rootsOfUnityToAlgEquiv n f ξ x = scale n f ξ x :=
  rfl

variable {n f} in
/-- XIII.5.3.0: if `U' = U[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` is connected (here: its ring is a domain
containing `B`), the `fᵢ` are units and `B` contains primitive `nᵢ`-th roots of unity, then the
group of `U`-automorphisms of `U'` is `μ_{n₁} × ⋯ × μ_{n_r}`. -/
theorem rootsOfUnityToAlgEquiv_bijective [IsDomain B] [IsDomain (KummerAlgebra n f)]
    (hB : Function.Injective (algebraMap B (KummerAlgebra n f))) (hf : ∀ i, IsUnit (f i))
    (hn : ∀ i, 0 < n i) (hζ : ∀ i, (primitiveRoots (n i) B).Nonempty) :
    Function.Bijective (rootsOfUnityToAlgEquiv n f) := by
  have hT : ∀ i, IsUnit (T n f i) := fun i ↦ isUnit_T (hn i) (hf i)
  refine ⟨fun ξ η h ↦ funext fun i ↦ ?_, fun σ ↦ ?_⟩
  · have h' := congrArg (fun φ : KummerAlgebra n f ≃ₐ[B] KummerAlgebra n f ↦ φ (T n f i)) h
    simp only [rootsOfUnityToAlgEquiv_apply, scale_T] at h'
    exact Subtype.ext (Units.ext (hB ((hT i).mul_left_injective h')))
  · have key : ∀ i, ∃ ξ : rootsOfUnity (n i) B,
        σ (T n f i) = algebraMap B _ ((ξ : Bˣ) : B) * T n f i := by
      intro i
      have : NeZero (n i) := ⟨(hn i).ne'⟩
      obtain ⟨u, hu⟩ := hT i
      have hy : (σ (T n f i) * ((u⁻¹ : (KummerAlgebra n f)ˣ) : KummerAlgebra n f)) ^ n i = 1 := by
        rw [mul_pow, ← map_pow, T_pow, AlgEquiv.commutes, ← T_pow, ← hu, ← mul_pow, Units.mul_inv,
          one_pow]
      let η : rootsOfUnity (n i) (KummerAlgebra n f) := rootsOfUnity.mkOfPowEq _ hy
      refine ⟨(rootsOfUnityEquivOfPrimitiveRoots hB (hζ i)).symm η, ?_⟩
      rw [rootsOfUnityEquivOfPrimitiveRoots_symm_apply]
      simp [η, ← hu]
    choose ξ hξ using key
    refine ⟨ξ, AlgEquiv.coe_toAlgHom_injective (algHom_ext fun i ↦ ?_)⟩
    simp [hξ]

/-- I.7.4, as used in XIII.5.1: if the `nᵢ` and the `fᵢ` are units of `B`, then
`B[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` is étale over `B` (its Jacobian `∏ nᵢ Tᵢ^{nᵢ - 1}` is a unit). -/
theorem etale [Finite ι] {n : ι → ℕ} {f : ι → B} (hn : ∀ i, IsUnit (n i : B))
    (hf : ∀ i, IsUnit (f i)) : Algebra.Etale B (KummerAlgebra n f) := by
  classical
  cases nonempty_fintype ι
  let P := Algebra.PreSubmersivePresentation.naive (R := B)
    (v := fun i ↦ (X i ^ n i - C (f i) : MvPolynomial ι B)) id Function.injective_id
  have hjac : IsUnit P.jacobian := by
    rw [P.jacobian_eq_jacobiMatrix_det]
    have : P.jacobiMatrix = Matrix.diagonal fun i ↦ C (n i : B) * X i ^ (n i - 1) := by
      ext i j
      rw [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
      by_cases h : i = j
      · subst h; simp
      · simp [h, Matrix.diagonal_apply_ne, Ne.symm h]
    rw [this, Matrix.det_diagonal, map_prod, IsUnit.prod_univ_iff]
    intro i
    have hT : algebraMap P.Ring (KummerAlgebra n f) (X i) = T n f i := rfl
    have hC : algebraMap P.Ring (KummerAlgebra n f) (C (n i : B)) = algebraMap B _ (n i) :=
      (IsScalarTower.algebraMap_apply B P.Ring _ _).symm
    rw [map_mul, map_pow, hC, hT]
    refine ((hn i).map (algebraMap B _)).mul ?_
    rcases Nat.eq_zero_or_pos (n i) with h0 | hpos
    · simp [h0]
    · exact (isUnit_T hpos (hf i)).pow _
  let Q : Algebra.SubmersivePresentation B _ ι ι := { P with jacobian_isUnit := hjac }
  have := Q.isStandardSmoothOfRelativeDimension (n := 0) (by simp [Algebra.Presentation.dimension])
  infer_instance

/-- XIII.5.2 for Kummer coverings: when the `tᵢ` are units and `nᵢ = eᵢ mᵢ`,
`B[Sᵢ]/(Sᵢ^{eᵢ} - tᵢ^{nᵢ})` is isomorphic to `B[Wᵢ]/(Wᵢ^{eᵢ} - 1)` by `Sᵢ ↦ tᵢ^{mᵢ} Wᵢ`. -/
noncomputable def equivOne (e m : ι → ℕ) (t : ι → Bˣ) :
    KummerAlgebra e (fun i ↦ (t i : B) ^ (e i * m i)) ≃ₐ[B] KummerAlgebra e (fun _ ↦ (1 : B)) :=
  AlgEquiv.ofAlgHom
    (lift (fun i ↦ algebraMap B _ ((t i : B) ^ m i) * T e _ i) fun i ↦ by
      rw [mul_pow, ← map_pow, T_pow, ← map_mul, mul_one, ← pow_mul, mul_comm (m i)])
    (lift (fun i ↦ algebraMap B _ ((((t i)⁻¹ : Bˣ) : B) ^ m i) * T e _ i) fun i ↦ by
      rw [mul_pow, ← map_pow, T_pow, ← map_mul, ← pow_mul, mul_comm (m i) (e i), ← mul_pow,
        Units.inv_mul, one_pow, map_one])
    (algHom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, lift_T, map_mul, AlgHom.commutes, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, ← mul_pow, Units.inv_mul, one_pow, map_one, one_mul])
    (algHom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, lift_T, map_mul, AlgHom.commutes, AlgHom.id_apply]
      rw [← mul_assoc, ← map_mul, ← mul_pow, Units.mul_inv, one_pow, map_one, one_mul])

section BaseChange

variable (A : Type*) [CommRing A] [Algebra B A]

/-- The base change of `B[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)` to a `B`-algebra `A` is `A[Tᵢ]/(Tᵢ^{nᵢ} - fᵢ)`. -/
noncomputable def baseChangeEquiv :
    A ⊗[B] KummerAlgebra n f ≃ₐ[A] KummerAlgebra n (fun i ↦ algebraMap B A (f i)) :=
  AlgEquiv.ofAlgHom
    (Algebra.TensorProduct.lift (Algebra.ofId A _)
      (lift (T n _) fun i ↦ by rw [T_pow, ← IsScalarTower.algebraMap_apply])
      fun _ _ ↦ Commute.all _ _)
    (lift (B := A) (n := n) (f := fun i ↦ algebraMap B A (f i)) (A := A ⊗[B] KummerAlgebra n f)
      (fun i ↦ (1 : A) ⊗ₜ[B] T n f i) fun i ↦ by
        rw [Algebra.TensorProduct.tmul_pow, one_pow, T_pow, ← IsScalarTower.algebraMap_apply,
          ← Algebra.TensorProduct.algebraMap_apply'])
    (algHom_ext fun i ↦ by simp)
    (Algebra.TensorProduct.ext (AlgHom.ext fun a ↦ by simp) (by apply algHom_ext; intro i; simp))

end BaseChange


section Extension

variable [Finite ι] (A' : Type w) (B' : Type w) [CommRing A'] [CommRing B'] [Algebra A' B']

/-- XIII.5.2 for Kummer coverings. Let `A'` be the ring of `X'` and `B'` that of `U'`, in which
`fᵢ = tᵢ^{nᵢ}` with `tᵢ` invertible and `nᵢ = eᵢ mᵢ`. Then the Kummer covering
`V' = U'[Sᵢ]/(Sᵢ^{eᵢ} - fᵢ)` is the restriction to `U'` of `X'[Wᵢ]/(Wᵢ^{eᵢ} - 1)`, which is étale
over `X'` when the `eᵢ` are invertible on `X'`. -/
theorem etale_and_nonempty_equiv (e m : ι → ℕ) (he : ∀ i, IsUnit (e i : A')) (t : ι → B'ˣ) :
    Algebra.Etale A' (KummerAlgebra e fun _ ↦ (1 : A')) ∧
      Nonempty (KummerAlgebra e (fun i ↦ (t i : B') ^ (e i * m i)) ≃ₐ[B']
        B' ⊗[A'] KummerAlgebra e fun _ ↦ (1 : A')) := by
  refine ⟨etale he fun _ ↦ isUnit_one, ⟨(equivOne e m t).trans ?_⟩⟩
  refine AlgEquiv.symm ((baseChangeEquiv e (fun _ ↦ (1 : A')) B').trans ?_)
  have h : (fun _ : ι ↦ algebraMap A' B' 1) = fun _ ↦ (1 : B') := funext fun _ ↦ map_one _
  exact h ▸ AlgEquiv.refl

end Extension

end KummerAlgebra

end SGA.SGA1.ExposeXIII
