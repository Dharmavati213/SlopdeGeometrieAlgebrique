/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import SGA.SGA1.ExposeXI.PrincipalCovering

/-!
# SGA 1, Exposé XI, §6: Kummer theory

Over `S = Spec A`, the Kummer group is `μ_n = Spec A[t]/(tⁿ - 1)`, the kernel of the `n`-th
power map `u_n` of `𝔾_m` (XI.6.1), and the Kummer covering attached to a unit `a` is the fibre
`u_n⁻¹(a) = Spec A[T]/(Tⁿ - a)`, a principal homogeneous bundle under `μ_n` (XI.6.2); it is
the image of `a` under the coboundary `H⁰(S, 𝒪_S^*) → H¹(S, μ_n)` of XI.6.4.

This file works with rings, i.e. affine `S`:

* `kummerBasis`: `A[T]/(Tⁿ - a)` is free with basis `1, T, …, Tⁿ⁻¹` (XI.6.1);
* `kummerPointsEquiv`: its `B`-points are the `n`-th roots of `a` in `B`, so `μ_n` is the kernel
  of `u_n` and the Kummer covering is the fibre of `u_n` over `a` (XI.6.1, XI.6.4);
* `etale_kummer`: it is étale when `n` and `a` are units (XI.6.1);
* `kummerTorsorEquiv`: `K ⊗_A K ≅ K ⊗_A μ_n`, i.e. it is formally principal homogeneous
  under `μ_n` (XI.6.2);
* `IsPrimitiveRootOver`, `bijective_muEval_iff`: `μ_n ≅ (ℤ/n)` through `ζ` if and only if `ζ`
  is a primitive `n`-th root of unity over `A`, which forces `n` to be a unit (XI.6.3);
* `isPrincipalCovering_kummer`: with such a `ζ`, the Kummer covering is a principal covering with
  group `ℤ/n` (XI.6.3, classical Kummer theory);
* `Kummer.nonempty_algHom_iff`: the Kummer covering of `a` is trivial (has a section) if and
  only if `a` is an `n`-th power (exactness of XI.6.4 at `H⁰(S, 𝒪_S^*)`);
* `kummer_nonempty_equivariant_iff`: with a primitive root, the Kummer coverings of `a` and `b`
  are isomorphic principal coverings if and only if `a/b` is an `n`-th power (injectivity of
  `A^*/A^{*n} → H¹`, XI.6.4–XI.6.5);
* `etale_mu_iff`: `μ_n` is étale if and only if `n` is a unit (XI.6.1).

That Kummer coverings are torsors under the group scheme `μ_n` (with its Hopf algebra structure)
is in `KummerTorsor.lean`.
-/

namespace SGA.SGA1.ExposeXI

open Polynomial TensorProduct

section Etale

variable {A : Type*} [CommRing A]

/-- `A[X]/(f)` is étale over `A` if `f` is monic and `f'` is invertible modulo `f`
(a standard étale algebra, I.7). -/
theorem etale_adjoinRoot {f : A[X]} (hf : f.Monic) {p₁ p₂ : A[X]}
    (h : derivative f * p₁ + f * p₂ = 1) : Algebra.Etale A (AdjoinRoot f) := by
  let P : StandardEtalePair A := ⟨f, hf, 1, p₁, p₂, 0, by rw [pow_zero, h]⟩
  have hP : P.HasMap (AdjoinRoot.root f) :=
    ⟨by change aeval _ f = 0; rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self],
      by change IsUnit (aeval _ (1 : A[X])); rw [map_one]; exact isUnit_one⟩
  have hX : f.eval₂ (Algebra.ofId A P.Ring : A →+* P.Ring) P.X = 0 := by
    have := P.hasMap_X
    exact this.1
  let e : P.Ring ≃ₐ[A] AdjoinRoot f := AlgEquiv.ofAlgHom (P.lift _ hP)
    (AdjoinRoot.liftAlgHom f (Algebra.ofId A P.Ring) P.X hX)
    (by ext; rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root, StandardEtalePair.lift_X]; rfl)
    (by ext; rw [AlgHom.comp_apply, StandardEtalePair.lift_X, AdjoinRoot.liftAlgHom_root]; rfl)
  exact .of_equiv e

end Etale

variable (A : Type*) [CommRing A]

/-- XI.6.2: the Kummer covering `Spec A[T]/(Tⁿ - a)` of rank `n` attached to `a`. -/
abbrev KummerAlgebra (n : ℕ) (a : A) : Type _ := AdjoinRoot (X ^ n - C a : A[X])

/-- XI.6.1: the Kummer group `μ_n = Spec A[t]/(tⁿ - 1)`. -/
abbrev MuAlgebra (n : ℕ) : Type _ := AdjoinRoot (X ^ n - 1 : A[X])

variable {A} {n : ℕ} {a : A}

namespace Kummer

theorem root_pow (n : ℕ) (a : A) :
    AdjoinRoot.root (X ^ n - C a) ^ n = algebraMap A (KummerAlgebra A n a) a := by
  have := AdjoinRoot.eval₂_root (X ^ n - C a)
  rwa [eval₂_sub, eval₂_X_pow, eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] at this

theorem mu_root_pow (n : ℕ) : AdjoinRoot.root (X ^ n - 1 : A[X]) ^ n = 1 := by
  have := AdjoinRoot.eval₂_root (X ^ n - 1 : A[X])
  rwa [eval₂_sub, eval₂_X_pow, eval₂_one, sub_eq_zero] at this

theorem monic (n : ℕ) [NeZero n] (a : A) : (X ^ n - C a : A[X]).Monic :=
  monic_X_pow_sub_C a (NeZero.ne n)

variable (A n) in
/-- `μ_n` is the Kummer covering of `1`. -/
noncomputable def muEquiv : MuAlgebra A n ≃ₐ[A] KummerAlgebra A n 1 :=
  AdjoinRoot.algEquivOfEq A _ _ (by rw [map_one])

theorem isUnit_root (n : ℕ) [NeZero n] (ha : IsUnit a) :
    IsUnit (AdjoinRoot.root (X ^ n - C a)) := by
  rw [← isUnit_pow_iff (NeZero.ne n), root_pow]
  exact ha.map _

/-- XI.6.1: `A[T]/(Tⁿ - a)` is a free `A`-module with basis `1, T, …, Tⁿ⁻¹`. -/
noncomputable def basis (n : ℕ) [NeZero n] [Nontrivial A] (a : A) :
    Module.Basis (Fin n) A (KummerAlgebra A n a) :=
  (AdjoinRoot.powerBasis' (monic n a)).basis.reindex (finCongr natDegree_X_pow_sub_C)

theorem basis_apply [NeZero n] [Nontrivial A] (i : Fin n) :
    basis n a i = AdjoinRoot.root (X ^ n - C a) ^ (i : ℕ) := by
  simp [basis]
  rfl

instance [NeZero n] : Module.Finite A (KummerAlgebra A n a) :=
  (AdjoinRoot.powerBasis' (monic n a)).finite

instance [NeZero n] : Module.Free A (KummerAlgebra A n a) :=
  .of_basis (AdjoinRoot.powerBasis' (monic n a)).basis

/-- XI.6.1: `μ_n` (and every Kummer covering) is finite locally free of rank `n`. -/
theorem finrank_eq [NeZero n] [Nontrivial A] : Module.finrank A (KummerAlgebra A n a) = n := by
  rw [Module.finrank_eq_card_basis (basis n a), Fintype.card_fin]

instance [NeZero n] : Module.FaithfullyFlat A (KummerAlgebra A n a) := by
  cases subsingleton_or_nontrivial A
  · exact { toFlat := inferInstance
            submodule_ne_top := fun _ hm ↦ (hm.ne_top (Subsingleton.elim _ _)).elim }
  · exact faithfullyFlat_of_basis (basis n a)

variable (n a) in
/-- XI.6.1, XI.6.4: the `B`-points of `Spec A[T]/(Tⁿ - a)` are the `n`-th roots of `a` in `B`.
For `a = 1` this says that `μ_n` is the kernel of `u_n : 𝔾_m → 𝔾_m`; in general that the Kummer
covering is the fibre `u_n⁻¹(a)`, which is how XI.4 defines the coboundary `∂a`. -/
noncomputable def pointsEquiv (B : Type*) [CommRing B] [Algebra A B] :
    (KummerAlgebra A n a →ₐ[A] B) ≃ {x : B // x ^ n = algebraMap A B a} where
  toFun φ := ⟨φ (AdjoinRoot.root _), by rw [← map_pow, root_pow, AlgHom.commutes]⟩
  invFun x := AdjoinRoot.liftAlgHom _ (Algebra.ofId A B) x.1 (by
    change aeval x.1 (X ^ n - C a) = 0
    rw [map_sub, aeval_X_pow, aeval_C, x.2, sub_self])
  left_inv φ := by ext; simp
  right_inv x := by simp

/-- XI.6.4, exactness at the middle `H⁰(S, 𝒪_S^*)` (affine case): the Kummer covering of `a`
is trivial, i.e. has a section, if and only if `a` is an `n`-th power in `A`. -/
theorem nonempty_algHom_iff : Nonempty (KummerAlgebra A n a →ₐ[A] A) ↔ ∃ x : A, x ^ n = a :=
  ⟨fun ⟨φ⟩ ↦ ⟨_, (pointsEquiv n a A φ).2⟩, fun ⟨x, hx⟩ ↦ ⟨(pointsEquiv n a A).symm ⟨x, hx⟩⟩⟩

/-- XI.6.1: if `n` is a unit, `μ_n` is étale; more generally the Kummer covering of a unit `a`
is étale. -/
theorem etale [NeZero n] (hn : IsUnit (n : A)) (ha : IsUnit a) :
    Algebra.Etale A (KummerAlgebra A n a) := by
  set u : A := ((hn.unit⁻¹ : Aˣ) : A)
  set v : A := ((ha.unit⁻¹ : Aˣ) : A)
  refine etale_adjoinRoot (monic n a) (p₁ := C (u * v) * X) (p₂ := -C v) ?_
  have e1 : C (n : A) * C u = 1 := by rw [← map_mul, hn.mul_val_inv, map_one]
  have e2 : C a * C v = 1 := by rw [← map_mul, ha.mul_val_inv, map_one]
  have e3 : (X : A[X]) ^ (n - 1) * X = X ^ n := pow_sub_one_mul (NeZero.ne n) X
  rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero, map_mul]
  linear_combination (C v * X ^ n) * e1 + (C (n : A) * C u * C v) * e3 + e2

variable (n a) in
/-- XI.6.2: the coaction `K → K ⊗_A μ_n`, `T ↦ T ⊗ t`, of the Kummer group on the Kummer
covering `K = A[T]/(Tⁿ - a)`. -/
noncomputable def coaction : KummerAlgebra A n a →ₐ[A] KummerAlgebra A n a ⊗[A] MuAlgebra A n :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _)
    (AdjoinRoot.root (X ^ n - C a) ⊗ₜ AdjoinRoot.root (X ^ n - 1)) (by
      change aeval _ (X ^ n - C a) = 0
      rw [map_sub, aeval_X_pow, aeval_C, Algebra.TensorProduct.tmul_pow, root_pow, mu_root_pow,
        Algebra.TensorProduct.algebraMap_apply, sub_self])

@[simp]
theorem coaction_root :
    coaction n a (AdjoinRoot.root _) =
      AdjoinRoot.root (X ^ n - C a) ⊗ₜ AdjoinRoot.root (X ^ n - 1) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

variable (n) in
/-- The inverse `T⁻¹` of the root of `Tⁿ - a`, for a unit `a`. -/
noncomputable def rootInv [NeZero n] (ha : IsUnit a) : KummerAlgebra A n a :=
  ↑(isUnit_root n ha).unit⁻¹

theorem rootInv_mul_root [NeZero n] (ha : IsUnit a) :
    rootInv n ha * AdjoinRoot.root (X ^ n - C a) = 1 :=
  (isUnit_root n ha).val_inv_mul

theorem rootInv_tmul_root_pow [NeZero n] (ha : IsUnit a) :
    (rootInv n ha ⊗ₜ[A] AdjoinRoot.root (X ^ n - C a)) ^ n = 1 := by
  rw [Algebra.TensorProduct.tmul_pow, root_pow, Algebra.algebraMap_eq_smul_one,
    TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, ← root_pow, ← mul_pow,
    mul_comm (AdjoinRoot.root _), rootInv_mul_root, one_pow, Algebra.TensorProduct.one_def]

variable (n a) in
/-- The map `K ⊗_A K → K ⊗_A μ_n`, `x ⊗ y ↦ (x ⊗ 1) · coaction y`. -/
noncomputable def torsorHom :
    KummerAlgebra A n a ⊗[A] KummerAlgebra A n a →ₐ[KummerAlgebra A n a]
      KummerAlgebra A n a ⊗[A] MuAlgebra A n :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (coaction n a) fun _ _ ↦ .all _ _

variable (n) in
/-- The map `μ_n → K ⊗_A K`, `t ↦ T⁻¹ ⊗ T`. -/
noncomputable def muToTensor [NeZero n] (ha : IsUnit a) :
    MuAlgebra A n →ₐ[A] KummerAlgebra A n a ⊗[A] KummerAlgebra A n a :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (rootInv n ha ⊗ₜ AdjoinRoot.root (X ^ n - C a)) (by
    change aeval _ (X ^ n - 1) = 0
    rw [map_sub, aeval_X_pow, rootInv_tmul_root_pow, map_one, sub_self])

variable (n) in
/-- The inverse map `K ⊗_A μ_n → K ⊗_A K`, `x ⊗ t ↦ x T⁻¹ ⊗ T`. -/
noncomputable def torsorInvHom [NeZero n] (ha : IsUnit a) :
    KummerAlgebra A n a ⊗[A] MuAlgebra A n →ₐ[KummerAlgebra A n a]
      KummerAlgebra A n a ⊗[A] KummerAlgebra A n a :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft (muToTensor n ha)
    fun _ _ ↦ .all _ _

theorem torsorHom_tmul (x y : KummerAlgebra A n a) :
    torsorHom n a (x ⊗ₜ y) = (x ⊗ₜ 1) * coaction n a y :=
  (Algebra.TensorProduct.lift_tmul _ _ _ x y).trans
    (by rw [Algebra.TensorProduct.includeLeft_apply])

theorem torsorInvHom_tmul [NeZero n] (ha : IsUnit a) (x : KummerAlgebra A n a)
    (y : MuAlgebra A n) : torsorInvHom n ha (x ⊗ₜ y) = (x ⊗ₜ 1) * muToTensor n ha y :=
  (Algebra.TensorProduct.lift_tmul _ _ _ x y).trans
    (by rw [Algebra.TensorProduct.includeLeft_apply])

theorem muToTensor_root [NeZero n] (ha : IsUnit a) :
    muToTensor n ha (AdjoinRoot.root _) = rootInv n ha ⊗ₜ AdjoinRoot.root (X ^ n - C a) :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem torsorInvHom_comp_torsorHom [NeZero n] (ha : IsUnit a) :
    (torsorInvHom n ha).comp (torsorHom n a) = AlgHom.id _ _ := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AdjoinRoot.algHom_ext ?_)
  change torsorInvHom n ha (torsorHom n a (1 ⊗ₜ AdjoinRoot.root _)) = 1 ⊗ₜ AdjoinRoot.root _
  rw [torsorHom_tmul, coaction_root, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul,
    torsorInvHom_tmul, muToTensor_root, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    mul_comm, rootInv_mul_root]

theorem torsorHom_comp_torsorInvHom [NeZero n] (ha : IsUnit a) :
    (torsorHom n a).comp (torsorInvHom n ha) = AlgHom.id _ _ := by
  refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AdjoinRoot.algHom_ext ?_)
  change torsorHom n a (torsorInvHom n ha (1 ⊗ₜ AdjoinRoot.root _)) = 1 ⊗ₜ AdjoinRoot.root _
  rw [torsorInvHom_tmul, muToTensor_root, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    one_mul, torsorHom_tmul, coaction_root, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    rootInv_mul_root]

variable (n) in
/-- XI.6.2: a Kummer covering of a unit is formally principal homogeneous under `μ_n`: the map
`x ⊗ y ↦ (x ⊗ 1) · coaction y` is an isomorphism `K ⊗_A K ≅ K ⊗_A μ_n`. -/
noncomputable def torsorEquiv [NeZero n] (ha : IsUnit a) :
    KummerAlgebra A n a ⊗[A] KummerAlgebra A n a ≃ₐ[KummerAlgebra A n a]
      KummerAlgebra A n a ⊗[A] MuAlgebra A n :=
  AlgEquiv.ofAlgHom _ _ (torsorHom_comp_torsorInvHom ha) (torsorInvHom_comp_torsorHom ha)

@[simp]
theorem torsorEquiv_tmul [NeZero n] (ha : IsUnit a) (x y : KummerAlgebra A n a) :
    torsorEquiv n ha (x ⊗ₜ y) = (x ⊗ₜ 1) * coaction n a y :=
  torsorHom_tmul x y

section Action

variable (n a) in
/-- The endomorphism `T ↦ u T` of `A[T]/(Tⁿ - a)` for `uⁿ = 1`. -/
noncomputable def scaleHom (u : A) (hu : u ^ n = 1) :
    KummerAlgebra A n a →ₐ[A] KummerAlgebra A n a :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (algebraMap A _ u * AdjoinRoot.root _) (by
    change aeval _ (X ^ n - C a) = 0
    rw [map_sub, aeval_X_pow, aeval_C, mul_pow, ← map_pow, hu, map_one, one_mul, root_pow,
      sub_self])

theorem scaleHom_root (u : A) (hu : u ^ n = 1) :
    scaleHom n a u hu (AdjoinRoot.root _) = algebraMap A _ u * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem scaleHom_comp (u v : A) (hu : u ^ n = 1) (hv : v ^ n = 1) :
    (scaleHom n a u hu).comp (scaleHom n a v hv) =
      scaleHom n a (u * v) (by rw [mul_pow, hu, hv, one_mul]) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, scaleHom_root, map_mul, AlgHom.commutes, scaleHom_root, scaleHom_root,
    map_mul, mul_left_comm, mul_assoc]

theorem scaleHom_one : scaleHom n a 1 (one_pow n) = AlgHom.id A _ := by
  refine AdjoinRoot.algHom_ext ?_
  rw [scaleHom_root, map_one, one_mul, AlgHom.id_apply]

variable (n a) in
/-- The automorphism `T ↦ u T` of `A[T]/(Tⁿ - a)` for `u ∈ μ_n(A)`. -/
noncomputable def scaleEquiv (u : rootsOfUnity n A) :
    KummerAlgebra A n a ≃ₐ[A] KummerAlgebra A n a :=
  AlgEquiv.ofAlgHom (scaleHom n a (u : Aˣ) ((mem_rootsOfUnity' n _).mp u.2))
    (scaleHom n a ((u⁻¹ : rootsOfUnity n A) : Aˣ) ((mem_rootsOfUnity' n _).mp (u⁻¹).2))
    (by rw [scaleHom_comp]; simp_rw [← Units.val_mul]; simp [scaleHom_one])
    (by rw [scaleHom_comp]; simp_rw [← Units.val_mul]; simp [scaleHom_one])

theorem scaleEquiv_root (u : rootsOfUnity n A) :
    scaleEquiv n a u (AdjoinRoot.root _) = algebraMap A _ ((u : Aˣ) : A) * AdjoinRoot.root _ :=
  scaleHom_root ((u : Aˣ) : A) ((mem_rootsOfUnity' n _).mp u.2)

theorem algEquiv_ext {e₁ e₂ : KummerAlgebra A n a ≃ₐ[A] KummerAlgebra A n a}
    (h : e₁ (AdjoinRoot.root _) = e₂ (AdjoinRoot.root _)) : e₁ = e₂ :=
  AlgEquiv.coe_toAlgHom_injective (AdjoinRoot.algHom_ext h)

variable (n a) in
/-- The action of `μ_n(A)` on the Kummer covering by `T ↦ u T`: the action of the constant
sections of `μ_n` underlying the coaction of XI.6.2. -/
noncomputable def rootsAction :
    rootsOfUnity n A →* (KummerAlgebra A n a ≃ₐ[A] KummerAlgebra A n a) where
  toFun := scaleEquiv n a
  map_one' := algEquiv_ext (by
    rw [scaleEquiv_root, OneMemClass.coe_one, Units.val_one, map_one, one_mul,
      AlgEquiv.one_apply])
  map_mul' u v := algEquiv_ext (by
    rw [AlgEquiv.mul_apply, scaleEquiv_root, scaleEquiv_root, map_mul, AlgEquiv.commutes,
      scaleEquiv_root, Subgroup.coe_mul, Units.val_mul, map_mul, mul_left_comm, mul_assoc])

theorem rootsAction_root (u : rootsOfUnity n A) :
    rootsAction n a u (AdjoinRoot.root _) = algebraMap A _ ((u : Aˣ) : A) * AdjoinRoot.root _ :=
  scaleEquiv_root _

end Action

end Kummer

section PrimitiveRoot

/-- XI.6.3: `ζ` is a *primitive `n`-th root of unity over `Spec A`*: `ζⁿ = 1` and `1 - ζⁱ` is
a unit for `0 < i < n`, i.e. `ζ` is a primitive `n`-th root of unity in every residue field of
`A`. When `μ_n` is étale this is SGA's condition "of order exactly `n` on each connected
component". -/
structure IsPrimitiveRootOver (ζ : A) (n : ℕ) : Prop where
  pow_eq_one : ζ ^ n = 1
  isUnit_one_sub_pow : ∀ i, 0 < i → i < n → IsUnit (1 - ζ ^ i)

variable {ζ : A}

namespace IsPrimitiveRootOver

variable (h : IsPrimitiveRootOver ζ n)
include h

theorem isUnit [NeZero n] : IsUnit ζ := IsUnit.of_pow_eq_one h.pow_eq_one (NeZero.ne n)

theorem isUnit_pow_sub_pow [NeZero n] {i j : ℕ} (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    IsUnit (ζ ^ i - ζ ^ j) := by
  rcases lt_or_gt_of_ne hij with h' | h'
  · have : ζ ^ i - ζ ^ j = ζ ^ i * (1 - ζ ^ (j - i)) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h'.le]
    rw [this]
    exact (h.isUnit.pow i).mul (h.isUnit_one_sub_pow _ (Nat.sub_pos_of_lt h') (by omega))
  · have : ζ ^ i - ζ ^ j = -(ζ ^ j * (1 - ζ ^ (i - j))) := by
      rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' h'.le, neg_sub]
    rw [this]
    exact ((h.isUnit.pow j).mul (h.isUnit_one_sub_pow _ (Nat.sub_pos_of_lt h') (by omega))).neg

/-- In a nontrivial ring, a primitive root over `A` is a primitive root in mathlib's sense. -/
theorem isPrimitiveRoot [Nontrivial A] [NeZero n] : IsPrimitiveRoot ζ n := by
  refine ⟨h.pow_eq_one, fun l hl ↦ ?_⟩
  by_contra hdvd
  have hpos : 0 < l % n := Nat.pos_of_ne_zero fun h0 ↦ hdvd (Nat.dvd_of_mod_eq_zero h0)
  have := h.isUnit_one_sub_pow _ hpos (Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne n)))
  rw [← pow_eq_pow_mod l h.pow_eq_one, hl, sub_self] at this
  exact not_isUnit_zero this

end IsPrimitiveRootOver

end PrimitiveRoot

section Eval

variable {ζ : A} [NeZero n]

omit [NeZero n] in
theorem pow_val_pow_eq_one (hζ : ζ ^ n = 1) (k : ZMod n) : (ζ ^ k.val) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem monic_X_pow_sub_one (n : ℕ) [NeZero n] : (X ^ n - 1 : A[X]).Monic := by
  simpa using monic_X_pow_sub_C (1 : A) (NeZero.ne n)

theorem natDegree_X_pow_sub_one_le (n : ℕ) : (X ^ n - 1 : A[X]).natDegree ≤ n :=
  (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le n) (by simp))

variable (n) in
/-- XI.6.3: the morphism `(ℤ/n)_S → μ_n` sending the generator to `ζ`; on rings it is
`A[t]/(tⁿ - 1) → A^{ℤ/n}`, `t ↦ (ζᵏ)_k`. -/
noncomputable def muEval (hζ : ζ ^ n = 1) : MuAlgebra A n →ₐ[A] (ZMod n → A) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (fun k ↦ ζ ^ k.val) (by
    change aeval (fun k : ZMod n ↦ ζ ^ k.val) (X ^ n - 1) = 0
    rw [map_sub, aeval_X_pow, map_one]
    funext k
    rw [Pi.sub_apply, Pi.pow_apply, pow_val_pow_eq_one hζ, Pi.one_apply, sub_self,
      Pi.zero_apply])

omit [NeZero n] in
theorem muEval_mk (hζ : ζ ^ n = 1) (p : A[X]) (k : ZMod n) :
    muEval n hζ (AdjoinRoot.mk _ p) k = p.eval (ζ ^ k.val) := by
  rw [muEval, AdjoinRoot.liftAlgHom_mk, Algebra.toRingHom_ofId, eval₂_algebraMap_pi_apply]

theorem X_pow_sub_one_eq_prod (h : IsPrimitiveRootOver ζ n) :
    (X ^ n - 1 : A[X]) = ∏ k : ZMod n, (X - C (ζ ^ k.val)) :=
  eq_prod_X_sub_C_of_isUnit_sub (monic_X_pow_sub_one n)
    (by rw [ZMod.card]; exact natDegree_X_pow_sub_one_le n)
    (fun k l hkl ↦ h.isUnit_pow_sub_pow (ZMod.val_lt k) (ZMod.val_lt l)
      fun e ↦ hkl (ZMod.val_injective n e))
    fun k ↦ by rw [eval_sub, eval_pow, eval_X, eval_one, pow_val_pow_eq_one h.pow_eq_one, sub_self]

/-- XI.6.3 (affine case): the morphism `(ℤ/n)_S → μ_n` defined by `ζ` is an isomorphism if and
only if `ζ` is a primitive `n`-th root of unity over `A`. -/
theorem bijective_muEval_iff (hζ : ζ ^ n = 1) :
    Function.Bijective (muEval n hζ) ↔ IsPrimitiveRootOver ζ n := by
  constructor
  · intro hbij
    refine ⟨hζ, fun i hi0 hin ↦ ?_⟩
    obtain ⟨y, hy⟩ := hbij.2 (Pi.single 0 1)
    induction y using AdjoinRoot.induction_on with | ih q => ?_
    have hne : (i : ZMod n) ≠ 0 := fun e ↦ by
      have := congrArg ZMod.val e
      rw [ZMod.val_cast_of_lt hin, ZMod.val_zero] at this
      omega
    have h0 := congrFun hy 0
    have hi := congrFun hy (i : ZMod n)
    rw [muEval_mk, ZMod.val_zero, pow_zero, Pi.single_eq_same] at h0
    rw [muEval_mk, ZMod.val_cast_of_lt hin] at hi
    simp only [Pi.single_apply, hne, ite_false] at hi
    have := sub_dvd_eval_sub 1 (ζ ^ i) q
    rw [h0, hi, sub_zero] at this
    exact isUnit_of_dvd_one this
  · intro h
    have hc : Pairwise fun k l : ZMod n ↦ IsUnit (ζ ^ k.val - ζ ^ l.val) :=
      fun k l hkl ↦ h.isUnit_pow_sub_pow (ZMod.val_lt k) (ZMod.val_lt l)
        fun e ↦ hkl (ZMod.val_injective n e)
    let E := (AdjoinRoot.algEquivOfEq A _ _ (X_pow_sub_one_eq_prod h)).trans
      (adjoinRootProdXSubCEquiv (fun k : ZMod n ↦ ζ ^ k.val) hc)
    have : muEval n hζ = E.toAlgHom := AdjoinRoot.algHom_ext (by
      change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = E (AdjoinRoot.root _)
      rw [AdjoinRoot.liftAlgHom_root, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root,
        adjoinRootProdXSubCEquiv_root])
    rw [this]
    exact E.bijective

/-- XI.6.3: if `μ_n ≅ (ℤ/n)` (i.e. there is a primitive `n`-th root of unity over `A`), then
`n` is a unit in `A`, so `μ_n` is étale (`Kummer.etale`). -/
theorem IsPrimitiveRootOver.isUnit_natCast (h : IsPrimitiveRootOver ζ n) : IsUnit (n : A) := by
  have hprod : ∏ k : ZMod n, (X - C (ζ ^ k.val)) =
      (X - C 1) * ∏ k ∈ (Finset.univ : Finset (ZMod n)).erase 0, (X - C (ζ ^ k.val)) := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ 0), ZMod.val_zero, pow_zero]
  have hgeom : (X - C 1) * ∑ i ∈ Finset.range n, (X : A[X]) ^ i = X ^ n - 1 := by
    rw [map_one, mul_comm, geom_sum_mul]
  have hcancel : ∑ i ∈ Finset.range n, (X : A[X]) ^ i =
      ∏ k ∈ (Finset.univ : Finset (ZMod n)).erase 0, (X - C (ζ ^ k.val)) :=
    (monic_X_sub_C (1 : A)).isRegular.left (by
      dsimp only
      rw [hgeom, ← hprod, X_pow_sub_one_eq_prod h])
  have := congrArg (eval 1) hcancel
  simp only [eval_finsetSum, eval_pow, eval_X, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, eval_prod, eval_sub, eval_C] at this
  rw [this, IsUnit.prod_iff]
  intro k hk
  exact h.isUnit_one_sub_pow _ (Nat.pos_of_ne_zero fun e ↦ (Finset.ne_of_mem_erase hk)
    ((ZMod.val_eq_zero k).mp e)) (ZMod.val_lt k)

variable (n) in
/-- The homomorphism `ℤ/n → μ_n(A)`, `k ↦ ζᵏ` (XI.6.2: homomorphisms `(ℤ/n)_S → G` correspond
to sections of `G` whose `n`-th power is `1`). -/
noncomputable def zmodToRoots (hζ : ζ ^ n = 1) : Multiplicative (ZMod n) →* rootsOfUnity n A where
  toFun k := rootsOfUnity.mkOfPowEq ζ hζ ^ (Multiplicative.toAdd k).val
  map_one' := by rw [toAdd_one, ZMod.val_zero, pow_zero]
  map_mul' k l := by
    have hx : rootsOfUnity.mkOfPowEq ζ hζ ^ n = 1 := Subtype.ext (by
      rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact (mem_rootsOfUnity _ _).mp (rootsOfUnity.mkOfPowEq ζ hζ).2)
    rw [toAdd_mul, ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ hx]

theorem coe_zmodToRoots (hζ : ζ ^ n = 1) (k : Multiplicative (ZMod n)) :
    ((zmodToRoots n hζ k : Aˣ) : A) = ζ ^ (Multiplicative.toAdd k).val := by
  simp [zmodToRoots]

variable (n a) in
/-- XI.6.3: the action of `ℤ/n` on the Kummer covering, `k` acting by `T ↦ ζᵏ T`. -/
noncomputable def kummerAction (hζ : ζ ^ n = 1) :
    Multiplicative (ZMod n) →* (KummerAlgebra A n a ≃ₐ[A] KummerAlgebra A n a) :=
  (Kummer.rootsAction n a).comp (zmodToRoots n hζ)

theorem kummerAction_root (hζ : ζ ^ n = 1) (k : Multiplicative (ZMod n)) :
    kummerAction n a hζ k (AdjoinRoot.root _) =
      algebraMap A _ (ζ ^ (Multiplicative.toAdd k).val) * AdjoinRoot.root _ := by
  rw [kummerAction, MonoidHom.comp_apply, Kummer.rootsAction_root, coe_zmodToRoots]

/-- XI.6.3 and classical Kummer theory: if `ζ` is a primitive `n`-th root of unity over `A` and
`a` is a unit, then `A[T]/(Tⁿ - a)` is a principal covering of `A` with group `ℤ/n`, `k` acting
by `T ↦ ζᵏ T`. In particular it is finite étale (`IsPrincipalCovering.etale`). -/
theorem isPrincipalCovering_kummer [Nontrivial A] (h : IsPrimitiveRootOver ζ n)
    (ha : IsUnit a) : IsPrincipalCovering (kummerAction n a h.pow_eq_one) := by
  refine isPrincipalCovering_adjoinRoot (Kummer.monic n a)
    (by rw [natDegree_X_pow_sub_C, Fintype.card_multiplicative, ZMod.card]) _ fun k l hkl ↦ ?_
  dsimp only
  rw [kummerAction_root, kummerAction_root, ← sub_mul, ← map_sub]
  refine ((h.isUnit_pow_sub_pow (ZMod.val_lt _) (ZMod.val_lt _) fun e ↦ hkl ?_).map _).mul
    (Kummer.isUnit_root n ha)
  exact Multiplicative.toAdd.injective (ZMod.val_injective n e)

end Eval

section Classification

variable {ζ : A} [NeZero n]

variable (n) in
/-- The morphism `A[T]/(Tⁿ - a) → A[T]/(Tⁿ - b)`, `T ↦ c T`, for `a = cⁿ b`. -/
noncomputable def kummerScaleHom (a b c : A) (h : a = c ^ n * b) :
    KummerAlgebra A n a →ₐ[A] KummerAlgebra A n b :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (algebraMap A _ c * AdjoinRoot.root _) (by
    change aeval _ (X ^ n - C a) = 0
    rw [map_sub, aeval_X_pow, aeval_C, mul_pow, Kummer.root_pow, ← map_pow, ← map_mul, ← h,
      sub_self])

omit [NeZero n] in
theorem kummerScaleHom_root (a b c : A) (h : a = c ^ n * b) :
    kummerScaleHom n a b c h (AdjoinRoot.root _) = algebraMap A _ c * AdjoinRoot.root _ :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

omit [NeZero n] in
theorem kummerScaleHom_comp (a b c d : A) (h : a = c ^ n * b) (h' : b = d ^ n * a)
    (hcd : d * c = 1) :
    (kummerScaleHom n b a d h').comp (kummerScaleHom n a b c h) = AlgHom.id A _ := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, kummerScaleHom_root, map_mul, AlgHom.commutes, kummerScaleHom_root,
    ← mul_assoc, ← map_mul, mul_comm c, hcd, map_one, one_mul, AlgHom.id_apply]

/-- XI.6.4, XI.6.5 (affine case, classical Kummer theory): if `ζ` is a primitive `n`-th root of
unity over `A`, the Kummer coverings of two units `a` and `b` are isomorphic as principal
coverings with group `ℤ/n` if and only if `a / b` is an `n`-th power; that is, the map
`A^*/A^{*n} → H¹(S, ℤ/n)` is well defined and injective. -/
theorem kummer_nonempty_equivariant_iff [Nontrivial A] (h : IsPrimitiveRootOver ζ n) {a b : A}
    (ha : IsUnit a) (hb : IsUnit b) :
    (∃ e : KummerAlgebra A n a ≃ₐ[A] KummerAlgebra A n b, ∀ k x,
      e (kummerAction n a h.pow_eq_one k x) = kummerAction n b h.pow_eq_one k (e x)) ↔
      ∃ c : A, a = c ^ n * b := by
  constructor
  · rintro ⟨e, he⟩
    set x := e (AdjoinRoot.root _)
    set r := AdjoinRoot.root (X ^ n - C b)
    have hfix : ∀ k, kummerAction n b h.pow_eq_one k (x * r ^ (n - 1)) = x * r ^ (n - 1) := by
      intro k
      rw [map_mul, map_pow, ← he, kummerAction_root, map_mul, AlgEquiv.commutes,
        kummerAction_root, mul_pow, ← map_pow, mul_mul_mul_comm, ← map_mul, ← pow_succ',
        Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n)), pow_val_pow_eq_one h.pow_eq_one,
        map_one, one_mul]
    obtain ⟨d, hd⟩ := ((isPrincipalCovering_kummer (a := b) h hb).mem_range_algebraMap_iff _).mpr
      hfix
    have hrn : r ^ n = algebraMap A _ b := Kummer.root_pow n b
    have hx : x = algebraMap A _ (d * ↑hb.unit⁻¹) * r := by
      have hn1 : r ^ n = r ^ (n - 1) * r := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero (NeZero.ne n))]
      have h1 : x * r ^ n = algebraMap A _ d * r := by
        rw [hn1, ← mul_assoc, ← hd]
      rw [hrn] at h1
      calc x = x * algebraMap A _ b * algebraMap A _ ↑hb.unit⁻¹ := by
            rw [mul_assoc, ← map_mul, hb.mul_val_inv, map_one, mul_one]
        _ = _ := by rw [h1, map_mul]; ring
    have hxn : x ^ n = algebraMap A _ a := by rw [← map_pow, Kummer.root_pow, AlgEquiv.commutes]
    rw [hx, mul_pow, hrn, ← map_pow, ← map_mul] at hxn
    have hff := (isPrincipalCovering_kummer (a := b) h hb).faithfullyFlat
    exact ⟨d * ↑hb.unit⁻¹, ((RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective hxn).symm⟩
  · rintro ⟨c, hc⟩
    have hcu : IsUnit c := by
      have : IsUnit (c ^ n * b) := hc ▸ ha
      exact (isUnit_pow_iff (NeZero.ne n)).mp (isUnit_of_mul_isUnit_left this)
    have hc' : b = (↑hcu.unit⁻¹ : A) ^ n * a := by
      rw [hc, ← mul_assoc, ← mul_pow, hcu.val_inv_mul, one_pow, one_mul]
    refine ⟨AlgEquiv.ofAlgHom (kummerScaleHom n a b c hc) (kummerScaleHom n b a _ hc')
      (kummerScaleHom_comp b a _ c hc' hc hcu.mul_val_inv)
      (kummerScaleHom_comp a b c _ hc hc' hcu.val_inv_mul), fun k x ↦ ?_⟩
    have : (kummerScaleHom n a b c hc).comp (kummerAction n a h.pow_eq_one k : _ →ₐ[A] _) =
        (kummerAction n b h.pow_eq_one k : _ →ₐ[A] _).comp (kummerScaleHom n a b c hc) := by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
        kummerAction_root, map_mul, kummerScaleHom_root, AlgHom.commutes, map_mul,
        kummerAction_root, AlgEquiv.commutes]
      ring
    exact AlgHom.congr_fun this x

end Classification

section EtaleIff

/-- XI.6.3: over a domain, a primitive `n`-th root of unity in mathlib's sense is primitive over
`A` as soon as `n` is a unit. -/
theorem IsPrimitiveRootOver.of_isPrimitiveRoot [IsDomain A] {ζ : A} (h : IsPrimitiveRoot ζ n)
    (hn : IsUnit (n : A)) : IsPrimitiveRootOver ζ n := by
  refine ⟨h.pow_eq_one, fun i hi0 hin ↦ ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hprod := h.prod_one_sub_pow_eq_order
  have hdvd : 1 - ζ ^ i ∣ ∏ k ∈ Finset.range m, (1 - ζ ^ (k + 1)) := by
    have := Finset.dvd_prod_of_mem (fun k ↦ 1 - ζ ^ (k + 1))
      (Finset.mem_range.mpr (show i - 1 < m by omega))
    rwa [Nat.sub_add_cancel hi0] at this
  rw [hprod] at hdvd
  exact isUnit_of_dvd_unit hdvd (by exact_mod_cast hn)

variable (n) in
/-- XI.6.1, over a field: `μ_n` is not étale when the characteristic divides `n`. -/
theorem not_etale_mu_of_natCast_eq_zero (k : Type*) [Field k] [NeZero n] (hn : (n : k) = 0) :
    ¬ Algebra.Etale k (MuAlgebra k n) := by
  intro het
  set p := ringChar k
  have hpn : p ∣ n := (ringChar.spec k n).mp hn
  have hp0 : p ≠ 0 := fun h0 ↦ NeZero.ne n (Nat.eq_zero_of_zero_dvd (h0 ▸ hpn))
  have hp : p.Prime := (CharP.char_is_prime_or_zero k p).resolve_right hp0
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ := hpn
  have hm0 : 0 < m := Nat.pos_of_ne_zero fun h0 ↦ NeZero.ne n (by rw [hm, h0, mul_zero])
  have hC : ∀ r : ℕ, (X ^ r - 1 : k[X]) = X ^ r - C 1 := fun r ↦ by rw [map_one]
  have : Nontrivial (MuAlgebra k n) := AdjoinRoot.nontrivial _ (by
    rw [hC, degree_X_pow_sub_C (Nat.pos_of_ne_zero (NeZero.ne n))]
    exact_mod_cast NeZero.ne n)
  have : CharP (MuAlgebra k n) p :=
    charP_of_injective_algebraMap (algebraMap k (MuAlgebra k n)).injective p
  have hred : IsReduced (MuAlgebra k n) := Algebra.FormallyUnramified.isReduced_of_field k _
  set x : MuAlgebra k n := AdjoinRoot.root _ ^ m - 1
  have hx : x ^ p = 0 := by
    rw [sub_pow_char, one_pow, ← pow_mul, mul_comm, ← hm, Kummer.mu_root_pow, sub_self]
  have hx0 : x ≠ 0 := by
    intro h0
    have h0' : AdjoinRoot.mk (X ^ n - 1 : k[X]) (X ^ m - 1) = 0 := by
      rw [map_sub, map_pow, AdjoinRoot.mk_X, map_one]; exact h0
    rw [AdjoinRoot.mk_eq_zero] at h0'
    have hne : (X ^ m - 1 : k[X]) ≠ 0 := by rw [hC]; exact X_pow_sub_C_ne_zero hm0 _
    have h1 := natDegree_le_of_dvd h0' hne
    rw [hC, hC, natDegree_X_pow_sub_C, natDegree_X_pow_sub_C] at h1
    have : 2 * m ≤ p * m := Nat.mul_le_mul_right m hp.two_le
    omega
  exact hx0 (hred.eq_zero x ⟨p, hx⟩)

/-- XI.6.1: `μ_n` is étale over `A` if and only if `n` is a unit in `A`, i.e. if and only if the
residue characteristics of `Spec A` are prime to `n`. -/
theorem etale_mu_iff [NeZero n] : Algebra.Etale A (MuAlgebra A n) ↔ IsUnit (n : A) := by
  constructor
  · intro het
    by_contra hn
    obtain ⟨m, hm, hnm⟩ := exists_max_ideal_of_mem_nonunits hn
    let : Field (A ⧸ m) := Ideal.Quotient.field m
    let e : (A ⧸ m) ⊗[A] MuAlgebra A n ≃ₐ[A ⧸ m] MuAlgebra (A ⧸ m) n :=
      (tensorAdjoinRootEquiv (A ⧸ m) (X ^ n - 1)).trans
        (AdjoinRoot.algEquivOfEq (A ⧸ m) _ _ (by simp))
    refine not_etale_mu_of_natCast_eq_zero n (A ⧸ m) ?_ (.of_equiv e)
    rw [← map_natCast (Ideal.Quotient.mk m), Ideal.Quotient.eq_zero_iff_mem]
    exact hnm
  · intro hn
    have := Kummer.etale (a := (1 : A)) hn isUnit_one
    exact .of_equiv (Kummer.muEquiv A n).symm

end EtaleIff

end SGA.SGA1.ExposeXI
