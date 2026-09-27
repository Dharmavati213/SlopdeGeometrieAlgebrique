/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.QuotSMulTop
import SGA.Foundations.CommAlg.Depth
import SGA.SGA1.ExposeIV.LocalCriterion

/-!
# Depth along flat local homomorphisms

Let `A → B` be a flat local homomorphism of noetherian local rings with residue field
`k = A/𝔪_A`, `M` a finite `A`-module and `N` a finite `B`-module that is flat over `A`. Then
(EGA IV₂ 6.3.1; Matsumura, *Commutative Ring Theory*, §23)

  `depth_B (N ⊗_A M) = depth_A M + depth_B (N ⊗_A k)`.

For `M = A` and `N = B` this gives `depth B = depth A + depth (B/𝔪_A B)`, and together with the
dimension formula `dim B = dim A + dim (B/𝔪_A B)` it gives: `B` is Cohen–Macaulay iff `A` and the
closed fibre `B/𝔪_A B` are (EGA IV₂ §6.3).

## Main results

* `IsLocalRing.depth_tensorProduct_eq`: the depth formula for modules (EGA IV₂ 6.3.1).
* `IsLocalRing.depth_eq_add_of_flat`: `depth B = depth A + depth F` for any local ring `F`
  presented as `B/𝔪_A B`.
* `IsLocalRing.ringKrullDim_eq_add_of_flat`: `dim B = dim A + dim F`.
* `IsLocalRing.depth_eq_ringKrullDim_iff_of_flat`: `B` is Cohen–Macaulay iff `A` and `F` are.
* `IsLocalRing.ringKrullDim_eq_depth_add_iff_of_flat`: if `F` is Cohen–Macaulay, `A` and `B`
  have the same codepth `dim - depth`.
* `Ideal.depth_map_of_surjective`: the depth of a module over a quotient ring does not depend on
  the ring over which it is computed.

Depth is `Ideal.depth` (weakly regular sequences), so the zero module has depth `⊤`; the formula
holds in `ℕ∞` without nontriviality assumptions. Cohen–Macaulayness of a noetherian local ring `R`
is written `((maximalIdeal R).depth R : WithBot ℕ∞) = ringKrullDim R`.

The proof is the classical induction: an `M`-regular element of `𝔪_A` stays regular on `N ⊗ M`
by flatness; an element of `𝔪_B` regular on `N ⊗ k` is regular on `N` with `A`-flat cokernel by
the local flatness criterion (SGA 1 IV.5.7), hence regular on `N ⊗ M`; in depth `0` both sides
contain a nonzero vector killed by the maximal ideal (associated primes and prime avoidance).
-/

universe u

open IsLocalRing RingTheory.Sequence TensorProduct
open scoped Pointwise

namespace Ideal

/-- A module with a trivial underlying type has infinite depth. -/
theorem depth_eq_top_of_subsingleton {R : Type*} [CommRing R] (I : Ideal R) (M : Type*)
    [AddCommGroup M] [Module R M] [Subsingleton M] : I.depth M = ⊤ := by
  rw [Ideal.depth_eq_top_iff]
  intro n
  refine ⟨List.replicate n 0, by simp, fun r hr ↦ (List.eq_of_mem_replicate hr) ▸ I.zero_mem, ?_⟩
  induction n generalizing M with
  | zero => exact IsWeaklyRegular.nil R M
  | succ n ih =>
    rw [List.replicate_succ, isWeaklyRegular_cons_iff]
    exact ⟨fun a b _ ↦ Subsingleton.elim a b, ih _⟩

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Change of rings: for a surjection `R → S`, an ideal `I` of `R` and an `S`-module `P`, the
`I S`-depth of `P` over `S` is the `I`-depth of `P` over `R`. -/
theorem depth_map_of_surjective (hs : Function.Surjective (algebraMap R S)) (I : Ideal R)
    (P : Type*) [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P] :
    (I.map (algebraMap R S)).depth P = I.depth P := by
  classical
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff, le_depth_iff]
  constructor
  · rintro ⟨ss, hlen, hmem, hreg⟩
    let g : S → R := fun s ↦ if h : ∃ r ∈ I, algebraMap R S r = s then h.choose else 0
    have hg : ∀ s ∈ ss, g s ∈ I ∧ algebraMap R S (g s) = s := fun s hs' ↦ by
      have h : ∃ r ∈ I, algebraMap R S r = s :=
        (Ideal.mem_map_iff_of_surjective _ hs).mp (hmem s hs')
      simp only [g, h, ↓reduceDIte]
      exact h.choose_spec
    have hmap : (ss.map g).map (algebraMap R S) = ss := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id ss]
      exact List.map_congr_left fun s hs' ↦ (hg s hs').2
    refine ⟨ss.map g, by simp [hlen], fun r hr ↦ ?_, ?_⟩
    · obtain ⟨s, hs', rfl⟩ := List.mem_map.mp hr
      exact (hg s hs').1
    · rw [← isWeaklyRegular_map_algebraMap_iff S P, hmap]
      exact hreg
  · rintro ⟨rs, hlen, hmem, hreg⟩
    refine ⟨rs.map (algebraMap R S), by simp [hlen], fun s hs' ↦ ?_,
      (isWeaklyRegular_map_algebraMap_iff S P rs).mpr hreg⟩
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs'
    exact Ideal.mem_map_of_mem _ (hmem r hr)

end Ideal

namespace QuotSMulTop

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  (M : Type u) [AddCommGroup M] [Module A M]

/-- Heterobasic form of `QuotSMulTop.tensorQuotSMulTopEquivQuotSMulTop`: for `x ∈ A` and a
`B`-module `N`, `N ⊗_A (M/xM) ≅ (N ⊗_A M)/x(N ⊗_A M)` as `B`-modules. -/
noncomputable def tensorAlgebraMapEquiv (x : A) :
    N ⊗[A] QuotSMulTop x M ≃ₗ[B] QuotSMulTop (algebraMap A B x) (N ⊗[A] M) :=
  (AlgebraTensorModule.cancelBaseChange A B B N (QuotSMulTop x M)).symm ≪≫ₗ
    LinearEquiv.lTensor N (algebraMapTensorEquivTensorQuotSMulTop x M B).symm ≪≫ₗ
    tensorQuotSMulTopEquivQuotSMulTop (algebraMap A B x) N (B ⊗[A] M) ≪≫ₗ
    QuotSMulTop.congr (algebraMap A B x) (AlgebraTensorModule.cancelBaseChange A B B N M)

/-- Heterobasic form of `QuotSMulTop.quotSMulTopTensorEquivQuotSMulTop`: for `y ∈ B`,
`(N/yN) ⊗_A M ≅ (N ⊗_A M)/y(N ⊗_A M)` as `B`-modules. -/
noncomputable def quotTensorEquiv (y : B) :
    QuotSMulTop y N ⊗[A] M ≃ₗ[B] QuotSMulTop y (N ⊗[A] M) :=
  (AlgebraTensorModule.cancelBaseChange A B B (QuotSMulTop y N) M).symm ≪≫ₗ
    quotSMulTopTensorEquivQuotSMulTop y (B ⊗[A] M) N ≪≫ₗ
    QuotSMulTop.congr y (AlgebraTensorModule.cancelBaseChange A B B N M)

end QuotSMulTop

section Regular

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  (N : Type u) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  (M : Type u) [AddCommGroup M] [Module A M]

/-- If `x ∈ A` is `M`-regular and `N` is `A`-flat, the image of `x` in `B` is `N ⊗_A M`-regular. -/
theorem IsSMulRegular.tensor_algebraMap_of_flat [Module.Flat A N] {x : A}
    (hx : IsSMulRegular M x) : IsSMulRegular (N ⊗[A] M) (algebraMap A B x) := by
  have h := Module.Flat.lTensor_preserves_injective_linearMap (M := N)
    (DistribSMul.toLinearMap A M x) hx
  have heq : ⇑((DistribSMul.toLinearMap A M x).lTensor N) =
      fun y : N ⊗[A] M ↦ algebraMap A B x • y := by
    funext y
    rw [algebraMap_smul]
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul n m => simp
    | add y z hy hz => simp_all [smul_add]
  rw [heq] at h
  exact h

private theorem coe_rTensor_restrictScalars_smul (y : B) :
    ⇑(((DistribSMul.toLinearMap B N y).restrictScalars A).rTensor M) =
      fun z : N ⊗[A] M ↦ y • z := by
  funext z
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul n m => simp [TensorProduct.smul_tmul']
  | add y z hy hz => simp_all [smul_add]

end Regular

namespace IsLocalRing

section DepthZero

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- A module containing a nonzero vector killed by the maximal ideal has depth `0`. -/
theorem depth_eq_zero_of_smul_eq_zero {M : Type*} [AddCommGroup M] [Module R M] {m : M}
    (hm : m ≠ 0) (h : ∀ r ∈ maximalIdeal R, r • m = 0) : (maximalIdeal R).depth M = 0 := by
  rw [← Order.lt_one_iff, lt_iff_not_ge, Ideal.one_le_depth_iff]
  rintro ⟨r, hr, hreg⟩
  exact hm (hreg (by simpa using h r hr : r • m = r • (0 : M)))

variable [IsNoetherianRing R] {M : Type u} [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module of depth `0` over a noetherian local ring contains a nonzero vector killed by
the maximal ideal, i.e. the maximal ideal is an associated prime. -/
theorem exists_ne_zero_forall_smul_eq_zero_of_depth_eq_zero
    (h : (maximalIdeal R).depth M = 0) :
    ∃ m : M, m ≠ 0 ∧ ∀ r ∈ maximalIdeal R, r • m = 0 := by
  classical
  have hreg : ∀ r ∈ maximalIdeal R, ¬ IsSMulRegular M r := fun r hr hr' ↦ by
    have := (Ideal.one_le_depth_iff).mpr ⟨r, hr, hr'⟩
    rw [h] at this
    exact absurd this (by simp)
  have hsub : ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ p ∈ (associatedPrimes.finite R M).toFinset, (p : Set R) := by
    intro r hr
    have hz : r ∈ { r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0 } := by
      by_contra hne
      apply hreg r hr
      intro a b hab
      by_contra hab'
      exact hne ⟨a - b, sub_ne_zero.mpr hab', by rw [smul_sub]; exact sub_eq_zero.mpr hab⟩
    rw [← biUnion_associatedPrimes_eq_zero_divisors] at hz
    simpa using hz
  obtain ⟨p, hp, hle⟩ := (Ideal.subset_union_prime (f := id) ⊥ ⊥ (fun i hi _ _ ↦
    ((Set.Finite.mem_toFinset _).mp hi).isPrime)).mp hsub
  have hpA : IsAssociatedPrime p M := (Set.Finite.mem_toFinset _).mp hp
  have hpm : p = maximalIdeal R :=
    ((maximalIdeal.isMaximal R).eq_of_le hpA.isPrime.ne_top hle).symm
  obtain ⟨-, x, hx⟩ := (isAssociatedPrime_iff).mp hpA
  refine ⟨x, fun hx0 ↦ hpA.isPrime.ne_top ?_, fun r hr ↦ ?_⟩
  · rw [hx, hx0]
    ext r
    simp [Submodule.mem_colon_singleton]
  · have : r ∈ p := hpm ▸ hr
    rw [hx, Submodule.mem_colon_singleton] at this
    simpa using this

end DepthZero

/-- The depth of a local ring is invariant under ring isomorphisms. -/
theorem depth_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (e : R ≃+* S) : (maximalIdeal R).depth R = (maximalIdeal S).depth S := by
  let := e.toRingHom.toAlgebra
  have h := Ideal.depth_map_of_surjective (R := R) (S := S) e.surjective (maximalIdeal R) S
  rw [map_maximalIdeal_of_surjective (algebraMap R S) e.surjective] at h
  rw [h]
  exact Ideal.depth_eq_of_linearEquiv (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl).toLinearEquiv

/-- The dimension of a noetherian local ring is a natural number. -/
theorem exists_natCast_eq_ringKrullDim (R : Type*) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ∃ m : ℕ, ringKrullDim R = ((m : ℕ∞) : WithBot ℕ∞) := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ringKrullDim_ne_bot (R := R))
  have hlt := ringKrullDim_lt_top (R := R)
  rw [← hd] at hlt
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (WithBot.coe_lt_coe.mp hlt).ne
  exact ⟨m, hd.symm⟩

/-- The depth of a noetherian local ring is a natural number. -/
theorem exists_natCast_eq_depth (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] : ∃ m : ℕ, (maximalIdeal R).depth R = m :=
  ENat.ne_top_iff_exists.mp (depth_ne_top (M := R)) |>.imp fun _ h ↦ h.symm

section Flat

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

/-- Nakayama: if `N` is a finite `B`-module with `N ⊗_A k = 0`, then `N = 0`. -/
theorem subsingleton_of_subsingleton_tensor_residueField
    (N : Type u) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [Subsingleton (N ⊗[A] (A ⧸ maximalIdeal A))] : Subsingleton N := by
  have h1 : Subsingleton (N ⧸ (maximalIdeal A) • (⊤ : Submodule A N)) :=
    (tensorQuotEquivQuotSMul N (maximalIdeal A)).symm.toEquiv.subsingleton
  rw [Submodule.Quotient.subsingleton_iff] at h1
  have h2 : (⊤ : Submodule B N) ≤
      (maximalIdeal A).map (algebraMap A B) • (⊤ : Submodule B N) := by
    intro n _
    have hn : n ∈ (maximalIdeal A) • (⊤ : Submodule A N) := by rw [h1]; trivial
    have hle : (maximalIdeal A) • (⊤ : Submodule A N) ≤
        (((maximalIdeal A).map (algebraMap A B)) • (⊤ : Submodule B N)).restrictScalars A := by
      refine Submodule.smul_le.2 fun a ha y _ ↦ ?_
      rw [Submodule.restrictScalars_mem, ← algebraMap_smul B a y]
      exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ ha) trivial
    exact hle hn
  have h3 := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ ⊤
    (Module.finite_def.mp inferInstance) h2
    (SGA.SGA1.ExposeIV.map_maximalIdeal_le_jacobson _ le_rfl)
  exact (Submodule.subsingleton_iff B).mp (subsingleton_iff_bot_eq_top.mp h3.symm)

variable [IsNoetherianRing A] [IsNoetherianRing B]

open SGA.SGA1.ExposeIV in
private theorem depth_tensorProduct_aux (a b : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
      (N : Type u) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
      [Module.Finite B N] [Module.Flat A N],
      (maximalIdeal A).depth M = a →
      (maximalIdeal B).depth (N ⊗[A] (A ⧸ maximalIdeal A)) = b →
      (maximalIdeal B).depth (N ⊗[A] M) = a + b := by
  induction a with
  | succ a iha =>
    -- an `M`-regular `x ∈ 𝔪_A` is `N ⊗ M`-regular, and `N ⊗ (M/xM) = (N ⊗ M)/x`
    intro M _ _ _ N _ _ _ _ _ _ hM hN
    have hfin : Module.Finite B (N ⊗[A] M) := finite_tensorProduct N M
    have h1 : 1 ≤ (maximalIdeal A).depth M := by rw [hM]; exact_mod_cast Nat.le_add_left 1 a
    obtain ⟨x, hx, hreg⟩ := Ideal.one_le_depth_iff.mp h1
    have hq := Ideal.depth_quotSMulTop_add_one hx hreg
    rw [hM, Nat.cast_add, Nat.cast_one] at hq
    have hq' := iha (QuotSMulTop x M) N (ENat.add_left_injective_of_ne_top ENat.one_ne_top hq) hN
    rw [Ideal.depth_eq_of_linearEquiv (QuotSMulTop.tensorAlgebraMapEquiv N M x)] at hq'
    rw [← Ideal.depth_quotSMulTop_add_one (algebraMap_mem_maximalIdeal hx)
      (IsSMulRegular.tensor_algebraMap_of_flat N M hreg), hq']
    push_cast
    ring
  | zero =>
    induction b with
    | succ b ihb =>
      -- a `y ∈ 𝔪_B` regular on `N ⊗ k` is `N`-regular with `N/yN` flat over `A` (IV.5.7)
      intro M _ _ _ N _ _ _ _ _ _ hM hN
      have hfin : Module.Finite B (N ⊗[A] M) := finite_tensorProduct N M
      have hfink : Module.Finite B (N ⊗[A] (A ⧸ maximalIdeal A)) :=
        finite_tensorProduct N (A ⧸ maximalIdeal A)
      have h1 : 1 ≤ (maximalIdeal B).depth (N ⊗[A] (A ⧸ maximalIdeal A)) := by
        rw [hN]; exact_mod_cast Nat.le_add_left 1 b
      obtain ⟨y, hy, hreg⟩ := Ideal.one_le_depth_iff.mp h1
      let u := DistribSMul.toLinearMap B N y
      have hinj : Function.Injective ((u.restrictScalars A).rTensor (A ⧸ maximalIdeal A)) := by
        rw [coe_rTensor_restrictScalars_smul]; exact hreg
      obtain ⟨hu, hflat⟩ := (injective_and_flat_coker_iff u).mpr hinj
      have hrange : y • (⊤ : Submodule B N) = LinearMap.range u := by
        rw [Submodule.pointwise_smul_def, Submodule.map_top]
      have : Module.Flat A (QuotSMulTop y N) := Module.Flat.of_linearEquiv
        ((Submodule.quotEquivOfEq _ _ hrange).restrictScalars A)
      have hexact : Function.Exact (u.restrictScalars A)
          ((y • (⊤ : Submodule B N)).mkQ.restrictScalars A) := by
        intro n
        simp [hrange]
      have hregM : IsSMulRegular (N ⊗[A] M) y := by
        have := (rTensor_shortExact_of_flat (M'' := QuotSMulTop y N) (u.restrictScalars A)
          ((y • (⊤ : Submodule B N)).mkQ.restrictScalars A) hu hexact
          (Submodule.mkQ_surjective (y • (⊤ : Submodule B N))) M).1
        rwa [coe_rTensor_restrictScalars_smul] at this
      have hqk := Ideal.depth_quotSMulTop_add_one hy hreg
      rw [hN, Nat.cast_add, Nat.cast_one, ← Ideal.depth_eq_of_linearEquiv
        (QuotSMulTop.quotTensorEquiv N (A ⧸ maximalIdeal A) y)] at hqk
      have hq' := ihb M (QuotSMulTop y N) hM
        (ENat.add_left_injective_of_ne_top ENat.one_ne_top hqk)
      rw [Ideal.depth_eq_of_linearEquiv (QuotSMulTop.quotTensorEquiv N M y)] at hq'
      rw [← Ideal.depth_quotSMulTop_add_one hy hregM, hq']
      push_cast
      ring
    | zero =>
      -- vectors killed by `𝔪_A` in `M` and by `𝔪_B` in `N ⊗ k` give one killed by `𝔪_B` in
      -- `N ⊗ M`, through the injection `N ⊗ k → N ⊗ M`
      intro M _ _ _ N _ _ _ _ _ _ hM hN
      have hfink : Module.Finite B (N ⊗[A] (A ⧸ maximalIdeal A)) :=
        finite_tensorProduct N (A ⧸ maximalIdeal A)
      obtain ⟨z, hz0, hz⟩ := exists_ne_zero_forall_smul_eq_zero_of_depth_eq_zero hM
      obtain ⟨w, hw0, hw⟩ := exists_ne_zero_forall_smul_eq_zero_of_depth_eq_zero hN
      let f : (A ⧸ maximalIdeal A) →ₗ[A] M := (maximalIdeal A).liftQ
        (LinearMap.toSpanSingleton A M z) (fun r hr ↦ by simpa using hz r hr)
      have hf : Function.Injective f := by
        rw [injective_iff_map_eq_zero]
        intro c hc
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
        by_contra hne
        have hr : r ∉ maximalIdeal A := fun hr ↦ hne (Ideal.Quotient.eq_zero_iff_mem.mpr hr)
        have hc' : r • z = 0 := hc
        obtain ⟨v, rfl⟩ := (IsLocalRing.notMem_maximalIdeal.mp hr)
        exact hz0 (by simpa using congrArg (fun m ↦ (↑v⁻¹ : A) • m) hc')
      let g := AlgebraTensorModule.lTensor B N f
      have hg : Function.Injective g := by
        rw [AlgebraTensorModule.coe_lTensor]
        exact Module.Flat.lTensor_preserves_injective_linearMap f hf
      simp only [CharP.cast_eq_zero, add_zero]
      exact depth_eq_zero_of_smul_eq_zero (m := g w)
        (fun h ↦ hw0 (hg (h.trans (map_zero g).symm)))
        (fun r hr ↦ by rw [← map_smul, hw r hr, map_zero])

open SGA.SGA1.ExposeIV in
/-- **Depth along a flat local homomorphism** (EGA IV₂ 6.3.1): let `A → B` be a local
homomorphism of noetherian local rings, `M` a finite `A`-module and `N` a finite `B`-module flat
over `A`. Then `depth_B (N ⊗_A M) = depth_A M + depth_B (N ⊗_A k)`, `k = A/𝔪_A`.

EGA writes the last term as the depth of `N/𝔪_A N` over the fibre ring `B/𝔪_A B`, which is the
same (`Ideal.depth_map_of_surjective`). -/
theorem depth_tensorProduct_eq (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (N : Type u) [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [Module.Finite B N] [Module.Flat A N] :
    (maximalIdeal B).depth (N ⊗[A] M) =
      (maximalIdeal A).depth M + (maximalIdeal B).depth (N ⊗[A] (A ⧸ maximalIdeal A)) := by
  by_cases hM : Subsingleton M
  · rw [Ideal.depth_eq_top_of_subsingleton _ M,
      Ideal.depth_eq_top_of_subsingleton (maximalIdeal B) (N ⊗[A] M), top_add]
  by_cases hN : Subsingleton (N ⊗[A] (A ⧸ maximalIdeal A))
  · have : Subsingleton N := subsingleton_of_subsingleton_tensor_residueField (A := A) (B := B) N
    rw [Ideal.depth_eq_top_of_subsingleton (maximalIdeal B) (N ⊗[A] (A ⧸ maximalIdeal A)),
      Ideal.depth_eq_top_of_subsingleton (maximalIdeal B) (N ⊗[A] M), add_top]
  rw [not_subsingleton_iff_nontrivial] at hM hN
  have : Module.Finite B (N ⊗[A] (A ⧸ maximalIdeal A)) :=
    finite_tensorProduct N (A ⧸ maximalIdeal A)
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp (depth_ne_top (R := A) (M := M))
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp
    (depth_ne_top (R := B) (M := N ⊗[A] (A ⧸ maximalIdeal A)))
  rw [← ha, ← hb]
  exact depth_tensorProduct_aux a b M N ha.symm hb.symm

variable [Module.Flat A B] {F : Type u} [CommRing F] [IsLocalRing F] {φ : B →+* F}
  (hφ : Function.Surjective φ) (hker : RingHom.ker φ = (maximalIdeal A).map (algebraMap A B))

include hφ hker

/-- **Depth along a flat local homomorphism**, ring form (EGA IV₂ 6.3.1): if `A → B` is a flat
local homomorphism of noetherian local rings and `F = B/𝔪_A B` is its closed fibre (given as any
local ring with a surjection `φ : B → F` of kernel `𝔪_A B`), then
`depth B = depth A + depth F`. -/
theorem depth_eq_add_of_flat :
    (maximalIdeal B).depth B = (maximalIdeal A).depth A + (maximalIdeal F).depth F := by
  have h := depth_tensorProduct_eq A B (A := A) (B := B)
  rw [Ideal.depth_eq_of_linearEquiv (AlgebraTensorModule.rid A B B)] at h
  rw [h]
  congr 1
  let := φ.toAlgebra
  let e₁ : B ⊗[A] (A ⧸ maximalIdeal A) ≃ₗ[B] B ⧸ (maximalIdeal A).map (algebraMap A B) :=
    (Ideal.qoutMapEquivTensorQout B).symm
  let e₂ : (B ⧸ (maximalIdeal A).map (algebraMap A B)) ≃ₐ[B] F :=
    (Ideal.quotientEquivAlgOfEq B hker.symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId B F) hφ)
  rw [Ideal.depth_eq_of_linearEquiv (e₁.trans e₂.toLinearEquiv),
    ← Ideal.depth_map_of_surjective hφ (maximalIdeal B) F,
    map_maximalIdeal_of_surjective (algebraMap B F) hφ]

/-- **Dimension along a flat local homomorphism** (EGA IV₂ 6.1.1): with `F = B/𝔪_A B` as in
`depth_eq_add_of_flat`, `dim B = dim A + dim F`. -/
theorem ringKrullDim_eq_add_of_flat :
    ringKrullDim B = ringKrullDim A + ringKrullDim F := by
  set J := (maximalIdeal A).map (algebraMap A B)
  let e : B ⧸ J ≃+* F :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hφ)
  have : Nontrivial (B ⧸ J) := e.toEquiv.nontrivial
  have : IsLocalRing (B ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A)
    (maximalIdeal B)
  rw [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, h, WithBot.coe_add,
    maximalIdeal_height_eq_ringKrullDim, maximalIdeal_height_eq_ringKrullDim,
    ringKrullDim_eq_of_ringEquiv e]

/-- **Cohen–Macaulay rings along a flat local homomorphism** (EGA IV₂ §6.3): with
`F = B/𝔪_A B` as in `depth_eq_add_of_flat`, `B` is Cohen–Macaulay iff `A` and `F` are. -/
theorem depth_eq_ringKrullDim_iff_of_flat :
    ((maximalIdeal B).depth B : WithBot ℕ∞) = ringKrullDim B ↔
      ((maximalIdeal A).depth A : WithBot ℕ∞) = ringKrullDim A ∧
        ((maximalIdeal F).depth F : WithBot ℕ∞) = ringKrullDim F := by
  have : IsNoetherianRing F := isNoetherianRing_of_surjective B F φ hφ
  have hA := depth_le_ringKrullDim (R := A) (M := A)
  have hF := depth_le_ringKrullDim (R := F) (M := F)
  rw [depth_eq_add_of_flat hφ hker, ringKrullDim_eq_add_of_flat hφ hker]
  obtain ⟨a, ha⟩ := exists_natCast_eq_depth A
  obtain ⟨f, hf⟩ := exists_natCast_eq_depth F
  obtain ⟨m, hm⟩ := exists_natCast_eq_ringKrullDim A
  obtain ⟨n, hn⟩ := exists_natCast_eq_ringKrullDim F
  rw [ha, hm] at hA ⊢
  rw [hf, hn] at hF ⊢
  norm_cast at hA hF ⊢
  omega

/-- **Codepth along a flat local homomorphism**: with `F = B/𝔪_A B` as in `depth_eq_add_of_flat`
and `F` Cohen–Macaulay, `A` and `B` have the same codepth `dim - depth`: for every `c : ℕ`,
`dim B = depth B + c` iff `dim A = depth A + c`. -/
theorem ringKrullDim_eq_depth_add_iff_of_flat
    (hF : ((maximalIdeal F).depth F : WithBot ℕ∞) = ringKrullDim F) (c : ℕ) :
    ringKrullDim B = ((maximalIdeal B).depth B : WithBot ℕ∞) + ((c : ℕ∞) : WithBot ℕ∞) ↔
      ringKrullDim A = ((maximalIdeal A).depth A : WithBot ℕ∞) + ((c : ℕ∞) : WithBot ℕ∞) := by
  rw [depth_eq_add_of_flat hφ hker, ringKrullDim_eq_add_of_flat hφ hker, ← hF]
  have : IsNoetherianRing F := isNoetherianRing_of_surjective B F φ hφ
  obtain ⟨a, ha⟩ := exists_natCast_eq_depth A
  obtain ⟨f, hf⟩ := exists_natCast_eq_depth F
  obtain ⟨m, hm⟩ := exists_natCast_eq_ringKrullDim A
  rw [ha, hm, hf]
  norm_cast
  omega

end Flat

end IsLocalRing
