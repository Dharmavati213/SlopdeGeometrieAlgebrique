/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced
import SGA.Foundations.Fields.Separable

/-!
# Geometrically reduced algebras over a field

Mathlib defines `Algebra.IsGeometricallyReduced k A` by: `AlgebraicClosure k ⊗_k A` is reduced.
We show that this is equivalent to the definition of EGA IV 4.6.2 and Stacks 030S
(`L ⊗_k A` is reduced for every field extension `L / k`) and give the usual criteria.

## Main results

- `Algebra.IsGeometricallyReduced.isReduced_tensorProduct`: if `A` is geometrically reduced over
  `k`, then `L ⊗_k A` is reduced for every field `L` over `k` (the TODO of
  `Mathlib.RingTheory.Nilpotent.GeometricallyReduced`, for a base field).
- `Algebra.isGeometricallyReduced_iff_isReduced_tensorProduct`: it suffices to test one field
  containing the `p`-th roots of the elements of `k` (`k^{1/p}`, the perfect closure, …)
  (Stacks 030V).
- `Algebra.isGeometricallyReduced_iff_forall_minimalPrimes`: a noetherian `k`-algebra `A` is
  geometrically reduced iff it is reduced and its local rings at the minimal primes (the fields
  of fractions of its irreducible components) are separable extensions of `k` (Stacks 030U,
  EGA IV 4.6.3).
- `Algebra.IsGeometricallyReduced.of_perfectField`: over a perfect field, reduced algebras are
  geometrically reduced (Stacks 030U, EGA IV 4.6.1).
-/

universe u

open TensorProduct

section Flat

variable {A M : Type*} [CommRing A] [IsReduced A]

/-- In a reduced ring, an element outside all minimal primes is a non-zero-divisor. -/
theorem mem_nonZeroDivisors_of_forall_notMem_minimalPrimes {a : A}
    (ha : ∀ p ∈ minimalPrimes A, a ∉ p) : a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff_right]
  intro y hy
  by_contra hy0
  have : a ∈ ⋃ p ∈ minimalPrimes A, (p : Set A) := by
    rw [minimalPrimes, Ideal.iUnion_minimalPrimes]
    have hr : (⊥ : Ideal A).radical = ⊥ := nilradical_eq_zero A
    refine ⟨y, ?_, ?_⟩
    · rwa [hr, Ideal.mem_bot]
    · rw [hr, Ideal.mem_bot, mul_comm]
      exact hy
  simp only [Set.mem_iUnion, SetLike.mem_coe] at this
  obtain ⟨p, hp, hap⟩ := this
  exact ha p hp hap

variable [IsNoetherianRing A] [AddCommGroup M] [Module A M] [Module.Flat A M]

/-- Over a reduced noetherian ring `A`, an element of a flat `A`-module that vanishes at every
minimal prime (i.e. is killed by an element outside each minimal prime) is zero: `M` embeds in
`∏_{𝔭 minimal} M_𝔭`. -/
theorem Module.Flat.eq_zero_of_forall_minimalPrimes {x : M}
    (h : ∀ p ∈ minimalPrimes A, ∃ a ∉ p, a • x = 0) : x = 0 := by
  let J : Ideal A := (Submodule.span A {x}).annihilator
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hJ : ¬ (J : Set A) ⊆ ⋃ p ∈ (↑hfin.toFinset : Set (Ideal A)), ((id p : Ideal A) : Set A) := by
    rw [Ideal.subset_union_prime (f := id) ⊥ ⊥
      fun p hp _ _ ↦ ((hfin.mem_toFinset.mp hp).isPrime)]
    rintro ⟨p, hp, hJp⟩
    obtain ⟨a, ha, hax⟩ := h p (hfin.mem_toFinset.mp hp)
    exact ha (hJp ((Submodule.mem_annihilator_span_singleton x a).mpr hax))
  obtain ⟨a, haJ, hanot⟩ := Set.not_subset.mp hJ
  have hreg : a ∈ nonZeroDivisors A := mem_nonZeroDivisors_of_forall_notMem_minimalPrimes
    fun p hp hap ↦ hanot (Set.mem_biUnion (by simpa using hp) hap)
  exact (Module.Flat.isSMulRegular_of_nonZeroDivisors hreg).right_eq_zero_of_smul
    ((Submodule.mem_annihilator_span_singleton x a).mp haJ)

end Flat

namespace Algebra

variable {k : Type*} {A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- In a reduced ring, the localization at a minimal prime is a field. -/
theorem isField_localization_atPrime_of_mem_minimalPrimes [IsReduced A] {p : Ideal A}
    [p.IsPrime] (hp : p ∈ minimalPrimes A) : IsField (Localization.AtPrime p) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq]
  have h := IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
    (A := Localization.AtPrime p) p ⊥ hp
  rw [Ideal.map_bot, Localization.AtPrime.map_eq_maximalIdeal] at h
  rw [← h]
  exact nilradical_eq_zero _

/-- If `A` is reduced after base change to `L`, so is every localization of `A`. -/
lemma isReduced_tensorProduct_of_isLocalization (L : Type*) [CommRing L] [Algebra k L]
    (M : Submonoid A) (B : Type u) [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsLocalization M B] [IsReduced (A ⊗[k] L)] : IsReduced (B ⊗[k] L) := by
  let := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A B) (AlgHom.id k L)).toAlgebra
  have : IsScalarTower A (A ⊗[k] L) (B ⊗[k] L) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply]
  have := IsLocalization.tensorProduct_tensorProduct k L M B (by
    ext; simp [RingHom.algebraMap_toAlgebra])
  exact isReduced_localizationPreserves (Algebra.algebraMapSubmonoid (A ⊗[k] L) M)
    (B ⊗[k] L) ‹_›

/-- `A_𝔭 ⊗_k L` is the localization of `A ⊗_k L` at `𝔭`. -/
lemma isLocalization_atPrime_tensorProduct (L : Type*) [CommRing L] [Algebra k L] (p : Ideal A)
    [p.IsPrime] :
    letI := (Algebra.TensorProduct.map (Algebra.ofId A (Localization.AtPrime p))
      (AlgHom.id k L)).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] L) p.primeCompl)
      (Localization.AtPrime p ⊗[k] L) := by
  let := (Algebra.TensorProduct.map (Algebra.ofId A (Localization.AtPrime p))
    (AlgHom.id k L)).toAlgebra
  exact IsLocalization.tensorProduct_tensorProduct k L p.primeCompl _ (by
    ext; simp [RingHom.algebraMap_toAlgebra])

/-- If `A ⊗_k L` is reduced, so is `A_𝔭 ⊗_k L`. -/
lemma isReduced_localization_atPrime_tensorProduct (L : Type*) [CommRing L] [Algebra k L]
    (p : Ideal A) [p.IsPrime] [IsReduced (A ⊗[k] L)] :
    IsReduced (Localization.AtPrime p ⊗[k] L) :=
  isReduced_tensorProduct_of_isLocalization L p.primeCompl _

/-- Let `A` be a reduced noetherian `k`-algebra and `L` a `k`-algebra. If `A_𝔭 ⊗_k L` is reduced
for every minimal prime `𝔭` of `A`, then `A ⊗_k L` is reduced. -/
theorem isReduced_tensorProduct_of_forall_minimalPrimes [IsNoetherianRing A] [IsReduced A]
    (L : Type*) [CommRing L] [Algebra k L]
    (h : ∀ (p : Ideal A) [p.IsPrime], p ∈ minimalPrimes A →
      IsReduced (Localization.AtPrime p ⊗[k] L)) :
    IsReduced (A ⊗[k] L) := by
  refine ⟨fun x hx ↦ Module.Flat.eq_zero_of_forall_minimalPrimes (A := A) fun p hp ↦ ?_⟩
  have := hp.isPrime
  let := (Algebra.TensorProduct.map (Algebra.ofId A (Localization.AtPrime p))
    (AlgHom.id k L)).toAlgebra
  have := isLocalization_atPrime_tensorProduct (k := k) L p
  have := h p hp
  have h0 : algebraMap (A ⊗[k] L) (Localization.AtPrime p ⊗[k] L) x = 0 :=
    (hx.map _).eq_zero
  obtain ⟨⟨_, a, ha, rfl⟩, hax⟩ :=
    (IsLocalization.map_eq_zero_iff (Algebra.algebraMapSubmonoid (A ⊗[k] L) p.primeCompl) _
      x).mp h0
  exact ⟨a, ha, by rwa [Algebra.smul_def]⟩

variable [IsNoetherianRing A]

/-- A noetherian `k`-algebra `A` is geometrically reduced iff it is reduced and its localizations
at minimal primes (the function fields of its irreducible components) are separable over `k`
(Stacks 030U, EGA IV 4.6.3). -/
theorem isGeometricallyReduced_iff_forall_minimalPrimes :
    IsGeometricallyReduced k A ↔ IsReduced A ∧
      ∀ (p : Ideal A) [p.IsPrime], p ∈ minimalPrimes A →
        IsGeometricallyReduced k (Localization.AtPrime p) := by
  refine ⟨fun h ↦ ⟨isReduced_of_isGeometricallyReduced k, fun p _ hp ↦ ?_⟩, fun ⟨_, h⟩ ↦ ?_⟩
  · have : IsReduced (A ⊗[k] AlgebraicClosure k) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k A (AlgebraicClosure k)).toAlgHom
        (Algebra.TensorProduct.comm k A _).injective
    have := isReduced_localization_atPrime_tensorProduct (k := k) (AlgebraicClosure k) p
    rw [isGeometricallyReduced_field_iff]
    exact isReduced_of_injective (Algebra.TensorProduct.comm k _ _).toAlgHom
      (Algebra.TensorProduct.comm k _ _).injective
  · rw [isGeometricallyReduced_field_iff]
    have := isReduced_tensorProduct_of_forall_minimalPrimes (k := k) (A := A)
      (AlgebraicClosure k) fun p _ hp ↦ by
        have := h p hp
        exact isReduced_of_injective (Algebra.TensorProduct.comm k _ _).toAlgHom
          (Algebra.TensorProduct.comm k _ _).injective
    exact isReduced_of_injective (Algebra.TensorProduct.comm k _ _).toAlgHom
      (Algebra.TensorProduct.comm k _ _).injective


end Algebra

namespace Algebra

variable {k : Type*} {A : Type u} [Field k] [CommRing A] [Algebra k A]

/-- The key step: let `L₀` be a field over `k` containing the `p`-th roots of the elements of `k`
(`p` the exponential characteristic). If `L₀ ⊗_k A` is reduced, then `L ⊗_k A` is reduced for
every field `L` over `k`. One reduces to `A` of finite type, hence noetherian and reduced; the
local rings of `A` at its minimal primes are fields, which are separable by MacLane's criterion.
-/
theorem isReduced_tensorProduct_of_isReduced_tensorProduct (L₀ : Type*) [Field L₀] [Algebra k L₀]
    (p : ℕ) [ExpChar k p] (hL₀ : ∀ c : k, ∃ e : L₀, e ^ p = algebraMap k L₀ c)
    [IsReduced (L₀ ⊗[k] A)] (L : Type*) [Field L] [Algebra k L] : IsReduced (L ⊗[k] A) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B hB ↦ ?_
  have : FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsNoetherianRing B := FiniteType.isNoetherianRing k B
  have : IsReduced (L₀ ⊗[k] B) := isReduced_of_injective
    (Algebra.TensorProduct.map (AlgHom.id L₀ L₀) B.val)
    (Module.Flat.lTensor_preserves_injective_linearMap (M := L₀) B.val.toLinearMap
      Subtype.val_injective)
  have : IsReduced (B ⊗[k] L₀) :=
    isReduced_of_injective (Algebra.TensorProduct.comm k B L₀).toAlgHom
      (Algebra.TensorProduct.comm k B L₀).injective
  have : IsReduced B := isReduced_of_injective
    (Algebra.TensorProduct.includeRight : B →ₐ[k] L₀ ⊗[k] B)
    (Algebra.TensorProduct.includeRight_injective (algebraMap k L₀).injective)
  have : IsReduced (B ⊗[k] L) := isReduced_tensorProduct_of_forall_minimalPrimes L fun q _ hq ↦ by
    have := isReduced_localization_atPrime_tensorProduct (k := k) L₀ q
    let := (isField_localization_atPrime_of_mem_minimalPrimes hq).toField
    have : IsReduced (L₀ ⊗[k] Localization.AtPrime q) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k _ _).toAlgHom
        (Algebra.TensorProduct.comm k _ _).injective
    have : IsGeometricallyReduced k (Localization.AtPrime q) :=
      (isGeometricallyReduced_iff_isReduced_tensorProduct_of_field L₀ p hL₀).mpr this
    exact IsGeometricallyReduced.isReduced_tensorProduct_right_of_field L
  exact isReduced_of_injective (Algebra.TensorProduct.comm k L B).toAlgHom
    (Algebra.TensorProduct.comm k L B).injective

/-- If `A` is geometrically reduced over `k`, then `L ⊗_k A` is reduced for every field `L` over
`k` (EGA IV 4.6.2, Stacks 030S; the TODO of `Mathlib.RingTheory.Nilpotent.GeometricallyReduced`
for a base field). -/
theorem IsGeometricallyReduced.isReduced_tensorProduct [IsGeometricallyReduced k A]
    (L : Type*) [Field L] [Algebra k L] : IsReduced (L ⊗[k] A) :=
  have := (isGeometricallyReduced_field_iff k A).mp ‹_›
  isReduced_tensorProduct_of_isReduced_tensorProduct (AlgebraicClosure k) (ringExpChar k)
    (exists_pow_eq_algebraMap_of_isAlgClosed _ _) L

/-- If `A` is geometrically reduced over `k`, then `A ⊗_k L` is reduced for every field `L`
over `k`. -/
theorem IsGeometricallyReduced.isReduced_tensorProduct_right [IsGeometricallyReduced k A]
    (L : Type*) [Field L] [Algebra k L] : IsReduced (A ⊗[k] L) :=
  have := IsGeometricallyReduced.isReduced_tensorProduct (k := k) (A := A) L
  isReduced_of_injective (Algebra.TensorProduct.comm k A L).toAlgHom
    (Algebra.TensorProduct.comm k A L).injective

/-- A `k`-algebra `A` is geometrically reduced iff `L ⊗_k A` is reduced for one field `L / k`
containing the `p`-th roots of the elements of `k`, e.g. `L = k^{1/p}` (Stacks 030V). -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct (L : Type*) [Field L] [Algebra k L]
    (p : ℕ) [ExpChar k p] (hL : ∀ c : k, ∃ e : L, e ^ p = algebraMap k L c) :
    IsGeometricallyReduced k A ↔ IsReduced (L ⊗[k] A) :=
  ⟨fun _ ↦ IsGeometricallyReduced.isReduced_tensorProduct L, fun _ ↦
    (isGeometricallyReduced_field_iff k A).mpr
      (isReduced_tensorProduct_of_isReduced_tensorProduct L p hL _)⟩

/-- A `k`-algebra `A` is geometrically reduced iff `L ⊗_k A` is reduced for one perfect field `L`
over `k`, e.g. the perfect closure of `k` (Stacks 030V). -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_of_perfectField (L : Type*) [Field L]
    [Algebra k L] [PerfectField L] : IsGeometricallyReduced k A ↔ IsReduced (L ⊗[k] A) :=
  isGeometricallyReduced_iff_isReduced_tensorProduct L (ringExpChar k)
    (exists_pow_eq_algebraMap_of_perfectField L _)

/-- A `k`-algebra `A` is geometrically reduced iff `L ⊗_k A` is reduced for every field `L`
over `k` (in the universe of `k`). -/
theorem isGeometricallyReduced_iff_forall_isReduced_tensorProduct {k : Type u_1} [Field k]
    [Algebra k A] :
    IsGeometricallyReduced k A ↔ ∀ (L : Type u_1) [Field L] [Algebra k L], IsReduced (L ⊗[k] A) :=
  ⟨fun _ L _ _ ↦ IsGeometricallyReduced.isReduced_tensorProduct L,
    fun h ↦ (isGeometricallyReduced_field_iff k A).mpr (h _)⟩

variable (k A) in
/-- Over a perfect field, every reduced algebra is geometrically reduced (Stacks 030U,
EGA IV 4.6.1). -/
theorem IsGeometricallyReduced.of_perfectField [PerfectField k] [IsReduced A] :
    IsGeometricallyReduced k A := by
  refine IsGeometricallyReduced.of_forall_fg fun B hB ↦ ?_
  have : FiniteType k B := (Subalgebra.fg_iff_finiteType B).mp hB
  have : IsNoetherianRing B := FiniteType.isNoetherianRing k B
  have : IsReduced B := isReduced_of_injective B.val Subtype.val_injective
  refine isGeometricallyReduced_iff_forall_minimalPrimes.mpr ⟨this, fun q _ hq ↦ ?_⟩
  let := (isField_localization_atPrime_of_mem_minimalPrimes hq).toField
  exact IsGeometricallyReduced.of_perfectField_of_field k _

variable (k A) in
/-- In characteristic zero, every reduced algebra is geometrically reduced. -/
theorem IsGeometricallyReduced.of_charZero [CharZero k] [IsReduced A] :
    IsGeometricallyReduced k A :=
  .of_perfectField k A

/-- If `A` is geometrically reduced over `k`, so is every localization of `A`. -/
theorem IsGeometricallyReduced.of_isLocalization [IsGeometricallyReduced k A] (M : Submonoid A)
    (B : Type u) [CommRing B] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [IsLocalization M B] : IsGeometricallyReduced k B := by
  have : IsReduced (A ⊗[k] AlgebraicClosure k) :=
    IsGeometricallyReduced.isReduced_tensorProduct_right (AlgebraicClosure k)
  have := isReduced_tensorProduct_of_isLocalization (k := k) (AlgebraicClosure k) M B
  exact (isGeometricallyReduced_field_iff k B).mpr (isReduced_of_injective
    (Algebra.TensorProduct.comm k _ _).toAlgHom (Algebra.TensorProduct.comm k _ _).injective)

end Algebra
