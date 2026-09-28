/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.RingTheory.Smooth.Locus
import SGA.Foundations.Fields.Differentials
import SGA.Foundations.Fields.MacLane

/-!
# Separable field extensions

A field extension `K / k`, not necessarily algebraic, is *separable* if `L ⊗_k K` is reduced for
every field extension `L / k` (Bourbaki, *Algèbre* V §15; EGA IV 4.6.1; Stacks, section
"Separable extensions, continued"). For a field `K` this is mathlib's
`Algebra.IsGeometricallyReduced k K` (defined by `AlgebraicClosure k ⊗_k K` reduced), which we use
as the notion of separability; we show it has the expected properties:

- `Algebra.IsGeometricallyReduced.isReduced_tensorProduct_of_field`: `L ⊗_k K` is then reduced for
  every field `L / k` (not only the algebraic closure); it suffices to test one `L` containing the
  `p`-th roots of the elements of `k`
  (`Algebra.isGeometricallyReduced_iff_isReduced_tensorProduct_of_field`).
- `Algebra.isGeometricallyReduced_iff_isSeparable`: for algebraic extensions it is
  `Algebra.IsSeparable`.
- `Algebra.IsGeometricallyReduced.of_perfectField_of_field`: every extension of a perfect field is
  separable.
- `Algebra.FormallySmooth.isGeometricallyReduced`: formally smooth extensions are separable
  (Cartier).
- `Algebra.isGeometricallyReduced_tfae`: MacLane's theorem. For `K / k` finitely generated, the
  following are equivalent: `K / k` separable; `L ⊗_k K` reduced for all `L`; MacLane's condition
  (`k`-linearly independent elements have `k`-linearly independent `p`-th powers); `K` separably
  generated; `K` formally smooth over `k`; `dim_K Ω[K⁄k] = trdeg_k K`; `dim_K Ω[K⁄k] ≤ trdeg_k K`
  (EGA 0_IV 21.4.2, 21.7.1; Matsumura Thm 26.2, 26.9; Stacks 030W).
- `Algebra.isSmoothAt_bot_iff_isGeometricallyReduced`: a domain essentially of finite type over
  `k` is smooth at its generic point iff its fraction field is separable over `k`.
- `Algebra.isGeometricallyReduced_iff_forall_isPurelyInseparable`: it suffices to test finite
  purely inseparable extensions.
-/

universe u v

open TensorProduct KaehlerDifferential

namespace Algebra

variable {k : Type v} {K : Type u} [Field k] [Field K] [Algebra k K]

section MacLane

/-- For a field `L` over `k`: if every element of `k` is a `p`-th power in `L` (e.g. `L` perfect)
and `L ⊗_k K` is reduced, then `K` satisfies MacLane's condition. -/
theorem linearIndepOn_pow_of_isReduced_tensorProduct (L : Type*) [Field L] [Algebra k L]
    (p : ℕ) [ExpChar k p] (hL : ∀ c : k, ∃ e : L, e ^ p = algebraMap k L c)
    [IsReduced (L ⊗[k] K)] (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) :=
  LinearIndependent.pow_of_isReduced_tensorProduct p hL hs

/-- A perfect field `L` over `k` contains the `p`-th roots of the elements of `k`. -/
lemma exists_pow_eq_algebraMap_of_perfectField (L : Type*) [Field L] [Algebra k L]
    [PerfectField L] (p : ℕ) [ExpChar k p] (c : k) : ∃ e : L, e ^ p = algebraMap k L c := by
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap k L).injective p
  exact surjective_frobenius L p _

/-- An algebraically closed field `L` over `k` contains the `p`-th roots of the elements of
`k`. -/
lemma exists_pow_eq_algebraMap_of_isAlgClosed (L : Type*) [Field L] [Algebra k L]
    [IsAlgClosed L] (p : ℕ) [ExpChar k p] (c : k) : ∃ e : L, e ^ p = algebraMap k L c :=
  IsAlgClosed.exists_pow_nat_eq _ (expChar_pos k p)

/-- A separable (geometrically reduced) extension satisfies MacLane's condition. -/
theorem IsGeometricallyReduced.linearIndepOn_pow [IsGeometricallyReduced k K] (p : ℕ)
    [ExpChar k p] (s : Finset K) (hs : LinearIndepOn k _root_.id (s : Set K)) :
    LinearIndepOn k (· ^ p) (s : Set K) :=
  have := (isGeometricallyReduced_field_iff k K).mp ‹_›
  linearIndepOn_pow_of_isReduced_tensorProduct (AlgebraicClosure k) p
    (exists_pow_eq_algebraMap_of_isAlgClosed _ p) s hs

/-- MacLane's condition implies separability, for arbitrary `K / k`. -/
theorem IsGeometricallyReduced.of_linearIndepOn_pow (p : ℕ) [ExpChar k p]
    (H : ∀ s : Finset K, LinearIndepOn k _root_.id (s : Set K) →
      LinearIndepOn k (· ^ p) (s : Set K)) : IsGeometricallyReduced k K :=
  (isGeometricallyReduced_field_iff k K).mpr
    (isReduced_tensorProduct_of_linearIndepOn_pow p H _)

/-- If `K / k` is separable, then `L ⊗_k K` is reduced for every field `L` over `k`
(EGA IV 4.6.1). See `Algebra.IsGeometricallyReduced.isReduced_tensorProduct` for arbitrary
`k`-algebras. -/
theorem IsGeometricallyReduced.isReduced_tensorProduct_of_field [IsGeometricallyReduced k K]
    (L : Type*) [Field L] [Algebra k L] : IsReduced (L ⊗[k] K) :=
  isReduced_tensorProduct_of_linearIndepOn_pow (ringExpChar k)
    (IsGeometricallyReduced.linearIndepOn_pow _) L

/-- If `K / k` is separable, then `K ⊗_k L` is reduced for every field `L` over `k`. -/
theorem IsGeometricallyReduced.isReduced_tensorProduct_right_of_field
    [IsGeometricallyReduced k K] (L : Type*) [Field L] [Algebra k L] : IsReduced (K ⊗[k] L) :=
  have := IsGeometricallyReduced.isReduced_tensorProduct_of_field (k := k) (K := K) L
  isReduced_of_injective (Algebra.TensorProduct.comm k K L).toAlgHom
    (Algebra.TensorProduct.comm k K L).injective

/-- `K / k` is separable iff `L ⊗_k K` is reduced for one field `L / k` containing the `p`-th
roots of the elements of `k` (e.g. `L = k^{1/p}`, the perfect closure, or an algebraic closure).
See `Algebra.isGeometricallyReduced_iff_isReduced_tensorProduct` for arbitrary `k`-algebras. -/
theorem isGeometricallyReduced_iff_isReduced_tensorProduct_of_field (L : Type*) [Field L]
    [Algebra k L] (p : ℕ) [ExpChar k p] (hL : ∀ c : k, ∃ e : L, e ^ p = algebraMap k L c) :
    IsGeometricallyReduced k K ↔ IsReduced (L ⊗[k] K) :=
  ⟨fun _ ↦ IsGeometricallyReduced.isReduced_tensorProduct_of_field L,
    fun _ ↦ .of_linearIndepOn_pow p (linearIndepOn_pow_of_isReduced_tensorProduct L p hL)⟩

/-- `K / k` is separable iff `L ⊗_k K` is reduced for every finite purely inseparable extension
`L` of `k` (taken inside an algebraic closure). -/
theorem isGeometricallyReduced_iff_forall_isPurelyInseparable :
    IsGeometricallyReduced k K ↔ ∀ L : IntermediateField k (AlgebraicClosure k),
      FiniteDimensional k L → IsPurelyInseparable k L → IsReduced (L ⊗[k] K) := by
  refine ⟨fun _ L _ _ ↦ IsGeometricallyReduced.isReduced_tensorProduct_of_field L, fun H ↦ ?_⟩
  refine .of_linearIndepOn_pow (ringExpChar k) fun s hs ↦ ?_
  rw [LinearIndepOn, linearIndependent_iff']
  intro t g hg
  choose e he using fun j : s ↦ exists_pow_eq_algebraMap_of_isAlgClosed (AlgebraicClosure k)
    (ringExpChar k) (g j)
  let L := IntermediateField.adjoin k (Set.range e)
  have : FiniteDimensional k L := IntermediateField.finiteDimensional_adjoin fun x _ ↦
    Algebra.IsIntegral.isIntegral x
  have : IsPurelyInseparable k L :=
    (IntermediateField.isPurelyInseparable_adjoin_iff_pow_mem k _ (ringExpChar k)).mpr
      fun _ ⟨j, hj⟩ ↦ ⟨1, g j, by simp [← hj, he]⟩
  have := H L ‹_› ‹_›
  exact LinearIndependent.eq_zero_of_sum_smul_pow_eq_zero (ringExpChar k) (L := L) hs
    (by simpa using hg) (e := fun j ↦ ⟨e j, IntermediateField.subset_adjoin k _ ⟨j, rfl⟩⟩)
    fun j _ ↦ Subtype.ext (by simpa using he j)

variable (k K) in
/-- Every field extension of a perfect field is separable. See
`Algebra.IsGeometricallyReduced.of_perfectField` for reduced `k`-algebras. -/
theorem IsGeometricallyReduced.of_perfectField_of_field [PerfectField k] :
    IsGeometricallyReduced k K := by
  refine .of_linearIndepOn_pow (ringExpChar k) fun s hs ↦ ?_
  have : ExpChar K (ringExpChar k) :=
    expChar_of_injective_algebraMap (algebraMap k K).injective _
  rw [LinearIndepOn, linearIndependent_iff'] at hs ⊢
  intro t g hg i hi
  obtain ⟨e, he⟩ : ∃ e : s → k, ∀ j, e j ^ ringExpChar k = g j :=
    ⟨fun j ↦ (frobeniusEquiv k (ringExpChar k)).symm (g j),
      fun j ↦ frobeniusEquiv_symm_pow_p k (ringExpChar k) (g j)⟩
  have : (∑ j ∈ t, e j • (j : K)) ^ ringExpChar k = 0 := by
    rw [← frobenius_def, map_sum]
    simpa [frobenius_def, smul_pow, he] using hg
  have := hs t e (pow_eq_zero_iff (expChar_ne_zero k _) |>.mp this) i hi
  rw [← he, this, zero_pow (expChar_ne_zero k _)]

/-- A formally smooth field extension is separable (Cartier; EGA 0_IV 19.6.1, 21.4.2;
Matsumura Thm 26.9). -/
theorem FormallySmooth.isGeometricallyReduced [FormallySmooth k K] :
    IsGeometricallyReduced k K :=
  .of_linearIndepOn_pow (ringExpChar k) fun _ hs ↦ FormallySmooth.linearIndependent_pow _ hs

/-- A separable finitely generated extension is separably generated (MacLane). -/
theorem IsGeometricallyReduced.isSeparablyGenerated [IsGeometricallyReduced k K]
    [EssFiniteType k K] : IsSeparablyGenerated k K :=
  IsSeparablyGenerated.of_linearIndepOn_pow (ringExpChar k)
    (IsGeometricallyReduced.linearIndepOn_pow _)

end MacLane

section Algebraic

/-- A separably generated algebraic extension is separable (its separating transcendence basis
is empty). -/
theorem IsSeparablyGenerated.isSeparable [Algebra.IsAlgebraic k K]
    (h : IsSeparablyGenerated k K) : Algebra.IsSeparable k K := by
  obtain ⟨s, hs, hsep⟩ := h
  obtain rfl : s = ∅ :=
    Set.isEmpty_coe_sort.mp (hs.isEmpty_iff_isAlgebraic.mpr inferInstance)
  rw [IntermediateField.adjoin_empty] at hsep
  have := IntermediateField.isSeparable_bot (F := k) (E := K)
  exact Algebra.IsSeparable.trans k (⊥ : IntermediateField k K) K

/-- For an algebraic extension, separability in the sense of `IsGeometricallyReduced` is
mathlib's `Algebra.IsSeparable`. -/
theorem isGeometricallyReduced_iff_isSeparable [Algebra.IsAlgebraic k K] :
    IsGeometricallyReduced k K ↔ Algebra.IsSeparable k K := by
  refine ⟨fun h ↦ ⟨fun x ↦ ?_⟩, fun _ ↦ IsSeparablyGenerated.of_isSeparable.isGeometricallyReduced⟩
  let E := IntermediateField.adjoin k {x}
  have : IsGeometricallyReduced k E := .of_injective E.val E.val.injective
  have : FiniteDimensional k E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have := (IsGeometricallyReduced.isSeparablyGenerated (k := k) (K := E)).isSeparable
  exact (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable k K).mp this

/-- An algebraic extension is formally smooth iff it is separable. For instance a finite
inseparable extension `K / k` is not smooth over `k`, although `Ω[K⁄k]` is free
(the remark after SGA 1 II.5.7). -/
theorem formallySmooth_iff_isSeparable [Algebra.IsAlgebraic k K] :
    FormallySmooth k K ↔ Algebra.IsSeparable k K :=
  ⟨fun _ ↦ isGeometricallyReduced_iff_isSeparable.mp FormallySmooth.isGeometricallyReduced,
    fun _ ↦ IsSeparablyGenerated.of_isSeparable.formallySmooth⟩

end Algebraic

section FiniteType

variable [EssFiniteType k K]

/-- A finitely generated extension is separable iff it is separably generated. -/
theorem isGeometricallyReduced_iff_isSeparablyGenerated :
    IsGeometricallyReduced k K ↔ IsSeparablyGenerated k K :=
  ⟨fun _ ↦ IsGeometricallyReduced.isSeparablyGenerated, fun h ↦ h.isGeometricallyReduced⟩

/-- A finitely generated extension is separable iff it is formally smooth (EGA 0_IV 19.6.1). -/
theorem formallySmooth_iff_isGeometricallyReduced :
    FormallySmooth k K ↔ IsGeometricallyReduced k K :=
  ⟨fun _ ↦ FormallySmooth.isGeometricallyReduced, fun _ ↦
    IsGeometricallyReduced.isSeparablyGenerated.formallySmooth⟩

/-- MacLane's theorem and the differential criterion for finitely generated field extensions
(EGA 0_IV 21.4.2, Matsumura Thm 26.2 and 26.9, Stacks 030W). Here `p` is the exponential
characteristic and `L` ranges over all field extensions of `k` in the universe of `k`. -/
theorem isGeometricallyReduced_tfae (p : ℕ) [ExpChar k p] :
    List.TFAE [
      IsGeometricallyReduced k K,
      ∀ (L : Type v) [Field L] [Algebra k L], IsReduced (L ⊗[k] K),
      ∀ s : Finset K, LinearIndepOn k _root_.id (s : Set K) → LinearIndepOn k (· ^ p) (s : Set K),
      IsSeparablyGenerated k K,
      FormallySmooth k K,
      Module.rank K Ω[K⁄k] = trdeg k K,
      Module.rank K Ω[K⁄k] ≤ trdeg k K] := by
  tfae_have 1 → 2 := fun _ L _ _ ↦ IsGeometricallyReduced.isReduced_tensorProduct_of_field L
  tfae_have 2 → 3 := fun h ↦
    have := h (AlgebraicClosure k)
    linearIndepOn_pow_of_isReduced_tensorProduct (AlgebraicClosure k) p
      (exists_pow_eq_algebraMap_of_isAlgClosed _ p)
  tfae_have 3 → 4 := IsSeparablyGenerated.of_linearIndepOn_pow p
  tfae_have 4 → 5 := IsSeparablyGenerated.formallySmooth
  tfae_have 5 → 1 := fun _ ↦ FormallySmooth.isGeometricallyReduced
  tfae_have 4 ↔ 6 := isSeparablyGenerated_iff_rank_kaehlerDifferential_eq
  tfae_have 4 ↔ 7 := isSeparablyGenerated_iff_rank_kaehlerDifferential_le
  tfae_finish

end FiniteType

section SmoothAt

/-- A domain `A` essentially of finite type over a field `k` is smooth over `k` at its generic
point iff its field of fractions `F` is separable over `k`. -/
theorem isSmoothAt_bot_iff_isGeometricallyReduced {A F : Type*} [CommRing A] [IsDomain A]
    [Algebra k A] [EssFiniteType k A] [Field F] [Algebra A F] [Algebra k F] [IsScalarTower k A F]
    [IsFractionRing A F] : IsSmoothAt k (⊥ : Ideal A) ↔ IsGeometricallyReduced k F := by
  have : IsFractionRing A (Localization.AtPrime (⊥ : Ideal A)) := by
    simpa [Ideal.primeCompl_bot] using Localization.isLocalization (M := (⊥ : Ideal A).primeCompl)
  let e : Localization.AtPrime (⊥ : Ideal A) ≃ₐ[k] F :=
    (IsLocalization.algEquiv (nonZeroDivisors A) _ _).restrictScalars k
  have : EssFiniteType k F :=
    have : EssFiniteType A F := .of_isLocalization F (nonZeroDivisors A)
    .comp k A F
  rw [← formallySmooth_iff_isGeometricallyReduced]
  exact ⟨fun _ ↦ .of_equiv e, fun _ ↦ .of_equiv e.symm⟩

end SmoothAt

end Algebra
