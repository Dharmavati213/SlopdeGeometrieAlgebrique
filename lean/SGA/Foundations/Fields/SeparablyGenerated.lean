/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Unramified.Field

/-!
# Separably generated field extensions

A field extension `K / k` is *separably generated* if it has a *separating transcendence basis*:
an algebraically independent family `s` such that `K` is separable algebraic over `k(s)`
(Bourbaki, *Algèbre* V §16; EGA IV 4.6; Matsumura, *Commutative ring theory*, §26).

## Main results

- `Algebra.IsSeparablyGenerated`: the predicate.
- `Algebra.IsSeparable.isReduced_tensorProduct`: if `K / E` is separable algebraic, then
  `F ⊗_E K` is reduced for every field `F` over `E`.
- `AlgebraicIndependent.isDomain_adjoin_tensorProduct`: for algebraically independent `x`,
  `k(x) ⊗_k L` is a domain for every field `L` over `k`.
- `Algebra.IsSeparablyGenerated.isReduced_tensorProduct`: a separably generated extension is
  geometrically reduced: `L ⊗_k K` is reduced for every field extension `L` of `k`.
- `Algebra.IsSeparablyGenerated.formallySmooth`: separably generated extensions are formally
  smooth (mathlib).
- Separably generated extensions in special cases: separable algebraic extensions, all extensions
  in characteristic zero, finitely generated extensions of perfect fields.
-/

open TensorProduct

namespace Algebra

variable (k K : Type*) [Field k] [Field K] [Algebra k K]

/-- A field extension `K / k` is *separably generated* if it admits a separating transcendence
basis, that is a transcendence basis `s` such that `K` is separable (algebraic) over `k(s)`. -/
def IsSeparablyGenerated : Prop :=
  ∃ s : Set K, IsTranscendenceBasis k ((↑) : s → K) ∧
    Algebra.IsSeparable (IntermediateField.adjoin k s) K

variable {k K}

lemma IsSeparablyGenerated.of_isTranscendenceBasis {ι : Type*} {x : ι → K}
    (hx : IsTranscendenceBasis k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    IsSeparablyGenerated k K :=
  ⟨Set.range x, hx.to_subtype_range, ‹_›⟩

/-- A separably generated extension is formally smooth. -/
lemma IsSeparablyGenerated.formallySmooth (h : IsSeparablyGenerated k K) :
    FormallySmooth k K := by
  obtain ⟨s, hs, _⟩ := h
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    rwa [Subtype.range_coe]
  exact .of_algebraicIndependent_of_isSeparable hs.1

/-- A separable algebraic extension is separably generated (by the empty transcendence
basis). -/
lemma IsSeparablyGenerated.of_isSeparable [Algebra.IsSeparable k K] :
    IsSeparablyGenerated k K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  obtain rfl : s = ∅ :=
    Set.isEmpty_coe_sort.mp (hs.isEmpty_iff_isAlgebraic.mpr inferInstance)
  refine ⟨∅, hs, ?_⟩
  rw [IntermediateField.adjoin_empty]
  exact Algebra.isSeparable_tower_top_of_isSeparable k (⊥ : IntermediateField k K) K

/-- In characteristic zero every field extension is separably generated. -/
lemma IsSeparablyGenerated.of_charZero [CharZero k] : IsSeparablyGenerated k K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  have : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K :=
    hs.isAlgebraic_field
  have : CharZero (IntermediateField.adjoin k (Set.range ((↑) : s → K))) :=
    charZero_of_injective_algebraMap (algebraMap k _).injective
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact .of_isTranscendenceBasis hs

variable (k K) in
/-- A finitely generated extension of a perfect field is separably generated (mathlib). -/
lemma IsSeparablyGenerated.of_perfectField [PerfectField k] [EssFiniteType k K] :
    IsSeparablyGenerated k K := by
  obtain ⟨s, hs, H⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  exact ⟨s, hs, H⟩

/-- A finitely generated separably generated extension has a finite separating transcendence
basis. -/
lemma IsSeparablyGenerated.exists_finset [EssFiniteType k K] (h : IsSeparablyGenerated k K) :
    ∃ s : Finset K, IsTranscendenceBasis k ((↑) : s → K) ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (s : Set K)) K := by
  obtain ⟨s, hs, hsep⟩ := h
  have : Finite s := finite_of_isTranscendenceBasis hs
  lift s to Finset K using Set.toFinite s
  exact ⟨s, hs, hsep⟩

end Algebra

section Reduced

/-- If `K / E` is separable algebraic, then `F ⊗_E K` is reduced for every field `F` over `E`
(it is a directed union of finite étale `F`-algebras). -/
theorem Algebra.IsSeparable.isReduced_tensorProduct {E K F : Type*} [Field E] [Field K] [Field F]
    [Algebra E K] [Algebra E F] [Algebra.IsSeparable E K] : IsReduced (F ⊗[E] K) := by
  refine IsReduced.tensorProduct_of_flat_of_forall_fg fun B ⟨t, ht⟩ ↦ ?_
  let B' := IntermediateField.adjoin E (t : Set K)
  have : FiniteDimensional E B' := IntermediateField.finiteDimensional_adjoin
    fun x _ ↦ (Algebra.IsSeparable.isSeparable E x).isIntegral
  have hle : B ≤ B'.toSubalgebra := ht ▸ IntermediateField.algebra_adjoin_le_adjoin E _
  have : Algebra.FormallyUnramified E B' := .of_isSeparable E B'
  have : IsReduced (F ⊗[E] B') := by
    exact Algebra.FormallyUnramified.isReduced_of_field F (F ⊗[E] B')
  exact isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id F F)
    (Subalgebra.inclusion hle)) (Module.Flat.lTensor_preserves_injective_linearMap (M := F)
      (Subalgebra.inclusion hle).toLinearMap (Subalgebra.inclusion_injective hle))

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- If `x` is algebraically independent over `k`, then `k(x) ⊗_k L` is a domain for every field
`L` over `k`: it is a localization of `L[X]`. -/
theorem AlgebraicIndependent.isDomain_adjoin_tensorProduct {k K ι : Type*} [Field k] [Field K]
    [Algebra k K] {x : ι → K} (hx : AlgebraicIndependent k x) (L : Type*) [Field L]
    [Algebra k L] : IsDomain (IntermediateField.adjoin k (Set.range x) ⊗[k] L) := by
  let A := Algebra.adjoin k (Set.range x)
  let E := IntermediateField.adjoin k (Set.range x)
  have hA : IsDomain (A ⊗[k] L) := by
    let e : A ⊗[k] L ≃ₐ[k] MvPolynomial ι L :=
      (Algebra.TensorProduct.congr hx.aevalEquiv.symm AlgEquiv.refl).trans
        ((Algebra.TensorProduct.comm k _ _).trans
          ((MvPolynomial.algebraTensorAlgEquiv k L).restrictScalars k))
    exact e.toMulEquiv.isDomain
  let := (Algebra.TensorProduct.map (Algebra.ofId A E) (AlgHom.id k L)).toAlgebra
  have := IsLocalization.tensorProduct_tensorProduct k L (nonZeroDivisors A) E (by
    ext; simp [RingHom.algebraMap_toAlgebra])
  refine IsLocalization.isDomain_of_le_nonZeroDivisors (E ⊗[k] L)
    (M := Algebra.algebraMapSubmonoid (A ⊗[k] L) (nonZeroDivisors A)) ?_
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero fun h ↦ nonZeroDivisors.ne_zero ha ?_
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply] at h
  exact Algebra.TensorProduct.includeLeft_injective (R := k) (S := k) (A := A) (B := L)
    (algebraMap k L).injective (a₁ := a) (a₂ := 0) (by simpa using h)

/-- If `E ⊗_k L` is a domain and `K / E` is separable algebraic, then `K ⊗_k L` is reduced:
it embeds in `K ⊗_E Frac(E ⊗_k L)`. -/
theorem isReduced_tensorProduct_of_isDomain_of_isSeparable {k E K L : Type*} [Field k] [Field E]
    [Field K] [Field L] [Algebra k E] [Algebra E K] [Algebra k K] [IsScalarTower k E K]
    [Algebra k L] [IsDomain (E ⊗[k] L)] [Algebra.IsSeparable E K] : IsReduced (K ⊗[k] L) := by
  let F := FractionRing (E ⊗[k] L)
  have : IsReduced (F ⊗[E] K) := Algebra.IsSeparable.isReduced_tensorProduct
  have : IsReduced (K ⊗[E] F) :=
    isReduced_of_injective (Algebra.TensorProduct.comm E K F).toAlgHom
      (Algebra.TensorProduct.comm E K F).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id K K)
      (IsScalarTower.toAlgHom E (E ⊗[k] L) F)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K)
      (IsScalarTower.toAlgHom E (E ⊗[k] L) F).toLinearMap
      (IsFractionRing.injective (E ⊗[k] L) F)
  have : IsReduced (K ⊗[E] (E ⊗[k] L)) := isReduced_of_injective _ hinj
  exact isReduced_of_injective (Algebra.TensorProduct.cancelBaseChange k E K K L).symm.toAlgHom
    (Algebra.TensorProduct.cancelBaseChange k E K K L).symm.injective

namespace Algebra.IsSeparablyGenerated

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A separably generated extension `K / k` is geometrically reduced: `K ⊗_k L` is reduced for
every field extension `L` of `k` (Bourbaki, *Algèbre* V §15, EGA IV 4.6.1). -/
theorem isReduced_tensorProduct_right (h : IsSeparablyGenerated k K) (L : Type*) [Field L]
    [Algebra k L] : IsReduced (K ⊗[k] L) := by
  obtain ⟨s, hs, _⟩ := h
  have : IsDomain (IntermediateField.adjoin k s ⊗[k] L) := by
    have := hs.1.isDomain_adjoin_tensorProduct L
    rwa [Subtype.range_coe] at this
  exact isReduced_tensorProduct_of_isDomain_of_isSeparable (E := IntermediateField.adjoin k s)

/-- A separably generated extension `K / k` is geometrically reduced: `L ⊗_k K` is reduced for
every field extension `L` of `k`. -/
theorem isReduced_tensorProduct (h : IsSeparablyGenerated k K) (L : Type*) [Field L]
    [Algebra k L] : IsReduced (L ⊗[k] K) :=
  have := h.isReduced_tensorProduct_right L
  isReduced_of_injective (Algebra.TensorProduct.comm k L K).toAlgHom
    (Algebra.TensorProduct.comm k L K).injective

/-- A separably generated extension is geometrically reduced in the sense of mathlib. -/
theorem isGeometricallyReduced (h : IsSeparablyGenerated k K) : IsGeometricallyReduced k K :=
  (isGeometricallyReduced_field_iff k K).mpr (h.isReduced_tensorProduct _)

end Algebra.IsSeparablyGenerated

end Reduced
