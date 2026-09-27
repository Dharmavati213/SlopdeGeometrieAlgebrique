/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import SGA.Foundations.Fields.SeparablyGenerated

/-!
# Differentials of field extensions and transcendence degree

Let `K / k` be a field extension. We relate `Ω[K⁄k]` to separating transcendence bases
(Bourbaki, *Algèbre* V §16, EGA 0_IV 21.4, Matsumura §26, Stacks, section "Separable
extensions, continued").

## Main results

- `AlgebraicIndependent.kaehlerBasis`: if `x` is a separating transcendence basis of `K / k`
  (or more generally `x` is algebraically independent and `K / k(x)` is separable algebraic),
  the `dxᵢ` form a basis of `Ω[K⁄k]`.
- `KaehlerDifferential.span_D_image_eq_top_of_adjoin_eq_top`: if `K = k(s)`, the `ds`, `s ∈ s`,
  generate `Ω[K⁄k]`.
- `isSeparable_adjoin_of_span_D_image_eq_top`: if `K / k` is finitely generated and the `ds`
  generate `Ω[K⁄k]`, then `K` is separable algebraic over `k(s)`.
- `Algebra.trdeg_le_rank_kaehlerDifferential`: for finitely generated `K / k`,
  `trdeg_k K ≤ dim_K Ω[K⁄k]`.
- `Algebra.isSeparablyGenerated_iff_rank_kaehlerDifferential_le` and
  `Algebra.isSeparablyGenerated_iff_rank_kaehlerDifferential_eq`: for finitely generated `K / k`,
  `K` is separably generated iff `dim_K Ω[K⁄k] = trdeg_k K`, iff `dim_K Ω[K⁄k] ≤ trdeg_k K`.
- `isTranscendenceBasis_of_span_D_eq_top`: if `trdeg_k K` elements `xᵢ` have differentials
  generating `Ω[K⁄k]`, they form a separating transcendence basis; conversely.
-/

open KaehlerDifferential Cardinal

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Basis

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- If `x` is algebraically independent over `k` and `K` is separable algebraic over `k(x)`,
then `K` is formally étale over `k[X]` (via `X ↦ x`). -/
lemma AlgebraicIndependent.formallyEtale_mvPolynomial {ι : Type*} {x : ι → K}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    letI := (MvPolynomial.aeval (R := k) x).toAlgebra
    Algebra.FormallyEtale (MvPolynomial ι k) K := by
  let A := Algebra.adjoin k (Set.range x)
  let L := IntermediateField.adjoin k (Set.range x)
  let e : MvPolynomial ι k ≃ₐ[k] A := hx.aevalEquiv
  let := (MvPolynomial.aeval (R := k) x).toAlgebra
  let : Algebra (MvPolynomial ι k) A := e.toRingEquiv.toRingHom.toAlgebra
  have : IsScalarTower (MvPolynomial ι k) A K := .of_algebraMap_eq fun P ↦ by
    change MvPolynomial.aeval x P = algebraMap A K (hx.aevalEquiv P)
    rw [hx.algebraMap_aevalEquiv]
  have : Algebra.FormallyEtale (MvPolynomial ι k) A :=
    .of_equiv (R := MvPolynomial ι k) (A := MvPolynomial ι k)
      (AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ ↦ rfl)
  have : Algebra.FormallyEtale A L := .of_isLocalization (nonZeroDivisors A)
  have : Algebra.FormallyEtale L K := .of_isSeparable L K
  have : Algebra.FormallyEtale A K := .comp A L K
  exact .comp _ A K

/-- If `x` is algebraically independent over `k` and `K` is separable algebraic over `k(x)`
(e.g. `x` is a separating transcendence basis), then the `dxᵢ` form a basis of `Ω[K⁄k]`. -/
noncomputable def AlgebraicIndependent.kaehlerBasis {ι : Type*} {x : ι → K}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    Module.Basis ι K Ω[K⁄k] :=
  letI := (MvPolynomial.aeval (R := k) x).toAlgebra
  haveI : IsScalarTower k (MvPolynomial ι k) K := .of_algebraMap_eq fun r ↦ by
    simp [RingHom.algebraMap_toAlgebra]
  haveI := hx.formallyEtale_mvPolynomial
  ((mvPolynomialBasis k ι).baseChange K).map
    (tensorKaehlerEquivOfFormallyEtale k (MvPolynomial ι k) K)

@[simp]
lemma AlgebraicIndependent.kaehlerBasis_apply {ι : Type*} {x : ι → K}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] (i : ι) :
    hx.kaehlerBasis i = D k K (x i) := by
  let := (MvPolynomial.aeval (R := k) x).toAlgebra
  rw [AlgebraicIndependent.kaehlerBasis]
  simp only [Module.Basis.map_apply, Module.Basis.baseChange_apply,
    tensorKaehlerEquivOfFormallyEtale_apply, mvPolynomialBasis_apply, mapBaseChange_tmul,
    one_smul, map_D, RingHom.algebraMap_toAlgebra]
  simp

/-- For a separating transcendence basis `x` of `K / k`, `dim_K Ω[K⁄k]` is the cardinality of
`x`, the transcendence degree. -/
lemma Algebra.IsSeparablyGenerated.rank_kaehlerDifferential
    (h : Algebra.IsSeparablyGenerated k K) : Module.rank K Ω[K⁄k] = Algebra.trdeg k K := by
  obtain ⟨s, hs, _⟩ := h
  have : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range ((↑) : s → K))) K := by
    rwa [Subtype.range_coe]
  rw [← hs.1.kaehlerBasis.mk_eq_rank'', hs.cardinalMk_eq_trdeg]

/-- For a separably generated extension, `dim_K Ω[K⁄k] = trdeg_k K` (as natural numbers; both
sides are `0` if the transcendence degree is infinite). -/
lemma Algebra.IsSeparablyGenerated.finrank_kaehlerDifferential
    (h : Algebra.IsSeparablyGenerated k K) :
    Module.finrank K Ω[K⁄k] = (Algebra.trdeg k K).toNat := by
  rw [Module.finrank, h.rank_kaehlerDifferential]

end Basis

section Span

/-- If `K = k(s)`, the differentials `ds` (`s ∈ s`) generate `Ω[K⁄k]` as a `K`-vector space. -/
lemma KaehlerDifferential.span_D_image_eq_top_of_adjoin_eq_top {s : Set K}
    (hs : IntermediateField.adjoin k s = ⊤) : Submodule.span K (D k K '' s) = ⊤ := by
  set M := Submodule.span K (D k K '' s)
  have H (y : K) (hy : y ∈ IntermediateField.adjoin k s) : D k K y ∈ M := by
    refine IntermediateField.adjoin_induction k (p := fun y _ ↦ D k K y ∈ M) ?_ ?_ ?_ ?_ ?_ hy
    · exact fun x hx ↦ Submodule.subset_span ⟨x, hx, rfl⟩
    · intro x
      rw [Derivation.map_algebraMap]
      exact M.zero_mem
    · intro x y _ _ hx hy
      rw [map_add]
      exact M.add_mem hx hy
    · intro x _ hx
      rw [Derivation.leibniz_inv]
      exact M.smul_mem _ hx
    · intro x y _ _ hx hy
      rw [Derivation.leibniz]
      exact M.add_mem (M.smul_mem x hy) (M.smul_mem y hx)
  rw [eq_top_iff, ← span_range_derivation k K, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  exact H y (hs ▸ IntermediateField.mem_top)

/-- If `K / k` is finitely generated and the differentials `ds` (`s ∈ s`) generate `Ω[K⁄k]`,
then `K` is separable algebraic over `k(s)`: indeed `Ω[K⁄k(s)] = 0`. -/
lemma isSeparable_adjoin_of_span_D_image_eq_top [Algebra.EssFiniteType k K] {s : Set K}
    (hs : Submodule.span K (D k K '' s) = ⊤) :
    Algebra.IsSeparable (IntermediateField.adjoin k s) K := by
  set E := IntermediateField.adjoin k s
  have : Algebra.EssFiniteType E K := .of_comp k E K
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨subsingleton_of_forall_eq 0 fun ω ↦ ?_⟩
  obtain ⟨ω, rfl⟩ := map_surjective k E K ω
  have hω : ω ∈ Submodule.span K (D k K '' s) := hs ▸ trivial
  have : Submodule.span K (D k K '' s) ≤ LinearMap.ker ((map k E K K).restrictScalars K) := by
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    have : y = algebraMap E K ⟨y, IntermediateField.subset_adjoin k s hy⟩ := rfl
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.coe_restrictScalars, map_D]
    rw [Algebra.algebraMap_self, RingHom.id_apply, this, Derivation.map_algebraMap]
  exact this hω

/-- If `K / k` is finitely generated, there is a finite `u ⊆ K` with `#u ≤ dim_K Ω[K⁄k]` whose
differentials generate `Ω[K⁄k]`. -/
lemma exists_finite_span_D_image_eq_top [Algebra.EssFiniteType k K] :
    ∃ u : Set K, u.Finite ∧ Submodule.span K (D k K '' u) = ⊤ ∧
      #u ≤ Module.rank K Ω[K⁄k] := by
  obtain ⟨t, ht⟩ := IntermediateField.fg_top k K
  have hspan := span_D_image_eq_top_of_adjoin_eq_top ht
  obtain ⟨b, hbt, hbspan, hbli⟩ := exists_linearIndependent K (D k K '' (t : Set K))
  choose! f hf hDf using fun ω (hω : ω ∈ b) ↦ hbt hω
  refine ⟨f '' b, ((t.finite_toSet.image _).subset hbt).image f, ?_, ?_⟩
  · refine eq_top_iff.mpr (hspan ▸ hbspan ▸ Submodule.span_mono ?_)
    intro ω hω
    exact ⟨f ω, ⟨ω, hω, rfl⟩, hDf ω hω⟩
  · exact mk_image_le.trans hbli.cardinal_le_rank

/-- For a finitely generated extension `K / k`, `trdeg_k K ≤ dim_K Ω[K⁄k]` (Stacks 07P2 part). -/
theorem Algebra.trdeg_le_rank_kaehlerDifferential [Algebra.EssFiniteType k K] :
    Algebra.trdeg k K ≤ Module.rank K Ω[K⁄k] := by
  obtain ⟨u, -, hu, hcard⟩ := exists_finite_span_D_image_eq_top (k := k) (K := K)
  have := isSeparable_adjoin_of_span_D_image_eq_top hu
  have : Algebra.IsAlgebraic (Algebra.adjoin k u) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp inferInstance
  exact (Algebra.IsAlgebraic.trdeg_le_cardinalMk k u).trans hcard

/-- Let `K / k` be finitely generated and `x₁, …, xₙ ∈ K` with `n ≤ trdeg_k K`. If the `dxᵢ`
generate `Ω[K⁄k]`, then the `xᵢ` form a separating transcendence basis of `K / k`
(SGA 1 II.5.8, and the errata to II.5.6). -/
theorem isTranscendenceBasis_of_span_D_eq_top [Algebra.EssFiniteType k K] {ι : Type*} [Finite ι]
    {x : ι → K} (hspan : Submodule.span K (Set.range (D k K ∘ x)) = ⊤)
    (hcard : (Nat.card ι : Cardinal) ≤ Algebra.trdeg k K) :
    IsTranscendenceBasis k x ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K := by
  have hsep : Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K :=
    isSeparable_adjoin_of_span_D_image_eq_top (by rwa [← Set.range_comp])
  have : Algebra.IsAlgebraic (Algebra.adjoin k (Set.range x)) K :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp inferInstance
  refine ⟨Algebra.IsAlgebraic.isTranscendenceBasis_of_lift_le_trdeg_of_finite k x ?_, hsep⟩
  have := Fintype.ofFinite ι
  simpa [Nat.card_eq_fintype_card] using hcard

/-- The differentials of a separating transcendence basis generate `Ω[K⁄k]` (they even form a
basis, `AlgebraicIndependent.kaehlerBasis`). -/
theorem span_D_eq_top_of_isTranscendenceBasis {ι : Type*} {x : ι → K}
    (hx : IsTranscendenceBasis k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    Submodule.span K (Set.range (D k K ∘ x)) = ⊤ := by
  rw [← hx.1.kaehlerBasis.span_eq]
  congr 1
  ext
  simp

/-- The differentials of a separating transcendence basis are linearly independent. -/
theorem linearIndependent_D_of_algebraicIndependent {ι : Type*} {x : ι → K}
    (hx : AlgebraicIndependent k x)
    [Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K] :
    LinearIndependent K (D k K ∘ x) := by
  convert hx.kaehlerBasis.linearIndependent
  ext
  simp

namespace Algebra

/-- For a finitely generated extension `K / k`: `K` is separably generated iff
`dim_K Ω[K⁄k] ≤ trdeg_k K`. -/
theorem isSeparablyGenerated_iff_rank_kaehlerDifferential_le [EssFiniteType k K] :
    IsSeparablyGenerated k K ↔ Module.rank K Ω[K⁄k] ≤ trdeg k K := by
  refine ⟨fun h ↦ h.rank_kaehlerDifferential.le, fun h ↦ ?_⟩
  obtain ⟨u, hfin, hu, hcard⟩ := exists_finite_span_D_image_eq_top (k := k) (K := K)
  have := hfin.to_subtype
  obtain ⟨hb, hsep⟩ := isTranscendenceBasis_of_span_D_eq_top (x := ((↑) : u → K))
    (by rwa [Set.range_comp, Subtype.range_coe])
    (by rw [Nat.cast_card]; exact hcard.trans h)
  exact .of_isTranscendenceBasis hb

/-- For a finitely generated extension `K / k`: `K` is separably generated iff
`dim_K Ω[K⁄k] = trdeg_k K` (in general `dim_K Ω[K⁄k] ≥ trdeg_k K`). -/
theorem isSeparablyGenerated_iff_rank_kaehlerDifferential_eq [EssFiniteType k K] :
    IsSeparablyGenerated k K ↔ Module.rank K Ω[K⁄k] = trdeg k K :=
  ⟨fun h ↦ h.rank_kaehlerDifferential, fun h ↦
    isSeparablyGenerated_iff_rank_kaehlerDifferential_le.mpr h.le⟩

/-- For a finitely generated extension `K / k`, if `Ω[K⁄k]` is generated by `n ≤ trdeg_k K`
elements, then `K` is separably generated (SGA 1 II.5.6, (ii bis) ⇒ (i)). -/
theorem IsSeparablyGenerated.of_span_eq_top [EssFiniteType k K] {ι : Type*} [Finite ι]
    {ω : ι → Ω[K⁄k]} (hω : Submodule.span K (Set.range ω) = ⊤)
    (hcard : (Nat.card ι : Cardinal) ≤ trdeg k K) : IsSeparablyGenerated k K := by
  refine isSeparablyGenerated_iff_rank_kaehlerDifferential_le.mpr (le_trans ?_ hcard)
  have := Fintype.ofFinite ι
  rw [← rank_top, ← hω, Nat.card_eq_fintype_card]
  exact (rank_span_le _).trans (by simpa using Cardinal.mk_range_le_lift (f := ω))

/-- The errata to SGA 1 II.5.6: if `K / k` is finitely generated and separably generated and
`dx₁, …, dxₙ` is a basis of `Ω[K⁄k]`, then the `xᵢ` are algebraically independent, and even
form a separating transcendence basis. -/
theorem IsSeparablyGenerated.isTranscendenceBasis_of_basis [EssFiniteType k K]
    (h : IsSeparablyGenerated k K) {ι : Type*} {x : ι → K} (b : Module.Basis ι K Ω[K⁄k])
    (hb : ∀ i, b i = D k K (x i)) :
    IsTranscendenceBasis k x ∧
      Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K := by
  have : Module.Finite K Ω[K⁄k] := inferInstance
  have := Module.Finite.finite_basis b
  refine isTranscendenceBasis_of_span_D_eq_top ?_ ?_
  · rw [← b.span_eq]
    congr 1
    ext
    simp [hb]
  · have := Fintype.ofFinite ι
    rw [← h.rank_kaehlerDifferential, Nat.card_eq_fintype_card, ← Module.finrank_eq_card_basis b,
      Module.finrank_eq_rank]

end Algebra

/-- For a finitely generated extension `K / k` and `n = trdeg_k K` elements `xᵢ ∈ K`, the
following are equivalent: the `xᵢ` form a separating transcendence basis; the `dxᵢ` form a basis
of `Ω[K⁄k]`; the `dxᵢ` generate `Ω[K⁄k]` (SGA 1 II.5.8 (ii) and the remark after II.5.6). -/
theorem isTranscendenceBasis_and_isSeparable_tfae [Algebra.EssFiniteType k K] {ι : Type*}
    [Finite ι] {x : ι → K} (hcard : (Nat.card ι : Cardinal) = Algebra.trdeg k K) :
    List.TFAE [
      IsTranscendenceBasis k x ∧
        Algebra.IsSeparable (IntermediateField.adjoin k (Set.range x)) K,
      LinearIndependent K (D k K ∘ x) ∧ Submodule.span K (Set.range (D k K ∘ x)) = ⊤,
      Submodule.span K (Set.range (D k K ∘ x)) = ⊤] := by
  tfae_have 1 → 2 := fun ⟨hx, _⟩ ↦
    ⟨linearIndependent_D_of_algebraicIndependent hx.1, span_D_eq_top_of_isTranscendenceBasis hx⟩
  tfae_have 2 → 3 := And.right
  tfae_have 3 → 1 := fun h ↦ isTranscendenceBasis_of_span_D_eq_top h hcard.le
  tfae_finish

end Span
