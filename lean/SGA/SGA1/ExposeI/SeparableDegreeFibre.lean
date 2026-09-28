/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.FieldTheory.SeparableDegree
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeI.StandardEtale

/-!
# SGA 1, Exposé I, I.10.12: the separable degree of the closed fibre

Let `A` be an integrally closed local domain with residue field `k` and fraction field `K`, `L` a
finite extension of `K` and `B ⊆ L` a finite `A`-subalgebra with fraction field `L`. Let `n'` be
the separable degree of `B/𝔪B` over `k`, i.e. the number of its geometric points
`B → k̄` (`= ∑_q [κ(q) : k]_s` over the primes `q` of `B` over `𝔪`). Then `n' ≤ [L : K]_s`, and
`n' = [L : K]` iff `B` is étale over `A` (I.10.12).

This is proved here when `k` is infinite, following SGA's proof of the equality case
(`separableDegree_fiber_le_of_infinite`). A single element `b ∈ B` separates the geometric points
(`finite_algHom_and_exists_injective`; a vector space over an infinite field is not a finite union
of proper subspaces). They are roots of the reduction of the minimal polynomial `F ∈ A[X]` of `b`,
and a reduction of an irreducible polynomial has at most as many distinct roots as its separable
degree (`natSepDegree_map_le`): this gives `n' ≤ [K(b) : K]_s ≤ [L : K]_s`. If `n' = [L : K]`, then
`L = K(b)` and the reduction of `F` is separable, so `A[b] ≅ A[t]/(F)` is étale (I.7.4), hence
integrally closed with fraction field `L` (I.9.5(i)), and contains `B`. Conversely, if `B` is
étale, `B ≅ A[t]/(F)` with `F` monic separable (I.7.5), which has `deg F ≥ [L : K]` geometric
points. For a finite residue field SGA reduces to the infinite case through `A(t)`; the general
case (`separableDegree_fiber_le_Statement`) is proved in `GeometricPoints` through the strict
henselization instead.
-/

universe u

namespace SGA.SGA1.ExposeI

open Polynomial IsLocalRing IntermediateField

section Reduction

variable {A K k : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K] [Field k]

/-- Reduction does not increase the separable degree: if `F ∈ A[X]` is irreducible over the
fraction field `K` of `A`, the number of distinct roots of `F` reduced along `A → k` is at most
the separable degree of `F` over `K`. (Write `F = G(X^{q^m})` with `G` separable over `K`; then
`G ∈ A[X]` and the reduction of `F` has at most `deg G` distinct roots.) -/
theorem natSepDegree_map_le (φ : A →+* k) {F : A[X]}
    (hirr : Irreducible (F.map (algebraMap A K))) :
    (F.map φ).natSepDegree ≤ (F.map (algebraMap A K)).natSepDegree := by
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨q, hK⟩ := ExpChar.exists K
  -- `k` has the same exponential characteristic as `K`, unless `K` has characteristic `0`
  have hk : q = 1 ∨ ExpChar k q := by
    rcases hK with _ | ⟨hprime⟩
    · exact Or.inl rfl
    · refine Or.inr (ExpChar.prime hprime (hchar := ?_))
      rw [CharP.charP_iff_prime_eq_zero hprime]
      have hqA : (q : A) = 0 := hinj (by rw [map_natCast, map_zero, CharP.cast_eq_zero])
      rw [← map_natCast φ, hqA, map_zero]
  obtain ⟨g, hg, m, hgf⟩ := hirr.hasSeparableContraction q
  rw [IsSeparableContraction.natSepDegree_eq ⟨hg, m, hgf⟩]
  have hq : 0 < q ^ m := pow_pos (expChar_pos K q) m
  -- `g` has coefficients in `A`
  have hlift : g ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [← coeff_expand_mul hq, hgf, coeff_map]
    exact ⟨_, rfl⟩
  obtain ⟨G, hGg⟩ := hlift
  replace hGg : G.map (algebraMap A K) = g := hGg
  have hGdeg : G.natDegree = g.natDegree := by
    rw [← hGg, natDegree_map_eq_of_injective hinj]
  -- `F = G(X^{q^m})`
  have hF : F = expand A (q ^ m) G := by
    apply Polynomial.map_injective _ hinj
    rw [map_expand, hGg, hgf]
  have hle : (G.map φ).natSepDegree ≤ g.natDegree :=
    (natSepDegree_le_natDegree _).trans (natDegree_map_le.trans hGdeg.le)
  rw [hF, map_expand]
  rcases hk with hone | hk
  · rw [hone, one_pow, expand_one]
    exact hle
  · rw [natSepDegree_expand]
    exact hle

end Reduction

section Points

variable {A B : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B]

/-- The geometric points `B → k̄` of the closed fibre of a finite `A`-algebra `B` (`A` local with
residue field `k`) are finite in number, and when `k` is infinite they are separated by a single
element of `B`. -/
theorem finite_algHom_and_exists_injective [Infinite (ResidueField A)] :
    Finite (B →ₐ[A] AlgebraicClosure (ResidueField A)) ∧
      ∃ b : B, Function.Injective fun φ : B →ₐ[A] AlgebraicClosure (ResidueField A) ↦ φ b := by
  classical
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  let I := (maximalIdeal A).map (algebraMap A B)
  let R := B ⧸ I
  let : Algebra k R := Ideal.Quotient.algebraQuotientMapQuotient
  have : IsScalarTower A k R := Ideal.Quotient.tower_quotient_map_quotient
  have : Module.Finite k R := Module.Finite.of_restrictScalars_finite A k R
  have hsurj : Function.Surjective (algebraMap A k) := residue_surjective
  -- a point of `B` is a point of `R = B / 𝔪 B`
  have hI (φ : B →ₐ[A] Ω) : I ≤ RingHom.ker φ := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, IsScalarTower.algebraMap_apply A k Ω,
      show algebraMap A k a = 0 from (residue_eq_zero_iff a).mpr ha, map_zero]
  let ρ (φ : B →ₐ[A] Ω) : R →ₐ[k] Ω :=
    AlgHom.extendScalarsOfSurjective hsurj (Ideal.Quotient.liftₐ I φ (hI φ))
  have hρ (φ : B →ₐ[A] Ω) (b : B) : ρ φ (Ideal.Quotient.mk I b) = φ b := rfl
  have hρinj : Function.Injective ρ := fun φ ψ h ↦ AlgHom.ext fun b ↦ by
    rw [← hρ φ, ← hρ ψ, h]
  have hfinR : Finite (R →ₐ[k] Ω) := by
    have := cardinalMk_algHom k R Ω
    rw [Module.finrank_linearMap_self] at this
    exact Cardinal.mk_lt_aleph0_iff.mp (this.trans_lt Cardinal.natCast_lt_aleph0)
  refine ⟨Finite.of_injective ρ hρinj, ?_⟩
  -- avoid the finitely many proper subspaces where two points agree
  let ι := {p : (R →ₐ[k] Ω) × (R →ₐ[k] Ω) // p.1 ≠ p.2}
  let N (p : ι) : Submodule k R := LinearMap.ker (p.1.1.toLinearMap - p.1.2.toLinearMap)
  have hN (p : ι) : N p ≠ ⊤ := fun h ↦ p.2 (AlgHom.ext fun r ↦ by
    have : r ∈ N p := h ▸ Submodule.mem_top
    simpa [N, sub_eq_zero] using this)
  obtain ⟨r, hr⟩ := Submodule.exists_forall_notMem_of_forall_ne_top N hN
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
  refine ⟨b, fun φ ψ h ↦ hρinj ?_⟩
  by_contra hne
  exact hr ⟨(ρ φ, ρ ψ), hne⟩ (by simpa [N, sub_eq_zero, hρ] using h)

end Points

section Degree

variable {A K L : Type u} [CommRing A] [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A]
  [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [FiniteDimensional K L] (B : Subalgebra A L) [Module.Finite A B]

omit [IsLocalRing A] [IsDomain A] [IsIntegrallyClosed A] [FiniteDimensional K L]
  [Module.Finite A B] in
/-- A geometric point `φ : B → k̄` of the closed fibre sends `b` to a root of the reduction of the
minimal polynomial of `b` over `A`. -/
lemma algHom_mem_aroots {Ω : Type*} [Field Ω] [Algebra A Ω] (k : Type*) [Field k] [Algebra A k]
    [Algebra k Ω] [IsScalarTower A k Ω] (φ : B →ₐ[A] Ω) (b : B) (hb : IsIntegral A (b : L)) :
    φ b ∈ ((minpoly A (b : L)).map (algebraMap A k)).aroots Ω := by
  rw [mem_aroots]
  refine ⟨((minpoly.monic hb).map _).ne_zero, ?_⟩
  rw [aeval_map_algebraMap, aeval_algHom_apply]
  have : (aeval b (minpoly A (b : L)) : L) = 0 := by
    rw [Polynomial.aeval_subalgebra_coe, minpoly.aeval]
  rw [show aeval b (minpoly A (b : L)) = 0 from Subtype.val_injective this, map_zero]

/-- I.10.12, first part, when the residue field `k` of `A` is infinite: let `A` be an integrally
closed local domain with fraction field `K`, `L/K` finite and `B ⊆ L` a finite `A`-subalgebra.
The number `n'` of geometric points of the closed fibre of `B` (the separable degree of `B/𝔪B`
over `k`) is at most the separable degree `[L : K]_s`. A single `b ∈ B` separates the geometric
points, which are then roots of the reduction of the minimal polynomial of `b` (in `A[X]`, `A`
being integrally closed); such a reduction has at most `[K(b) : K]_s` distinct roots. -/
theorem card_algHom_le_finSepDegree [Infinite (ResidueField A)] :
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) ≤ Field.finSepDegree K L := by
  classical
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  obtain ⟨hfin, b, hb⟩ := finite_algHom_and_exists_injective (A := A) (B := B)
  have hx : IsIntegral A (b : L) := (Algebra.IsIntegral.isIntegral (R := A) b).map B.val
  let F := minpoly A (b : L)
  have hFK : minpoly K (b : L) = F.map (algebraMap A K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hx
  have hxK : IsIntegral K (b : L) := hx.tower_top
  have hirr : Irreducible (F.map (algebraMap A K)) := hFK ▸ minpoly.irreducible hxK
  let r := (F.map (algebraMap A k)).aroots Ω
  have h1 : Nat.card (B →ₐ[A] Ω) ≤ r.toFinset.card := by
    have := Fintype.ofFinite (B →ₐ[A] Ω)
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective
      (fun φ ↦ ⟨φ b, Multiset.mem_toFinset.mpr (algHom_mem_aroots B k φ b hx)⟩)
      fun φ ψ h ↦ hb (congrArg Subtype.val h)
  have h2 : r.toFinset.card = (F.map (algebraMap A k)).natSepDegree :=
    (natSepDegree_eq_of_isAlgClosed Ω _).symm
  have h3 := natSepDegree_map_le (K := K) (algebraMap A k) hirr
  rw [← hFK, ← IntermediateField.finSepDegree_adjoin_simple_eq_natSepDegree K L hxK.isAlgebraic]
    at h3
  have h4 := Field.finSepDegree_mul_finSepDegree_of_isAlgebraic K K⟮(b : L)⟯ L
  have h5 : 0 < Field.finSepDegree K⟮(b : L)⟯ L := Nat.pos_of_ne_zero (NeZero.ne _)
  have h6 : Field.finSepDegree K K⟮(b : L)⟯ ≤ Field.finSepDegree K L :=
    h4 ▸ Nat.le_mul_of_pos_right _ h5
  exact h1.trans (h2.le.trans (h3.trans h6))

/-- I.10.12, the equality case, when the residue field of `A` is infinite: if `n' = [L : K]`,
then `B` is étale over `A`. With `b ∈ B` separating the geometric points, the reduction of the
minimal polynomial `F` of `b` has `n' = [L : K]` distinct roots, so `L = K(b)` and the reduction
of `F` is separable: `A[b] ≅ A[t]/(F)` is étale over `A` (I.7.4), hence integrally closed
(I.9.5(i)) with fraction field `L`, so it contains the integral elements `B ⊇ A[b]`. -/
theorem etale_of_card_algHom_eq_finrank [Infinite (ResidueField A)]
    (h : Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) = Module.finrank K L) :
    Algebra.Etale A B := by
  classical
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  obtain ⟨hfin, b, hb⟩ := finite_algHom_and_exists_injective (A := A) (B := B)
  replace h : Nat.card (B →ₐ[A] Ω) = Module.finrank K L := h
  let x : L := b
  have hx : IsIntegral A x := (Algebra.IsIntegral.isIntegral (R := A) b).map B.val
  let F := minpoly A x
  have hFm : F.Monic := minpoly.monic hx
  have hFK : minpoly K x = F.map (algebraMap A K) :=
    minpoly.isIntegrallyClosed_eq_field_fractions' K hx
  have hxK : IsIntegral K x := hx.tower_top
  let r := (F.map (algebraMap A k)).aroots Ω
  have h1 : Nat.card (B →ₐ[A] Ω) ≤ r.toFinset.card := by
    have := Fintype.ofFinite (B →ₐ[A] Ω)
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_le_of_injective
      (fun φ ↦ ⟨φ b, Multiset.mem_toFinset.mpr (algHom_mem_aroots B k φ b hx)⟩)
      fun φ ψ h ↦ hb (congrArg Subtype.val h)
  have h2 : r.toFinset.card = (F.map (algebraMap A k)).natSepDegree :=
    (natSepDegree_eq_of_isAlgClosed Ω _).symm
  have h3 : (F.map (algebraMap A k)).natDegree = (minpoly K x).natDegree := by
    rw [hFK, hFm.natDegree_map, hFm.natDegree_map]
  have h4 : (minpoly K x).natDegree = Module.finrank K K⟮x⟯ :=
    (IntermediateField.adjoin.finrank hxK).symm
  have h5 : Module.finrank K K⟮x⟯ ≤ Module.finrank K L := K⟮x⟯.toSubmodule.finrank_le
  have h6 := natSepDegree_le_natDegree (F.map (algebraMap A k))
  -- all these inequalities are equalities
  have hsep : (F.map (algebraMap A k)).Separable := by
    rw [← natSepDegree_eq_natDegree_iff _ (hFm.map _).ne_zero]
    omega
  have htop : K⟮x⟯ = ⊤ := IntermediateField.eq_of_le_of_finrank_eq le_top (by
    rw [IntermediateField.finrank_top']
    omega)
  -- `A[x] ≅ A[t]/(F)` is étale over `A`
  have hFs : F.Separable := by
    refine separable_of_separable_map_residue hFm ?_
    rwa [← ResidueField.algebraMap_eq]
  let T := Algebra.adjoin A {x}
  have hAL : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : Module.IsTorsionFree A L := Module.isTorsionFree_iff_algebraMap_injective.mpr hAL
  have : Algebra.Etale A T := by
    have := etale_adjoinRoot_of_separable hFm hFs
    exact .of_equiv (minpoly.equivAdjoin hx)
  -- `A[x]` is integrally closed, with fraction field `L`
  have : IsIntegrallyClosed T := IsIntegrallyClosed.of_localization_maximal fun P _ _ ↦
    (isDomain_and_isIntegrallyClosed_localization_of_etale (A := A) P).2
  have : IsFractionRing T L := IsFractionRing.of_field T L fun z ↦ by
    have hz : z ∈ (K⟮x⟯).toSubalgebra := by rw [htop]; trivial
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hxK.isAlgebraic,
      Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨a, ha, hP⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors A) p
    set P := IsLocalization.integerNormalization (nonZeroDivisors A) p
    have key : aeval x P = algebraMap A L a * aeval x p := by
      rw [← aeval_map_algebraMap K x P, hP, ← algebraMap_smul K a p, map_smul, Algebra.smul_def,
        ← IsScalarTower.algebraMap_apply]
    refine ⟨⟨aeval x P, Polynomial.aeval_mem_adjoin_singleton A x⟩, algebraMap A T a, ?_⟩
    have ha' : algebraMap A L a ≠ 0 :=
      (map_ne_zero_iff _ hAL).mpr (nonZeroDivisors.ne_zero ha)
    rw [eq_div_iff (by simpa using ha')]
    change _ = aeval x P
    rw [key, mul_comm]
    rfl
  -- `B = A[x]`
  have hBT : B = T := by
    refine le_antisymm (fun y hy ↦ ?_) (Algebra.adjoin_le (Set.singleton_subset_iff.mpr b.2))
    have hyint : IsIntegral T y :=
      ((Algebra.IsIntegral.isIntegral (R := A) (⟨y, hy⟩ : B)).map B.val).tower_top
    obtain ⟨t, ht⟩ := IsIntegrallyClosed.isIntegral_iff.mp hyint
    rw [← ht]
    exact t.2
  exact .of_equiv (Subalgebra.equivOfEq T B hBT.symm)

/-- I.10.12, when the residue field of `A` is infinite: if `B` is étale over `A` (and has fraction
field `L`), then `n' = [L : K]`. By I.7.5, `B ≅ A[t]/(F)` with `F` monic separable; the `deg F`
distinct roots of the reduction of `F` give `deg F` geometric points, and `[L : K] ≤ deg F`
since `L = K(x)` for the class `x` of `t`. -/
theorem card_algHom_eq_finrank_of_etale [Infinite (ResidueField A)] [Algebra.Etale A B]
    [IsFractionRing B L] :
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) = Module.finrank K L := by
  classical
  let k := ResidueField A
  let Ω := AlgebraicClosure k
  change Nat.card (B →ₐ[A] Ω) = _
  obtain ⟨F, hFm, hFs, -, ⟨e⟩⟩ := exists_algEquiv_adjoinRoot_of_etale_of_infinite (A := A) (B := B)
  obtain ⟨hfin, -⟩ := finite_algHom_and_exists_injective (A := A) (B := B)
  -- `deg F` geometric points
  have hsep : (F.map (algebraMap A k)).Separable := hFs.map
  have hcard : Fintype.card ((F.map (algebraMap A k)).rootSet Ω) = F.natDegree := by
    rw [card_rootSet_eq_natDegree hsep (IsAlgClosed.splits _), hFm.natDegree_map]
  have hroot (z : (F.map (algebraMap A k)).rootSet Ω) :
      F.eval₂ (Algebra.ofId A Ω : A →+* Ω) z = 0 := by
    have := (mem_rootSet.mp z.2).2
    rwa [aeval_map_algebraMap] at this
  let ι (z : (F.map (algebraMap A k)).rootSet Ω) : B →ₐ[A] Ω :=
    (AdjoinRoot.liftAlgHom F (Algebra.ofId A Ω) z (hroot z)).comp e.symm.toAlgHom
  have hι : Function.Injective ι := fun z w h ↦ Subtype.ext (by
    have := congr($h (e (AdjoinRoot.root F)))
    simpa [ι] using this)
  have h1 : F.natDegree ≤ Nat.card (B →ₐ[A] Ω) := by
    rw [← hcard, ← Nat.card_eq_fintype_card]
    exact Nat.card_le_card_of_injective ι hι
  -- `L = K(x)`, `x` the class of `t`
  let x : L := e (AdjoinRoot.root F)
  have hxF : aeval x F = 0 := by
    have h0 : aeval (AdjoinRoot.root F) F = 0 := by rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
    have := congrArg (B.val.comp e.toAlgHom) h0
    rwa [map_zero, ← aeval_algHom_apply] at this
  have hxK : IsIntegral K x := ⟨F.map (algebraMap A K), hFm.map _, by
    rw [← aeval_def, aeval_map_algebraMap, hxF]⟩
  have hB (y : B) : (y : L) ∈ K⟮x⟯ := by
    obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (e.symm y)
    have hy : (y : L) = aeval x p := by
      rw [← e.apply_symm_apply y, ← hp, ← AdjoinRoot.aeval_eq, ← aeval_algHom_apply]
      exact Polynomial.aeval_subalgebra_coe p B _
    rw [hy]
    have hle : Algebra.adjoin A {x} ≤ (K⟮x⟯.toSubalgebra.restrictScalars A) :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr (mem_adjoin_simple_self K x))
    exact hle (Polynomial.aeval_mem_adjoin_singleton A x)
  have htop : K⟮x⟯ = ⊤ := eq_top_iff.mpr fun z _ ↦ by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := B) z
    exact div_mem (hB a) (hB b)
  have hn : Module.finrank K L ≤ F.natDegree := by
    rw [← IntermediateField.finrank_top', ← htop, IntermediateField.adjoin.finrank hxK,
      ← hFm.natDegree_map (algebraMap A K)]
    exact natDegree_le_natDegree (minpoly.min K x (hFm.map _) (by
      rw [aeval_map_algebraMap, hxF]))
  have h2 : Nat.card (B →ₐ[A] Ω) ≤ Field.finSepDegree K L := card_algHom_le_finSepDegree (K := K) B
  have h3 := Field.finSepDegree_le_finrank K L
  omega

/-- I.10.12, when the residue field `k` of `A` is infinite: let `A` be an integrally closed local
domain with fraction field `K`, `L/K` finite, and `B ⊆ L` a finite `A`-subalgebra with fraction
field `L`. The separable degree `n'` of `B/𝔪B` over `k` (its number of geometric points) satisfies
`n' ≤ [L : K]_s`, and `n' = [L : K]` iff `B` is étale over `A`. (SGA's `A` is noetherian; this is
not needed.) -/
theorem separableDegree_fiber_le_of_infinite [Infinite (ResidueField A)] [IsFractionRing B L] :
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) ≤ Field.finSepDegree K L ∧
      (Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) = Module.finrank K L ↔
        Algebra.Etale A B) :=
  ⟨card_algHom_le_finSepDegree B, fun h ↦ etale_of_card_algHom_eq_finrank B h,
    fun _ ↦ card_algHom_eq_finrank_of_etale B⟩

end Degree

/-- I.10.12 (statement; proved in `SGA.SGA1.ExposeI.GeometricPoints`, and for an infinite
residue field in `separableDegree_fiber_le_of_infinite`): let `A` be a normal noetherian local
domain with fraction field `K`, `L` a finite extension of `K`, and `B ⊆ L` a finite
`A`-subalgebra with fraction field `L`. The separable degree `n'` of `B/𝔪B` over `k`, i.e. its
number of geometric points `B → k̄` (the sum of the separable degrees of its residue field
extensions), satisfies
`n' ≤ [L : K]_s`, and `n' = [L : K]` iff `B` is étale over `A`. SGA reduces the case of a finite
residue field to the infinite one through `A(t) = A[t]_{𝔪[t]}`. -/
def separableDegree_fiber_le_Statement : Prop :=
  ∀ (A K L : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [Field L] [Algebra K L]
    [Algebra A L] [IsScalarTower A K L] [FiniteDimensional K L] (B : Subalgebra A L),
    Module.Finite A B → IsFractionRing B L →
    Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) ≤ Field.finSepDegree K L ∧
      (Nat.card (B →ₐ[A] AlgebraicClosure (ResidueField A)) = Module.finrank K L ↔
        Algebra.Etale A B)


end SGA.SGA1.ExposeI
