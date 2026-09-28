/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.IntegralClosure.GoingDown
import SGA.Foundations.CommAlg.AuslanderBuchsbaum
import SGA.Foundations.CommAlg.Discriminant
import SGA.Foundations.CommAlg.Normal

/-!
# Zariski–Nagata purity for regular local rings of dimension two

Let `A` be a regular local ring of dimension `2` and `B` a finite `A`-algebra which is a normal
domain containing `A`. If `B` is étale over `A` at every prime not lying over the maximal ideal
(i.e. over the punctured spectrum of `A`), then `B` is étale over `A`
(`IsRegularLocalRing.etale_of_isIntegrallyClosed`; Stacks 0BMB in dimension `2`, SGA 1 X.3.2 and
SGA 2 X.3.4 in dimension `2`).

The proof is the one sketched in SGA 1, X.3:

* `B` is normal, so the associated primes of `B/xB` have height one; by going down they do not lie
  over `𝔪_A`, hence prime avoidance gives an `A`-regular sequence `x, y` on `B`: `depth_A B ≥ 2`
  (`exists_isWeaklyRegular_pair_of_isIntegrallyClosed`);
* then `B` is free over `A` since `A` is regular of dimension `2`
  (`IsRegularLocalRing.free_of_isWeaklyRegular`);
* the discriminant of a basis of `B` is a unit at every non-maximal prime of `A` (SGA 1, I.4.10),
  so it lies in no prime of height `≤ 1`, hence is a unit by Krull's principal ideal theorem, and
  `B` is étale (I.4.10 again).

The depth form `IsRegularLocalRing.etale_of_isWeaklyRegular` (with a `B`-regular sequence in `𝔪_A`
instead of normality) is the base case of the induction on the dimension in
`SGA.Foundations.CommAlg.PurityInduction`, which also localizes it at primes
(`Algebra.isEtaleAt_of_isWeaklyRegular`).
-/

universe u v

open IsLocalRing RingTheory.Sequence

section Depth

variable {A : Type u} {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]

/-- If `B` is a noetherian normal domain over a local ring `A`, `x ∈ A` has nonzero image in `B`,
and no height-one prime of `B` lies over `𝔪_A`, there is a finite set `S` of primes of `A` not
containing `𝔪_A` such that `x, y` is a `B`-regular sequence for every `y` outside the primes of `S`
(the contractions of the associated primes of `B/xB`). -/
theorem exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed [IsNoetherianRing B] [IsDomain B]
    [IsIntegrallyClosed B] {x : A} (hx0 : algebraMap A B x ≠ 0)
    (h1 : ∀ P : Ideal B, P.IsPrime → P.height = 1 → P.comap (algebraMap A B) ≠ maximalIdeal A) :
    ∃ S : Finset (Ideal A), (∀ P ∈ S, P.IsPrime ∧ ¬ maximalIdeal A ≤ P) ∧
      ∀ y : A, (∀ P ∈ S, y ∉ P) → IsWeaklyRegular B [x, y] := by
  classical
  set x' := algebraMap A B x
  have hxreg : IsSMulRegular B x := by
    rw [← isSMulRegular_algebraMap_iff (A := B)]
    exact (IsRegular.of_ne_zero hx0).left
  -- the associated primes of `B/x'B` do not lie over `𝔪_A`
  let Q := B ⧸ Ideal.span {x'}
  have hfin : (associatedPrimes B Q).Finite := associatedPrimes.finite B Q
  refine ⟨hfin.toFinset.image (Ideal.comap (algebraMap A B)), fun P hP ↦ ?_, fun y hyS ↦ ?_⟩
  · obtain ⟨P', hP', rfl⟩ := Finset.mem_image.mp hP
    rw [Set.Finite.mem_toFinset] at hP'
    have := hP'.isPrime
    refine ⟨Ideal.IsPrime.comap _, fun hle ↦ ?_⟩
    have hne := h1 P' this (IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hx0 hP')
    exact hne ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.comap _).ne_top hle).symm
  have hyP : ∀ P ∈ associatedPrimes B Q, algebraMap A B y ∉ P := fun P hP hyP ↦
    hyS _ (Finset.mem_image.mpr ⟨P, by simpa [Set.Finite.mem_toFinset] using hP, rfl⟩) hyP
  have hyQ : ∀ q : Q, algebraMap A B y • q = 0 → q = 0 := by
    intro q hq
    by_contra hq0
    have hmem : algebraMap A B y ∈ ⋃ p ∈ associatedPrimes B Q, (p : Set B) := by
      rw [biUnion_associatedPrimes_eq_zero_divisors]
      exact ⟨q, hq0, hq⟩
    simp only [Set.mem_iUnion, SetLike.mem_coe] at hmem
    obtain ⟨P, hP, hyP'⟩ := hmem
    exact hyP P hP hyP'
  have hyreg : IsSMulRegular (QuotSMulTop x B) y := by
    intro u v huv
    rw [← sub_eq_zero, ← smul_sub] at huv
    rw [← sub_eq_zero]
    generalize u - v = w at huv ⊢
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_smul_pointwise_iff_exists] at huv
    obtain ⟨d, -, hd⟩ := huv
    have : Ideal.Quotient.mk (Ideal.span {x'}) c = 0 := by
      apply hyQ
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
      refine ⟨d, ?_⟩
      rw [mul_comm, ← Algebra.smul_def, ← Algebra.smul_def, hd]
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at this
    obtain ⟨e, rfl⟩ := this
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨e, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩
  exact IsWeaklyRegular.cons hxreg ((isWeaklyRegular_singleton_iff _ y).mpr hyreg)

/-- Prime avoidance in a local ring: some element of `𝔪` lies outside finitely many primes
not containing `𝔪`. -/
theorem IsLocalRing.exists_mem_maximalIdeal_forall_notMem (S : Finset (Ideal A))
    (hS : ∀ P ∈ S, P.IsPrime ∧ ¬ maximalIdeal A ≤ P) :
    ∃ y ∈ maximalIdeal A, ∀ P ∈ S, y ∉ P := by
  classical
  have hy : ¬ ((maximalIdeal A : Set A) ⊆ ⋃ P ∈ (S : Set (Ideal A)), (P : Set A)) := by
    rw [Ideal.subset_union_prime ⊥ ⊥ (fun P hP _ _ ↦ (hS P hP).1)]
    rintro ⟨P, hP, hle⟩
    exact (hS P hP).2 hle
  obtain ⟨y, hym, hyP⟩ := Set.not_subset.mp hy
  simp only [Set.mem_iUnion, SetLike.mem_coe, not_exists] at hyP
  exact ⟨y, hym, fun P hP ↦ hyP P hP⟩

/-- If `B` is a noetherian normal domain over a local ring `A`, `x ∈ A` has nonzero image in `B`,
and no height-one prime of `B` lies over `𝔪_A`, then `x` extends to a `B`-regular sequence `x, y`
with `y ∈ 𝔪_A`. -/
theorem exists_isWeaklyRegular_pair_of_isIntegrallyClosed [IsNoetherianRing B] [IsDomain B]
    [IsIntegrallyClosed B] {x : A} (hx0 : algebraMap A B x ≠ 0)
    (h1 : ∀ P : Ideal B, P.IsPrime → P.height = 1 → P.comap (algebraMap A B) ≠ maximalIdeal A) :
    ∃ y ∈ maximalIdeal A, IsWeaklyRegular B [x, y] := by
  obtain ⟨S, hS, hreg⟩ := exists_finset_isWeaklyRegular_pair_of_isIntegrallyClosed hx0 h1
  obtain ⟨y, hym, hyS⟩ := IsLocalRing.exists_mem_maximalIdeal_forall_notMem S hS
  exact ⟨y, hym, hreg y hyS⟩

end Depth

section Discriminant

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If `B` is free over `A` and `B_f` is formally étale over `A`, then the discriminant of a
basis of `B` lies in no prime of `A` not containing `f`. -/
theorem discr_notMem_of_formallyEtale_away (b : Module.Basis ι A B) {f : A}
    (hf : Algebra.FormallyEtale A (Localization.Away (algebraMap A B f))) {p : Ideal A}
    [p.IsPrime] (hfp : f ∉ p) : Algebra.discr A b ∉ p := by
  let M := Submonoid.powers f
  let Af := Localization.Away f
  let Bf := Localization (Algebra.algebraMapSubmonoid B M)
  have hM : Algebra.algebraMapSubmonoid B M = Submonoid.powers (algebraMap A B f) :=
    Submonoid.map_powers _ _
  have : IsLocalization (Algebra.algebraMapSubmonoid B M)
      (Localization.Away (algebraMap A B f)) := by
    rw [hM]
    infer_instance
  let e : Bf ≃ₐ[B] Localization.Away (algebraMap A B f) :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid B M) _ _
  have : Algebra.FormallyEtale A Bf := Algebra.FormallyEtale.of_equiv (e.restrictScalars A).symm
  have : Algebra.FormallyEtale Af Bf := Algebra.FormallyEtale.localization_base M
  have hunit := Algebra.isUnit_discr_of_formallyEtale (b.localizationLocalization Af M Bf)
  rw [Algebra.discr_localizationLocalization] at hunit
  intro hd
  have hprime : (p.map (algebraMap A Af)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M Af p ‹_›
      ((Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hfp)
  exact hprime.ne_top (Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hd) hunit)

end Discriminant

namespace IsRegularLocalRing

variable {A : Type u} {B : Type u} [CommRing A] [IsRegularLocalRing A] [CommRing B] [Algebra A B]

theorem height_maximalIdeal_eq_two (hdim : ringKrullDim A = 2) : (maximalIdeal A).height = 2 := by
  have := maximalIdeal_height_eq_ringKrullDim (R := A)
  rw [hdim] at this
  exact WithBot.coe_injective this

/-- Zariski–Nagata purity in dimension two, depth form (Stacks 0BMB). Let `A` be a regular local
ring of dimension `2` and `B` a finite `A`-algebra of depth `2` over `A` (i.e. with a `B`-regular
sequence `x, y` in `𝔪_A`). If `B_f` is (formally) étale over `A` for every `f ∈ 𝔪_A`, i.e. `B` is
étale over the punctured spectrum of `A`, then `B` is étale over `A`. -/
theorem etale_of_isWeaklyRegular [Module.Finite A B] (hdim : ringKrullDim A = 2) {x y : A}
    (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A) (hreg : IsWeaklyRegular B [x, y])
    (hU : ∀ f ∈ maximalIdeal A, Algebra.FormallyEtale A (Localization.Away (algebraMap A B f))) :
    Algebra.Etale A B := by
  classical
  have hm := height_maximalIdeal_eq_two hdim
  -- `B` is free over `A`
  have : Module.Free A B := free_of_isWeaklyRegular B (rs := [x, y])
    (by simpa using ⟨hx, hy⟩) hreg (by rw [hdim]; rfl)
  let b := Module.Free.chooseBasis A B
  -- the discriminant avoids every non-maximal prime
  have hd : ∀ p : Ideal A, p.IsPrime → p ≠ maximalIdeal A → Algebra.discr A b ∉ p := by
    intro p _ hpm
    obtain ⟨f, hfm, hfp⟩ : ∃ f ∈ maximalIdeal A, f ∉ p :=
      Set.not_subset.mp fun h ↦ hpm (((maximalIdeal.isMaximal A).eq_of_le
        (Ideal.IsPrime.ne_top ‹_›) h).symm)
    exact discr_notMem_of_formallyEtale_away b (hU f hfm) hfp
  -- hence it is a unit (Krull's principal ideal theorem)
  have hunit : IsUnit (Algebra.discr A b) := by
    by_contra hnu
    have hle : Ideal.span {Algebra.discr A b} ≤ maximalIdeal A := by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact hnu
    obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le hle
    have hp1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ p hp
    have := hp.1.1
    refine hd p this (fun hpm ↦ ?_) (hp.1.2 (Ideal.mem_span_singleton_self _))
    rw [hpm, hm] at hp1
    exact absurd hp1 (by decide)
  exact Algebra.etale_of_isUnit_discr hunit

/-- The algebraic purity theorem `etale_of_isWeaklyRegular` with the hypothesis on the punctured
spectrum stated prime by prime: `B` is étale over `A` at every prime not lying over `𝔪_A`. -/
theorem etale_of_isWeaklyRegular_of_isEtaleAt [Module.Finite A B] (hdim : ringKrullDim A = 2)
    {x y : A} (hx : x ∈ maximalIdeal A) (hy : y ∈ maximalIdeal A)
    (hreg : IsWeaklyRegular B [x, y])
    (hU : ∀ (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  refine etale_of_isWeaklyRegular hdim hx hy hreg fun f hfm ↦ ?_
  rw [← Algebra.basicOpen_subset_etaleLocus_iff]
  intro q hq
  apply hU
  intro hqm
  apply hq
  rw [← Ideal.mem_comap, hqm]
  exact hfm

/-- Zariski–Nagata purity in dimension two (Stacks 0BMB; SGA 1, X.3.2 in dimension `2`, for `B`
finite over `A`). Let `A` be a regular local ring of dimension `2` and `B` a finite `A`-algebra
which is a normal domain containing `A`. If `B` is étale over `A` at every prime not lying over
the maximal ideal of `A`, then `B` is étale over `A`. -/
theorem etale_of_isIntegrallyClosed [IsDomain B] [IsIntegrallyClosed B] [Module.Finite A B]
    (hinj : Function.Injective (algebraMap A B)) (hdim : ringKrullDim A = 2)
    (hU : ∀ (q : Ideal B) [q.IsPrime], q.comap (algebraMap A B) ≠ maximalIdeal A →
      Algebra.IsEtaleAt A q) :
    Algebra.Etale A B := by
  classical
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have hm := height_maximalIdeal_eq_two hdim
  -- a nonzero element of the maximal ideal
  obtain ⟨x, hxm, hx0⟩ : ∃ x ∈ maximalIdeal A, x ≠ 0 := by
    by_contra! h
    have : maximalIdeal A = ⊥ := eq_bot_iff.mpr fun x hx ↦ h x hx
    rw [this, Ideal.height_bot] at hm
    exact absurd hm (by decide)
  -- height-one primes of `B` do not lie over `𝔪_A` (going down)
  have h1 : ∀ P : Ideal B, P.IsPrime → P.height = 1 →
      P.comap (algebraMap A B) ≠ maximalIdeal A := by
    intro P _ hP hPm
    have : P.LiesOver (maximalIdeal A) := ⟨hPm.symm⟩
    have := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) P
    rw [hP, hm] at this
    have h2 : (2 : ℕ∞) ≤ 1 := this ▸ le_self_add
    exact absurd h2 (by decide)
  obtain ⟨y, hym, hreg⟩ := exists_isWeaklyRegular_pair_of_isIntegrallyClosed
    ((map_ne_zero_iff _ hinj).mpr hx0) h1
  refine etale_of_isWeaklyRegular hdim hxm hym hreg fun f hfm ↦ ?_
  rw [← Algebra.basicOpen_subset_etaleLocus_iff]
  intro q hq
  apply hU
  intro hqm
  apply hq
  rw [← Ideal.mem_comap, hqm]
  exact hfm

end IsRegularLocalRing

