/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.Normal.Closure
import SGA.Foundations.Ramification.TameInertia

/-!
# Tame ramification in Galois towers

Let `B/A` be a finite flat extension of domains with `B` a Dedekind domain and Galois group `G`,
`p` a prime of `A`, `P ≠ 0` a prime of `B` over `p`, and `W_P ⊆ I_P` the wild inertia group
(`Ideal.wildInertia`). We say that a prime `Q` over `p` is *tamely ramified* when its
ramification index is prime to the residue characteristic and its residue extension is
separable (Serre, *Local fields*, IV §2).

* `Ideal.natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot`: `P` is tamely ramified (i.e.
  `|I_P|` is prime to the residue characteristic, `Ideal.card_inertia_natCast_ne_zero_iff`) if
  and only if `W_P = 1`;
* `Ideal.tame_under_iff_wildInertia_le`: for an intermediate ring `C` with Galois group `H ≤ G`
  for `B/C`, the prime `P ∩ C` of `C` is tamely ramified over `p` if and only if `W_P ⊆ H`;
* `Ideal.wildInertia_le_normalCore`: if this holds for all primes over `p`, then the `W_P` lie in
  the largest normal subgroup of `G` contained in `H`;
* `normalCore_fixingSubgroup_range_eq_bot`: when `M` is a normal closure of `E/K`, the subgroup
  of `Gal(M/K)` fixing `E` contains no nontrivial normal subgroup.

Together: a finite separable extension is tamely ramified at all primes over `p` if and only if
its Galois closure is (SGA 1 XIII 2.0, 2.0.2). We also record that in a finite cyclic group a
subgroup whose order divides that of another is contained in it
(`Subgroup.le_of_card_dvd_of_isCyclic`), used for Abhyankar's lemma (SGA 1 X.3.6, XIII.5.2).
-/

open scoped Pointwise

/-- In a finite cyclic group, a subgroup whose order divides that of another is contained in it. -/
theorem Subgroup.le_of_card_dvd_of_isCyclic {α : Type*} [Group α] [Finite α] [IsCyclic α]
    {A B : Subgroup α} (h : Nat.card B ∣ Nat.card A) : B ≤ A := by
  classical
  cases nonempty_fintype α
  intro x hx
  have hx1 : x ^ Nat.card A = 1 := by
    obtain ⟨k, hk⟩ := h
    have : (⟨x, hx⟩ : B) ^ Nat.card B = 1 := pow_card_eq_one'
    rw [hk, pow_mul, show x ^ Nat.card B = 1 from congrArg Subtype.val this, one_pow]
  by_contra hxA
  have hle := IsCyclic.card_pow_eq_one_le (α := α) (Nat.card_pos (α := A))
  have hsub : insert x (A : Set α).toFinset ⊆ Finset.univ.filter (· ^ Nat.card A = 1) := by
    intro y hy
    rw [Finset.mem_insert, Set.mem_toFinset] at hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hy with rfl | hy
    · exact hx1
    · exact congrArg Subtype.val (pow_card_eq_one' (G := A) (x := ⟨y, hy⟩))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simpa using hxA), Set.toFinset_card,
    ← Nat.card_eq_fintype_card] at hcard
  change (Nat.card A + 1) ≤ _ at hcard
  omega

namespace Ideal

section ResidueChar

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime]
  (P : Ideal B) [P.IsPrime] [P.LiesOver p]

omit [P.IsPrime] in
/-- An integer is nonzero in `κ(p)` if and only if it is nonzero in `B/P`. -/
lemma natCast_residueField_ne_zero_iff (n : ℕ) :
    (n : p.ResidueField) ≠ 0 ↔ (n : B ⧸ P) ≠ 0 := by
  rw [Ne, Ne, ← map_natCast (algebraMap A p.ResidueField), Ideal.algebraMap_residueField_eq_zero,
    ← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem,
    ← map_natCast (algebraMap A B), ← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def P p]

/-- An integer is prime to the characteristic of the residue field of a local ring if and only if
it is nonzero in the residue field of the maximal ideal. -/
lemma _root_.IsLocalRing.not_ringChar_dvd_iff {R : Type*} [CommRing R] [IsLocalRing R] (n : ℕ) :
    ¬ ringChar (IsLocalRing.ResidueField R) ∣ n ↔
      (n : (IsLocalRing.maximalIdeal R).ResidueField) ≠ 0 := by
  rw [← CharP.cast_eq_zero_iff (IsLocalRing.ResidueField R), ← map_natCast (IsLocalRing.residue R),
    IsLocalRing.residue_eq_zero_iff, Ne,
    ← map_natCast (algebraMap R (IsLocalRing.maximalIdeal R).ResidueField),
    Ideal.algebraMap_residueField_eq_zero]

end ResidueChar

section Galois

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A] [IsDedekindDomain B]
  [Module.Finite A B] [Module.Flat A B]
  {G : Type*} [Group G] [Finite G] [MulSemiringAction G B] [IsGaloisGroup G A B]
  (p : Ideal A) [p.IsPrime] (P : Ideal B) [P.IsPrime] [P.LiesOver p]

omit [Module.Finite A B] [Module.Flat A B] in
lemma exists_isLocalUniformizer_of_ne_bot (hP : P ≠ ⊥) :
    P.IsMaximal ∧ ∃ π, P.IsLocalUniformizer π :=
  ⟨Ideal.IsPrime.isMaximal ‹_› hP, exists_isLocalUniformizer P hP⟩

omit [IsDomain A] [Module.Finite A B] [Module.Flat A B] in
/-- A nonzero prime `P` has inertia group of order prime to the residue characteristic if and
only if its wild inertia group is trivial. -/
theorem natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot (hP : P ≠ ⊥) :
    (Nat.card (P.inertia G) : p.ResidueField) ≠ 0 ↔ wildInertia G P = ⊥ := by
  obtain ⟨_, hπ⟩ := exists_isLocalUniformizer_of_ne_bot P hP
  have : FaithfulSMul G B := IsGaloisGroup.faithful A
  rw [natCast_residueField_ne_zero_iff p P, ← Subgroup.relIndex_bot_left,
    natCast_relIndex_inertia_ne_zero_iff hπ, le_bot_iff]

variable {C : Type*} [CommRing C] [Algebra A C] [Algebra C B] [IsScalarTower A C B] [IsDomain C]
  [Module.Finite A C] [Module.Finite C B] [Module.Flat C B] (H : Subgroup G) [IsGaloisGroup H C B]

/-- Let `C` be an intermediate ring with Galois group `H ≤ G` for `B/C`, and `P ≠ 0` a prime of `B`
over `p`. Then `Q = P ∩ C` is tamely ramified over `p` (ramification index prime to the residue
characteristic and separable residue extension) if and only if `H` contains the wild inertia
group of `P`. -/
theorem tame_under_iff_wildInertia_le (hP : P ≠ ⊥) :
    letI := Localization.AtPrime.algebraOfLiesOver p (P.under C)
    ((P.under C).ramificationIdx A : p.ResidueField) ≠ 0 ∧
      Algebra.IsSeparable p.ResidueField (P.under C).ResidueField ↔ wildInertia G P ≤ H := by
  obtain ⟨_, hπ⟩ := exists_isLocalUniformizer_of_ne_bot P hP
  have : FaithfulSMul G B := IsGaloisGroup.faithful A
  have : (P.under C).LiesOver p := ⟨by rw [Ideal.under_under, ← Ideal.over_def P p]⟩
  let := Localization.AtPrime.algebraOfLiesOver p (P.under C)
  rw [← natCast_relIndex_inertia_ne_zero_iff hπ, ← natCast_residueField_ne_zero_iff p P,
    relIndex_inertia_eq (C := C) H p P, Nat.cast_mul, mul_ne_zero_iff,
    Field.natCast_finInsepDegree_ne_zero_iff]

omit [IsDomain A] [IsDedekindDomain B] [Module.Finite A B] [Module.Flat A B] [Finite G]
  [IsGaloisGroup G A B] [p.IsPrime] in
/-- If every prime `P'` of `B` over `p` has its wild inertia group in `H`, then the wild inertia
groups lie in the largest normal subgroup of `G` contained in `H`. -/
theorem wildInertia_le_normalCore [SMulCommClass G A B] (H : Subgroup G)
    (h : ∀ P' : Ideal B, P'.IsPrime → P'.LiesOver p → wildInertia G P' ≤ H) :
    wildInertia G P ≤ H.normalCore := by
  intro σ hσ g
  have : (g • P).IsPrime := Ideal.map_isPrime_of_equiv (MulSemiringAction.toRingEquiv G B g)
  have : (g • P).LiesOver p := inferInstance
  exact h (g • P) ‹_› ‹_› (conj_mem_wildInertia hσ g)

end Galois

end Ideal

section NormalClosure

variable (K E M : Type*) [Field K] [Field E] [Field M] [Algebra K E] [Algebra K M] [Algebra E M]
  [IsScalarTower K E M] [FiniteDimensional K M] [IsGalois K M]

/-- If `M` is a normal closure of `E/K`, the subgroup of `Gal(M/K)` fixing `E` contains no
nontrivial normal subgroup of `Gal(M/K)`. -/
theorem normalCore_fixingSubgroup_range_eq_bot [IsNormalClosure K E M] :
    (fixingSubgroup Gal(M/K) (Set.range (algebraMap E M))).normalCore = ⊥ := by
  set N := (fixingSubgroup Gal(M/K) (Set.range (algebraMap E M))).normalCore
  have : FiniteDimensional K E := FiniteDimensional.left K E M
  have htop : IntermediateField.normalClosure K E M = ⊤ :=
    (Algebra.IsAlgebraic.isNormalClosure_iff.mp inferInstance).2
  have hle : IntermediateField.normalClosure K E M ≤ IntermediateField.fixedField N := by
    rw [normalClosure_def]
    refine iSup_le fun f ↦ ?_
    rintro _ ⟨x, rfl⟩ ⟨σ, hσ⟩
    let g : Gal(M/K) := AlgEquiv.ofBijective (f.liftNormal M) (AlgHom.normal_bijective K M M _)
    have hg : g (algebraMap E M x) = f x := f.liftNormal_commutes M x
    have h1 : (g⁻¹ * σ * g) (algebraMap E M x) = algebraMap E M x := by
      have := hσ g⁻¹ ⟨algebraMap E M x, ⟨x, rfl⟩⟩
      rwa [inv_inv, AlgEquiv.smul_def] at this
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hg] at h1
    have h2 := congrArg g h1
    rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply, hg] at h2
    exact h2
  rw [htop, top_le_iff] at hle
  rw [← IntermediateField.fixingSubgroup_fixedField N, hle, IntermediateField.fixingSubgroup_top]

end NormalClosure
