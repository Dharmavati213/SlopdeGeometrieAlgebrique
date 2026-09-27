/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.Galois.Basic
import SGA.Foundations.Ramification.IntegralClosure
import SGA.Foundations.Ramification.Tame

/-!
# SGA 1, Exposé X, 3: tame inertia groups and Abhyankar's lemma

Let `V` be a discrete valuation ring with fraction field `K` and `L/K` a finite Galois extension
with group `G`. For a maximal ideal `P` of the normalization of `V` in `L`, the inertia group
`G_i = P.inertia G` is formed by the elements of the decomposition group acting trivially on the
residue field; `L` is *tamely ramified* over `V` when `n_i = |G_i|` is prime to the residue
characteristic `p` (X.3). We prove:

* X.3: `G_i` then embeds canonically in `k'^*` (by `σ ↦ σ(π)/π mod P`) and is isomorphic to the
  group of `n_i`-th roots of unity of `k'`; in particular it is cyclic
  (`inertiaEquivRootsOfUnity`, `isCyclic_inertia`);
* X.3.6 (Abhyankar's lemma): for two tamely ramified Galois extensions `L`, `K'` of `K` with
  inertia groups of orders `n ∣ m`, a composite `L'` of `L` and `K'` is unramified over the
  normalization of `V` in `K'` (`ramificationIdx_eq_one_and_isSeparable_of_dvd`).

The proofs use the tame character and the wild inertia group of
`SGA.Foundations.Ramification.TameInertia`; the group-theoretic core of X.3.6 in SGA is
`SGA.SGA1.ExposeX.injective_snd_of_isCyclic`, here replaced by
`Subgroup.le_of_card_dvd_of_isCyclic`.
-/

namespace SGA.SGA1.ExposeX

open IsLocalRing

variable (V K : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K]
  [Algebra V K] [IsFractionRing V K]

/-- A prime of the normalization of `V` over the maximal ideal is nonzero. -/
lemma ne_bot_of_liesOver_maximalIdeal (M : Type*) [Field M] [Algebra K M] [Algebra V M]
    [IsScalarTower V K M] (P : Ideal (integralClosure V M)) [P.LiesOver (maximalIdeal V)] :
    P ≠ ⊥ := by
  rintro rfl
  apply IsDiscreteValuationRing.not_a_field V
  rw [Ideal.over_def (⊥ : Ideal (integralClosure V M)) (maximalIdeal V), Ideal.under,
    ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
      (integralClosure.algebraMap_injective_of_isFractionRing V K M)]

section Tame

variable (L : Type*) [Field L] [Algebra K L] [Algebra V L] [IsScalarTower V K L]
  [FiniteDimensional K L] [IsGalois K L]
  (P : Ideal (integralClosure V L)) [P.IsPrime] [P.LiesOver (maximalIdeal V)]

/-- X.3: the inertia group of a tamely ramified Galois extension `L/K` (its order `n_i` is prime
to the residue characteristic) is isomorphic, by `σ ↦ σ(π)/π mod P`, to the group of `n_i`-th
roots of unity of the residue field `k' = S/P` (here `π` is any local uniformizer at `P`). -/
theorem nonempty_inertiaEquivRootsOfUnity
    (hP : ¬ ringChar (ResidueField V) ∣ Nat.card (P.inertia Gal(L/K))) :
    Nonempty (P.inertia Gal(L/K) ≃*
      rootsOfUnity (Nat.card (P.inertia Gal(L/K))) (integralClosure V L ⧸ P)) := by
  have := integralClosure.isDedekindDomain' V K L
  have := integralClosure.isGaloisGroup V K L
  have : FaithfulSMul Gal(L/K) (integralClosure V L) := IsGaloisGroup.faithful V
  obtain ⟨_, π, hπ⟩ := Ideal.exists_isLocalUniformizer_of_ne_bot P
    (ne_bot_of_liesOver_maximalIdeal V K L P)
  rw [IsLocalRing.not_ringChar_dvd_iff,
    Ideal.natCast_residueField_ne_zero_iff (maximalIdeal V) P] at hP
  exact ⟨hπ.inertiaEquivRootsOfUnity hP⟩

/-- X.3: the inertia group of a tamely ramified Galois extension is cyclic. -/
theorem isCyclic_inertia (hP : ¬ ringChar (ResidueField V) ∣ Nat.card (P.inertia Gal(L/K))) :
    IsCyclic (P.inertia Gal(L/K)) := by
  obtain ⟨e⟩ := nonempty_inertiaEquivRootsOfUnity V K L P hP
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Tame

section Abhyankar

variable {K} (L' : Type*) [Field L'] [Algebra K L'] [Algebra V L'] [IsScalarTower V K L']
  [FiniteDimensional K L']

instance isScalarTower_intermediateField (E : IntermediateField K L') : IsScalarTower V E L' :=
  .of_algebraMap_eq fun _ ↦ rfl

omit [FiniteDimensional K L'] in
/-- The fixing subgroup of an intermediate field, written with the image of its inclusion. -/
lemma fixingSubgroup_range_algebraMap (E : IntermediateField K L') :
    fixingSubgroup Gal(L'/K) (Set.range (algebraMap E L')) = E.fixingSubgroup := by
  congr 1
  ext x
  exact ⟨fun ⟨y, hy⟩ ↦ hy ▸ y.2, fun hx ↦ ⟨⟨x, hx⟩, rfl⟩⟩

/-- X.3.6 (Abhyankar's lemma). Let `V` be a discrete valuation ring with fraction field `K`, `L`
and `K'` two finite Galois extensions of `K` tamely ramified over `V`, `n` and `m` the orders of
the corresponding inertia groups (at the primes over the maximal ideal of `V`, which are
conjugate), and `L'` a composite extension of `L` and `K'` (here `L` and `K'` are subfields of
`L'` with `L ⊔ K' = L'`). If `m` is a multiple of `n`, then `L'` is unramified over the
localizations of the normalization `V'` of `V` in `K'`: every prime `P` of the normalization of
`V` in `L'` has ramification index `1` over `V'` and a separable residue extension. -/
theorem ramificationIdx_eq_one_and_isSeparable_of_dvd (L K' : IntermediateField K L')
    [IsGalois K L] [IsGalois K K'] (hLK : L ⊔ K' = ⊤) (n m : ℕ)
    (hn : ∀ (Q : Ideal (integralClosure V L)) [Q.IsPrime], Q.LiesOver (maximalIdeal V) →
      Nat.card (Q.inertia Gal(L/K)) = n)
    (hm : ∀ (Q : Ideal (integralClosure V K')) [Q.IsPrime], Q.LiesOver (maximalIdeal V) →
      Nat.card (Q.inertia Gal(K'/K)) = m)
    (hnp : ¬ ringChar (ResidueField V) ∣ n) (hmp : ¬ ringChar (ResidueField V) ∣ m)
    (hnm : n ∣ m) (P : Ideal (integralClosure V L')) [P.IsPrime] [P.LiesOver (maximalIdeal V)] :
    letI := integralClosure.algebraOfTower V K' L'
    letI := Localization.AtPrime.algebraOfLiesOver (P.under (integralClosure V K')) P
    P.ramificationIdx (integralClosure V K') = 1 ∧
      Algebra.IsSeparable (P.under (integralClosure V K')).ResidueField P.ResidueField := by
  have : IsGalois K (L ⊔ K' : IntermediateField K L') := {}
  rw [hLK] at this
  have : IsGalois K L' := IsGalois.of_algEquiv IntermediateField.topEquiv
  have := integralClosure.isDedekindDomain' V K L'
  have := integralClosure.finite V K L'
  have := integralClosure.flat V K L'
  have := integralClosure.isGaloisGroup V K L'
  have : FaithfulSMul Gal(L'/K) (integralClosure V L') := IsGaloisGroup.faithful V
  have := integralClosure.isGaloisGroup V K L
  have := integralClosure.isGaloisGroup V K K'
  have := integralClosure.finite V K L
  have := integralClosure.finite V K K'
  have := integralClosure.flat V K L
  have := integralClosure.flat V K K'
  have hH : fixingSubgroup Gal(L'/K) (Set.range (algebraMap L L')) ⊓
      fixingSubgroup Gal(L'/K) (Set.range (algebraMap K' L')) = ⊥ := by
    rw [fixingSubgroup_range_algebraMap, fixingSubgroup_range_algebraMap,
      ← IntermediateField.fixingSubgroup_sup, hLK, IntermediateField.fixingSubgroup_top]
  set H₁ : Subgroup Gal(L'/K) := fixingSubgroup Gal(L'/K) (Set.range (algebraMap L L'))
  set H₂ : Subgroup Gal(L'/K) := fixingSubgroup Gal(L'/K) (Set.range (algebraMap K' L'))
  obtain ⟨_, hπ⟩ := Ideal.exists_isLocalUniformizer_of_ne_bot P
    (ne_bot_of_liesOver_maximalIdeal V K L' P)
  set I := P.inertia Gal(L'/K)
  -- the order of the inertia group of `L` (resp. `K'`) is the index of `I ∩ H₁` (resp. `I ∩ H₂`)
  have hidx₁ : H₁.relIndex I = n := by
    let := integralClosure.algebraOfTower V L L'
    have := integralClosure.finite_of_tower V L L' K
    have := integralClosure.flat_of_tower V L L' K
    have := integralClosure.isGaloisGroup_of_tower V L L' K
    let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal V) (P.under (integralClosure V L))
    rw [Ideal.relIndex_inertia_eq (C := integralClosure V L) H₁ (maximalIdeal V) P,
      ← Ideal.card_inertia_eq_ramificationIdx_mul_finInsepDegree (G := Gal(L/K)) (maximalIdeal V)
        (P.under (integralClosure V L))]
    exact hn _ inferInstance
  have hidx₂ : H₂.relIndex I = m := by
    let := integralClosure.algebraOfTower V K' L'
    have := integralClosure.finite_of_tower V K' L' K
    have := integralClosure.flat_of_tower V K' L' K
    have := integralClosure.isGaloisGroup_of_tower V K' L' K
    let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal V) (P.under (integralClosure V K'))
    rw [Ideal.relIndex_inertia_eq (C := integralClosure V K') H₂ (maximalIdeal V) P,
      ← Ideal.card_inertia_eq_ramificationIdx_mul_finInsepDegree (G := Gal(K'/K))
        (maximalIdeal V) (P.under (integralClosure V K'))]
    exact hm _ inferInstance
  -- tameness: the wild inertia group lies in `H₁` and `H₂`, hence is trivial
  have hchar (k : ℕ) : ¬ ringChar (ResidueField V) ∣ k ↔ (k : integralClosure V L' ⧸ P) ≠ 0 := by
    rw [IsLocalRing.not_ringChar_dvd_iff, Ideal.natCast_residueField_ne_zero_iff (maximalIdeal V) P]
  have hW₁ : Ideal.wildInertia Gal(L'/K) P ≤ H₁ := by
    rw [← Ideal.natCast_relIndex_inertia_ne_zero_iff hπ, hidx₁, ← hchar]
    exact hnp
  have hW₂ : Ideal.wildInertia Gal(L'/K) P ≤ H₂ := by
    rw [← Ideal.natCast_relIndex_inertia_ne_zero_iff hπ, hidx₂, ← hchar]
    exact hmp
  have hW : Ideal.wildInertia Gal(L'/K) P = ⊥ := le_bot_iff.mp (hH ▸ le_inf hW₁ hW₂)
  have hcard : ((Nat.card I : ℕ) : integralClosure V L' ⧸ P) ≠ 0 := by
    rw [← Ideal.natCast_residueField_ne_zero_iff (maximalIdeal V) P,
      Ideal.natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot (maximalIdeal V) P
        (ne_bot_of_liesOver_maximalIdeal V K L' P)]
    exact hW
  have := Ideal.isCyclic_inertia Gal(L'/K) P hπ hcard
  -- in the cyclic group `I`, `I ∩ H₂ ≤ I ∩ H₁` since `n ∣ m`, hence `I ∩ H₂ = 1`
  have hA : H₂.subgroupOf I ≤ H₁.subgroupOf I := by
    apply Subgroup.le_of_card_dvd_of_isCyclic
    have h₁ := (H₁.subgroupOf I).card_mul_index
    have h₂ := (H₂.subgroupOf I).card_mul_index
    rw [← Subgroup.relIndex, hidx₁] at h₁
    rw [← Subgroup.relIndex, hidx₂] at h₂
    obtain ⟨k, rfl⟩ := hnm
    refine ⟨k, Nat.eq_of_mul_eq_mul_right (m := n) (Nat.pos_of_ne_zero fun h ↦ ?_) ?_⟩
    · rw [h, mul_zero] at h₁
      exact (Nat.card_pos (α := I)).ne' h₁.symm
    · rw [h₁, ← h₂]
      ring
  have hinert : P.inertia H₂ = ⊥ := by
    refine eq_bot_iff.mpr fun σ hσ ↦ ?_
    have h₂ : (⟨σ, hσ⟩ : I) ∈ H₂.subgroupOf I := Subgroup.mem_subgroupOf.mpr σ.2
    have h₁ : (σ : Gal(L'/K)) ∈ H₁ := Subgroup.mem_subgroupOf.mp (hA h₂)
    have : (σ : Gal(L'/K)) ∈ H₁ ⊓ H₂ := ⟨h₁, σ.2⟩
    rw [hH, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (Subtype.ext this)
  -- the inertia group of `P` over `K'` is trivial: `e = 1` and the residue extension is separable
  let := integralClosure.algebraOfTower V K' L'
  have := integralClosure.finite_of_tower V K' L' K
  have := integralClosure.flat_of_tower V K' L' K
  have := integralClosure.isGaloisGroup_of_tower V K' L' K
  let := Localization.AtPrime.algebraOfLiesOver (P.under (integralClosure V K')) P
  have h := Ideal.card_inertia_eq_ramificationIdx_mul_finInsepDegree (G := H₂)
    (P.under (integralClosure V K')) P
  rw [hinert, Subgroup.card_bot, eq_comm, mul_eq_one] at h
  exact ⟨h.1, (isSeparable_iff_finInsepDegree_eq_one _ _).mpr h.2⟩

end Abhyankar

end SGA.SGA1.ExposeX
