/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Unramified.LocalRing
import SGA.Foundations.Ramification.BaseLocalization
import SGA.Foundations.Ramification.Henselian
import SGA.Foundations.Ramification.IntegralClosure
import SGA.Foundations.Ramification.Tame
import SGA.Foundations.Ramification.Transport

/-!
# SGA 1, Exposé XIII, 2.0: tamely ramified extensions of a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue characteristic exponent
`p`. SGA (XIII 2.0, following X.3) calls a finite separable extension `L/K` *tamely ramified*
over `R` when the inertia groups of its Galois closure `L'` have order prime to `p`
(`IsTameExtension`; the inertia groups are those of the primes of the normalization of `R` in
`L'`), and an étale `K`-algebra tamely ramified when its factors are (`IsTameAlgebra`).
Classically (Serre, *Local fields*, IV §2) one asks instead that every prime of the normalization
`S` of `R` in `L` have ramification index prime to `p` and separable residue extension
(`IsTamelyRamifiedOver`). We prove:

* XIII 2.0 (structure of inertia groups): an inertia group is an extension of a cyclic group of
  order prime to `p` by a normal `p`-group (`exists_isPGroup_isCyclic_quotient_inertia`; the
  `p`-group is the wild inertia group `Ideal.wildInertia`), also for inseparable residue
  extensions, as indicated in SGA;
* for a Galois extension, the inertia group has order prime to `p` if and only if the prime is
  tamely ramified in the classical sense (`isTamelyRamifiedAt_iff_card_inertia`), with no
  assumption on the residue fields;
* a Galois extension of degree prime to `p` is tamely ramified (`isTameExtension_of_isGalois`,
  over any local ring), and its ramification indices divide the degree
  (`ramificationIdx_dvd_finrank`);
* the two notions agree for every finite separable extension
  (`isTameExtension_iff_isTamelyRamifiedOver`): `L` is tamely ramified at all primes if and only
  if its Galois closure is; equivalently, in any finite Galois extension `M ⊇ L`, the wild inertia
  groups lie in `Gal(M/L)` (`isTameExtension_iff_forall_wildInertia_le_of_isGalois`);
* XIII 2.0.1: over a strictly henselian `R`, `L` is tamely ramified if and only if `[L : K]` is
  prime to `p` (`isTameExtension_iff_not_dvd_finrank`), and then `L/K` is cyclic Galois
  (`isGalois_and_isCyclic_of_isTameExtension`);
* XIII 2.0.3, first two assertions: subextensions and composites of tamely ramified extensions
  are tamely ramified (`IsTameExtension.of_algHom`, `IsTameExtension.of_adjoin_eq_top`), hence
  subalgebras and tensor products of tamely ramified étale algebras
  (`IsTameAlgebra.subalgebra`, `IsTameAlgebra.tensorProduct`);
* XIII 2.0.2 and the last two assertions of 2.0.3: for a local homomorphism `R → R'` of discrete
  valuation rings, tame ramification is preserved by `L ↦ K' ⊗_K L`
  (`IsTameExtension.of_adjoin_range_eq_top`, `IsTameAlgebra.baseChange`: the inertia groups of
  `K'N/K'`, `N` the Galois closure, embed into those of `N/K`); conversely, if `𝔪_R` generates
  `𝔪_{R'}` and the residue extension is separable, `L` is tamely ramified as soon as `K' ⊗_K L`
  is (`IsTameExtension.of_isTameAlgebra_tensorProduct`, `IsTameAlgebra.of_baseChange`, by
  comparing ramification indices and residue fields in `R → R' → R'_{F'}`,
  `isTamelyRamifiedAt_of_tower`).

The proofs use the tame character and the wild inertia group of
`SGA.Foundations.Ramification.TameInertia`.
-/

universe u v

namespace SGA.SGA1.ExposeXIII

open IsLocalRing

section Classical

variable (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- XIII.2.0, at one prime: `q` is tamely ramified over `R` when its ramification index is prime
to the residue characteristic (it does not lie in `q ∩ R`) and its residue field extension is
separable. -/
def IsTamelyRamifiedAt (q : Ideal S) [q.IsPrime] : Prop :=
  letI := Localization.AtPrime.algebraOfLiesOver (q.under R) q
  (q.ramificationIdx R : R) ∉ q.under R ∧
    Algebra.IsSeparable (q.under R).ResidueField q.ResidueField

variable (S) in
/-- XIII.2.0: for a local ring `R` (in SGA a discrete valuation ring and `S` the normalisation of
`R` in an étale algebra over its fraction field), `S` is tamely ramified over `R` when it is tamely
ramified at every prime over the maximal ideal of `R`. -/
def IsTamelyRamifiedOver [IsLocalRing R] : Prop :=
  ∀ (q : Ideal S) [q.IsPrime], q.LiesOver (maximalIdeal R) → IsTamelyRamifiedAt R q

/-- An unramified prime is tamely ramified: its ramification index is `1` and its residue
extension is separable. -/
theorem isTamelyRamifiedAt_of_isUnramifiedAt [Algebra.EssFiniteType R S] (q : Ideal S)
    [q.IsPrime] [Algebra.IsUnramifiedAt R q] : IsTamelyRamifiedAt R q := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ramificationIdx_eq_one, Nat.cast_one]
    exact Ideal.IsPrime.one_notMem inferInstance
  · exact inferInstance

/-- An étale algebra over a local ring is tamely ramified over it. -/
theorem isTamelyRamifiedOver_of_etale [IsLocalRing R] [Algebra.Etale R S] :
    IsTamelyRamifiedOver R S :=
  fun q _ _ ↦ isTamelyRamifiedAt_of_isUnramifiedAt R q

/-- An integer lies in a prime `p` if and only if it vanishes in `κ(p)`. -/
lemma natCast_mem_iff_residueField (p : Ideal R) [p.IsPrime] (n : ℕ) :
    (n : R) ∈ p ↔ (n : p.ResidueField) = 0 := by
  rw [← map_natCast (algebraMap R p.ResidueField), Ideal.algebraMap_residueField_eq_zero]

/-- `IsTamelyRamifiedAt` in terms of a prime `p` below `q`. -/
lemma isTamelyRamifiedAt_iff_of_liesOver (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    [q.LiesOver p] :
    IsTamelyRamifiedAt R q ↔
      letI := Localization.AtPrime.algebraOfLiesOver p q
      (q.ramificationIdx R : p.ResidueField) ≠ 0 ∧
        Algebra.IsSeparable p.ResidueField q.ResidueField := by
  obtain rfl := Ideal.over_def q p
  rw [IsTamelyRamifiedAt, natCast_mem_iff_residueField]

/-- XIII.2.0 and X.3: for a Galois extension of domains with group `G`, `P` is tamely ramified if
and only if its inertia group has order prime to the residue characteristic. This is the
definition of tame ramification used in SGA; no assumption on the residue fields is needed. -/
theorem isTamelyRamifiedAt_iff_card_inertia [IsDomain R] [IsDomain S] [Module.Finite R S]
    [Module.Flat R S] (G : Type*) [Group G] [Finite G] [MulSemiringAction G S]
    [IsGaloisGroup G R S] (P : Ideal S) [P.IsPrime] :
    IsTamelyRamifiedAt R P ↔ (Nat.card (P.inertia G) : R) ∉ P.under R := by
  rw [isTamelyRamifiedAt_iff_of_liesOver R (P.under R), natCast_mem_iff_residueField]
  exact (Ideal.card_inertia_natCast_ne_zero_iff (P.under R) P).symm

/-- Tame ramification at a prime is invariant under isomorphisms of `R`-algebras. -/
theorem isTamelyRamifiedAt_map_algEquiv_iff {S' : Type*} [CommRing S'] [Algebra R S']
    (e : S ≃ₐ[R] S') (q : Ideal S) [q.IsPrime] :
    haveI : (q.map e).IsPrime := Ideal.map_isPrime_of_equiv e
    IsTamelyRamifiedAt R (q.map e) ↔ IsTamelyRamifiedAt R q := by
  have : (q.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have : (q.map e).LiesOver (q.under R) := ⟨(Ideal.under_map_algEquiv e q).symm⟩
  rw [isTamelyRamifiedAt_iff_of_liesOver R (q.under R) (q.map e),
    isTamelyRamifiedAt_iff_of_liesOver R (q.under R) q, Ideal.ramificationIdx_map_algEquiv,
    Ideal.isSeparable_residueField_map_algEquiv_iff e q (q.under R)]

/-- Tame ramification at a prime only depends on the local ring: for `f : S → S'` and a prime
`q'` of `S'` such that `S_{f⁻¹ q'} → S'_{q'}` is an isomorphism, `f⁻¹ q'` is tamely ramified if and
only if `q'` is. -/
theorem isTamelyRamifiedAt_comap_iff_of_bijective {S' : Type*} [CommRing S'] [Algebra R S']
    (f : S →ₐ[R] S') (q' : Ideal S') [q'.IsPrime]
    (hf : Function.Bijective (Localization.localAlgHom (q'.comap f) q' f rfl)) :
    IsTamelyRamifiedAt R (q'.comap f) ↔ IsTamelyRamifiedAt R q' := by
  have : (q'.comap f).LiesOver (q'.under R) := ⟨(Ideal.under_comap_algHom f q').symm⟩
  rw [isTamelyRamifiedAt_iff_of_liesOver R (q'.under R) (q'.comap f),
    isTamelyRamifiedAt_iff_of_liesOver R (q'.under R) q',
    Ideal.ramificationIdx_comap_of_bijective f q' hf,
    Ideal.isSeparable_residueField_comap_iff_of_bijective f q' hf (q'.under R)]

/-- Tame ramification is invariant under localization of the base: for a prime `P` of `S` over
`p` and `Rₚ = R_p`, `Sₚ = S_p`, the prime `P Sₚ` is tamely ramified over `Rₚ` if and only if `P`
is tamely ramified over `R`. -/
theorem isTamelyRamifiedAt_map_iff_of_isLocalization (p : Ideal R) [p.IsPrime] (Rₚ : Type*)
    [CommRing Rₚ] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] (Sₚ : Type*)
    [CommRing Sₚ] [Algebra S Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    [Algebra Rₚ Sₚ] [Algebra R Sₚ] [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ] (P : Ideal S)
    [P.IsPrime] [P.LiesOver p] :
    haveI := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
    IsTamelyRamifiedAt Rₚ (P.map (algebraMap S Sₚ)) ↔ IsTamelyRamifiedAt R P := by
  have := IsLocalization.AtPrime.isPrime_map_of_liesOver S p Sₚ P
  have := IsLocalization.AtPrime.liesOver_map_of_liesOver p Rₚ Sₚ P
  rw [isTamelyRamifiedAt_iff_of_liesOver Rₚ (maximalIdeal Rₚ),
    isTamelyRamifiedAt_iff_of_liesOver R p,
    IsLocalization.AtPrime.ramificationIdx_map_eq_ramificationIdx p Rₚ Sₚ P,
    IsLocalization.AtPrime.isSeparable_residueField_map_iff p Rₚ Sₚ P, Ne, Ne,
    ← natCast_mem_iff_residueField, ← natCast_mem_iff_residueField,
    ← map_natCast (algebraMap R Rₚ), IsLocalization.AtPrime.to_map_mem_maximal_iff Rₚ p]

/-- The local ring of `e⁻¹ q'` for an isomorphism `e` is that of `q'`. -/
lemma bijective_localAlgHom_algEquiv {S' : Type*} [CommRing S'] [Algebra R S']
    (e : S ≃ₐ[R] S') (q' : Ideal S') [q'.IsPrime] :
    Function.Bijective (Localization.localAlgHom (q'.comap (e : S →ₐ[R] S')) q'
      (e : S →ₐ[R] S') rfl) :=
  (Localization.localRingEquiv (q'.comap (e : S →ₐ[R] S')) q' e.toRingEquiv rfl).bijective

/-- `IsTamelyRamifiedOver` is invariant under isomorphisms of `R`-algebras. -/
theorem IsTamelyRamifiedOver.of_algEquiv [IsLocalRing R] {S' : Type*} [CommRing S']
    [Algebra R S'] (e : S ≃ₐ[R] S') (h : IsTamelyRamifiedOver R S) :
    IsTamelyRamifiedOver R S' := by
  intro Q' _ hQ'
  set Q := Q'.comap e
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  have hQQ' : Q.map e = Q' := Ideal.map_comap_of_surjective _ e.surjective Q'
  have : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
    ⟨by rw [Ideal.over_def Q' (IsLocalRing.maximalIdeal R), ← hQQ', Ideal.under_map_algEquiv]⟩
  have := (isTamelyRamifiedAt_map_algEquiv_iff R e Q).mpr (h Q this)
  convert this
  exact hQQ'.symm

/-- Tame ramification at all primes over `p` is invariant under isomorphisms of `R`-algebras. -/
theorem forall_isTamelyRamifiedAt_of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S']
    (e : S ≃ₐ[R] S') (p : Ideal R)
    (h : ∀ (Q : Ideal S) [Q.IsPrime], Q.LiesOver p → IsTamelyRamifiedAt R Q) :
    ∀ (Q' : Ideal S') [Q'.IsPrime], Q'.LiesOver p → IsTamelyRamifiedAt R Q' := by
  intro Q' _ hQ'
  have : (Q'.comap e.toAlgHom).IsPrime := Ideal.comap_isPrime _ _
  have hb := bijective_localAlgHom_algEquiv R e Q'
  refine (isTamelyRamifiedAt_comap_iff_of_bijective R _ Q' hb).mp (h _ ⟨?_⟩)
  rw [Ideal.under_comap_algHom, ← Ideal.over_def Q' p]

/-- The ramification indices over `p` are invariant under isomorphisms of `R`-algebras. -/
theorem forall_ramificationIdx_dvd_of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S']
    (e : S ≃ₐ[R] S') (p : Ideal R) (k : ℕ)
    (h : ∀ Q : Ideal S, Q.IsPrime → Q.LiesOver p → Q.ramificationIdx R ∣ k) :
    ∀ Q' : Ideal S', Q'.IsPrime → Q'.LiesOver p → Q'.ramificationIdx R ∣ k := by
  intro Q' _ hQ'
  have : (Q'.comap e.toAlgHom).IsPrime := Ideal.comap_isPrime _ _
  have hb := bijective_localAlgHom_algEquiv R e Q'
  rw [← Ideal.ramificationIdx_comap_of_bijective _ Q' hb]
  refine h _ inferInstance ⟨?_⟩
  rw [Ideal.under_comap_algHom, ← Ideal.over_def Q' p]

theorem isTamelyRamifiedOver_congr [IsLocalRing R] {S' : Type*} [CommRing S'] [Algebra R S']
    (e : S ≃ₐ[R] S') : IsTamelyRamifiedOver R S ↔ IsTamelyRamifiedOver R S' :=
  ⟨.of_algEquiv R e, .of_algEquiv R e.symm⟩

end Classical

section Galois

variable (R : Type u) [CommRing R] [IsLocalRing R] {K : Type*} [Field K] [Algebra R K]

/-- The Galois closure of `L/K` (when `L/K` is separable), as a subfield of an algebraic closure
of `L`. -/
noncomputable abbrev galoisClosure (K L : Type*) [Field K] [Field L] [Algebra K L] :
    IntermediateField K (AlgebraicClosure L) :=
  IntermediateField.normalClosure K L (AlgebraicClosure L)

instance isGalois_galoisClosure (L : Type*) [Field L] [Algebra K L] [Algebra.IsSeparable K L] :
    IsGalois K (galoisClosure K L) := by
  refine { to_isSeparable := ?_, to_normal := inferInstance }
  rw [← le_separableClosure_iff]
  change IntermediateField.normalClosure K L (AlgebraicClosure L) ≤ _
  rw [normalClosure_def]
  refine iSup_le fun f ↦ ?_
  have : Algebra.IsSeparable K f.fieldRange := Algebra.IsSeparable.of_algHom _ _
    (f.equivFieldRange.symm : f.fieldRange →ₐ[K] L)
  exact (le_separableClosure_iff K _ _).mpr this

instance isScalarTower_galoisClosure (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] : IsScalarTower R L (galoisClosure K L) :=
  .of_algebraMap_eq fun r ↦ Subtype.ext (by
    change algebraMap R (AlgebraicClosure L) r =
      algebraMap L (AlgebraicClosure L) (algebraMap R L r)
    rw [← IsScalarTower.algebraMap_apply])

/-- XIII 2.0, for a field extension: `L` is tamely ramified over `R` when the inertia groups of its
Galois closure `L'` have order prime to the residue characteristic. The inertia groups are those
of `Gal(L'/K)` at the primes of the normalization of `R` in `L'` over the maximal ideal (for a
discrete valuation ring `R` these correspond to the valuations of `L'` extending that of `R`). -/
def IsTameExtension (L : Type*) [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] :
    Prop :=
  ∀ (P : Ideal (integralClosure R (galoisClosure K L))) [P.IsPrime],
    P.LiesOver (maximalIdeal R) →
      ¬ ringChar (ResidueField R) ∣ Nat.card (P.inertia Gal(galoisClosure K L/K))

/-- XIII 2.0: an étale `K`-algebra `L` is tamely ramified over `R` when all its factors
`L/m` (for `m` maximal) are. -/
def IsTameAlgebra (L : Type*) [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] :
    Prop :=
  ∀ (m : Ideal L) (_ : m.IsMaximal),
    letI := Ideal.Quotient.field m
    IsTameExtension R (K := K) (L ⧸ m)

lemma isTameExtension_of_ringChar_eq_zero (h : ringChar (ResidueField R) = 0) (L : Type*)
    [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] :
    IsTameExtension R (K := K) L := by
  intro P _ _ hdvd
  rw [h, zero_dvd_iff] at hdvd
  exact (Nat.card_pos (α := P.inertia Gal(galoisClosure K L/K))).ne' hdvd

/-- In residue characteristic zero every finite étale algebra is tamely ramified (used in
XIII 2.6). -/
lemma isTameAlgebra_of_ringChar_eq_zero (h : ringChar (ResidueField R) = 0) (L : Type*)
    [CommRing L] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Module.Finite K L] :
    IsTameAlgebra R (K := K) L := by
  intro m hm
  let _ := Ideal.Quotient.field m
  exact isTameExtension_of_ringChar_eq_zero R h (L ⧸ m)

/-- An integer vanishes in the residue field `R/m` if and only if it vanishes in `κ(m)`. -/
lemma natCast_residueField_eq_zero_iff (n : ℕ) :
    (n : ResidueField R) = 0 ↔ (n : (maximalIdeal R).ResidueField) = 0 := by
  rw [← natCast_mem_iff_residueField, ← map_natCast (residue R), residue_eq_zero_iff]

lemma not_ringChar_dvd_iff (n : ℕ) :
    ¬ ringChar (ResidueField R) ∣ n ↔ (n : (maximalIdeal R).ResidueField) ≠ 0 := by
  rw [← CharP.cast_eq_zero_iff (ResidueField R), natCast_residueField_eq_zero_iff]

/-- The Galois closure of a normal extension `L/K` is (the image of) `L`. -/
lemma galoisClosure_eq_fieldRange (L : Type*) [Field L] [Algebra K L] [Normal K L] :
    galoisClosure K L = (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).fieldRange := by
  set ι := IsScalarTower.toAlgHom K L (AlgebraicClosure L)
  rw [galoisClosure, normalClosure_def]
  refine le_antisymm (iSup_le fun f ↦ ?_) (le_iSup_of_le ι le_rfl)
  let e : L ≃ₐ[K] ι.fieldRange := AlgEquiv.ofInjectiveField ι
  have : Normal K ι.fieldRange := Normal.of_algEquiv e
  have h := AlgHom.fieldRange_of_normal (f.comp e.symm.toAlgHom)
  have : f.fieldRange = (f.comp e.symm.toAlgHom).fieldRange := by
    ext x
    simp only [AlgHom.mem_fieldRange, AlgHom.coe_comp, Function.comp_apply]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨e y, by simpa using hy⟩, fun ⟨y, hy⟩ ↦ ⟨_, hy⟩⟩
  rw [this, h]

/-- The Galois closure of a finite normal extension `L/K` has degree `[L : K]`. -/
lemma finrank_galoisClosure (L : Type*) [Field L] [Algebra K L] [Normal K L] :
    Module.finrank K (galoisClosure K L) = Module.finrank K L := by
  rw [(IntermediateField.equivOfEq (galoisClosure_eq_fieldRange L)).toLinearEquiv.finrank_eq]
  exact (AlgEquiv.ofInjectiveField
    (IsScalarTower.toAlgHom K L (AlgebraicClosure L))).toLinearEquiv.finrank_eq.symm

/-- XIII 2.0: a finite Galois extension `L/K` of degree prime to the residue characteristic of the
local ring `R` is tamely ramified over `R`: its inertia groups have order dividing `[L : K]`. -/
theorem isTameExtension_of_isGalois (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
    (h : ¬ ringChar (ResidueField R) ∣ Module.finrank K L) :
    IsTameExtension R (K := K) L := by
  intro P _ _ hdvd
  apply h
  refine hdvd.trans ((Subgroup.card_subgroup_dvd_card _).trans ?_)
  rw [IsGalois.card_aut_eq_finrank, finrank_galoisClosure]

end Galois

section DiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A prime of the normalization of `R` over the maximal ideal is nonzero. -/
lemma ne_bot_of_liesOver_maximalIdeal (M : Type*) [Field M] [Algebra K M] [Algebra R M]
    [IsScalarTower R K M] (P : Ideal (integralClosure R M)) [P.LiesOver (maximalIdeal R)] :
    P ≠ ⊥ := by
  rintro rfl
  apply IsDiscreteValuationRing.not_a_field R
  rw [Ideal.over_def (⊥ : Ideal (integralClosure R M)) (maximalIdeal R), Ideal.under,
    ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
      (integralClosure.algebraMap_injective_of_isFractionRing R K M)]

/-- XIII 2.0 (Serre, *Local fields*, IV §2, Cor. 4 when the residue extension is separable; SGA
indicates how the proof extends to the general case): let `L/K` be a finite Galois extension and
`P` a prime of the normalization of `R` in `L` over the maximal ideal. The inertia group of `P`
is an extension of a cyclic group of order prime to the residue characteristic `p` by a normal
`p`-group (the wild inertia group). Here `p` is the characteristic exponent of the residue field
(`1` in characteristic zero, when the `p`-group is trivial). -/
theorem exists_isPGroup_isCyclic_quotient_inertia (L : Type*) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal (integralClosure R L)) [P.IsPrime] [P.LiesOver (maximalIdeal R)] :
    ∃ (W : Subgroup (P.inertia Gal(L/K))) (_ : W.Normal),
      IsPGroup (ringExpChar (ResidueField R)) W ∧ IsCyclic (P.inertia Gal(L/K) ⧸ W) ∧
        (Nat.card (P.inertia Gal(L/K) ⧸ W)).Coprime (ringExpChar (ResidueField R)) := by
  have := integralClosure.isDedekindDomain' R K L
  have := integralClosure.isGaloisGroup R K L
  have : FaithfulSMul Gal(L/K) (integralClosure R L) := IsGaloisGroup.faithful R
  obtain ⟨_, hπ⟩ := Ideal.exists_isLocalUniformizer_of_ne_bot P
    (ne_bot_of_liesOver_maximalIdeal R (K := K) L P)
  -- the characteristic of `B/P` is that of the residue field of `R`
  have hchar (n : ℕ) : (n : integralClosure R L ⧸ P) = 0 ↔ (n : ResidueField R) = 0 := by
    rw [natCast_residueField_eq_zero_iff, ← not_ne_iff, ← not_ne_iff (b := (0 : _)),
      Ideal.natCast_residueField_ne_zero_iff (maximalIdeal R) P]
  have hexp : ringExpChar (integralClosure R L ⧸ P) = ringExpChar (ResidueField R) := by
    have : CharP (integralClosure R L ⧸ P) (ringChar (ResidueField R)) :=
      ⟨fun n ↦ (hchar n).trans (CharP.cast_eq_zero_iff _ _ n)⟩
    rw [ringExpChar, ringExpChar, ringChar.eq (integralClosure R L ⧸ P) (ringChar _)]
  obtain ⟨W, hW, hp, hc, hcard⟩ := Ideal.exists_isPGroup_isCyclic_quotient_inertia Gal(L/K) P hπ
  refine ⟨W, hW, hexp ▸ hp, hc, ?_⟩
  have hq : ExpChar (ResidueField R) (ringExpChar (ResidueField R)) := inferInstance
  generalize ringExpChar (ResidueField R) = q at hq
  cases hq with
  | zero => exact Nat.coprime_one_right _
  | prime hprime =>
    refine ((Nat.Prime.coprime_iff_not_dvd hprime).mpr fun hdvd ↦ hcard ?_).symm
    rw [hchar, CharP.cast_eq_zero_iff (ResidueField R) q]
    exact hdvd

/-- The Galois closure `L'` of `L` is tamely ramified if and only if the wild inertia groups of
`L'` are trivial. -/
lemma isTameExtension_iff_forall_wildInertia_eq_bot (L : Type*) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsTameExtension R (K := K) L ↔
      ∀ P : Ideal (integralClosure R (galoisClosure K L)), P.IsPrime →
        P.LiesOver (maximalIdeal R) → Ideal.wildInertia Gal(galoisClosure K L/K) P = ⊥ := by
  set M := galoisClosure K L
  have := integralClosure.isDedekindDomain' R K M
  have := integralClosure.finite R K M
  have := integralClosure.flat R K M
  have := integralClosure.isGaloisGroup R K M
  refine forall_congr' fun P ↦ ⟨fun h hP hPp ↦ ?_, fun h hP hPp ↦ ?_⟩
  · rw [← Ideal.natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot (maximalIdeal R) P
      (ne_bot_of_liesOver_maximalIdeal R (K := K) M P), ← not_ringChar_dvd_iff]
    exact h hPp
  · rw [not_ringChar_dvd_iff, Ideal.natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot
      (maximalIdeal R) P (ne_bot_of_liesOver_maximalIdeal R (K := K) M P)]
    exact h hP hPp

/-- The Galois closure `L'` of `L` is tamely ramified if and only if the wild inertia groups of
`L'` lie in `Gal(L'/L)`. -/
lemma isTameExtension_iff_forall_wildInertia_le (L : Type*) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsTameExtension R (K := K) L ↔
      ∀ P : Ideal (integralClosure R (galoisClosure K L)), P.IsPrime →
        P.LiesOver (maximalIdeal R) → Ideal.wildInertia Gal(galoisClosure K L/K) P ≤
          fixingSubgroup Gal(galoisClosure K L/K)
            (Set.range (algebraMap L (galoisClosure K L))) := by
  have := integralClosure.isDedekindDomain' R K (galoisClosure K L)
  have := integralClosure.finite R K (galoisClosure K L)
  have := integralClosure.flat R K (galoisClosure K L)
  have := integralClosure.isGaloisGroup R K (galoisClosure K L)
  rw [isTameExtension_iff_forall_wildInertia_eq_bot]
  refine ⟨fun h P hP hPp ↦ (h P hP hPp).le.trans bot_le, fun h P hP hPp ↦ ?_⟩
  have := Ideal.wildInertia_le_normalCore (maximalIdeal R) P _ h
  rwa [normalCore_fixingSubgroup_range_eq_bot K L (galoisClosure K L), le_bot_iff] at this

/-- Let `M/K` be a finite Galois extension containing `E`. Then `E` is tamely ramified over `R` in
the classical sense (at every prime of its normalization) if and only if the wild inertia groups of
the primes of the normalization of `R` in `M` lie in `Gal(M/E)`. -/
theorem isTamelyRamifiedOver_iff_forall_wildInertia_le (E M : Type*) [Field E] [Algebra K E]
    [Algebra R E] [IsScalarTower R K E] [FiniteDimensional K E] [Algebra.IsSeparable K E]
    [Field M] [Algebra K M] [Algebra E M] [IsScalarTower K E M] [Algebra R M]
    [IsScalarTower R K M] [IsScalarTower R E M] [FiniteDimensional K M] [IsGalois K M] :
    IsTamelyRamifiedOver R (integralClosure R E) ↔
      ∀ P : Ideal (integralClosure R M), P.IsPrime → P.LiesOver (maximalIdeal R) →
        Ideal.wildInertia Gal(M/K) P ≤ fixingSubgroup Gal(M/K) (Set.range (algebraMap E M)) := by
  let := integralClosure.algebraOfTower R E M
  have := integralClosure.isDedekindDomain' R K M
  have := integralClosure.finite R K M
  have := integralClosure.flat R K M
  have := integralClosure.isGaloisGroup R K M
  have := integralClosure.finite R K E
  have := integralClosure.finite_of_tower R E M K
  have := integralClosure.flat_of_tower R E M K
  have := integralClosure.isGaloisGroup_of_tower R E M K
  have : FaithfulSMul (integralClosure R E) (integralClosure R M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (integralClosure.algebraMap_algebraOfTower_injective R E M)
  constructor
  · intro h P _ _
    rw [← Ideal.tame_under_iff_wildInertia_le (C := integralClosure R E) (maximalIdeal R) P
      (fixingSubgroup Gal(M/K) (Set.range (algebraMap E M)))
      (ne_bot_of_liesOver_maximalIdeal R (K := K) M P),
      ← isTamelyRamifiedAt_iff_of_liesOver]
    exact h _ inferInstance
  · intro h Q _ _
    obtain ⟨P, hP, hPQ⟩ := (inferInstance : Nonempty (Q.primesOver (integralClosure R M)))
    have : P.LiesOver (maximalIdeal R) := Ideal.LiesOver.trans P Q (maximalIdeal R)
    obtain rfl : Q = P.under (integralClosure R E) := Ideal.over_def P Q
    rw [isTamelyRamifiedAt_iff_of_liesOver R (maximalIdeal R),
      Ideal.tame_under_iff_wildInertia_le (C := integralClosure R E) (maximalIdeal R) P
      (fixingSubgroup Gal(M/K) (Set.range (algebraMap E M)))
        (ne_bot_of_liesOver_maximalIdeal R (K := K) M P)]
    exact h P hP inferInstance

/-- XIII 2.0: SGA's notion of tame ramification agrees with the classical one. A finite separable
extension `L/K` is tamely ramified over `R` (the inertia groups of its Galois closure have order
prime to the residue characteristic) if and only if every prime of the normalization of `R` in `L`
has ramification index prime to the residue characteristic and separable residue extension.
(Both conditions are equivalent to the wild inertia groups of the Galois closure being contained
in `Gal(L'/L)`, hence trivial, since `Gal(L'/L)` contains no nontrivial normal subgroup.) -/
theorem isTameExtension_iff_isTamelyRamifiedOver (L : Type*) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsTameExtension R (K := K) L ↔ IsTamelyRamifiedOver R (integralClosure R L) := by
  rw [isTameExtension_iff_forall_wildInertia_le,
    isTamelyRamifiedOver_iff_forall_wildInertia_le R (K := K) L (galoisClosure K L)]

/-- `L` is tamely ramified over `R` if and only if, in some (equivalently, any) finite Galois
extension `M/K` containing `L`, the wild inertia groups lie in `Gal(M/L)`. -/
theorem isTameExtension_iff_forall_wildInertia_le_of_isGalois (L M : Type*) [Field L]
    [Algebra K L] [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L]
    [Algebra.IsSeparable K L] [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [Algebra R M] [IsScalarTower R K M] [IsScalarTower R L M] [FiniteDimensional K M]
    [IsGalois K M] :
    IsTameExtension R (K := K) L ↔
      ∀ P : Ideal (integralClosure R M), P.IsPrime → P.LiesOver (maximalIdeal R) →
        Ideal.wildInertia Gal(M/K) P ≤ fixingSubgroup Gal(M/K) (Set.range (algebraMap L M)) := by
  rw [isTameExtension_iff_isTamelyRamifiedOver,
    isTamelyRamifiedOver_iff_forall_wildInertia_le R (K := K) L M]

/-- In a Galois extension `L/K`, the ramification indices over the discrete valuation ring `R` of
the primes of the normalization of `R` in `L` divide `[L : K]`. -/
theorem ramificationIdx_dvd_finrank (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [IsGalois K L] (Q : Ideal (integralClosure R L))
    [Q.IsPrime] [Q.LiesOver (maximalIdeal R)] : Q.ramificationIdx R ∣ Module.finrank K L := by
  have := integralClosure.finite R K L
  have := integralClosure.flat R K L
  have := integralClosure.isGaloisGroup R K L
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (maximalIdeal R)
    (integralClosure R L) Gal(L/K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (maximalIdeal R) Q Gal(L/K),
    IsGalois.card_aut_eq_finrank] at h
  rw [← h]
  exact (Dvd.intro _ rfl).mul_left _

/-- An integer is prime to the residue characteristic of `R` if and only if it is nonzero in
`B/P`, for `P` over the maximal ideal. -/
lemma not_ringChar_dvd_iff_quotient {B : Type*} [CommRing B] [Algebra R B] (P : Ideal B)
    [P.IsPrime] [P.LiesOver (maximalIdeal R)] (n : ℕ) :
    ¬ ringChar (ResidueField R) ∣ n ↔ (n : B ⧸ P) ≠ 0 := by
  rw [not_ringChar_dvd_iff, Ideal.natCast_residueField_ne_zero_iff (maximalIdeal R) P]

/-- The index of `Gal(M/L)` in `Gal(M/K)` is `[L : K]`. -/
lemma index_fixingSubgroup_range (L M : Type*) [Field L] [Field M] [Algebra K L] [Algebra K M]
    [Algebra L M] [IsScalarTower K L M] [FiniteDimensional K M] [IsGalois K M] :
    (fixingSubgroup Gal(M/K) (Set.range (algebraMap L M))).index = Module.finrank K L := by
  have : FiniteDimensional K L := FiniteDimensional.left K L M
  have := IsGaloisGroup.of_isScalarTower Gal(M/K) K M L
  have h1 := (fixingSubgroup Gal(M/K) (Set.range (algebraMap L M))).index_mul_card
  rw [IsGaloisGroup.card_eq_finrank _ L M, IsGalois.card_aut_eq_finrank,
    ← Module.finrank_mul_finrank K L M] at h1
  have : FiniteDimensional L M := Module.Finite.of_restrictScalars_finite K L M
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos h1

section Stability

/-- XIII 2.0.3 for fields: a subextension of a tamely ramified extension is tamely ramified. Here
the subextension is given by a `K`-embedding `f : F₀ → F`. -/
theorem IsTameExtension.of_algHom {F₀ F : Type*} [Field F₀] [Field F] [Algebra K F₀]
    [Algebra K F] [Algebra R F₀] [Algebra R F] [IsScalarTower R K F₀] [IsScalarTower R K F]
    [FiniteDimensional K F] [Algebra.IsSeparable K F] (f : F₀ →ₐ[K] F)
    (hF : IsTameExtension R (K := K) F) : IsTameExtension R (K := K) F₀ := by
  have : FiniteDimensional K F₀ := FiniteDimensional.of_injective f.toLinearMap f.injective
  have : Algebra.IsSeparable K F₀ := Algebra.IsSeparable.of_algHom (F := K) (E := F₀) (E' := F) f
  let : Algebra F₀ (galoisClosure K F) :=
    ((algebraMap F (galoisClosure K F)).comp f.toRingHom).toAlgebra
  have : IsScalarTower K F₀ (galoisClosure K F) := .of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, f.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower R F₀ (galoisClosure K F) := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R K F₀, IsScalarTower.algebraMap_apply R K,
      ← IsScalarTower.algebraMap_apply K F₀]
  rw [isTameExtension_iff_forall_wildInertia_le_of_isGalois R F₀ (galoisClosure K F)]
  rw [isTameExtension_iff_forall_wildInertia_le] at hF
  refine fun P hP hPm ↦ (hF P hP hPm).trans (fixingSubgroup_antitone _ _ ?_)
  rintro _ ⟨x, rfl⟩
  exact ⟨f x, rfl⟩

/-- If `f : F → E` is a `K`-embedding and `F` is tamely ramified, the wild inertia groups of the
Galois closure of `E` fix the image of `F`. -/
lemma wildInertia_le_of_algHom {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra K E]
    [Algebra R F] [Algebra R E] [IsScalarTower R K F] [IsScalarTower R K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (f : F →ₐ[K] E)
    (hF : IsTameExtension R (K := K) F) :
    ∀ P : Ideal (integralClosure R (galoisClosure K E)), P.IsPrime →
      P.LiesOver (maximalIdeal R) → Ideal.wildInertia Gal(galoisClosure K E/K) P ≤
        fixingSubgroup Gal(galoisClosure K E/K)
          ((algebraMap E (galoisClosure K E)) '' Set.range f) := by
  set N := galoisClosure K E
  have : FiniteDimensional K F := FiniteDimensional.of_injective f.toLinearMap f.injective
  have : Algebra.IsSeparable K F := Algebra.IsSeparable.of_algHom (F := K) (E := F) (E' := E) f
  let : Algebra F N := ((algebraMap E N).comp f.toRingHom).toAlgebra
  have : IsScalarTower K F N := .of_algebraMap_eq fun x ↦ by
    rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, f.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower R F N := .of_algebraMap_eq fun x ↦ by
    rw [IsScalarTower.algebraMap_apply R K F, IsScalarTower.algebraMap_apply R K,
      ← IsScalarTower.algebraMap_apply K F]
  rw [isTameExtension_iff_forall_wildInertia_le_of_isGalois R F N] at hF
  refine fun P hP hPm ↦ (hF P hP hPm).trans (le_of_eq (congrArg _ ?_))
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨f x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨x, rfl⟩

/-- XIII 2.0.3 for fields: a composite of tamely ramified extensions is tamely ramified. Here `E`
is generated by the images of `K`-embeddings `f₁ : F₁ → E` and `f₂ : F₂ → E`. -/
theorem IsTameExtension.of_adjoin_eq_top {F₁ F₂ E : Type*} [Field F₁] [Field F₂] [Field E]
    [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra R F₁] [Algebra R F₂] [Algebra R E]
    [IsScalarTower R K F₁] [IsScalarTower R K F₂] [IsScalarTower R K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E] (f₁ : F₁ →ₐ[K] E) (f₂ : F₂ →ₐ[K] E)
    (h : Algebra.adjoin K (Set.range f₁ ∪ Set.range f₂) = ⊤)
    (h₁ : IsTameExtension R (K := K) F₁) (h₂ : IsTameExtension R (K := K) F₂) :
    IsTameExtension R (K := K) E := by
  set N := galoisClosure K E
  rw [isTameExtension_iff_forall_wildInertia_le]
  intro P hP hPm σ hσ
  have hσ₁ := wildInertia_le_of_algHom R f₁ h₁ P hP hPm hσ
  have hσ₂ := wildInertia_le_of_algHom R f₂ h₂ P hP hPm hσ
  let ι := IsScalarTower.toAlgHom K E N
  have hS : Algebra.adjoin K (Set.range f₁ ∪ Set.range f₂) ≤
      AlgHom.equalizer ((σ : Gal(N/K)).toAlgHom.comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    rintro _ (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact (mem_fixingSubgroup_iff _).mp hσ₁ _ ⟨_, ⟨x, rfl⟩, rfl⟩
    · exact (mem_fixingSubgroup_iff _).mp hσ₂ _ ⟨_, ⟨x, rfl⟩, rfl⟩
  rw [h, top_le_iff] at hS
  rintro ⟨_, ⟨y, rfl⟩⟩
  have hy : y ∈ AlgHom.equalizer ((σ : Gal(N/K)).toAlgHom.comp ι) ι := hS ▸ Algebra.mem_top
  exact hy

variable (K) in
/-- The kernel of a `K`-algebra map from a finite `K`-algebra to a field is maximal. -/
lemma isMaximal_ker_of_finite {A E : Type*} [CommRing A] [Algebra K A] [Module.Finite K A]
    [Field E] [Algebra K E] (f : A →ₐ[K] E) : (RingHom.ker f).IsMaximal := by
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime _
  infer_instance

/-- XIII 2.0.3: a subalgebra of a tamely ramified étale algebra is tamely ramified. -/
theorem IsTameAlgebra.subalgebra {L : Type*} [CommRing L] [Algebra K L] [Algebra.Etale K L]
    [Algebra R L] [IsScalarTower R K L] (hL : IsTameAlgebra R (K := K) L) (L₀ : Subalgebra K L) :
    IsTameAlgebra R (K := K) L₀ := by
  intro m₀ hm₀
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have : Module.Finite L₀ L := Module.Finite.of_restrictScalars_finite K L₀ L
  obtain ⟨m, hm, hmm₀⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := L) m₀
    (by rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective L₀ L)];
        exact bot_le)
  let := Ideal.Quotient.field m₀
  let := Ideal.Quotient.field m
  exact IsTameExtension.of_algHom R
    (Ideal.quotientMapₐ m (IsScalarTower.toAlgHom K L₀ L) hmm₀.ge) (hL m hm)

/-- XIII 2.0.3: a tensor product of tamely ramified étale algebras is tamely ramified. -/
theorem IsTameAlgebra.tensorProduct {L M : Type*} [CommRing L] [Algebra K L] [Algebra.Etale K L]
    [Algebra R L] [IsScalarTower R K L] [CommRing M] [Algebra K M] [Algebra.Etale K M]
    [Algebra R M] [IsScalarTower R K M] (hL : IsTameAlgebra R (K := K) L)
    (hM : IsTameAlgebra R (K := K) M) : IsTameAlgebra R (K := K) (TensorProduct K L M) := by
  intro n hn
  let := Ideal.Quotient.field n
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  have : Module.Finite K M := Algebra.FormallyUnramified.finite_of_free K M
  have : Algebra.Etale K (TensorProduct K L M) := Algebra.Etale.comp K L _
  have : Module.Finite K (TensorProduct K L M) :=
    Algebra.FormallyUnramified.finite_of_free K _
  set g₁ := (Ideal.Quotient.mkₐ K n).comp
    (Algebra.TensorProduct.includeLeft : L →ₐ[K] TensorProduct K L M)
  set g₂ := (Ideal.Quotient.mkₐ K n).comp Algebra.TensorProduct.includeRight
  have h₁ := isMaximal_ker_of_finite K g₁
  have h₂ := isMaximal_ker_of_finite K g₂
  let := Ideal.Quotient.field (RingHom.ker g₁)
  let := Ideal.Quotient.field (RingHom.ker g₂)
  refine IsTameExtension.of_adjoin_eq_top R (Ideal.kerLiftAlg g₁) (Ideal.kerLiftAlg g₂) ?_
    (hL _ h₁) (hM _ h₂)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have : Ideal.Quotient.mk n (a ⊗ₜ[K] b) =
        Ideal.kerLiftAlg g₁ (Ideal.Quotient.mk _ a) *
          Ideal.kerLiftAlg g₂ (Ideal.Quotient.mk _ b) := by
      rw [Ideal.kerLiftAlg_mk, Ideal.kerLiftAlg_mk]
      simp only [g₁, g₂, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply,
        ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact mul_mem (Algebra.subset_adjoin (Or.inl ⟨_, rfl⟩))
      (Algebra.subset_adjoin (Or.inr ⟨_, rfl⟩))
  | add x y hx hy => simpa using add_mem hx hy

end Stability

section StrictlyHenselian

variable [HenselianLocalRing R] [IsSepClosed (ResidueField R)]

/-- XIII 2.0.1, main step: over a strictly henselian discrete valuation ring `R`, the whole Galois
group of the Galois closure `L'` of `L` is an inertia group, so that `L` is tamely ramified if and
only if `[L' : K]` is prime to the residue characteristic. -/
theorem isTameExtension_iff_not_dvd_card (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsTameExtension R (K := K) L ↔
      ¬ ringChar (ResidueField R) ∣ Nat.card Gal(galoisClosure K L/K) := by
  set M := galoisClosure K L
  have := integralClosure.finite R K M
  have := integralClosure.flat R K M
  have := integralClosure.isGaloisGroup R K M
  have : FaithfulSMul R (integralClosure R M) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (integralClosure.algebraMap_injective_of_isFractionRing R K M)
  obtain ⟨P, hP, hPm⟩ := (inferInstance : Nonempty ((maximalIdeal R).primesOver
    (integralClosure R M)))
  refine ⟨fun h ↦ ?_, fun h P' _ _ ↦ ?_⟩
  · have := h P hPm
    rwa [Ideal.inertia_eq_top_of_isSepClosed (A := R) P, Subgroup.card_top] at this
  · rwa [Ideal.inertia_eq_top_of_isSepClosed (A := R) P', Subgroup.card_top]

/-- XIII 2.0.1: over a strictly henselian discrete valuation ring `R`, a finite separable
extension `L` of the fraction field `K` is tamely ramified if and only if `[L : K]` is prime to
the residue characteristic. -/
theorem isTameExtension_iff_not_dvd_finrank (L : Type*) [Field L] [Algebra K L] [Algebra R L]
    [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsTameExtension R (K := K) L ↔ ¬ ringChar (ResidueField R) ∣ Module.finrank K L := by
  set M := galoisClosure K L
  set G := Gal(M/K)
  have := integralClosure.isDedekindDomain' R K M
  have := integralClosure.finite R K M
  have := integralClosure.flat R K M
  have := integralClosure.isGaloisGroup R K M
  have : FaithfulSMul G (integralClosure R M) := IsGaloisGroup.faithful R
  constructor
  · intro h hdvd
    rw [isTameExtension_iff_not_dvd_card, IsGalois.card_aut_eq_finrank,
      ← Module.finrank_mul_finrank K L M] at h
    exact h (hdvd.mul_right _)
  · intro h
    rw [isTameExtension_iff_forall_wildInertia_le]
    intro P _ _
    obtain ⟨_, hπ⟩ := Ideal.exists_isLocalUniformizer_of_ne_bot P
      (ne_bot_of_liesOver_maximalIdeal R (K := K) M P)
    rw [← Ideal.natCast_relIndex_inertia_ne_zero_iff hπ,
      Ideal.inertia_eq_top_of_isSepClosed (A := R) P, Subgroup.relIndex_top_right,
      index_fixingSubgroup_range, ← not_ringChar_dvd_iff_quotient R P]
    exact h

/-- XIII 2.0.1: over a strictly henselian discrete valuation ring `R`, a tamely ramified finite
separable extension `L` of the fraction field `K` is a cyclic Galois extension (its Galois closure
has Galois group an inertia group of order prime to the residue characteristic, hence cyclic). -/
theorem isGalois_and_isCyclic_of_isTameExtension (L : Type*) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hL : IsTameExtension R (K := K) L) : IsGalois K L ∧ IsCyclic Gal(L/K) := by
  set M := galoisClosure K L
  set G := Gal(M/K)
  have := integralClosure.isDedekindDomain' R K M
  have := integralClosure.finite R K M
  have := integralClosure.flat R K M
  have := integralClosure.isGaloisGroup R K M
  have : FaithfulSMul G (integralClosure R M) := IsGaloisGroup.faithful R
  have : FaithfulSMul R (integralClosure R M) := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (integralClosure.algebraMap_injective_of_isFractionRing R K M)
  obtain ⟨P, hP, hPm⟩ := (inferInstance : Nonempty ((maximalIdeal R).primesOver
    (integralClosure R M)))
  obtain ⟨_, hπ⟩ := Ideal.exists_isLocalUniformizer_of_ne_bot P
    (ne_bot_of_liesOver_maximalIdeal R (K := K) M P)
  have hI := Ideal.inertia_eq_top_of_isSepClosed (A := R) (G := G) P
  rw [isTameExtension_iff_not_dvd_card, not_ringChar_dvd_iff_quotient R P] at hL
  have hcyc := Ideal.isCyclic_inertia G P hπ (by rwa [hI, Subgroup.card_top])
  rw [hI] at hcyc
  have : IsCyclic G := isCyclic_of_surjective Subgroup.topEquiv.toMonoidHom
    Subgroup.topEquiv.surjective
  set F := (IsScalarTower.toAlgHom K L M).fieldRange
  have hF : IsGalois K F := by
    have := IsGalois.of_fixedField_normal_subgroup F.fixingSubgroup
    rwa [IsGalois.fixedField_fixingSubgroup] at this
  have : IsGalois K L := IsGalois.of_algEquiv (IsScalarTower.toAlgHom K L M).equivFieldRange.symm
  exact ⟨this, isCyclic_of_surjective (AlgEquiv.restrictNormalHom L)
    (AlgEquiv.restrictNormalHom_surjective M)⟩

end StrictlyHenselian

end DiscreteValuationRing

section BaseChange

open Polynomial

variable {R R' : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R']
  [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [IsLocalHom (algebraMap R R')]
  {K K' : Type*} [Field K] [Field K'] [Algebra R K] [IsFractionRing R K] [Algebra R' K']
  [IsFractionRing R' K'] [Algebra K K'] [Algebra R K'] [IsScalarTower R K K']
  [IsScalarTower R R' K']

omit [IsFractionRing R K] in
/-- XIII 2.0.2 (and 2.0.3), inertia form: tame ramification is preserved by extension of the
discrete valuation ring. Let `R → R'` be a local homomorphism of discrete valuation rings, `L` a
finite separable extension of `K = Frac R` tamely ramified over `R`, and `F'` an extension of
`K' = Frac R'` generated by an image of `L`. Then `F'` is tamely ramified over `R'`: the inertia
groups of `K' N / K'`, `N` the Galois closure of `L`, embed into those of `N / K`. -/
theorem IsTameExtension.of_adjoin_range_eq_top {L F' : Type*} [Field L] [Field F'] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F'] [Algebra R' F']
    [IsScalarTower R' K' F'] (f : L →ₐ[K] F') (hgen : IntermediateField.adjoin K' (Set.range f) = ⊤)
    (hL : IsTameExtension R (K := K) L) : IsTameExtension R' (K := K') F' := by
  classical
  -- the Galois closure `N` of `L`, splitting field of a separable polynomial `T`
  obtain ⟨T, hTsep, hTsplit⟩ := IsGalois.is_separable_splitting_field K (galoisClosure K L)
  -- an embedding `ι : N → Ā` extending `L → F' → Ā`
  let : Algebra L (AlgebraicClosure F') :=
    ((algebraMap F' (AlgebraicClosure F')).comp f.toRingHom).toAlgebra
  have : IsScalarTower K L (AlgebraicClosure F') := .of_algebraMap_eq fun k ↦ by
    change _ = algebraMap F' _ (f (algebraMap K L k))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply]
  have : Algebra.IsAlgebraic L (galoisClosure K L) := Algebra.IsAlgebraic.tower_top (K := K) L
  let ιL : galoisClosure K L →ₐ[L] AlgebraicClosure F' := IsAlgClosed.lift
  let ι : galoisClosure K L →ₐ[K] AlgebraicClosure F' := ιL.restrictScalars K
  have hιf (l : L) : ι (algebraMap L (galoisClosure K L) l) =
      algebraMap F' (AlgebraicClosure F') (f l) := ιL.commutes l
  -- `M' = K'(roots of T)`, a Galois extension of `K'` containing `ι N` and `F'`
  have hroot (x : AlgebraicClosure F') :
      x ∈ (T.map (algebraMap K K')).rootSet (AlgebraicClosure F') ↔
        x ∈ T.rootSet (AlgebraicClosure F') := by
    rw [mem_rootSet, mem_rootSet, aeval_map_algebraMap,
      Polynomial.map_ne_zero_iff (algebraMap K K').injective]
  let M' : IntermediateField K' (AlgebraicClosure F') :=
    IntermediateField.adjoin K' ((T.map (algebraMap K K')).rootSet (AlgebraicClosure F'))
  have : (T.map (algebraMap K K')).IsSplittingField K' M' :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : IsGalois K' M' := IsGalois.of_separable_splitting_field (p := T.map (algebraMap K K'))
    hTsep.map
  have : FiniteDimensional K' M' := IsSplittingField.finiteDimensional M'
    (T.map (algebraMap K K'))
  have hιM (x : galoisClosure K L) : ι x ∈ M' := by
    have hx : ι x ∈ ι.range := ⟨x, rfl⟩
    rw [← IsSplittingField.adjoin_rootSet_eq_range (galoisClosure K L) T ι] at hx
    refine Algebra.adjoin_le (S := (M'.restrictScalars K).toSubalgebra) ?_ hx
    intro y hy
    exact IntermediateField.subset_adjoin K' _ ((hroot y).mpr hy)
  let ιM : galoisClosure K L →ₐ[K] M' :=
    { toFun x := ⟨ι x, hιM x⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' x y := Subtype.ext (map_mul ι x y)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' x y := Subtype.ext (map_add ι x y)
      commutes' k := Subtype.ext (ι.commutes k) }
  have hfM (y : F') : algebraMap F' (AlgebraicClosure F') y ∈ M' := by
    have hy : y ∈ (⊤ : IntermediateField K' F') := trivial
    rw [← hgen] at hy
    have : IsScalarTower.toAlgHom K' F' (AlgebraicClosure F') y ∈
        (IntermediateField.adjoin K' (Set.range f)).map
          (IsScalarTower.toAlgHom K' F' (AlgebraicClosure F')) := ⟨y, hy, rfl⟩
    rw [IntermediateField.adjoin_map] at this
    refine (IntermediateField.adjoin_le_iff.mpr ?_) this
    rintro _ ⟨_, ⟨l, rfl⟩, rfl⟩
    rw [IsScalarTower.coe_toAlgHom', ← hιf]
    exact hιM _
  let fM : F' →ₐ[K'] M' :=
    { toFun y := ⟨algebraMap F' (AlgebraicClosure F') y, hfM y⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' x y := Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' x y := Subtype.ext (map_add _ x y)
      commutes' k := Subtype.ext ((IsScalarTower.toAlgHom K' F' (AlgebraicClosure F')).commutes k) }
  -- restriction `ρ : Gal(M'/K') → Gal(N/K)`, injective
  let : Algebra (galoisClosure K L) M' := ιM.toRingHom.toAlgebra
  have : IsScalarTower K (galoisClosure K L) M' := IsScalarTower.of_algHom ιM
  let res : Gal(M'/K') →* Gal(M'/K) :=
    { toFun σ := σ.restrictScalars K
      map_one' := rfl
      map_mul' _ _ := rfl }
  let ρ : Gal(M'/K') →* Gal(galoisClosure K L/K) :=
    (AlgEquiv.restrictNormalHom (galoisClosure K L)).comp res
  have hρ (σ : Gal(M'/K')) (x : galoisClosure K L) : ιM (ρ σ x) = σ (ιM x) :=
    AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) (galoisClosure K L) x
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_one ρ).mpr fun σ hσ ↦ AlgEquiv.ext fun y ↦ ?_
    have hfix (x : galoisClosure K L) : σ (ιM x) = ιM x := by
      rw [← hρ, hσ]
      rfl
    obtain ⟨y, hy⟩ := y
    change σ ⟨y, hy⟩ = ⟨y, hy⟩
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz =>
      have hz' : z ∈ ι.range := by
        rw [← IsSplittingField.adjoin_rootSet_eq_range (galoisClosure K L) T ι]
        exact Algebra.subset_adjoin ((hroot z).mp hz)
      obtain ⟨x, rfl⟩ := hz'
      exact hfix x
    | algebraMap k => exact σ.commutes k
    | add x y hx hy ihx ihy =>
      have := congrArg₂ (· + ·) ihx ihy
      rw [← map_add] at this
      exact this
    | inv x hx ihx =>
      have := congrArg (·⁻¹) ihx
      rw [← map_inv₀] at this
      exact this
    | mul x y hx hy ihx ihy =>
      have := congrArg₂ (· * ·) ihx ihy
      rw [← map_mul] at this
      exact this
  -- the map of normalizations `φ : R_N → R'_{M'}`
  have hRN : (algebraMap R' (AlgebraicClosure F')).comp (algebraMap R R') =
      ι.toRingHom.comp (algebraMap R (galoisClosure K L)) := by
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply R' K' (AlgebraicClosure F'),
      ← IsScalarTower.algebraMap_apply R R' K', IsScalarTower.algebraMap_apply R K K',
      ← IsScalarTower.algebraMap_apply K K' (AlgebraicClosure F'),
      IsScalarTower.algebraMap_apply R K (galoisClosure K L), ι.commutes]
  have hint (x : integralClosure R (galoisClosure K L)) : IsIntegral R' (ιM x) := by
    have h1 : IsIntegral R' (ι x) := by
      obtain ⟨q, hq, hqx⟩ := x.2
      refine ⟨q.map (algebraMap R R'), hq.map _, ?_⟩
      rw [eval₂_map, hRN]
      have := congrArg ι.toRingHom hqx
      rwa [hom_eval₂, map_zero] at this
    exact (isIntegral_algHom_iff (M'.val.restrictScalars R') Subtype.val_injective).mp h1
  let φ : integralClosure R (galoisClosure K L) →+* integralClosure R' M' :=
    { toFun x := ⟨ιM x, hint x⟩
      map_one' := Subtype.ext (map_one ιM)
      map_mul' x y := Subtype.ext (map_mul ιM x.1 y.1)
      map_zero' := Subtype.ext (map_zero ιM)
      map_add' x y := Subtype.ext (map_add ιM x.1 y.1) }
  have hφ (σ : Gal(M'/K')) (x : integralClosure R (galoisClosure K L)) :
      φ (ρ σ • x) = σ • φ x := Subtype.ext (hρ σ x)
  have hφR (r : R) : φ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) :=
    Subtype.ext (Subtype.ext (RingHom.congr_fun hRN r).symm)
  -- `M'` is tamely ramified over `R'`: its inertia groups embed into those of `N`
  have hM' : IsTameExtension R' (K := K') M' := by
    have := integralClosure.isDedekindDomain' R' K' M'
    have := integralClosure.isGaloisGroup R' K' M'
    rw [isTameExtension_iff_forall_wildInertia_le_of_isGalois R' M' M']
    intro P' _ hP'
    have hne := ne_bot_of_liesOver_maximalIdeal R' (K := K') M' P'
    have : (P'.comap φ).IsPrime := Ideal.comap_isPrime _ _
    have : (P'.comap φ).LiesOver (maximalIdeal R) := ⟨by
      ext r
      change r ∈ maximalIdeal R ↔ φ (algebraMap R _ r) ∈ P'
      rw [hφR, ← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def P' (maximalIdeal R'),
        IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        mem_nonunits_iff, isUnit_map_iff]⟩
    have hmap : (P'.inertia Gal(M'/K')).map ρ ≤
        (P'.comap φ).inertia Gal(galoisClosure K L/K) := by
      rintro _ ⟨σ, hσ, rfl⟩
      rw [SetLike.mem_coe, Ideal.mem_inertia] at hσ
      rw [Ideal.mem_inertia]
      intro x
      change φ (ρ σ • x - x) ∈ P'
      rw [map_sub, hφ]
      exact hσ (φ x)
    have hdvd : Nat.card (P'.inertia Gal(M'/K')) ∣
        Nat.card ((P'.comap φ).inertia Gal(galoisClosure K L/K)) := by
      rw [← Subgroup.card_map_of_injective hρinj]
      exact Subgroup.card_dvd_of_le hmap
    have h := hL (P'.comap φ) inferInstance
    have hc : ¬ ringChar (ResidueField R') ∣ Nat.card (P'.inertia Gal(M'/K')) := by
      rw [← Algebra.ringChar_eq (ResidueField R) (ResidueField R')]
      exact fun h' ↦ h (h'.trans hdvd)
    rw [(Ideal.natCast_card_inertia_ne_zero_iff_wildInertia_eq_bot (maximalIdeal R') P'
      hne).mp ((IsLocalRing.not_ringChar_dvd_iff _).mp hc)]
    exact bot_le
  exact IsTameExtension.of_algHom R' fM hM'

/-- If the maximal ideal of `R` generates that of `R'`, the ramification index of `𝔪_{R'}` over
`R` is `1`. -/
lemma ramificationIdx_maximalIdeal_eq_one
    (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R') :
    (maximalIdeal R').ramificationIdx R = 1 := by
  rw [Ideal.ramificationIdx_eq (maximalIdeal R) (maximalIdeal R')]
  have hmap : (maximalIdeal R).map (algebraMap R (Localization.AtPrime (maximalIdeal R'))) =
      maximalIdeal (Localization.AtPrime (maximalIdeal R')) := by
    rw [IsScalarTower.algebraMap_eq R R' (Localization.AtPrime (maximalIdeal R')),
      ← Ideal.map_map, hm, Localization.AtPrime.map_eq_maximalIdeal]
  have : IsSimpleModule (Localization.AtPrime (maximalIdeal R'))
      (Localization.AtPrime (maximalIdeal R') ⧸
        maximalIdeal (Localization.AtPrime (maximalIdeal R'))) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  rw [hmap, Module.length_eq_one]
  rfl

/-- XIII 2.0.2, Serre-style descent of tameness along `R → R'`: let `S` be a Dedekind domain over
`R` and `W` a domain over `S` and over `R'`, flat over both. If `Q' ⊆ W` over `Q ⊆ S` and over
`𝔪_{R'}` is tamely ramified over `R'`, then `Q` is tamely ramified over `R`, provided `𝔪_R`
generates `𝔪_{R'}` and the residue extension of `R'/R` is separable. -/
theorem isTamelyRamifiedAt_of_tower
    (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    [Algebra.IsSeparable (ResidueField R) (ResidueField R')] {S W : Type*} [CommRing S]
    [CommRing W] [Algebra R S] [Algebra S W] [Algebra R W] [Algebra R' W] [IsScalarTower R S W]
    [IsScalarTower R R' W] [Module.Flat S W] [Module.Flat R' W] (Q : Ideal S) [Q.IsPrime]
    [Q.LiesOver (maximalIdeal R)] (Q' : Ideal W) [Q'.IsPrime] [Q'.LiesOver Q]
    [Q'.LiesOver (maximalIdeal R')] (h : IsTamelyRamifiedAt R' Q') : IsTamelyRamifiedAt R Q := by
  have : Q'.LiesOver (maximalIdeal R) := Ideal.LiesOver.trans Q' Q (maximalIdeal R)
  -- ramification indices
  have h1 := Ideal.ramificationIdx_tower (R := R) Q Q'
  have h2 := Ideal.ramificationIdx_tower (R := R) (maximalIdeal R') Q'
  rw [ramificationIdx_maximalIdeal_eq_one hm, one_mul] at h2
  rw [isTamelyRamifiedAt_iff_of_liesOver R' (maximalIdeal R') Q'] at h
  rw [isTamelyRamifiedAt_iff_of_liesOver R (maximalIdeal R) Q]
  refine ⟨fun he ↦ h.1 ?_, ?_⟩
  · -- the ramification index of `Q` divides that of `Q'` over `R'`
    rw [← natCast_mem_iff_residueField] at he ⊢
    have : ((Q'.ramificationIdx R' : ℕ) : R') = algebraMap R R' (Q'.ramificationIdx R') :=
      (map_natCast _ _).symm
    rw [this, ← hm]
    refine Ideal.mem_map_of_mem _ ?_
    have hdvd : Q.ramificationIdx R ∣ Q'.ramificationIdx R' := ⟨Q'.ramificationIdx S, by
      rw [← h1, h2]⟩
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ he
  · -- the residue extensions
    let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) (maximalIdeal R')
    let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) Q
    let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R') Q'
    let := Localization.AtPrime.algebraOfLiesOver Q Q'
    let := Localization.AtPrime.algebraOfLiesOver (maximalIdeal R) Q'
    have : Algebra.IsSeparable (maximalIdeal R).ResidueField (maximalIdeal R').ResidueField :=
      Algebra.isSeparable_residueField_iff.mpr (inferInstanceAs
        (Algebra.IsSeparable (ResidueField R) (ResidueField R')))
    have := h.2
    have : Algebra.IsSeparable (maximalIdeal R).ResidueField Q'.ResidueField :=
      Algebra.IsSeparable.trans (maximalIdeal R).ResidueField (maximalIdeal R').ResidueField _
    exact Algebra.isSeparable_tower_bot_of_isSeparable _ _ Q'.ResidueField

/-- XIII 2.0.2, converse direction: let `R → R'` be a local homomorphism of discrete valuation
rings such that `𝔪_R` generates `𝔪_{R'}` (a uniformizer goes to a uniformizer) and the residue
extension is separable. If `K' ⊗_K L` is tamely ramified over `R'`, then `L` is tamely ramified
over `R`. For a prime `Q` over `𝔪_R` of the normalization of `R` in `L`, we find a factor `F'` of
`K' ⊗_K L` and a prime of the normalization of `R'` in `F'` over `Q` and `𝔪_{R'}` (using the
transitivity of the Galois group of the Galois closure `N` of `L` on the primes over `𝔪_R`), and
compare ramification indices and residue fields (`isTamelyRamifiedAt_of_tower`). -/
theorem IsTameExtension.of_isTameAlgebra_tensorProduct
    (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    [Algebra.IsSeparable (ResidueField R) (ResidueField R')] {L : Type*} [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (h : IsTameAlgebra R' (K := K') (TensorProduct K K' L)) : IsTameExtension R (K := K) L := by
  classical
  rw [isTameExtension_iff_isTamelyRamifiedOver]
  intro Q _ hQ
  -- the Galois closure `N` of `L`, splitting field of a separable polynomial `T`
  obtain ⟨T, hTsep, hTsplit⟩ := IsGalois.is_separable_splitting_field K (galoisClosure K L)
  let ι : galoisClosure K L →ₐ[K] AlgebraicClosure K' := IsAlgClosed.lift
  have hroot (x : AlgebraicClosure K') :
      x ∈ (T.map (algebraMap K K')).rootSet (AlgebraicClosure K') ↔
        x ∈ T.rootSet (AlgebraicClosure K') := by
    rw [mem_rootSet, mem_rootSet, aeval_map_algebraMap,
      Polynomial.map_ne_zero_iff (algebraMap K K').injective]
  let M' : IntermediateField K' (AlgebraicClosure K') :=
    IntermediateField.adjoin K' ((T.map (algebraMap K K')).rootSet (AlgebraicClosure K'))
  have : (T.map (algebraMap K K')).IsSplittingField K' M' :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : IsGalois K' M' := IsGalois.of_separable_splitting_field (p := T.map (algebraMap K K'))
    hTsep.map
  have : FiniteDimensional K' M' := IsSplittingField.finiteDimensional M'
    (T.map (algebraMap K K'))
  have hιM (x : galoisClosure K L) : ι x ∈ M' := by
    have hx : ι x ∈ ι.range := ⟨x, rfl⟩
    rw [← IsSplittingField.adjoin_rootSet_eq_range (galoisClosure K L) T ι] at hx
    refine Algebra.adjoin_le (S := (M'.restrictScalars K).toSubalgebra) ?_ hx
    intro y hy
    exact IntermediateField.subset_adjoin K' _ ((hroot y).mpr hy)
  let ιM : galoisClosure K L →ₐ[K] M' :=
    { toFun x := ⟨ι x, hιM x⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' x y := Subtype.ext (map_mul ι x y)
      map_zero' := Subtype.ext (map_zero ι)
      map_add' x y := Subtype.ext (map_add ι x y)
      commutes' k := Subtype.ext (ι.commutes k) }
  -- the map of normalizations `φ : R_N → R'_{M'}`
  have hRN : (algebraMap R' (AlgebraicClosure K')).comp (algebraMap R R') =
      ι.toRingHom.comp (algebraMap R (galoisClosure K L)) := by
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [IsScalarTower.algebraMap_apply R' K' (AlgebraicClosure K'),
      ← IsScalarTower.algebraMap_apply R R' K', IsScalarTower.algebraMap_apply R K K',
      ← IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K'),
      IsScalarTower.algebraMap_apply R K (galoisClosure K L), ι.commutes]
  have hint (x : integralClosure R (galoisClosure K L)) : IsIntegral R' (ιM x) := by
    have h1 : IsIntegral R' (ι x) := by
      obtain ⟨q, hq, hqx⟩ := x.2
      refine ⟨q.map (algebraMap R R'), hq.map _, ?_⟩
      rw [eval₂_map, hRN]
      have := congrArg ι.toRingHom hqx
      rwa [hom_eval₂, map_zero] at this
    exact (isIntegral_algHom_iff (M'.val.restrictScalars R') Subtype.val_injective).mp h1
  let φ : integralClosure R (galoisClosure K L) →+* integralClosure R' M' :=
    { toFun x := ⟨ιM x, hint x⟩
      map_one' := Subtype.ext (map_one ιM)
      map_mul' x y := Subtype.ext (map_mul ιM x.1 y.1)
      map_zero' := Subtype.ext (map_zero ιM)
      map_add' x y := Subtype.ext (map_add ιM x.1 y.1) }
  have hφR (r : R) : φ (algebraMap R _ r) = algebraMap R' _ (algebraMap R R' r) :=
    Subtype.ext (Subtype.ext (RingHom.congr_fun hRN r).symm)
  -- a prime `P'₀` of `R'_{M'}` over `𝔪_{R'}`, and its trace `P₀` on `R_N`
  have : Algebra.IsIntegral R' (integralClosure R' M') := inferInstance
  have : FaithfulSMul R' (integralClosure R' M') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (by
      refine Function.Injective.of_comp (f := ((integralClosure R' M').val : _ → M')) ?_
      have : ((integralClosure R' M').val : integralClosure R' M' → M') ∘
          algebraMap R' (integralClosure R' M') = algebraMap K' M' ∘ algebraMap R' K' := by
        ext r
        simp [IsScalarTower.algebraMap_apply R' K' M']
      rw [this]
      exact (algebraMap K' M').injective.comp (IsFractionRing.injective R' K'))
  obtain ⟨P'₀, _, hP'₀⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
    (S := integralClosure R' M') (maximalIdeal R')
  have : (P'₀.comap φ).IsPrime := Ideal.comap_isPrime _ _
  have : (P'₀.comap φ).LiesOver (maximalIdeal R) := ⟨by
    ext r
    change r ∈ maximalIdeal R ↔ φ (algebraMap R _ r) ∈ P'₀
    rw [hφR, ← Ideal.mem_comap, ← Ideal.under_def, ← Ideal.over_def P'₀ (maximalIdeal R'),
      IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      mem_nonunits_iff, isUnit_map_iff]⟩
  -- a prime `P` of `R_N` over `Q`, conjugate to `P₀`
  let := integralClosure.algebraOfTower R L (galoisClosure K L)
  have : Algebra.IsIntegral (integralClosure R L) (integralClosure R (galoisClosure K L)) :=
    ⟨fun x ↦ (Algebra.IsIntegral.isIntegral (R := R) x).tower_top⟩
  obtain ⟨P, -, _, hPQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := integralClosure R
    (galoisClosure K L)) Q ⊥ (by
      rw [Ideal.comap_bot_of_injective _ (integralClosure.algebraMap_algebraOfTower_injective R L
        (galoisClosure K L))]
      exact bot_le)
  have : P.LiesOver Q := ⟨hPQ.symm⟩
  have : P.LiesOver (maximalIdeal R) := Ideal.LiesOver.trans P Q (maximalIdeal R)
  have := integralClosure.isGaloisGroup R K (galoisClosure K L)
  obtain ⟨τ, hτ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (maximalIdeal R) P (P'₀.comap φ)
    Gal(galoisClosure K L/K)
  -- the embedding `λ = ιM ∘ τ` of `L` into `M'` and the factor `F' = K'(λ L)` of `K' ⊗_K L`
  let lam : L →ₐ[K] M' :=
    ιM.comp ((τ : galoisClosure K L ≃ₐ[K] galoisClosure K L).toAlgHom.comp
      (IsScalarTower.toAlgHom K L (galoisClosure K L)))
  let F' : IntermediateField K' M' := IntermediateField.adjoin K' (Set.range lam)
  let lam' : L →ₐ[K] F' :=
    { toFun l := ⟨lam l, IntermediateField.subset_adjoin K' _ ⟨l, rfl⟩⟩
      map_one' := Subtype.ext (map_one lam)
      map_mul' x y := Subtype.ext (map_mul lam x y)
      map_zero' := Subtype.ext (map_zero lam)
      map_add' x y := Subtype.ext (map_add lam x y)
      commutes' k := Subtype.ext (lam.commutes k) }
  let Λ : TensorProduct K K' L →ₐ[K'] F' :=
    Algebra.TensorProduct.lift (Algebra.ofId K' F') lam' fun _ _ ↦ Commute.all _ _
  have hΛ : Function.Surjective Λ := by
    have key : ∀ y ∈ Algebra.adjoin K' (Set.range lam), ∃ a, (Λ a : M') = y := by
      intro y hy
      induction hy using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        exact ⟨1 ⊗ₜ l, by simp [Λ, lam']⟩
      | algebraMap c => exact ⟨c ⊗ₜ 1, by simp [Λ]⟩
      | add x y _ _ ihx ihy =>
        obtain ⟨a, ha⟩ := ihx
        obtain ⟨b, hb⟩ := ihy
        exact ⟨a + b, by rw [map_add, IntermediateField.coe_add, ha, hb]⟩
      | mul x y _ _ ihx ihy =>
        obtain ⟨a, ha⟩ := ihx
        obtain ⟨b, hb⟩ := ihy
        exact ⟨a * b, by rw [map_mul, IntermediateField.coe_mul, ha, hb]⟩
    rintro ⟨y, hy⟩
    have hy' : y ∈ F'.toSubalgebra := hy
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic fun x _ ↦
      (Algebra.IsAlgebraic.isAlgebraic (R := K') x)] at hy'
    obtain ⟨a, ha⟩ := key y hy'
    exact ⟨a, Subtype.ext ha⟩
  -- `F'` is a factor of `K' ⊗_K L`, hence tamely ramified over `R'`
  have hmax : (RingHom.ker Λ).IsMaximal := RingHom.ker_isMaximal_of_surjective Λ hΛ
  let := Ideal.Quotient.field (RingHom.ker Λ)
  have hq := h (RingHom.ker Λ) hmax
  let e : (TensorProduct K K' L ⧸ RingHom.ker Λ) ≃ₐ[K'] F' :=
    Ideal.quotientKerAlgEquivOfSurjective hΛ
  have : Algebra.IsSeparable K' F' := Algebra.isSeparable_tower_bot_of_isSeparable K' F' M'
  have : FiniteDimensional K' (TensorProduct K K' L ⧸ RingHom.ker Λ) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  have : Algebra.IsSeparable K' (TensorProduct K K' L ⧸ RingHom.ker Λ) :=
    Algebra.IsSeparable.of_algHom K' _ e.toAlgHom
  have hF' : IsTameExtension R' (K := K') F' := IsTameExtension.of_algHom R' e.symm.toAlgHom hq
  -- the prime `Q'` of `W = R'_{F'}` under `P'₀`
  have : IsScalarTower R' F' M' := .of_algebraMap_eq fun _ ↦ rfl
  let := integralClosure.algebraOfTower R' F' M'
  let Q' := P'₀.comap (algebraMap (integralClosure R' F') (integralClosure R' M'))
  have : Q'.IsPrime := Ideal.comap_isPrime _ _
  have : Q'.LiesOver (maximalIdeal R') := ⟨by
    rw [Ideal.over_def P'₀ (maximalIdeal R')]
    change Ideal.comap _ P'₀ = Ideal.comap _ (Ideal.comap _ P'₀)
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]⟩
  have htame' : IsTamelyRamifiedAt R' Q' :=
    (isTameExtension_iff_isTamelyRamifiedOver R' F').mp hF' Q' inferInstance
  -- `W` as an algebra over `S = R_L`
  have hint' (x : integralClosure R L) : IsIntegral R' (lam' x) :=
    (isIntegral_algHom_iff (F'.val.restrictScalars R') Subtype.val_injective).mp
      (hint (τ • algebraMap (integralClosure R L) (integralClosure R (galoisClosure K L)) x))
  let σS : integralClosure R L →+* integralClosure R' F' :=
    { toFun x := ⟨lam' x, hint' x⟩
      map_one' := Subtype.ext (map_one lam')
      map_mul' x y := Subtype.ext (map_mul lam' x.1 y.1)
      map_zero' := Subtype.ext (map_zero lam')
      map_add' x y := Subtype.ext (map_add lam' x.1 y.1) }
  let : Algebra (integralClosure R L) (integralClosure R' F') := σS.toAlgebra
  let : Algebra R (integralClosure R' F') :=
    ((algebraMap R' (integralClosure R' F')).comp (algebraMap R R')).toAlgebra
  have : IsScalarTower R R' (integralClosure R' F') := .of_algebraMap_eq fun _ ↦ rfl
  have hRA (r : R) : algebraMap R' (AlgebraicClosure K') (algebraMap R R' r) =
      algebraMap K (AlgebraicClosure K') (algebraMap R K r) := by
    rw [IsScalarTower.algebraMap_apply R' K' (AlgebraicClosure K'),
      ← IsScalarTower.algebraMap_apply R R' K', IsScalarTower.algebraMap_apply R K K',
      ← IsScalarTower.algebraMap_apply K K' (AlgebraicClosure K')]
  have : IsScalarTower R (integralClosure R L) (integralClosure R' F') :=
    .of_algebraMap_eq fun r ↦ Subtype.ext (Subtype.ext (by
      have e1 : ((algebraMap R (integralClosure R' F') r : F') : M') =
          algebraMap R' M' (algebraMap R R' r) := rfl
      have e2 : ((algebraMap (integralClosure R L) (integralClosure R' F')
          (algebraMap R (integralClosure R L) r) : F') : M') = lam (algebraMap R L r) := rfl
      rw [e1, e2, IsScalarTower.algebraMap_apply R K L, lam.commutes]
      exact Subtype.ext (hRA r)))
  -- flatness
  have : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain' R K L
  have hσinj : Function.Injective σS := by
    intro x y hxy
    exact Subtype.ext (lam'.injective (congrArg Subtype.val hxy))
  have : Module.IsTorsionFree (integralClosure R L) (integralClosure R' F') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hσinj
  have : Module.IsTorsionFree R' (integralClosure R' F') :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      refine Function.Injective.of_comp (f := ((integralClosure R' F').val : _ → F')) ?_
      have : ((integralClosure R' F').val : integralClosure R' F' → F') ∘
          algebraMap R' (integralClosure R' F') = algebraMap K' F' ∘ algebraMap R' K' := by
        ext r
        simp [IsScalarTower.algebraMap_apply R' K' F']
      rw [this]
      exact (algebraMap K' F').injective.comp (IsFractionRing.injective R' K'))
  -- `Q'` lies over `Q`
  have : Q'.LiesOver Q := ⟨by
    ext x
    rw [← hPQ, Ideal.mem_comap, Ideal.mem_comap]
    change _ ↔ algebraMap _ (integralClosure R' M') (σS x) ∈ P'₀
    rw [← Ideal.smul_mem_pointwise_smul_iff (a := τ), hτ, Ideal.mem_comap]
    rfl⟩
  exact isTamelyRamifiedAt_of_tower hm Q Q' htame'

omit [IsFractionRing R K] in
/-- XIII 2.0.2 (and 2.0.3), for étale algebras: tame ramification is preserved by a local
homomorphism of discrete valuation rings `R → R'`: if `L` is tamely ramified over `R`, then
`K' ⊗_K L` is tamely ramified over `R'`. -/
theorem IsTameAlgebra.baseChange {L : Type*} [CommRing L] [Algebra K L] [Algebra.Etale K L]
    [Algebra R L] [IsScalarTower R K L] (hL : IsTameAlgebra R (K := K) L) :
    IsTameAlgebra R' (K := K') (TensorProduct K K' L) := by
  intro n hn
  let := Ideal.Quotient.field n
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  let g := (Ideal.Quotient.mkₐ K n).comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] TensorProduct K K' L)
  have h₁ := isMaximal_ker_of_finite K g
  let := Ideal.Quotient.field (RingHom.ker g)
  refine IsTameExtension.of_adjoin_range_eq_top (Ideal.kerLiftAlg g) ?_ (hL _ h₁)
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | tmul k l =>
    have : (k ⊗ₜ[K] l : TensorProduct K K' L) =
        algebraMap K' _ k * Algebra.TensorProduct.includeRight l := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this, map_mul]
    refine mul_mem (IntermediateField.algebraMap_mem _ k) (IntermediateField.subset_adjoin _ _
      ⟨Ideal.Quotient.mk _ l, ?_⟩)
    rw [Ideal.kerLiftAlg_mk]
    rfl
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- A quotient of a tamely ramified étale algebra is tamely ramified. -/
theorem IsTameAlgebra.of_surjective {E E₂ : Type*} [CommRing E] [CommRing E₂] [Algebra K E]
    [Algebra K E₂] [Algebra.Etale K E] [Algebra R E] [IsScalarTower R K E] [Algebra R E₂]
    [IsScalarTower R K E₂] (φ : E →ₐ[K] E₂) (hφ : Function.Surjective φ)
    (h : IsTameAlgebra R (K := K) E) : IsTameAlgebra R (K := K) E₂ := by
  intro n hn
  let := Ideal.Quotient.field n
  have : Module.Finite K E := Algebra.FormallyUnramified.finite_of_free K E
  let g := (Ideal.Quotient.mkₐ K n).comp φ
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have h₁ := isMaximal_ker_of_finite K g
  let := Ideal.Quotient.field (RingHom.ker g)
  exact IsTameExtension.of_algHom R (Ideal.quotientKerAlgEquivOfSurjective hg).symm.toAlgHom
    (h _ h₁)

/-- XIII 2.0.2, algebra level, converse direction: if `𝔪_R` generates `𝔪_{R'}` and the residue
extension is separable, `L` is tamely ramified over `R` as soon as `K' ⊗_K L` is tamely ramified
over `R'`. -/
theorem IsTameAlgebra.of_baseChange (hm : (maximalIdeal R).map (algebraMap R R') = maximalIdeal R')
    [Algebra.IsSeparable (ResidueField R) (ResidueField R')] {L : Type*} [CommRing L]
    [Algebra K L] [Algebra.Etale K L] [Algebra R L] [IsScalarTower R K L]
    (h : IsTameAlgebra R' (K := K') (TensorProduct K K' L)) : IsTameAlgebra R (K := K) L := by
  intro m hm'
  let := Ideal.Quotient.field m
  have : Module.Finite K L := Algebra.FormallyUnramified.finite_of_free K L
  let φ : TensorProduct K K' L →ₐ[K'] TensorProduct K K' (L ⧸ m) :=
    Algebra.TensorProduct.map (AlgHom.id K' K') (Ideal.Quotient.mkₐ K m)
  have hφ : Function.Surjective φ :=
    Algebra.TensorProduct.map_surjective _ _ Function.surjective_id Ideal.Quotient.mk_surjective
  have h' : IsTameAlgebra R' (K := K') (TensorProduct K K' (L ⧸ m)) :=
    IsTameAlgebra.of_surjective (R := R') φ hφ h
  exact IsTameExtension.of_isTameAlgebra_tensorProduct hm h'

end BaseChange

end SGA.SGA1.ExposeXIII
