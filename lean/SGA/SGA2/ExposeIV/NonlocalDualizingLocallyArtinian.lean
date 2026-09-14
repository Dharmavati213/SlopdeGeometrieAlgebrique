/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.NonlocalDualizingFunctor
import SGA.SGA2.ExposeIV.SupportedLocallyArtinian
import SGA.SGA2.ExposeIII.AssociatedPrimes

/-!
# IV.4.2: the actual nonlocal representing coefficient is locally Artinian

Essential extensions preserve the original associated primes. Associated
primes of a semisimple module are maximal, so every finite submodule of
an essential extension of a semisimple module has finite length. Applied
to the genuinely constructed envelope of the residue-field sum, this
proves local Artinianness without a new support or finiteness hypothesis.
-/

noncomputable section

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual direct sum of residue fields is semisimple. -/
instance allResidueFieldSum_semisimple : IsSemisimpleModule R (allResidueFieldSum R) := by
  change IsSemisimpleModule R (Π₀ m : MaximalIdealIndex R, (residueFieldFamily m : Type u))
  have (m : MaximalIdealIndex R) : IsSimpleModule R (residueFieldFamily m) :=
    residueFieldFamily_simple m
  infer_instance

variable [IsNoetherianRing R]

/-- An essential embedding preserves the actual set of associated primes.
No finite-generation hypothesis on either module is used. -/
theorem EssentialModuleMap.associatedPrimes_eq {M E : ModuleCat.{u} R}
    {i : M ⟶ E} (hi : EssentialModuleMap i) :
    associatedPrimes R E = associatedPrimes R M := by
  apply Set.Subset.antisymm _ (associatedPrimes.subset_of_injective hi.1)
  intro p hp
  obtain ⟨hpPrime, x, hx0, hpx⟩ := (ExposeIII.mem_associatedPrimes_iff E).mp hp
  have hmem (a : R) : a ∈ p ↔ a • x = 0 := by
    rw [hpx, Submodule.mem_colon_singleton, Submodule.mem_bot]
  obtain ⟨r, hr, hr0⟩ := hi.2.2 x (by trivial) hx0
  obtain ⟨y, hy⟩ := hr
  have hrp : r ∉ p := fun h => hr0 ((hmem r).mp h)
  refine (ExposeIII.mem_associatedPrimes_iff M).mpr ⟨hpPrime, y, ?_, ?_⟩
  · intro hy0
    exact hr0 (hy.symm.trans (by simp [hy0]))
  · ext a
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    constructor
    · intro ha
      apply hi.1
      rw [map_smul, hy, smul_comm, (hmem a).mp ha, smul_zero, map_zero]
    · intro ha
      have har : a * r ∈ p := (hmem _).mpr (by
        rw [mul_smul, ← hy, ← map_smul, ha, map_zero])
      exact (hpPrime.mem_or_mem har).resolve_right hrp

/-- Associated primes of any semisimple module over a noetherian ring are maximal. -/
theorem isMaximal_of_associatedPrime_semisimple (M : ModuleCat.{u} R)
    [IsSemisimpleModule R M] {p : Ideal R} (hp : p ∈ associatedPrimes R M) : p.IsMaximal := by
  obtain ⟨hpPrime, f, hf⟩ := (isAssociatedPrime_iff_exists_injective_linearMap p M).mp hp
  have : p.IsPrime := hpPrime
  have : IsSemisimpleModule R (R ⧸ p) := IsSemisimpleModule.of_injective f hf
  have : IsArtinian R (R ⧸ p) := inferInstance
  have : IsArtinianRing (R ⧸ p) := isArtinian_of_tower R inferInstance
  exact Ideal.Quotient.maximal_of_isField p (IsArtinianRing.isField_of_isDomain (R ⧸ p))

/-- A finite module all of whose associated primes are maximal has finite length.
The Artinian quotient by its actual annihilator is derived from the prime criterion. -/
theorem isFiniteLength_of_associatedPrimes_maximal (M : ModuleCat.{u} R) [Module.Finite R M]
    (hM : ∀ p ∈ associatedPrimes R M, p.IsMaximal) : IsFiniteLength R M := by
  let J := Module.annihilator R M
  have : IsArtinianRing (R ⧸ J) := by
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    intro p hp
    exact hM p (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hp)
  apply isFiniteLength_of_finite_of_support J M
  change Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)
  rw [Module.support_eq_zeroLocus]

/-- Every actual finite submodule of an essential extension of a semisimple
module has finite length. The extension need not itself be finite or injective. -/
theorem EssentialModuleMap.submodule_isFiniteLength {M E : ModuleCat.{u} R}
    {i : M ⟶ E} (hi : EssentialModuleMap i) [IsSemisimpleModule R M]
    (N : Submodule R E) [Module.Finite R N] : IsFiniteLength R N := by
  apply isFiniteLength_of_associatedPrimes_maximal (ModuleCat.of R N)
  intro p hp
  have hpE := associatedPrimes.subset_of_injective N.subtype_injective hp
  rw [hi.associatedPrimes_eq] at hpE
  exact isMaximal_of_associatedPrime_semisimple M hpE

/-- Essential extensions of semisimple modules are literally locally Artinian. -/
theorem EssentialModuleMap.locallyArtinian {M E : ModuleCat.{u} R}
    {i : M ⟶ E} (hi : EssentialModuleMap i) [IsSemisimpleModule R M] :
    ModuleLocallyArtinian (R := R) E := by
  intro N hN
  have : Module.Finite R N := Module.Finite.of_fg hN
  exact (isFiniteLength_iff_isNoetherian_isArtinian.mp (hi.submodule_isFiniteLength N)).2

/-- **IV.4.2, the actual nonlocal representing module:** every finitely
generated submodule of the constructed residue-sum envelope has finite length. -/
theorem allResidueFieldEnvelope_submodule_isFiniteLength
    (N : Submodule R (allResidueFieldEnvelope R).obj) [Module.Finite R N] :
    IsFiniteLength R N := by
  have : IsSemisimpleModule R (allResidueFieldSum R) := inferInstance
  exact (allResidueFieldEnvelope R).essential.submodule_isFiniteLength N

/-- **IV.4.2:** the original constructed representing coefficient is locally
Artinian. This is a conclusion, not a convention or a supplied hypothesis. -/
theorem allResidueFieldEnvelope_locallyArtinian :
    ModuleLocallyArtinian (R := R) (allResidueFieldEnvelope R).obj := by
  have : IsSemisimpleModule R (allResidueFieldSum R) := inferInstance
  exact (allResidueFieldEnvelope R).essential.locallyArtinian

end SGA.SGA2.ExposeIV
