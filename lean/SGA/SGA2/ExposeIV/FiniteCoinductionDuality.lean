/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CoinductionHomDuality
import SGA.SGA2.ExposeIV.HomDualResidueConverse
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# IV.4.3: duality under actual finite coinduction

Restriction along a finite local algebra carries the original finite
supported modules to finite supported modules. The genuine Hom adjunction
then transports finite Hom values and canonical biduality to `Hom_A(B,I)`.
Neither an adjunction comparison nor target biduality is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

/-- Over a local ring every actual finite-length module is supported at
its closed point. This is proved through its actual simple factors. -/
theorem localFiniteLength_supported {R : Type u} [CommRing R] [IsLocalRing R]
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    supportedModuleProperty (maximalIdeal R) M := by
  apply moduleFiniteLength_induction (supportedModuleProperty (maximalIdeal R))
    (fun N hN ↦ (supportedModuleProperty (maximalIdeal R)).prop_of_isZero hN)
    ?_ (fun _ hS h₁ h₃ ↦
      (supportedModuleProperty (maximalIdeal R)).prop_X₂_of_shortExact hS h₁ h₃) M hM
  intro N hN
  obtain ⟨m, hm, ⟨e⟩⟩ :=
    (isSimpleModule_iff_quot_maximal (R := R) (M := N)).mp hN
  change Module.support R N ⊆ _
  rw [e.support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
    eq_maximalIdeal hm]

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- Restricting an actually finite module along a finite algebra is finite. -/
theorem finite_restrictScalars_of_finite [Module.Finite A B]
    (M : ModuleCat.{u} B) [Module.Finite B M] :
    Module.Finite A ((restrictScalars (algebraMap A B)).obj M) := by
  let : IsScalarTower A B ((restrictScalars (algebraMap A B)).obj M) :=
    ⟨fun a b x ↦ by
      rw [Algebra.smul_def]
      change (algebraMap A B a * b) • x = algebraMap A B a • b • x
      exact mul_smul _ _ _⟩
  have : Module.Finite B ((restrictScalars (algebraMap A B)).obj M) :=
    inferInstanceAs (Module.Finite B M)
  exact Module.Finite.trans B _

variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]

/-- The support condition is preserved by restriction when the source
ideal maps into the target ideal. -/
theorem supported_restrictScalars_of_map_le (J : Ideal A) (K : Ideal B)
    (hJK : J.map (algebraMap A B) ≤ K) (M : ModuleCat.{u} B)
    [Module.Finite B M] (hM : supportedModuleProperty K M) :
    supportedModuleProperty J ((restrictScalars (algebraMap A B)).obj M) := by
  have := finite_restrictScalars_of_finite (A := A) M
  obtain ⟨n, hn⟩ := (support_subset_zeroLocus_iff_exists_pow_le_annihilator K M).mp hM
  apply (support_subset_zeroLocus_iff_exists_pow_le_annihilator J _).mpr
  refine ⟨n, fun a ha ↦ ?_⟩
  have hp : (J ^ n).map (algebraMap A B) ≤ K ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hJK n
  have ha' := hn (hp (Ideal.mem_map_of_mem (algebraMap A B) ha))
  apply Module.mem_annihilator.mpr
  intro x
  exact Module.mem_annihilator.mp ha' x

/-- Finite Hom values transfer along the genuine Hom adjunction. -/
theorem finiteSupportedHomValues_coinduced (J : Ideal A) (K : Ideal B)
    (hJK : J.map (algebraMap A B) ≤ K) (I : ModuleCat.{u} A)
    (hfin : FiniteSupportedHomValues J I) :
    FiniteSupportedHomValues K ((coextendScalars (algebraMap A B)).obj I) := by
  intro M hM hSupp
  have := finite_restrictScalars_of_finite (A := A) M
  have := hfin ((restrictScalars (algebraMap A B)).obj M) inferInstance
    (supported_restrictScalars_of_map_le J K hJK M hSupp)
  exact coinduced_moduleHomDual_finite (algebraMap A B) I M

/-- Canonical supported biduality transfers along the genuine Hom adjunction. -/
theorem supportedModuleBiduality_coinduced (J : Ideal A) (K : Ideal B)
    (hJK : J.map (algebraMap A B) ≤ K) (I : ModuleCat.{u} A)
    (hbid : SupportedModuleBiduality J I) :
    SupportedModuleBiduality K ((coextendScalars (algebraMap A B)).obj I) := by
  intro M hM hSupp
  have := finite_restrictScalars_of_finite (A := A) M
  have := hbid ((restrictScalars (algebraMap A B)).obj M) inferInstance
    (supported_restrictScalars_of_map_le J K hJK M hSupp)
  exact coinduced_moduleBidualEvaluation_isIso (algebraMap A B) I M

variable [IsLocalRing A] [IsLocalRing B]

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- A finite algebra between local rings carries the maximal ideal into
the maximal ideal; no extra local-homomorphism assumption is needed. -/
theorem finite_algebra_map_maximalIdeal_le :
    (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B := by
  have h := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (R := A) (maximalIdeal B)
  rw [Ideal.map_le_iff_le_comap, eq_maximalIdeal h]

/-- **IV.4.3:** actual `Hom_A(B,I)` has finite Hom values and the canonical
bidual isomorphisms over `B` whenever `I` does over `A`. -/
theorem finite_local_coinduction_duality (I : ModuleCat.{u} A)
    (hfin : FiniteSupportedHomValues (maximalIdeal A) I)
    (hbid : SupportedModuleBiduality (maximalIdeal A) I) :
    FiniteSupportedHomValues (maximalIdeal B)
        ((coextendScalars (algebraMap A B)).obj I) ∧
      SupportedModuleBiduality (maximalIdeal B)
        ((coextendScalars (algebraMap A B)).obj I) :=
  ⟨finiteSupportedHomValues_coinduced _ _ finite_algebra_map_maximalIdeal_le I hfin,
    supportedModuleBiduality_coinduced _ _ finite_algebra_map_maximalIdeal_le I hbid⟩

/-- The genuine coinduced module satisfies the original residue-field tests. -/
theorem finite_local_coinduction_residueTests (I : ModuleCat.{u} A) [Injective I]
    (hbid : SupportedModuleBiduality (maximalIdeal A) I) :
    moduleHomDualResidueTests (maximalIdeal B)
      ((coextendScalars (algebraMap A B)).obj I) := by
  have := coinduced_injective (algebraMap A B) I
  have hB := supportedModuleBiduality_coinduced (maximalIdeal A) (maximalIdeal B)
    finite_algebra_map_maximalIdeal_le I hbid
  intro m hm hle
  have hSupp : supportedModuleProperty (maximalIdeal B) (ModuleCat.of B (B ⧸ m)) := by
    change Module.support B (B ⧸ m) ⊆ _
    rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
    exact PrimeSpectrum.zeroLocus_anti_mono hle
  have := hB (ModuleCat.of B (B ⧸ m)) inferInstance hSupp
  exact moduleHomDual_residue_iso_of_bidually_reflexive _ m hm

/-- **IV.4.3**, directly on every actual finite-length `B`-module:
finite Hom values, canonical biduality, and preservation of `B`-length. -/
theorem finite_local_coinduction_finiteLength (I : ModuleCat.{u} A) [Injective I]
    (hbid : SupportedModuleBiduality (maximalIdeal A) I)
    (M : ModuleCat.{u} B) (hM : IsFiniteLength B M) :
    Module.Finite B ((moduleHomDual ((coextendScalars (algebraMap A B)).obj I)).obj (op M)) ∧
      IsIso (moduleBidualEvaluation ((coextendScalars (algebraMap A B)).obj I) M) ∧
      Module.length B ((moduleHomDual ((coextendScalars (algebraMap A B)).obj I)).obj
        (op M)) = Module.length B M := by
  have := coinduced_injective (algebraMap A B) I
  have hres := finite_local_coinduction_residueTests (B := B) I hbid
  have hSupp := localFiniteLength_supported M hM
  exact ⟨moduleHomDual_finite_finiteLength_of_residueTests _ _ hres M hM hSupp,
    moduleBidualEvaluation_isIso_finiteLength_of_residueTests _ _ hres M hM hSupp,
    moduleHomDual_length_finiteLength_of_residueTests _ _ hres M hM hSupp⟩

end SGA.SGA2.ExposeIV
