/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.ModuleBidualSimpleTests
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# Hom duality on finite modules with Artinian support

Under the hypotheses of SGA 2, IV.3.1, the original finite supported modules
have finite length: an ideal power annihilates each one, and its quotient
ring is Artinian. For arbitrary injective `H`, the actual residue-field Hom
tests therefore imply canonical biduality, finite Hom values, and preservation
of length. No finiteness of `H` or duality hypothesis on general modules is used.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Every power quotient is Artinian if the original quotient is Artinian.
This uses the unchanged prime support of positive powers, not an assumed
finite-length property of supported modules. -/
theorem isArtinianRing_quotient_pow (J : Ideal R) [IsArtinianRing (R ⧸ J)] (n : ℕ) :
    IsArtinianRing (R ⧸ J ^ n) := by
  by_cases hn : n = 0
  · subst n
    have : Subsingleton (R ⧸ J ^ 0) := by
      rw [pow_zero, Ideal.one_eq_top]
      infer_instance
    exact isArtinian_of_finite
  · apply isArtinianRing_iff_krullDimLE_zero.mpr
    apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
    have hmin : (J ^ n).minimalPrimes = J.minimalPrimes := by
      rw [← Ideal.radical_minimalPrimes, Ideal.radical_pow J hn, Ideal.radical_minimalPrimes]
    rw [hmin]
    exact Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mp
      (inferInstanceAs (Ring.KrullDimLE 0 (R ⧸ J)))

/-- A finite module with the original support in `V(J)` has finite length
when `R/J` is Artinian. The quotient-ring action is derived from its actual
annihilator, and the original `R`-module structure is preserved. -/
theorem isFiniteLength_of_finite_of_support (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M) :
    IsFiniteLength R M := by
  obtain ⟨n, hn⟩ := (support_subset_zeroLocus_iff_exists_pow_le_annihilator J M).mp hSupp
  have hT : Module.IsTorsionBySet R M (J ^ n : Ideal R) :=
    (Module.isTorsionBySet_iff_subset_annihilator R M).mpr hn
  let := hT.module
  have : Module.Finite (R ⧸ J ^ n) M :=
    Module.Finite.of_surjective hT.semilinearMap Function.surjective_id
  have : IsArtinianRing (R ⧸ J ^ n) := isArtinianRing_quotient_pow J n
  have hA : IsArtinian R M :=
    (hT.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hA⟩

/-- The actual objects of the supported finite category have finite length. -/
theorem supportedFinite_isFiniteLength (J : Ideal R) [IsArtinianRing (R ⧸ J)]
    (M : SupportedFGModuleCat J) : IsFiniteLength R M.obj :=
  isFiniteLength_of_finite_of_support J M.obj.obj M.property

/-- The residue-field tests of IV.3.1, stated for the original linear Hom
functor and the maximal ideals containing the given ideal. -/
def moduleHomDualResidueTests (J : Ideal R) (H : ModuleCat.{u} R) : Prop :=
  ∀ m : Ideal R, m.IsMaximal → J ≤ m →
    Nonempty ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m))) ≅
      ModuleCat.of R (R ⧸ m))

variable (J : Ideal R) [IsArtinianRing (R ⧸ J)]
variable (H : ModuleCat.{u} R) [Injective H] (hres : moduleHomDualResidueTests J H)

include hres

/-- IV.3.1(iii) gives the actual canonical bidual isomorphism on every
finite module with the original support. -/
theorem moduleBidualEvaluation_isIso_of_artinian_support
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M) :
    IsIso (moduleBidualEvaluation H M) :=
  moduleBidualEvaluation_isIso_finiteLength_of_residueTests J H hres M
    (isFiniteLength_of_finite_of_support J M hSupp) hSupp

/-- The actual Hom values are finite under IV.3.1(iii). -/
theorem moduleHomDual_finite_of_artinian_support
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M) :
    Module.Finite R ((moduleHomDual H).obj (op M)) :=
  moduleHomDual_finite_finiteLength_of_residueTests J H hres M
    (isFiniteLength_of_finite_of_support J M hSupp) hSupp

/-- IV.3.1(iii) gives length preservation for the original Hom values. -/
theorem moduleHomDual_length_of_artinian_support
    (M : ModuleCat.{u} R) [Module.Finite R M] (hSupp : supportedModuleProperty J M) :
    Module.length R ((moduleHomDual H).obj (op M)) = Module.length R M :=
  moduleHomDual_length_finiteLength_of_residueTests J H hres M
    (isFiniteLength_of_finite_of_support J M hSupp) hSupp

end SGA.SGA2.ExposeIV
