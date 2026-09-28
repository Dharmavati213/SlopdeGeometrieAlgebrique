/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.ResidueSumInjectiveEnvelope
import SGA.SGA2.ExposeIV.SupportedFunctorAnnihilatorStages

/-!
# IV.4.2: existence of a nonlocal dualizing functor

The coefficient is the genuinely constructed injective envelope of the
direct sum of all residue fields. The functor is actual linear Hom into
this coefficient. Exactness and canonical natural biduality hold on the
entire original finite-length category, not on a selected support stratum.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable (R : Type u) [CommRing R]

/-- A constructed dualizing functor on all original finite-length modules.
The construction in fact does not require noetherianity of the ring. -/
def nonlocalDualizingFunctor : (FiniteLengthModuleCat R)ᵒᵖ ⥤ FiniteLengthModuleCat R :=
  finiteLengthHomDual (allResidueFieldEnvelope R).obj allResidueFieldEnvelope_residueTests

instance : (nonlocalDualizingFunctor R).Additive := by
  unfold nonlocalDualizingFunctor
  infer_instance
instance : (nonlocalDualizingFunctor R).Linear R := by
  unfold nonlocalDualizingFunctor
  infer_instance
instance : (nonlocalDualizingFunctor R).PreservesHomology := by
  unfold nonlocalDualizingFunctor
  infer_instance
instance : PreservesFiniteLimits (nonlocalDualizingFunctor R) := by
  unfold nonlocalDualizingFunctor
  infer_instance
instance : PreservesFiniteColimits (nonlocalDualizingFunctor R) := by
  unfold nonlocalDualizingFunctor
  infer_instance

/-- The actual original linear Hom maps underlie the constructed endofunctor. -/
theorem nonlocalDualizingFunctor_forget :
    nonlocalDualizingFunctor R ⋙ finiteLengthInclusion R =
      (finiteLengthInclusion R).op ⋙ moduleHomDual (allResidueFieldEnvelope R).obj := rfl

/-- **IV.4.2, canonical biduality:** the original evaluation, natural on the
whole finite-length category, is an isomorphism. -/
def nonlocalDualizingEvaluationIso :
    𝟭 (FiniteLengthModuleCat R) ≅
      (nonlocalDualizingFunctor R).rightOp ⋙ nonlocalDualizingFunctor R :=
  finiteLengthHomEvaluationIso (allResidueFieldEnvelope R).obj
    allResidueFieldEnvelope_residueTests

@[simp]
theorem nonlocalDualizingEvaluationIso_apply (M : FiniteLengthModuleCat R)
    (x : M.obj) (f : M.obj ⟶ (allResidueFieldEnvelope R).obj) :
    ModuleCat.Hom.hom (((nonlocalDualizingEvaluationIso R).hom.app M).hom x) f = f.hom x := rfl

/-- Exactness means preservation of every original short exact sequence. -/
theorem nonlocalDualizingFunctor_shortExact {S : ShortComplex (FiniteLengthModuleCat R)}
    (hS : S.ShortExact) : (S.op.map (nonlocalDualizingFunctor R)).ShortExact :=
  hS.op.map_of_exact (nonlocalDualizingFunctor R)

/-- The exact contravariant endofunctor is a genuine anti-equivalence. -/
def nonlocalDualizingAntiEquivalence : (FiniteLengthModuleCat R)ᵒᵖ ≌ FiniteLengthModuleCat R :=
  finiteLengthHomAntiEquivalence (allResidueFieldEnvelope R).obj
    allResidueFieldEnvelope_residueTests

/-- The actual maximal-ideal annihilator in the constructed representing
module is one residue-field copy. It is not merely a test on an abstract dual. -/
def nonlocalDualizingAnnihilatorIso (m : MaximalIdealIndex R) :
    ModuleCat.of R (Submodule.torsionBySet R (allResidueFieldEnvelope R).obj (m.val : Set R)) ≅
      residueFieldFamily m :=
  (quotientHomAnnihilatorIso m.val (allResidueFieldEnvelope R).obj).symm ≪≫
    (allResidueFieldEnvelope_residueTests m.val m.property bot_le).some

/-- Each actual maximal-ideal annihilator has length exactly one. -/
theorem nonlocalDualizingAnnihilator_length (m : MaximalIdealIndex R) :
    Module.length R
      (Submodule.torsionBySet R (allResidueFieldEnvelope R).obj (m.val : Set R)) = 1 := by
  rw [(nonlocalDualizingAnnihilatorIso R m).toLinearEquiv.length_eq]
  exact Module.length_eq_one R (residueFieldFamily m)

end SGA.SGA2.ExposeIV
