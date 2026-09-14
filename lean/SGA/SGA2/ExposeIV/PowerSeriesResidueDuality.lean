/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.PowerSeriesLocalCohomologyResidue
import SGA.SGA2.ExposeIV.SupportedDualityTransport

/-!
# Residue formulas and duality for the actual power series ring

The glued coefficient-field linear residue form recovers the explicit
continuous-dual isomorphism by multiplication. Thus its product pairing
separates all original local-cohomology classes. The original top local
cohomology is supported dualizing, now via the explicit residue comparison.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

/-- The actual residue field is finite over the coefficient field, as the
actual first coordinate-power quotient. No extra finiteness is assumed. -/
instance powerSeriesResidueField_finite (d : ℕ) :
    Module.Finite K (ResidueField (MvPowerSeries (Fin d) K)) := by
  change Module.Finite K
    (MvPowerSeries (Fin d) K ⧸ maximalIdeal (MvPowerSeries (Fin d) K))
  rw [← powerSeriesCoordinatePowerIdeal_one K d]
  infer_instance

/-- The actual top local-cohomology module is supported dualizing by the
constructed residue isomorphism with the original Macaulay module. -/
theorem powerSeriesTopLocalCohomology_supportedDualizing (d : ℕ) :
    SupportedDualizingModule (powerSeriesTopLocalCohomology K d) :=
  SupportedDualizingModule.of_iso (powerSeriesLocalCohomologyIsoMacaulay K d).symm
    macaulayModule_supportedDualizing

/-- The explicit comparison is recovered from the residue form by original
power-series multiplication, with no alternate scalar action. -/
theorem powerSeriesLocalCohomologyResidue_smul (d : ℕ)
    (a : MvPowerSeries (Fin d) K) (x : powerSeriesTopLocalCohomology K d) :
    powerSeriesLocalCohomologyResidue K d (a • x) =
      (powerSeriesLocalCohomologyIsoContinuousDual K d).hom x a := by
  change (powerSeriesLocalCohomologyIsoContinuousDual K d).hom (a • x) 1 = _
  rw [map_smul]
  change (powerSeriesLocalCohomologyIsoContinuousDual K d).hom x (1 * a) = _
  rw [one_mul]

/-- The glued product-residue pairing separates every original local
cohomology class, not just each finite quotient separately. -/
theorem powerSeriesLocalCohomologyResidue_nondegenerate (d : ℕ)
    (x : powerSeriesTopLocalCohomology K d)
    (hx : ∀ a : MvPowerSeries (Fin d) K, powerSeriesLocalCohomologyResidue K d (a • x) = 0) :
    x = 0 := by
  let : TopologicalSpace (MvPowerSeries (Fin d) K) :=
    (maximalIdeal (MvPowerSeries (Fin d) K)).adicTopology
  let : TopologicalSpace K := ⊥
  apply (powerSeriesLocalCohomologyIsoContinuousDual K d).toLinearEquiv.injective
  change (powerSeriesLocalCohomologyIsoContinuousDual K d).hom x =
    (powerSeriesLocalCohomologyIsoContinuousDual K d).hom 0
  rw [map_zero]
  apply ContinuousLinearMap.ext
  intro a
  exact (powerSeriesLocalCohomologyResidue_smul K d a x).symm.trans (hx a)

/-- The literal monomial-basis formula in IV.5.5: the residue is one on
the top monomial and zero on every other bounded monomial. -/
theorem powerSeriesLocalCohomologyResidue_basis (d r : ℕ)
    (a : PowerSeriesPowerBox d (r + 1)) :
    powerSeriesLocalCohomologyResidue K d
      (powerSeriesLocalCohomologyStageι K d r (powerSeriesPowerQuotientBasis K d (r + 1) a)) =
      if powerSeriesResidueExponent d r = a.val then (1 : K) else 0 := by
  rw [powerSeriesPowerQuotientBasis_apply, powerSeriesLocalCohomologyResidue_stage,
    MvPowerSeries.coeff_monomial]

/-- The original glued residue form takes every coefficient-field value. -/
theorem powerSeriesLocalCohomologyResidue_surjective (d : ℕ) :
    Function.Surjective (powerSeriesLocalCohomologyResidue K d) := by
  have h : Function.Surjective (fun φ : powerSeriesContinuousDual K d => φ 1) := by
    intro c
    refine ⟨powerSeriesResidueToContinuous K d 0
      (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d 1)
        (MvPowerSeries.monomial (powerSeriesResidueExponent d 0) c)), ?_⟩
    simpa only [mul_one, MvPowerSeries.coeff_monomial_same] using
      powerSeriesResidueToContinuous_mk K d 0
        (MvPowerSeries.monomial (powerSeriesResidueExponent d 0) c) 1
  exact h.comp (powerSeriesLocalCohomologyIsoContinuousDual K d).toLinearEquiv.surjective

end SGA.SGA2.ExposeIV
