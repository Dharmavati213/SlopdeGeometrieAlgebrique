/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.PowerSeriesResidueColimit
import SGA.SGA2.ExposeIV.AdicContinuousDualEvaluation

/-!
# The explicit power-series local-cohomology/Macaulay comparison

For the actual power series ring, the original top local cohomology is
identified with its continuous dual and hence with its actual Macaulay
quotient-dual colimit. At every original Koszul quotient stage the map is
`f ↦ (a ↦ coeff_(r,…,r)(fa))`. The comparison is the constructed residue
map, not an abstract dualizing-module uniqueness isomorphism.

This does not construct a coefficient field or a Cohen presentation for an
arbitrary complete regular local ring, nor completed differentials or
parameter-independence of the intrinsic differential residue.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

/-- The original maximal-ideal local cohomology in the number of variables. -/
abbrev powerSeriesTopLocalCohomology (d : ℕ) : ModuleCat.{u} (MvPowerSeries (Fin d) K) :=
  (_root_.localCohomology (maximalIdeal (MvPowerSeries (Fin d) K)) d).obj
    (ModuleCat.of (MvPowerSeries (Fin d) K) (MvPowerSeries (Fin d) K))

/-- The original coordinate quotient colimit computes actual maximal-ideal
local cohomology, using the proved coordinate ideal and degree equalities. -/
def powerSeriesKoszulColimitIsoLocalCohomology (d : ℕ) :
    colimit (koszulTopQuotientDiagram (powerSeriesCoordinates K d)
      (ModuleCat.of (MvPowerSeries (Fin d) K) (MvPowerSeries (Fin d) K))) ≅
      powerSeriesTopLocalCohomology K d :=
  koszulTopQuotientColimitIsoLocalCohomology (powerSeriesCoordinates K d) _ ≪≫
    eqToIso (by rw [powerSeriesCoordinates_ideal, powerSeriesCoordinates_length])

/-- Omitting the zeroth stage is justified by the proved finality of the
positive-power index, including in the zero-variable case. -/
def powerSeriesPositiveColimitIsoLocalCohomology (d : ℕ) :
    colimit (powerSeriesPositiveQuotientDiagram K d) ≅ powerSeriesTopLocalCohomology K d :=
  Functor.Final.colimitIso positivePowerIndex _ ≪≫ powerSeriesKoszulColimitIsoLocalCohomology K d

/-- The original positive coordinate quotient stage map, through the actual
Koszul quotient/local-cohomology comparison. -/
def powerSeriesLocalCohomologyStageι (d r : ℕ) :
    ModuleCat.of (MvPowerSeries (Fin d) K)
      (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) ⟶
      powerSeriesTopLocalCohomology K d :=
  (powerSeriesKoszulQuotientIso K d (r + 1)).inv ≫
    colimit.ι (koszulTopQuotientDiagram (powerSeriesCoordinates K d)
      (ModuleCat.of (MvPowerSeries (Fin d) K) (MvPowerSeries (Fin d) K))) (r + 1) ≫
    (powerSeriesKoszulColimitIsoLocalCohomology K d).hom

/-- The cofinality comparison preserves the original quotient-stage maps. -/
@[reassoc]
theorem powerSeriesLocalCohomologyStageι_eq (d r : ℕ) :
    powerSeriesLocalCohomologyStageι K d r =
      (powerSeriesKoszulQuotientIso K d (r + 1)).inv ≫
        colimit.ι (powerSeriesPositiveQuotientDiagram K d) r ≫
        (powerSeriesPositiveColimitIsoLocalCohomology K d).hom := by
  dsimp only [powerSeriesPositiveColimitIsoLocalCohomology,
    powerSeriesPositiveQuotientDiagram, Iso.trans_hom]
  erw [Functor.Final.ι_colimitIso_hom_assoc]
  rfl

/-- **IV.5.5, explicit power-series comparison:** actual top local cohomology
is the continuous dual by the glued residue pairing. -/
def powerSeriesLocalCohomologyResidueConstruction (d : ℕ) :
    powerSeriesTopLocalCohomology K d ≅ powerSeriesContinuousDual K d :=
  (powerSeriesPositiveColimitIsoLocalCohomology K d).symm ≪≫ powerSeriesResidueColimitIso K d

-- Seal the checked construction together with its original-stage specification.
-- This avoids repeatedly unfolding the enormous chosen local-cohomology models
-- when checking pointwise formulas. The value and the specification are both
-- kernel checked; this introduces no mathematical assumption.
private opaque powerSeriesLocalCohomologyResidueData (d : ℕ) :
    {e : powerSeriesTopLocalCohomology K d ≅ powerSeriesContinuousDual K d //
      e = powerSeriesLocalCohomologyResidueConstruction K d ∧
        ∀ r, powerSeriesLocalCohomologyStageι K d r ≫ e.hom =
          powerSeriesResidueToContinuous K d r} :=
  ⟨powerSeriesLocalCohomologyResidueConstruction K d, rfl, fun r => by
    simp [powerSeriesLocalCohomologyStageι_eq, powerSeriesLocalCohomologyResidueConstruction,
      powerSeriesResidueStage]⟩

/-- The constructed residue isomorphism, retaining its proved original-stage
specification while hiding costly internal colimit reductions. -/
def powerSeriesLocalCohomologyIsoContinuousDual (d : ℕ) :
    powerSeriesTopLocalCohomology K d ≅ powerSeriesContinuousDual K d :=
  (powerSeriesLocalCohomologyResidueData K d).val

/-- The checked presentation is exactly the explicit original colimit
construction, not a separately chosen isomorphism with the same objects. -/
theorem powerSeriesLocalCohomologyIsoContinuousDual_eq_construction (d : ℕ) :
    powerSeriesLocalCohomologyIsoContinuousDual K d =
      powerSeriesLocalCohomologyResidueConstruction K d :=
  (powerSeriesLocalCohomologyResidueData K d).property.1

/-- The explicit comparison is exactly the finite residue pairing on every
original coordinate quotient stage. -/
@[reassoc (attr := simp)]
theorem powerSeriesLocalCohomologyIsoContinuousDual_stage (d r : ℕ) :
    powerSeriesLocalCohomologyStageι K d r ≫
      (powerSeriesLocalCohomologyIsoContinuousDual K d).hom =
      powerSeriesResidueToContinuous K d r :=
  (powerSeriesLocalCohomologyResidueData K d).property.2 r

/-- On original representatives, the continuous functional is literally
the top coefficient of the product. -/
theorem powerSeriesLocalCohomologyIsoContinuousDual_stage_apply (d r : ℕ)
    (f a : MvPowerSeries (Fin d) K) :
    (powerSeriesLocalCohomologyIsoContinuousDual K d).hom
      (powerSeriesLocalCohomologyStageι K d r
        (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) f)) a =
      MvPowerSeries.coeff (powerSeriesResidueExponent d r) (f * a) := by
  change (powerSeriesLocalCohomologyStageι K d r ≫
    (powerSeriesLocalCohomologyIsoContinuousDual K d).hom) _ a = _
  rw [powerSeriesLocalCohomologyIsoContinuousDual_stage]
  exact powerSeriesResidueToContinuous_mk K d r f a

/-- The explicit isomorphism with Macaulay's original quotient-dual colimit,
obtained from the constructed residue map and canonical continuous duality. -/
def powerSeriesLocalCohomologyIsoMacaulay (d : ℕ) :
    powerSeriesTopLocalCohomology K d ≅ macaulayModule (K := K) (A := MvPowerSeries (Fin d) K) :=
  powerSeriesLocalCohomologyIsoContinuousDual K d ≪≫ macaulayModuleIsoContinuousDual.symm

@[reassoc (attr := simp)]
theorem powerSeriesLocalCohomologyIsoMacaulay_continuous (d : ℕ) :
    (powerSeriesLocalCohomologyIsoMacaulay K d).hom ≫ macaulayModuleToContinuous =
      (powerSeriesLocalCohomologyIsoContinuousDual K d).hom := by
  simp [powerSeriesLocalCohomologyIsoMacaulay, ← macaulayModuleIsoContinuousDual_hom]

/-- The glued residue form, genuinely coefficient-field linear on original
local cohomology with its scalar-restricted module structure. -/
def powerSeriesLocalCohomologyResidue (d : ℕ) :
    (ModuleCat.restrictScalars (algebraMap K (MvPowerSeries (Fin d) K))).obj
      (powerSeriesTopLocalCohomology K d) →ₗ[K] K :=
  ((ModuleCat.restrictScalars (algebraMap K (MvPowerSeries (Fin d) K))).map
    (powerSeriesLocalCohomologyIsoContinuousDual K d).hom ≫
      adicContinuousDualEvaluation (maximalIdeal (MvPowerSeries (Fin d) K))).hom

/-- The source's top-coefficient residue formula on every positive stage. -/
@[simp]
theorem powerSeriesLocalCohomologyResidue_stage (d r : ℕ) (f : MvPowerSeries (Fin d) K) :
    powerSeriesLocalCohomologyResidue K d
      (powerSeriesLocalCohomologyStageι K d r
        (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) f)) =
      MvPowerSeries.coeff (powerSeriesResidueExponent d r) f := by
  change (powerSeriesLocalCohomologyIsoContinuousDual K d).hom
    (powerSeriesLocalCohomologyStageι K d r (Ideal.Quotient.mk _ f)) 1 = _
  simpa only [mul_one] using powerSeriesLocalCohomologyIsoContinuousDual_stage_apply K d r f 1

end SGA.SGA2.ExposeIV
