/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.PowerSeriesResiduePairing
import SGA.SGA2.ExposeII.KoszulTopQuotientColimit
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Actual coordinate ideals and residue transition formulas

The ordered coordinate list generates the actual maximal ideal. Its original
Koszul power quotients identify with the literal coordinate-power quotients.
Product multiplication shifts the top coefficient exactly as required by
the finite residue forms. All statements include zero variables.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

/-- The actual ordered coordinate list, including the empty list. -/
def powerSeriesCoordinates (d : ℕ) : List (MvPowerSeries (Fin d) K) :=
  List.ofFn MvPowerSeries.X

@[simp]
theorem powerSeriesCoordinates_length (d : ℕ) : (powerSeriesCoordinates K d).length = d :=
  List.length_ofFn

theorem powerSeriesCoordinates_powerIdeal (d r : ℕ) :
    koszulIdeal ((powerSeriesCoordinates K d).map (fun f => f ^ r)) =
      powerSeriesCoordinatePowerIdeal K d r := by
  unfold koszulIdeal powerSeriesCoordinatePowerIdeal
  congr 1
  ext f
  simp [powerSeriesCoordinates, List.mem_ofFn]

/-- The actual coordinate ideal is the maximal ideal, not an assumed
parameter ideal. -/
theorem powerSeriesCoordinatePowerIdeal_one (d : ℕ) :
    powerSeriesCoordinatePowerIdeal K d 1 = IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) := by
  rw [powerSeriesCoordinatePowerIdeal_eq_boxVanishing]
  ext f
  change (∀ a : Fin d →₀ ℕ, (∀ i, a i < 1) → MvPowerSeries.coeff a f = 0) ↔
    f ∈ nonunits (MvPowerSeries (Fin d) K)
  rw [mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  constructor
  · intro hf
    exact hf 0 (by simp)
  · intro hf a ha
    have hzero : a = 0 := by ext i; have := ha i; simpa using (by omega : a i = 0)
    simpa only [hzero, MvPowerSeries.coeff_zero_eq_constantCoeff] using hf

theorem powerSeriesCoordinates_ideal (d : ℕ) :
    koszulIdeal (powerSeriesCoordinates K d) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) := by
  simpa using (powerSeriesCoordinates_powerIdeal K d 1).trans
    (powerSeriesCoordinatePowerIdeal_one K d)

/-- Coordinate powers lie inside the same ordinary maximal-ideal power. -/
theorem powerSeriesCoordinatePowerIdeal_le_maximalIdeal_pow (d r : ℕ) :
    powerSeriesCoordinatePowerIdeal K d r ≤
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) ^ r := by
  have h := generatorPowerIdeal_le_pow
    (fun i : Fin d => (MvPowerSeries.X i : MvPowerSeries (Fin d) K)) r
  have he : Ideal.span (Set.range
      (fun i : Fin d => (MvPowerSeries.X i : MvPowerSeries (Fin d) K))) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) := by
    simpa [powerSeriesCoordinatePowerIdeal] using powerSeriesCoordinatePowerIdeal_one K d
  simpa only [he, generatorPowerIdeal, powerSeriesCoordinatePowerIdeal] using h

/-- Conversely every coordinate-power ideal contains an actual maximal-ideal
power; this is the finite-generator cofinality theorem. -/
theorem powerSeries_exists_maximalIdeal_pow_le_coordinatePowerIdeal (d r : ℕ) :
    ∃ k : ℕ, IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) ^ k ≤
      powerSeriesCoordinatePowerIdeal K d r := by
  have h := exists_pow_le_generatorPowerIdeal
    (fun i : Fin d => (MvPowerSeries.X i : MvPowerSeries (Fin d) K)) r
  have he : Ideal.span (Set.range
      (fun i : Fin d => (MvPowerSeries.X i : MvPowerSeries (Fin d) K))) =
      IsLocalRing.maximalIdeal (MvPowerSeries (Fin d) K) := by
    simpa [powerSeriesCoordinatePowerIdeal] using powerSeriesCoordinatePowerIdeal_one K d
  simpa only [he, generatorPowerIdeal, powerSeriesCoordinatePowerIdeal] using h

/-- The product of coordinate powers is literally the corresponding monomial. -/
theorem powerSeriesCoordinates_prod_pow (d s : ℕ) :
    ((powerSeriesCoordinates K d).map (fun f => f ^ s)).prod =
      MvPowerSeries.monomial (powerSeriesResidueExponent d s) (1 : K) := by
  rw [MvPowerSeries.monomial_one_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [powerSeriesCoordinates, List.map_ofFn, List.prod_ofFn]

/-- The original product transition preserves the top coefficient of a
positive coordinate-power quotient. -/
theorem powerSeriesResidue_transition_coeff (d : ℕ) {r s : ℕ} (hrs : r ≤ s)
    (f : MvPowerSeries (Fin d) K) :
    MvPowerSeries.coeff (powerSeriesResidueExponent d s)
      (((powerSeriesCoordinates K d).map (fun x => x ^ ((s + 1) - (r + 1)))).prod * f) =
      MvPowerSeries.coeff (powerSeriesResidueExponent d r) f := by
  rw [powerSeriesCoordinates_prod_pow]
  have he : powerSeriesResidueExponent d s =
      powerSeriesResidueExponent d ((s + 1) - (r + 1)) + powerSeriesResidueExponent d r := by
    ext i
    simp only [Finsupp.add_apply, powerSeriesResidueExponent_apply]
    omega
  rw [he, MvPowerSeries.coeff_add_monomial_mul, one_mul]

/-- The original Koszul coefficient quotient is the literal coordinate-power
quotient, with identity on representatives and original ring action. -/
def powerSeriesKoszulQuotientIso (d r : ℕ) :
    (koszulTopQuotientDiagram (powerSeriesCoordinates K d)
      (ModuleCat.of (MvPowerSeries (Fin d) K) (MvPowerSeries (Fin d) K))).obj r ≅
    ModuleCat.of (MvPowerSeries (Fin d) K)
      (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d r) :=
  (Submodule.quotEquivOfEq _ _ (by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, powerSeriesCoordinates_powerIdeal])).toModuleIso

@[simp]
theorem powerSeriesKoszulQuotientIso_hom_mk (d r : ℕ) (f : MvPowerSeries (Fin d) K) :
    (powerSeriesKoszulQuotientIso K d r).hom (Submodule.Quotient.mk f) =
      Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d r) f := rfl

/-- Positive powers give a cofinal subsequence of the original diagram. -/
def positivePowerIndex : ℕ ⥤ ℕ := (show Monotone (fun n : ℕ => n + 1) from
  fun _ _ h => Nat.add_le_add_right h 1).functor

instance positivePowerIndex_final : positivePowerIndex.Final :=
  (Monotone.final_functor_iff _).mpr (fun n => ⟨n, Nat.le_add_right n 1⟩)

end SGA.SGA2.ExposeIV
