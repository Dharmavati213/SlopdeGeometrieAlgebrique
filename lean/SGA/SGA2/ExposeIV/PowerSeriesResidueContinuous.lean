/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.PowerSeriesCoordinateIdeals
import SGA.SGA2.ExposeIV.MacaulayContinuousDual

/-!
# Finite residues as actual continuous functionals

The perfect finite residue pairing sends a coordinate-power quotient class
`x` to the continuous functional `a ↦ residue(xa)`. This is linear for the
original power-series-ring action on both sides. Each stage map is injective,
and every actual continuous functional is obtained at some stage.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (K : Type u) [Field K]

/-- The actual maximal-adic continuous dual of a power series ring. -/
abbrev powerSeriesContinuousDual (d : ℕ) : ModuleCat.{u} (MvPowerSeries (Fin d) K) :=
  ModuleCat.of (MvPowerSeries (Fin d) K)
    (adicContinuousDual (K := K) (maximalIdeal (MvPowerSeries (Fin d) K)))

/-- The actual product-residue pairing defines a continuous functional,
linearly for the original source-induced power-series-ring action. -/
def powerSeriesResidueToContinuous (d r : ℕ) :
    ModuleCat.of (MvPowerSeries (Fin d) K)
      (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) ⟶
    powerSeriesContinuousDual K d := by
  letI : TopologicalSpace (MvPowerSeries (Fin d) K) :=
    (maximalIdeal (MvPowerSeries (Fin d) K)).adicTopology
  letI : TopologicalSpace K := ⊥
  letI : DiscreteTopology K := discreteTopology_bot K
  refine ModuleCat.ofHom
    { toFun := fun x =>
        { toLinearMap := (powerSeriesPowerQuotientResiduePairing K d r x).comp
            ((powerSeriesCoordinatePowerIdeal K d (r + 1)).mkQ.restrictScalars K)
          cont := ?_ }
      map_add' := ?_
      map_smul' := ?_ }
  · apply (continuous_linearForm_adic_iff _ _).mpr
    obtain ⟨k, hk⟩ := powerSeries_exists_maximalIdeal_pow_le_coordinatePowerIdeal K d (r + 1)
    refine ⟨k, fun a ha => ?_⟩
    change powerSeriesPowerQuotientResiduePairing K d r x
      (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hk ha), map_zero]
  · intro x y
    apply ContinuousLinearMap.ext
    intro a
    change powerSeriesPowerQuotientResidue K d r
        ((x + y) * Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) a) = _
    rw [add_mul, map_add]
    rfl
  · intro a x
    apply ContinuousLinearMap.ext
    intro b
    change powerSeriesPowerQuotientResidue K d r
        ((Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) a * x) *
          Ideal.Quotient.mk _ b) =
      powerSeriesPowerQuotientResidue K d r (x * Ideal.Quotient.mk _ (b * a))
    rw [(Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1))).map_mul]
    congr 1
    ring

@[simp]
theorem powerSeriesResidueToContinuous_apply (d r : ℕ)
    (x : MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1))
    (a : MvPowerSeries (Fin d) K) :
    powerSeriesResidueToContinuous K d r x a =
      powerSeriesPowerQuotientResidue K d r
        (x * Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) a) := rfl

/-- The explicit residue functional on an original representative. -/
@[simp]
theorem powerSeriesResidueToContinuous_mk (d r : ℕ) (f a : MvPowerSeries (Fin d) K) :
    powerSeriesResidueToContinuous K d r
      (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) f) a =
      MvPowerSeries.coeff (powerSeriesResidueExponent d r) (f * a) := by
  rw [powerSeriesResidueToContinuous_apply, ← map_mul, powerSeriesPowerQuotientResidue_mk]

/-- No quotient class is lost by the actual continuous-dual stage map. -/
theorem powerSeriesResidueToContinuous_injective (d r : ℕ) :
    Function.Injective (powerSeriesResidueToContinuous K d r) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply powerSeriesPowerQuotientResidue_nondegenerate K d r x
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact congrArg (fun φ : powerSeriesContinuousDual K d => φ a) hx

/-- Every genuine continuous functional is the explicit residue pairing with
a class in an actual coordinate-power quotient. -/
theorem powerSeriesContinuousDual_exists_residue_stage (d : ℕ)
    (φ : powerSeriesContinuousDual K d) :
    ∃ r : ℕ, ∃ x : MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1),
      powerSeriesResidueToContinuous K d r x = φ := by
  let : TopologicalSpace (MvPowerSeries (Fin d) K) :=
    (maximalIdeal (MvPowerSeries (Fin d) K)).adicTopology
  let : TopologicalSpace K := ⊥
  obtain ⟨k, hk⟩ := (continuous_linearForm_adic_iff _ φ.toLinearMap).mp φ.cont
  have hI : powerSeriesCoordinatePowerIdeal K d (k + 1) ≤
      maximalIdeal (MvPowerSeries (Fin d) K) ^ k :=
    (powerSeriesCoordinatePowerIdeal_le_maximalIdeal_pow K d (k + 1)).trans
      (Ideal.pow_le_pow_right (Nat.le_succ k))
  let ψ : Module.Dual K
      (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (k + 1)) :=
    ((powerSeriesCoordinatePowerIdeal K d (k + 1)).restrictScalars K).liftQ
      φ.toLinearMap (fun a ha => hk a (hI ha))
  obtain ⟨x, hx⟩ := (powerSeriesPowerQuotientResidueEquiv K d k).surjective ψ
  refine ⟨k, x, ?_⟩
  apply ContinuousLinearMap.ext
  intro a
  exact DFunLike.congr_fun hx
    (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (k + 1)) a)

end SGA.SGA2.ExposeIV
