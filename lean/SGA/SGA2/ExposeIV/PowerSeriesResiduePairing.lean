/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.PowerSeriesPowerQuotientBasis
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The finite coordinate-power residue pairing

On the actual quotient by `X_i^(r+1)`, extraction of the coefficient of
`∏ X_i^r` gives a bilinear product pairing. Multiplication by a complementary
monomial recovers each original coefficient, proving nondegeneracy and a
perfect pairing on this finite quotient. The global residue functional and
its compatibility with the local-cohomology colimit are separate tasks.
-/

noncomputable section
universe u

namespace SGA.SGA2.ExposeIV

variable (K : Type u) [Field K]

/-- The top exponent in the coordinate box of side length `r+1`. -/
def powerSeriesResidueExponent (d r : ℕ) : Fin d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => r)

@[simp]
theorem powerSeriesResidueExponent_apply (d r : ℕ) (i : Fin d) :
    powerSeriesResidueExponent d r i = r := rfl

/-- The actual finite-stage residue extracts the coefficient of `∏ X_i^r`. -/
def powerSeriesPowerQuotientResidue (d r : ℕ) :
    (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) →ₗ[K] K :=
  (LinearMap.proj (⟨powerSeriesResidueExponent d r, fun _ => Nat.lt_succ_self r⟩ :
      PowerSeriesPowerBox d (r + 1))).comp
    (powerSeriesPowerQuotientEquiv K d (r + 1)).toLinearMap

@[simp]
theorem powerSeriesPowerQuotientResidue_mk (d r : ℕ) (f : MvPowerSeries (Fin d) K) :
    powerSeriesPowerQuotientResidue K d r
      (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1)) f) =
        MvPowerSeries.coeff (powerSeriesResidueExponent d r) f := rfl

/-- The exponent complementary to a bounded monomial. -/
def powerSeriesResidueComplement (d r : ℕ) (a : PowerSeriesPowerBox d (r + 1)) :
    Fin d →₀ ℕ := powerSeriesResidueExponent d r - a.val

theorem powerSeriesResidueExponent_eq_add_complement (d r : ℕ)
    (a : PowerSeriesPowerBox d (r + 1)) :
    powerSeriesResidueExponent d r = a.val + powerSeriesResidueComplement d r a := by
  ext i
  have := a.property i
  simp only [powerSeriesResidueExponent_apply, Finsupp.add_apply,
    powerSeriesResidueComplement, Finsupp.tsub_apply]
  omega

/-- Multiplication by the complementary monomial extracts the original
coefficient, including in the zero-variable case. -/
theorem powerSeriesPowerQuotientResidue_mul_complement (d r : ℕ)
    (x : MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1))
    (a : PowerSeriesPowerBox d (r + 1)) :
    powerSeriesPowerQuotientResidue K d r
      (x * Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1))
        (MvPowerSeries.monomial (powerSeriesResidueComplement d r a) (1 : K))) =
      powerSeriesPowerQuotientEquiv K d (r + 1) x a := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [← map_mul, powerSeriesPowerQuotientResidue_mk,
    powerSeriesPowerQuotientEquiv_apply_mk,
    powerSeriesResidueExponent_eq_add_complement d r a,
    MvPowerSeries.coeff_add_mul_monomial, mul_one]

/-- The product residue pairing is genuinely nondegenerate: no nonzero
class is invisible to all products. -/
theorem powerSeriesPowerQuotientResidue_nondegenerate (d r : ℕ)
    (x : MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1))
    (hx : ∀ y, powerSeriesPowerQuotientResidue K d r (x * y) = 0) : x = 0 := by
  apply (powerSeriesPowerQuotientEquiv K d (r + 1)).injective
  ext a
  simpa only [map_zero, Pi.zero_apply, powerSeriesPowerQuotientResidue_mul_complement]
    using hx (Ideal.Quotient.mk (powerSeriesCoordinatePowerIdeal K d (r + 1))
      (MvPowerSeries.monomial (powerSeriesResidueComplement d r a) (1 : K)))

/-- The actual bilinear product-residue pairing on the finite quotient. -/
def powerSeriesPowerQuotientResiduePairing (d r : ℕ) :
    (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) →ₗ[K]
      Module.Dual K (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) :=
  let Q := MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)
  ((LinearMap.llcomp K Q Q K) (powerSeriesPowerQuotientResidue K d r)).comp
    (LinearMap.mul K Q)

@[simp]
theorem powerSeriesPowerQuotientResiduePairing_apply (d r : ℕ)
    (x y : MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) :
    powerSeriesPowerQuotientResiduePairing K d r x y =
      powerSeriesPowerQuotientResidue K d r (x * y) := rfl

theorem powerSeriesPowerQuotientResiduePairing_injective (d r : ℕ) :
    Function.Injective (powerSeriesPowerQuotientResiduePairing K d r) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  apply powerSeriesPowerQuotientResidue_nondegenerate K d r x
  intro y
  exact DFunLike.congr_fun hx y

/-- The finite-stage product-residue pairing is perfect on the original
coordinate-power quotient, not just on an abstract isomorphic vector space. -/
def powerSeriesPowerQuotientResidueEquiv (d r : ℕ) :
    (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) ≃ₗ[K]
      Module.Dual K (MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) :=
  LinearEquiv.ofBijective (powerSeriesPowerQuotientResiduePairing K d r)
    ⟨powerSeriesPowerQuotientResiduePairing_injective K d r,
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (by simp)).mp
          (powerSeriesPowerQuotientResiduePairing_injective K d r)⟩

@[simp]
theorem powerSeriesPowerQuotientResidueEquiv_apply (d r : ℕ)
    (x y : MvPowerSeries (Fin d) K ⧸ powerSeriesCoordinatePowerIdeal K d (r + 1)) :
    powerSeriesPowerQuotientResidueEquiv K d r x y =
      powerSeriesPowerQuotientResidue K d r (x * y) := rfl

end SGA.SGA2.ExposeIV
