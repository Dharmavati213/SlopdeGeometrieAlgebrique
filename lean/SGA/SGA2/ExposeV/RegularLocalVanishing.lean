/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalDepth
import SGA.SGA2.ExposeIV.RegularLocalCohomologyDuality

/-!
# Exposé V.2: vanishing used by regular local duality

The original algebraic local cohomology vanishes above the actual dimension
for every coefficient module. This follows from the proved finite-length
projective-dimension bound for the actual maximal-ideal-power quotients,
not from an assumed global-dimension theorem. With ring coefficients it
also vanishes below the dimension, by its actual computed depth.

These are inputs to the local-duality theorem; the isomorphism of V.2.1 is
not asserted by this file.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local instance regularVanishingResidueField : Field (R ⧸ maximalIdeal R) :=
  Ideal.Quotient.field _

/-- Each original maximal-ideal-power quotient has finite length. -/
theorem regularLocal_powerQuotient_isFiniteLength (k : ℕ) :
    IsFiniteLength R (R ⧸ maximalIdeal R ^ k) := by
  apply isFiniteLength_of_finite_of_support (maximalIdeal R)
    (ModuleCat.of R (R ⧸ maximalIdeal R ^ k))
  exact (support_subset_zeroLocus_iff_exists_pow_le_annihilator (maximalIdeal R) _).mpr
    ⟨k, by rw [Ideal.annihilator_quotient]⟩

/-- The original quotient Ext vanishes above the dimension for arbitrary
coefficients, without finite generation of the coefficient module. -/
theorem regularLocal_powerModuleExt_isZero_of_gt (n : ℕ) (hdim : ringKrullDim R = n)
    (M : ModuleCat.{u} R) (i k : ℕ) (hi : n < i) :
    IsZero ((moduleExtPowerDiagram (maximalIdeal R) M i).obj k) :=
  (isZero_moduleExt_iff_subsingleton_ext
    (ModuleCat.of R (R ⧸ maximalIdeal R ^ k)) M i).mpr
      (regularLocal_ext_subsingleton_of_finiteLength_of_gt n hdim _ M
        (regularLocal_powerQuotient_isFiniteLength k) i hi)

/-- **V.2.1, upper vanishing input:** actual local cohomology vanishes
above the dimension for every original module, not only finite ones. -/
theorem regularLocal_localCohomology_isZero_of_gt (n : ℕ) (hdim : ringKrullDim R = n)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : n < i) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  apply IsZero.of_iso _ (moduleExtPowerColimitIsoLocalCohomology (maximalIdeal R) M i).symm
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro k
  exact (regularLocal_powerModuleExt_isZero_of_gt n hdim M i k hi).eq_of_src _ _

/-- **V.2.1, free rank-one input:** actual ring-coefficient local cohomology
vanishes below the dimension by the original ideal depth. -/
theorem regularLocal_localCohomology_ring_isZero_of_lt (n : ℕ)
    (hdim : ringKrullDim R = n) (i : ℕ) (hi : i < n) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj (ModuleCat.of R R)) :=
  isZero_localCohomology_of_lt_depth (maximalIdeal R) (ModuleCat.of R R) n
    (regularLocal_depth_eq n hdim).ge i hi

/-- Ring-coefficient local cohomology is concentrated in the actual
dimension, not in a degree chosen through a vanishing assumption. -/
theorem regularLocal_localCohomology_ring_isZero_of_ne (n : ℕ)
    (hdim : ringKrullDim R = n) (i : ℕ) (hi : i ≠ n) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj (ModuleCat.of R R)) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact regularLocal_localCohomology_ring_isZero_of_lt n hdim i h
  · exact regularLocal_localCohomology_isZero_of_gt n hdim (ModuleCat.of R R) i h

/-- The actual top local cohomology is nonzero, since its proved dualizing
coefficient has the residue field as its actual maximal-ideal annihilator. -/
theorem regularLocal_topLocalCohomology_not_isZero (n : ℕ)
    (hdim : ringKrullDim R = n) :
    ¬ IsZero ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) := by
  intro h
  have := ModuleCat.subsingleton_of_isZero h
  let e := (regularLocal_localCohomology_socle_iso n hdim).some
  have h01 : (0 : R ⧸ maximalIdeal R) = 1 :=
    e.toLinearEquiv.symm.injective (Subsingleton.elim _ _)
  exact zero_ne_one h01

end SGA.SGA2.ExposeV
