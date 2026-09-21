/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualCompletion
import SGA.SGA2.ExposeV.FiniteLengthLocalization
import SGA.SGA2.ExposeV.ModuleExtLocalization
import SGA.SGA2.ExposeIV.MatlisFiniteLengthDetection

/-!
# The finite-length and support steps of V.3.5

Over a regular local ring, original local cohomology has the same extended
length as complementary original module-valued Ext. Thus finite length of
local cohomology is equivalent to vanishing of the localizations of that Ext
module away from the closed point. Completeness of the base is not required.

The genuine Ext-localization comparison also gives the criterion using Ext
over the local ring at each point. The full V.3.5 is proved separately in
`LocalCohomologyFiniteLengthCriterion`, using the proved regularity and
dimension formula for prime localizations. The quotient reduction is proved
in `LocalCohomologyQuotientTransport`; the algebraic change-of-rings comparisons
are proved in `SurjectiveScalarChange` and `SurjectiveDualityChange`.
-/

noncomputable section
universe u
open CategoryTheory Opposite IsLocalRing
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Local duality preserves extended length, even over a noncomplete base. -/
theorem regularLocal_localCohomology_length_eq_ext
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.length R ((_root_.localCohomology (maximalIdeal R) i).obj M) =
      Module.length R (moduleExtValue M (ModuleCat.of R R) j) :=
  (regularLocal_localCohomologyHomIso n hdim i j h M).toLinearEquiv.length_eq.trans
    ((regularLocal_localCohomology_dualizing n hdim).moduleHomDual_length _)

/-- **V.3.5, duality step:** finite length of original local cohomology is
equivalent to finite length of complementary original Ext, without completion. -/
theorem regularLocal_localCohomology_finiteLength_iff_ext
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M) ↔
      IsFiniteLength R (moduleExtValue M (ModuleCat.of R R) j) := by
  rw [← Module.length_ne_top_iff, ← Module.length_ne_top_iff,
    regularLocal_localCohomology_length_eq_ext n hdim i j h M]

/-- **V.3.5, through the support step:** finite length is equivalent to
vanishing of localizations of complementary Ext. The local-cohomology
form is proved in `LocalCohomologyFiniteLengthCriterion`. -/
theorem regularLocal_localCohomology_finiteLength_iff_localizedExt
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M) ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R →
        Subsingleton (LocalizedModule p.asIdeal.primeCompl
          (moduleExtValue M (ModuleCat.of R R) j)) :=
  (regularLocal_localCohomology_finiteLength_iff_ext n hdim i j h M).trans
    (finiteLength_iff_localizedModule_subsingleton _)

/-- **V.3.5, through Ext base change:** the criterion now uses actual Ext
over the localized rings, with their actual ring coefficient modules. -/
theorem regularLocal_localCohomology_finiteLength_iff_ext_atPrime
    (n : ℕ) (hdim : ringKrullDim R = n) (i j : ℕ) (h : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M) ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R →
        Limits.IsZero (moduleExtValue (M.localizedModule p.asIdeal.primeCompl)
          (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) j) := by
  rw [regularLocal_localCohomology_finiteLength_iff_localizedExt n hdim i j h M]
  apply forall_congr'
  intro p
  apply imp_congr_right
  intro _
  rw [ModuleCat.isZero_iff_subsingleton]
  exact localizedModule_ext_ring_subsingleton_iff p.asIdeal.primeCompl M j

end SGA.SGA2.ExposeV
