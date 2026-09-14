/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.FiniteProjectiveDimension
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.LocalProperties.ProjectiveDimension

/-!
# The actual residue field as a localized cyclic module

The original localization of `R/p` is the residue field of the actual local
ring `R_p`, linearly over `R_p`. Its map on original elements is the original
quotient-to-residue-field map. Consequently the residue fields at every
prime of a regular local ring have finite projective dimension over those
local rings. The converse homological criterion for regularity is proved
separately in `HomologicalRegularityCriterion`.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The image of the prime complement consists of all nonzero elements of
the original domain quotient. -/
theorem primeCompl_map_quotient (p : Ideal R) [p.IsPrime] :
    Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl = nonZeroDivisors (R ⧸ p) := by
  ext z
  change (∃ r : R, r ∈ p.primeCompl ∧ algebraMap R (R ⧸ p) r = z) ↔ _
  rw [mem_nonZeroDivisors_iff_ne_zero]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact fun h ↦ hr (Ideal.Quotient.eq_zero_iff_mem.mp h)
  · intro hz
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨r, fun h ↦ hz (Ideal.Quotient.eq_zero_iff_mem.mpr h), rfl⟩

/-- The original quotient-to-residue-field map is a module localization
at the original prime complement. -/
instance residueField_isLocalizedModule (p : Ideal R) [p.IsPrime] :
    IsLocalizedModule p.primeCompl
      ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R) := by
  have : IsLocalizedModule (Algebra.algebraMapSubmonoid (R ⧸ p) p.primeCompl)
      (Algebra.linearMap (R ⧸ p) p.ResidueField) := by
    rw [primeCompl_map_quotient]
    infer_instance
  exact IsLocalizedModule.restrictScalars p.primeCompl _

/-- The actual localized cyclic module is the actual residue field,
with linearity over the localized ring. -/
def localizedPrimeQuotientResidueFieldIso (p : Ideal R) [p.IsPrime] :
    (ModuleCat.of R (R ⧸ p)).localizedModule p.primeCompl ≅
      ModuleCat.of (Localization.AtPrime p) (ResidueField (Localization.AtPrime p)) := by
  have := ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of R (R ⧸ p)) p.primeCompl
  exact (LinearEquiv.extendScalarsOfIsLocalization p.primeCompl (Localization.AtPrime p)
    (IsLocalizedModule.linearEquiv p.primeCompl
      ((ModuleCat.of R (R ⧸ p)).localizedModuleMkLinearMap p.primeCompl)
      ((Algebra.linearMap (R ⧸ p) p.ResidueField).restrictScalars R))).toModuleIso

/-- The comparison retains the original residue class of each element. -/
@[simp]
theorem localizedPrimeQuotientResidueFieldIso_hom_mk (p : Ideal R) [p.IsPrime] (x : R ⧸ p) :
    (localizedPrimeQuotientResidueFieldIso p).hom
        ((ModuleCat.of R (R ⧸ p)).localizedModuleMkLinearMap p.primeCompl x) =
      algebraMap (R ⧸ p) p.ResidueField x := by
  simp [localizedPrimeQuotientResidueFieldIso, LinearEquiv.extendScalarsOfIsLocalization]

/-- A finite projective-dimension bound on the original cyclic module
descends to the actual residue field over the local ring at the prime. -/
theorem residueField_atPrime_hasProjectiveDimensionLE (p : Ideal R) [p.IsPrime]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (R ⧸ p)) n] :
    HasProjectiveDimensionLE
      (ModuleCat.of (Localization.AtPrime p) (ResidueField (Localization.AtPrime p))) n := by
  have := ModuleCat.localizedModule_hasProjectiveDimensionLE n p.primeCompl
    (ModuleCat.of R (R ⧸ p))
  exact hasProjectiveDimensionLT_of_iso (localizedPrimeQuotientResidueFieldIso p) (n + 1)

/-- The residue field at every prime of an actual regular local ring has
projective dimension bounded by the original ring's Krull dimension. -/
theorem regularLocal_residueField_atPrime_hasProjectiveDimensionLE [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) (p : Ideal R) [p.IsPrime] :
    HasProjectiveDimensionLE
      (ModuleCat.of (Localization.AtPrime p) (ResidueField (Localization.AtPrime p))) n := by
  have := regularLocal_finite_hasProjectiveDimensionLE n hdim (ModuleCat.of R (R ⧸ p))
  exact residueField_atPrime_hasProjectiveDimensionLE p n

/-- Every finite module over the actual local ring at a prime has the
same uniform bound. No regularity instance for that local ring is assumed. -/
theorem regularLocal_finite_atPrime_hasProjectiveDimensionLE [IsRegularLocalRing R]
    (n : ℕ) (hdim : ringKrullDim R = n) (p : Ideal R) [p.IsPrime]
    (M : ModuleCat.{u} (Localization.AtPrime p)) [Module.Finite (Localization.AtPrime p) M] :
    HasProjectiveDimensionLE M n := by
  have := regularLocal_residueField_atPrime_hasProjectiveDimensionLE n hdim p
  exact finite_hasProjectiveDimensionLE_of_residueField n M

end SGA.SGA2.ExposeV
