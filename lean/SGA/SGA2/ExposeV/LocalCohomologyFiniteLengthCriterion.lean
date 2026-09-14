/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RegularLocalDimensionFormula
import SGA.SGA2.ExposeV.PuncturedDepthCriterion

/-!
# V.3.5 and V.3.6: finite length and punctured local cohomology

Original local duality and Ext localization, together with the proved
regularity and dimension formula for prime localizations, give V.3.5 over
regular local rings. Degrees beyond the dimension and negative shifted
degrees are treated separately, using genuine upper vanishing. The original
quotient comparison gives the full criterion for every local ring presented
as a quotient of a regular local ring. The proved depth comparison then
gives V.3.6, without assuming V.3.5 as an additional hypothesis.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- Local duality detects actual zero objects, not only finite length. -/
theorem regularLocal_localCohomology_isZero_iff_ext (n : ℕ)
    (hn : ringKrullDim R = n) (i j : ℕ) (hij : i + j = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj M) ↔
      IsZero (moduleExtValue M (ModuleCat.of R R) j) :=
  (regularLocal_localCohomologyHomIso n hn i j hij M).isZero_iff.trans
    (moduleHomDual_isZero_iff _ _
      (SGA.SGA2.ExposeIV.regularLocal_localCohomology_dualizing n hn))

/-- Within the original ring dimension, punctured shifted vanishing is
exactly the actual complementary Ext vanishing condition. If the shift
would be negative, that Ext vanishes above the local ring's dimension. -/
theorem regularLocal_puncturedVanishing_iff_ext_atPrime (n : ℕ)
    (hn : ringKrullDim R = n) (i q : ℕ) (hiq : i + q = n)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    puncturedLocalCohomologyVanishing M i ↔
      ∀ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R →
        IsZero (moduleExtValue (M.localizedModule p.asIdeal.primeCompl)
          (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) q) := by
  constructor
  · intro h p hp
    let Rp := Localization.AtPrime p.asIdeal
    have := regularLocal_atPrime_isRegularLocalRing p.asIdeal
    let s := (maximalIdeal Rp).spanFinrank
    have hs : ringKrullDim Rp = s := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    let : IsLocalRing (R ⧸ p.asIdeal) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
    let d := (LTSeries.longestOf (PrimeSpectrum (R ⧸ p.asIdeal))).length
    have hd : ringKrullDim (R ⧸ p.asIdeal) = d :=
      Order.krullDim_eq_length_of_finiteDimensionalOrder
    have hsd : s + d = n := by
      have heq := regularLocal_atPrime_dimension_add_quotient p.asIdeal
      rw [hs, hd, hn, ← Nat.cast_add] at heq
      exact_mod_cast heq
    have : Module.Finite Rp (M.localizedModule p.asIdeal.primeCompl) :=
      Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
        (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
    by_cases hdi : d ≤ i
    · exact (regularLocal_localCohomology_isZero_iff_ext s hs (i - d) q (by omega)
        (M.localizedModule p.asIdeal.primeCompl)).mp
          (h p hp d (i - d) hd (Nat.sub_add_cancel hdi))
    · exact regularLocal_moduleExt_isZero_of_gt s hs _ _ q (by omega)
  · intro h p hp d j hd hji
    let Rp := Localization.AtPrime p.asIdeal
    have := regularLocal_atPrime_isRegularLocalRing p.asIdeal
    let s := (maximalIdeal Rp).spanFinrank
    have hs : ringKrullDim Rp = s := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
    have hsd : s + d = n := by
      have heq := regularLocal_atPrime_dimension_add_quotient p.asIdeal
      rw [hs, hd, hn, ← Nat.cast_add] at heq
      exact_mod_cast heq
    have : Module.Finite Rp (M.localizedModule p.asIdeal.primeCompl) :=
      Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
        (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
    exact (regularLocal_localCohomology_isZero_iff_ext s hs j q (by omega)
      (M.localizedModule p.asIdeal.primeCompl)).mpr (h p hp)

/-- Above the original dimension, all the shifted punctured values vanish.
The coefficient module need not be finite for this upper-vanishing result. -/
theorem regularLocal_puncturedVanishing_of_gt (n : ℕ) (hn : ringKrullDim R = n)
    (M : ModuleCat.{u} R) (i : ℕ) (hi : n < i) :
    puncturedLocalCohomologyVanishing M i := by
  intro p _ d j hd hji
  let Rp := Localization.AtPrime p.asIdeal
  have := regularLocal_atPrime_isRegularLocalRing p.asIdeal
  let s := (maximalIdeal Rp).spanFinrank
  have hs : ringKrullDim Rp = s := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  have hsd : s + d = n := by
    have heq := regularLocal_atPrime_dimension_add_quotient p.asIdeal
    rw [hs, hd, hn, ← Nat.cast_add] at heq
    exact_mod_cast heq
  exact regularLocal_localCohomology_isZero_of_gt s hs _ j (by omega)

/-- **V.3.5, regular-local case.** Finite length of original local
cohomology is equivalent to the source's shifted vanishing at every
nonclosed point, in every degree. No localization regularity or dimension
formula is assumed: both have been proved from the original ring hypothesis. -/
theorem regularLocal_localCohomology_finiteLength_iff_punctured
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) :
    IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M) ↔
      puncturedLocalCohomologyVanishing M i := by
  let n := (maximalIdeal R).spanFinrank
  have hn : ringKrullDim R = n := IsRegularLocalRing.spanFinrank_maximalIdeal.symm
  by_cases hi : i ≤ n
  · exact (regularLocal_localCohomology_finiteLength_iff_ext_atPrime n hn i (n - i)
      (Nat.add_sub_of_le hi) M).trans
        (regularLocal_puncturedVanishing_iff_ext_atPrime n hn i (n - i)
          (Nat.add_sub_of_le hi) M).symm
  · have hzero := regularLocal_localCohomology_isZero_of_gt n hn M i (by omega)
    have := ModuleCat.subsingleton_of_isZero hzero
    exact ⟨fun _ ↦ regularLocal_puncturedVanishing_of_gt n hn M i (by omega),
      fun _ ↦ IsFiniteLength.of_subsingleton⟩

/-- **V.3.6, regular-local case.** Finite length through a threshold is
equivalent to the actual punctured depth inequality, including infinite depth. -/
theorem regularLocal_localCohomology_finiteLength_le_iff_depth
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (∀ i ≤ n, IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M)) ↔
      puncturedDepthBound M n :=
  localCohomology_finiteLength_le_iff_depth_of_criterion M n
    (fun i _ ↦ regularLocal_localCohomology_finiteLength_iff_punctured M i)

variable {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]

/-- **V.3.5.** For a finite module over a quotient of a regular local
ring, the original local cohomology has finite length exactly when its
shifted actual localizations vanish away from the closed point. -/
theorem localCohomology_finiteLength_iff_punctured_of_surjective
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (M : ModuleCat.{u} S) [Module.Finite S M] (i : ℕ) :
    IsFiniteLength S ((_root_.localCohomology (maximalIdeal S) i).obj M) ↔
      puncturedLocalCohomologyVanishing M i := by
  have : Module.Finite R ((ModuleCat.restrictScalars σ).obj M) :=
    (restrictScalars_finite_iff_of_surjective σ hσ M).mpr inferInstance
  exact (localCohomologyFiniteLengthCriterion_iff_of_surjective σ hσ M i).mp
    (regularLocal_localCohomology_finiteLength_iff_punctured
      ((ModuleCat.restrictScalars σ).obj M) i)

/-- **V.3.6.** The full depth criterion for finite modules over quotients
of regular local rings, without an additional finite-length equivalence
hypothesis. Negative shifted thresholds and infinite depth are retained. -/
theorem localCohomology_finiteLength_le_iff_depth_of_surjective
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (M : ModuleCat.{u} S) [Module.Finite S M] (n : ℕ) :
    (∀ i ≤ n, IsFiniteLength S ((_root_.localCohomology (maximalIdeal S) i).obj M)) ↔
      puncturedDepthBound M n :=
  localCohomology_finiteLength_le_iff_depth_of_criterion M n
    (fun i _ ↦ localCohomology_finiteLength_iff_punctured_of_surjective σ hσ M i)

end SGA.SGA2.ExposeV
