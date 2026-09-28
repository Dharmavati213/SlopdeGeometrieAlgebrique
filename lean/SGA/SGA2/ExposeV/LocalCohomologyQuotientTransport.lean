/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.SurjectiveLocalization
import SGA.SGA2.ExposeV.LocalDualityFiniteFree
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# The quotient reduction of V.3.5

Both conditions in V.3.5 are invariant under a surjection of noetherian
local rings. The local condition uses actual cohomology of the original
localized modules, with the dimension of the corresponding prime quotient.
Points outside the image contribute zero modules. Negative cohomological
degrees impose no condition: a degree `j` is tested exactly when `j + d = i`.

This file proves the quotient reduction. The full regular-local case and
V.3.5 are proved separately in `LocalCohomologyFiniteLengthCriterion`.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
variable (σ : R →+* S) (hσ : Function.Surjective σ)
variable [IsNoetherianRing R] [IsNoetherianRing S]

/-- Local cohomology of the original localized coefficient modules agrees
after restriction along the actual surjection of the local rings. -/
def localCohomologyAtPrimeScalarChangeIso (q : Ideal S) [q.IsPrime]
    (M : ModuleCat.{u} S) (i : ℕ) :
    (_root_.localCohomology (maximalIdeal (Localization.AtPrime (q.comap σ))) i).obj
        (((ModuleCat.restrictScalars σ).obj M).localizedModule (q.comap σ).primeCompl) ≅
      (ModuleCat.restrictScalars (Localization.localRingHom (q.comap σ) q σ rfl)).obj
        ((_root_.localCohomology (maximalIdeal (Localization.AtPrime q)) i).obj
          (M.localizedModule q.primeCompl)) :=
  (_root_.localCohomology (maximalIdeal (Localization.AtPrime (q.comap σ))) i).mapIso
      (localizedRestrictScalarsIso σ hσ q M) ≪≫
    localRing_localCohomologyScalarChangeIso
      (Localization.localRingHom (q.comap σ) q σ rfl)
      (localRingHom_surjective σ hσ q) (M.localizedModule q.primeCompl) i

include hσ in
/-- Vanishing at corresponding points is unchanged in every nonnegative degree. -/
theorem localCohomologyAtPrime_isZero_iff_of_surjective (q : Ideal S) [q.IsPrime]
    (M : ModuleCat.{u} S) (i : ℕ) :
    IsZero ((_root_.localCohomology (maximalIdeal (Localization.AtPrime (q.comap σ))) i).obj
        (((ModuleCat.restrictScalars σ).obj M).localizedModule (q.comap σ).primeCompl)) ↔
      IsZero ((_root_.localCohomology (maximalIdeal (Localization.AtPrime q)) i).obj
        (M.localizedModule q.primeCompl)) := by
  rw [(localCohomologyAtPrimeScalarChangeIso σ hσ q M i).isZero_iff,
    ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  rfl

omit [IsNoetherianRing R] [IsNoetherianRing S] in
/-- Outside the closed image all the localized local-cohomology groups vanish. -/
theorem localCohomologyAtPrime_isZero_of_ker_not_le (M : ModuleCat.{u} S)
    (p : PrimeSpectrum R) (hp : ¬ RingHom.ker σ ≤ p.asIdeal) (i : ℕ) :
    IsZero ((_root_.localCohomology (maximalIdeal (Localization.AtPrime p.asIdeal)) i).obj
      (((ModuleCat.restrictScalars σ).obj M).localizedModule p.asIdeal.primeCompl)) :=
  (_root_.localCohomology (maximalIdeal (Localization.AtPrime p.asIdeal)) i).map_isZero
    (localizedRestrictScalars_isZero_of_ker_not_le σ M p hp)

/-- The shifted vanishing condition in V.3.5, on actual localizations.
The equation `j + d = i` implements the zero convention in negative degrees,
without incorrectly replacing a negative degree by degree zero. -/
def puncturedLocalCohomologyVanishing [IsLocalRing R] (M : ModuleCat.{u} R) (i : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R →
    ∀ d j : ℕ, ringKrullDim (R ⧸ p.asIdeal) = d → j + d = i →
      IsZero ((_root_.localCohomology (maximalIdeal (Localization.AtPrime p.asIdeal)) j).obj
        (M.localizedModule p.asIdeal.primeCompl))

variable [IsLocalRing R] [IsLocalRing S]
include hσ

/-- **V.3.5, quotient reduction of condition (b):** the shifted punctured
vanishing condition is unchanged by restriction along a surjection. -/
theorem puncturedLocalCohomologyVanishing_iff_of_surjective
    (M : ModuleCat.{u} S) (i : ℕ) :
    puncturedLocalCohomologyVanishing ((ModuleCat.restrictScalars σ).obj M) i ↔
      puncturedLocalCohomologyVanishing M i := by
  constructor
  · intro h q hq d j hd hj
    apply (localCohomologyAtPrime_isZero_iff_of_surjective σ hσ q.asIdeal M j).mp
    apply h (PrimeSpectrum.comap σ q)
    · exact fun heq ↦ hq ((comap_eq_maximalIdeal_iff_of_surjective σ hσ q.asIdeal).mp heq)
    · exact (ringKrullDim_quotient_comap_of_surjective σ hσ q.asIdeal).trans hd
    · exact hj
  · intro h p hp d j hd hj
    by_cases hker : RingHom.ker σ ≤ p.asIdeal
    · obtain ⟨q, rfl⟩ : p ∈ Set.range (PrimeSpectrum.comap σ) := by
        rw [_root_.range_comap_of_surjective S σ hσ]
        exact hker
      apply (localCohomologyAtPrime_isZero_iff_of_surjective σ hσ q.asIdeal M j).mpr
      apply h q
      · exact fun heq ↦ hp ((comap_eq_maximalIdeal_iff_of_surjective σ hσ q.asIdeal).mpr heq)
      · exact (ringKrullDim_quotient_comap_of_surjective σ hσ q.asIdeal).symm.trans hd
      · exact hj
    · exact localCohomologyAtPrime_isZero_of_ker_not_le σ M p hker j

/-- **V.3.5, full quotient reduction:** the equivalence to be proved over
the quotient is exactly the equivalence for the restricted original module.
No regularity, dimension formula, or local duality is assumed by this reduction. -/
theorem localCohomologyFiniteLengthCriterion_iff_of_surjective
    (M : ModuleCat.{u} S) (i : ℕ) :
    (IsFiniteLength R
        ((_root_.localCohomology (maximalIdeal R) i).obj ((ModuleCat.restrictScalars σ).obj M)) ↔
      puncturedLocalCohomologyVanishing ((ModuleCat.restrictScalars σ).obj M) i) ↔
    (IsFiniteLength S ((_root_.localCohomology (maximalIdeal S) i).obj M) ↔
      puncturedLocalCohomologyVanishing M i) :=
  iff_congr (localRing_localCohomology_finiteLength_iff_of_surjective σ hσ M i)
    (puncturedLocalCohomologyVanishing_iff_of_surjective σ hσ M i)

end SGA.SGA2.ExposeV
