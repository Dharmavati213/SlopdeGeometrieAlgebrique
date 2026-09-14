/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyQuotientTransport
import SGA.SGA2.ExposeIII.DepthLocalCohomology
import Mathlib.RingTheory.Localization.Finiteness

/-!
# The depth deduction in V.3.6

On the original prime localizations, shifted vanishing through degree `n`
is equivalent to `n < depth(M_p) + dim(R/p)`. This is the negative-degree-safe
form of the depth inequality in V.3.6 and includes zero localized modules
(infinite depth). The deduction of V.3.6 from V.3.5 is proved explicitly;
the full V.3.5 and V.3.6 are proved in `LocalCohomologyFiniteLengthCriterion`.
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

private theorem sub_succ_le_enat_iff (n d : ℕ) (a : ℕ∞) :
    ((n + 1 - d : ℕ) : ℕ∞) ≤ a ↔ (n : ℕ∞) < a + d := by
  cases a using ENat.recTopCoe with
  | top => simp
  | coe k =>
    norm_cast
    omega

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Shifted vanishing at one point is measured by its actual localized
module depth. No subtraction in the natural numbers is used for the degree. -/
theorem localized_depth_add_dim_gt_iff (M : ModuleCat.{u} R) [Module.Finite R M]
    (p : PrimeSpectrum R) (n d : ℕ) :
    (n : ℕ∞) < depth (maximalIdeal (Localization.AtPrime p.asIdeal))
        (M.localizedModule p.asIdeal.primeCompl) + d ↔
      ∀ j : ℕ, j + d ≤ n →
        IsZero ((_root_.localCohomology (maximalIdeal (Localization.AtPrime p.asIdeal)) j).obj
          (M.localizedModule p.asIdeal.primeCompl)) := by
  have : Module.Finite (Localization.AtPrime p.asIdeal)
      (M.localizedModule p.asIdeal.primeCompl) :=
    Module.Finite.of_isLocalizedModule p.asIdeal.primeCompl
      (M.localizedModuleMkLinearMap p.asIdeal.primeCompl)
  rw [← sub_succ_le_enat_iff,
    le_depth_iff_localCohomology_vanishes]
  exact forall_congr' fun j ↦ imp_congr_left (by omega)

/-- The punctured depth condition of V.3.6, including infinite depth and
negative shifted thresholds. -/
def puncturedDepthBound [IsLocalRing R] (M : ModuleCat.{u} R) (n : ℕ) : Prop :=
  ∀ p : PrimeSpectrum R, p.asIdeal ≠ maximalIdeal R →
    ∀ d : ℕ, ringKrullDim (R ⧸ p.asIdeal) = d →
      (n : ℕ∞) < depth (maximalIdeal (Localization.AtPrime p.asIdeal))
        (M.localizedModule p.asIdeal.primeCompl) + d

variable [IsLocalRing R]

/-- **V.3.6, depth step:** all shifted local vanishing conditions through
degree `n` are equivalent to the literal depth inequality at every nonclosed
point. This holds over every noetherian local ring. -/
theorem puncturedLocalCohomologyVanishing_le_iff_depth
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (∀ i ≤ n, puncturedLocalCohomologyVanishing M i) ↔ puncturedDepthBound M n := by
  constructor
  · intro h p hp d hd
    apply (localized_depth_add_dim_gt_iff M p n d).mpr
    intro j hj
    exact h (j + d) hj p hp d j hd rfl
  · intro h i hi p hp d j hd hj
    apply (localized_depth_add_dim_gt_iff M p n d).mp (h p hp d hd) j
    omega

/-- **V.3.6, deduction from V.3.5:** once the finite-length equivalence is
proved through `n` for this module, the stated depth criterion follows.
This conditional deduction is applied to the proved full criterion in
`LocalCohomologyFiniteLengthCriterion`. -/
theorem localCohomology_finiteLength_le_iff_depth_of_criterion
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    (hcriterion : ∀ i ≤ n,
      IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M) ↔
        puncturedLocalCohomologyVanishing M i) :
    (∀ i ≤ n, IsFiniteLength R ((_root_.localCohomology (maximalIdeal R) i).obj M)) ↔
      puncturedDepthBound M n :=
  (forall_congr' fun i ↦ forall_congr' fun hi ↦ hcriterion i hi).trans
    (puncturedLocalCohomologyVanishing_le_iff_depth M n)

/-- The actual punctured depth inequality is invariant under a quotient
presentation, just as the local-cohomology condition is. -/
theorem puncturedDepthBound_iff_of_surjective
    {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    (σ : R →+* S) (hσ : Function.Surjective σ)
    (M : ModuleCat.{u} S) [Module.Finite S M] (n : ℕ) :
    puncturedDepthBound ((ModuleCat.restrictScalars σ).obj M) n ↔ puncturedDepthBound M n := by
  have : Module.Finite R ((ModuleCat.restrictScalars σ).obj M) :=
    (restrictScalars_finite_iff_of_surjective σ hσ M).mpr inferInstance
  rw [← puncturedLocalCohomologyVanishing_le_iff_depth,
    ← puncturedLocalCohomologyVanishing_le_iff_depth]
  exact forall_congr' fun i ↦ forall_congr' fun _ ↦
    puncturedLocalCohomologyVanishing_iff_of_surjective σ hσ M i

end SGA.SGA2.ExposeV
