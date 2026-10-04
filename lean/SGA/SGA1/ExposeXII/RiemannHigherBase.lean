/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigher
import SGA.SGA1.ExposeXII.RiemannSimplyConnected
import SGA.SGA1.ExposeXII.RiemannReductionUniverse
import SGA.SGA1.ExposeIII.SmoothLift

/-!
# SGA 1, Exposé XII, 5.1 for hypersurface complements in dimension `0`

* `RiemannHigher.isLocalization_away_of_dvd_pow`: if `r ∣ r' ^ m` and `r' ∣ r ^ n`, a
  localization away from `r` is one away from `r'` (the form of
  `ExposeIII.isLocalization_away_of_dvd_pow` used to compare basic opens with the same zero set).
* `hypersurfaceComplementRiemannExistence_zero`: `HypersurfaceComplementRiemannExistenceStatement`
  for `d = 0` (a point). The case `d = 1` is in `SGA.SGA1.ExposeXII.RiemannHigherLine`.
-/

noncomputable section

open CategoryTheory

namespace SGA.SGA1.ExposeXII

namespace RiemannHigher

/-- If `r ∣ r' ^ m` and `r' ∣ r ^ n`, a localization away from `r` is a localization away from
`r'` (the two basic opens coincide). From `ExposeIII.isLocalization_away_of_dvd_pow`. -/
lemma isLocalization_away_of_dvd_pow {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {r r' : R} {m n : ℕ} (h₁ : r ∣ r' ^ m) (h₂ : r' ∣ r ^ n) [IsLocalization.Away r S] :
    IsLocalization.Away r' S := by
  obtain ⟨d, hd⟩ := h₁
  refine ExposeIII.isLocalization_away_of_dvd_pow (isUnit_of_dvd_unit (map_dvd _ h₂) ?_) hd
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit r).pow n

end RiemannHigher

/-- XII.5.1 for hypersurface complements in `𝔸⁰`: `ℂ[∅][1/f]`, `f ≠ 0`, is `ℂ`. -/
theorem hypersurfaceComplementRiemannExistence_zero :
    HypersurfaceComplementRiemannExistenceStatement 0 := by
  intro f hf
  let e₀ := MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)
  have hu : IsUnit f := by
    rw [← e₀.symm_apply_apply f]
    exact (Ne.isUnit (by simpa using hf)).map e₀.symm
  let e : MvPolynomial (Fin 0) ℂ ≃ₐ[MvPolynomial (Fin 0) ℂ] Localization.Away f :=
    IsLocalization.atUnit _ _ f hu
  exact (isEquivalence_pointsFunctor_iff_of_algEquiv (e.restrictScalars ℂ)).mp
    (riemannExistence_mvPolynomial 0)

end SGA.SGA1.ExposeXII
