/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherBase
import SGA.SGA1.ExposeXII.RiemannReductionNoether

/-!
# SGA 1, Exposé XII, 5.1 for `ℂ` minus the zeros of a polynomial

* `riemannExistence_polynomial_away`: XII.5.1 for `ℂ[t][1/p]`, `p ≠ 0`, i.e. `ℂ` minus the roots
  of `p`. It is `PuncturedPlane.riemannExistence_coordRing` (proved by xii51 and xii4 through
  compact Riemann surfaces, this project's route) for the set `S` of roots, since
  `ℂ[t][1/p] = ℂ[t][1/∏_{a ∈ S} (t - a)]` (`NoetherCurve.isLocalization_away_coordRing`). These are
  the fibres of the families of punctured lines in the induction step of
  `SGA.SGA1.ExposeXII.RiemannHigher`.
* `hypersurfaceComplementRiemannExistence_one`: `HypersurfaceComplementRiemannExistenceStatement 1`.
-/

noncomputable section

open CategoryTheory Polynomial

namespace SGA.SGA1.ExposeXII

/-- XII.5.1 for `ℂ` minus the zeros of a nonzero polynomial `p`, `X = Spec ℂ[t][1/p]`: this is
`PuncturedPlane.riemannExistence_coordRing` for the set `S` of roots of `p`, since
`ℂ[t][1/p] = ℂ[t][1/∏_{a ∈ S} (t - a)]`. -/
theorem riemannExistence_polynomial_away (p : ℂ[X]) (hp : p ≠ 0) :
    (pointsFunctor ℂ (Localization.Away p)).IsEquivalence := by
  have := NoetherCurve.isLocalization_away_coordRing hp
  let e : Localization.Away p ≃ₐ[ℂ[X]] PuncturedPlane.coordRing p.roots.toFinset :=
    IsLocalization.algEquiv (Submonoid.powers p) _ _
  exact (isEquivalence_pointsFunctor_iff_of_algEquiv (e.restrictScalars ℂ)).mpr
    (PuncturedPlane.riemannExistence_coordRing _)

/-- XII.5.1 for hypersurface complements in `𝔸¹`, i.e. `ℂ` minus a finite set
(`riemannExistence_polynomial_away`). -/
theorem hypersurfaceComplementRiemannExistence_one :
    HypersurfaceComplementRiemannExistenceStatement 1 := by
  intro f hf
  let e₁ : MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] ℂ[X] := (MvPolynomial.finSuccEquiv ℂ 0).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.isEmptyAlgEquiv ℂ (Fin 0)))
  have hp : e₁ f ≠ 0 := by simpa using hf
  have hM : Submonoid.map e₁ (Submonoid.powers f) = Submonoid.powers (e₁ f) :=
    Submonoid.map_powers _ _
  let e : Localization.Away f ≃ₐ[ℂ] Localization.Away (e₁ f) :=
    IsLocalization.algEquivOfAlgEquiv (M := Submonoid.powers f) (T := Submonoid.powers (e₁ f))
      (Localization.Away f) (Localization.Away (e₁ f)) e₁ hM
  exact (isEquivalence_pointsFunctor_iff_of_algEquiv e).mpr
    (riemannExistence_polynomial_away _ hp)

end SGA.SGA1.ExposeXII
