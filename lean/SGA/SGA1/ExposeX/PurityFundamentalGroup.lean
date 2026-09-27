/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality
import SGA.SGA1.ExposeX.Purity

/-!
# SGA 1, Exposé X, 3.3: the fundamental group and purity

The last assertion of X.3.3 for the fundamental groups `π₁(U, t̄) → π₁(X, t̄)` of Exposé V: for
regular locally noetherian schemes `X` and opens `U` with complement of codimension `≥ 2`
(`bijective_map_of_isRegularScheme`), in particular for the punctured spectrum of a regular local
ring of dimension `≥ 2` (`bijective_map_puncturedSpectrum`). The equivalences of categories are
in `Purity`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeX

variable (Ω : Type u) [Field Ω]

/-- X.3.3, last assertion (from X.3.3): if `X` is regular and locally noetherian and `X \ U` has
codimension `≥ 2`, then `π₁(U, t̄) → π₁(X, t̄)` is an isomorphism for every geometric point `t̄`
of `U`. -/
theorem bijective_map_of_purity (h : PurityCoveringsStatement.{u}) {X : Scheme.{u}}
    [IsLocallyNoetherian X] (hX : IsRegularScheme X) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (t : Spec (.of Ω) ⟶ U) : Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω U.ι t) :=
  have := h hX U hU
  ExposeV.autMap_bijective _ _

/-- X.3.3, last assertion: if `X` is regular and locally noetherian and `X \ U` has codimension
`≥ 2`, then `π₁(U, t̄) → π₁(X, t̄)` is an isomorphism for every geometric point `t̄` of `U`. -/
theorem bijective_map_of_isRegularScheme {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsRegularScheme X) (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (t : Spec (.of Ω) ⟶ U) : Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω U.ι t) :=
  bijective_map_of_purity Ω purityCoverings hX U hU t

/-- X.3.3, last assertion, for regular schemes of dimension `≤ 2`: if `X` is regular and locally
noetherian with local rings of dimension `≤ 2` and `X \ U` has codimension `≥ 2`, then
`π₁(U, t̄) → π₁(X, t̄)` is an isomorphism for every geometric point `t̄` of `U`. -/
theorem bijective_map_of_ringKrullDim_le_two {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsRegularScheme X) (hdim : ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (U : X.Opens) (hU : ∀ x : X, x ∉ U → 2 ≤ ringKrullDim (X.presheaf.stalk x))
    (t : Spec (.of Ω) ⟶ U) : Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω U.ι t) :=
  have := isEquivalence_pullback_of_isRegularScheme_of_ringKrullDim_le_two hX hdim U hU
  ExposeV.autMap_bijective _ _

/-- X.3.3, last assertion, for the punctured spectrum `U` of a regular local ring `A` of
dimension `≥ 2`: `π₁(U, t̄) → π₁(Spec A, t̄)` is an isomorphism for every geometric point `t̄` of
`U`. -/
theorem bijective_map_puncturedSpectrum (A : CommRingCat.{u}) [IsRegularLocalRing A]
    (hdim : 2 ≤ ringKrullDim A) (t : Spec (.of Ω) ⟶ puncturedSpectrum A) :
    Function.Bijective (ExposeV.etaleFundamentalGroup.map Ω (puncturedSpectrum A).ι t) :=
  have := isEquivalence_pullback_puncturedSpectrum A hdim
  ExposeV.autMap_bijective _ _

end SGA.SGA1.ExposeX
