/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.LocalAcyclicityComparison
import SGA.SGA1.ExposeXIII.LocalAcyclicity

/-!
# Smooth base change in degree `0`, given SGA 4 XV 2.1

SGA 4 XV 2.1 (`SGA.SGA1.ExposeXIII.LocalAsphericitySmoothStatement`) says that smooth morphisms are
universally locally `1`-aspherical, in particular locally `0`-acyclic. Together with the
comparison of the Milnor-fibre and base-change forms
(`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic`) it gives the
smooth base change theorem for direct images of étale sheaves of sets (SGA 4 XVI 1.1 in degree
`0`): `SGA.SGA1.ExposeXIII.isIso_etaleBaseChangeMap_of_smooth_of_localAsphericitySmoothStatement`.
Without SGA 4 XV 2.1 it holds for étale `g`
(`AlgebraicGeometry.Scheme.isIso_etaleBaseChangeMap_of_etale`).

## References

* [SGA 4, Exposé XV, 2.1; Exposé XVI, 1.1][sga4]
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- **Smooth base change in degree `0`** (SGA 4 XVI 1.1 for sheaves of sets), given SGA 4 XV 2.1
(`LocalAsphericitySmoothStatement`): for a cartesian square `X' = X ×_Y Y'` with `g` smooth and
`f` quasi-compact and quasi-separated, the base change morphism `g^* f_* F ⟶ f'_* h^* F` is an
isomorphism for every étale sheaf of sets `F` on `X`. -/
theorem isIso_etaleBaseChangeMap_of_smooth_of_localAsphericitySmoothStatement
    (H : LocalAsphericitySmoothStatement.{u}) (hsq : IsPullback h f' f g) [QuasiCompact f]
    [QuasiSeparated f] [Smooth g] (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((Scheme.etaleBaseChangeMap hsq.w).app F) :=
  Scheme.isIso_etaleBaseChangeMap_of_flat_of_isLocallyZeroAcyclic hsq
    (H g).isUniversallyLocallyZeroAcyclic.isLocallyAcyclicFor F

end SGA.SGA1.ExposeXIII
