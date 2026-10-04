/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.ClosureComparison
import SGA.SGA1.ExposeXII.FundamentalGroup
import SGA.SGA1.ExposeXII.GAGAFiberSeparating
import SGA.SGA1.ExposeXII.LocalTopologySLSC
import SGA.SGA1.ExposeXII.RiemannCurvesSymmetric

/-!
# SGA 1, Exposé XII: statements proved by later theorems

Some `…Statement`s of Exposé XII were recorded as inputs before the theorems that prove them
were available. This file names the proofs.

* `coveringFundamentalGroupStatement`: the topological input of XII.5.2, affine case
  (`CoveringFundamentalGroupStatement`), in every universe. `X(ℂ)` is locally path-connected
  (`Points.locallyPathConnectedSpace`) and semilocally simply connected
  (`Points.semilocallySimplyConnectedSpace`), so a connected `X(ℂ)` satisfies the hypotheses of
  `TopCat.FiniteCovering.nonempty_autFiber_continuousMulEquiv`.
* `fundamentalGroupComparison_of_riemannExistence`: XII.5.2, affine case
  (`FundamentalGroupComparisonStatement`), from XII.5.1 (`RiemannExistenceStatement`) alone. The
  scheme form is `schemeFundamentalGroupComparison_of_riemannExistence`.
* `separatingFunctionStatement`: the analytic input of XII.5.1 for curves in the form "a
  function injective on one fibre" (`SeparatingFunctionStatement`), from
  `fiberSeparatingFunction`.
* `Points.closureComparisonStatement_zero`: XII.2.2 for affine `X = Spec A`, for `A : Type`
  (`Points.ClosureComparisonStatement.{0}`), from Rückert's Nullstellensatz. Other universes are
  not derived. The scheme form is `SchemePoints.closureComparison`.
-/

namespace SGA.SGA1.ExposeXII

universe u

/-- XII.5.2, topological input, affine case: for `A` of finite type over `ℂ` with `X(ℂ)`
connected, the automorphism group of the fibre functor of finite coverings of `X(ℂ)` at `x` is the
profinite completion of `π₁(X(ℂ), x)`. Holds because `X(ℂ)` is locally path-connected and
semilocally simply connected (instances `Points.locallyPathConnectedSpace`,
`Points.semilocallySimplyConnectedSpace`). -/
theorem coveringFundamentalGroupStatement : CoveringFundamentalGroupStatement.{u} :=
  fun A _ _ _ _ x ↦ TopCat.FiniteCovering.nonempty_autFiber_continuousMulEquiv
    (TopCat.of (Points ℂ A)) x

/-- XII.5.2, affine case, from XII.5.1 alone: for `A` of finite type over `ℂ` with `Spec A`
connected, the étale fundamental group of `Spec A` at `x` is isomorphic to the profinite completion
of `π₁(X(ℂ), x)`. The other inputs, XII.2.4 (`Points.connectedComparison`) and the topological
input (`coveringFundamentalGroupStatement`), are proved. -/
theorem fundamentalGroupComparison_of_riemannExistence (H : RiemannExistenceStatement.{u}) :
    FundamentalGroupComparisonStatement.{u} :=
  fundamentalGroupComparison' H coveringFundamentalGroupStatement

/-- XII.5.1 for curves, analytic input, one-fibre form: every connected finite covering of
`ℂ ∖ S`, `S` finite, carries a holomorphic function, meromorphic at the punctures and at
infinity, which is injective on some fibre. It follows from the form with a separating function
for every fibre (`fiberSeparatingFunction`). -/
theorem separatingFunctionStatement : SeparatingFunctionStatement :=
  separatingFunctionStatement_of_fiberSeparatingFunctionStatement fiberSeparatingFunction

/-- XII.2.2, affine case, for `A : Type`: for a constructible subset `T` of `X = Spec A`, `A` of
finite type over `ℂ`, the closure of `T(ℂ)` in `X(ℂ)` is `(closure T)(ℂ)`. From Rückert's
Nullstellensatz (`AffineAnalytification.rueckertNullstellensatz`). -/
theorem Points.closureComparisonStatement_zero : Points.ClosureComparisonStatement.{0} :=
  Points.closureComparisonStatement_of_rueckert AffineAnalytification.rueckertNullstellensatz

end SGA.SGA1.ExposeXII
