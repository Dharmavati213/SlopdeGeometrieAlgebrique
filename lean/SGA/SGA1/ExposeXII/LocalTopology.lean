/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.FundamentalGroup

/-!
# SGA 1, Exposé XII, 5.2: the topological input, local path-connectedness and semilocal simple
connectedness of `X(ℂ)`

SGA's proof of XII.5.2 (`π₁(X, x)` is the profinite completion of `π₁(X(ℂ), x)`) uses one fact
about the topology of `X(ℂ)`, without comment: every finite covering of `X(ℂ)` is a quotient of
the universal covering by a subgroup of finite index. That holds for a connected space which is
locally path-connected and semilocally simply connected
(`TopCat.FiniteCovering.nonempty_autFiber_continuousMulEquiv`). This file records these two
properties of `X(ℂ)` as the precise topological input of XII.5.2:

* `LocallyPathConnectedStatement`: `X(ℂ)` is locally path-connected, for every `X` locally of
  finite type over `ℂ`;
* `SemilocallySimplyConnectedStatement`: `X(ℂ)` is semilocally simply connected.

With the Riemann existence theorem XII.5.1 they give XII.5.2
(`schemeFundamentalGroupComparison_of_lpc_slsc`). Both also follow from the stronger
`LocallyContractibleStatement` (a basis of contractible neighbourhoods; classically a consequence
of the triangulability of complex algebraic sets), see
`locallyPathConnectedStatement_of_locallyContractible` and
`semilocallySimplyConnectedStatement_of_locallyContractible`. SGA itself never cites
triangulation for XII.5.2 (IX.5.7 mentions the triangulability of singular varieties only as an
assumption that its own argument avoids).

Status: both statements are proved for every `X`, without triangulation:
`locallyPathConnectedStatement` (`LocalTopologyLPC.lean`) and
`semilocallySimplyConnectedStatement` (`LocalTopologySLSC.lean`). Hence XII.5.2 holds for every
connected `X` locally of finite type over `ℂ`, conditional only on XII.5.1
(`schemeFundamentalGroupComparison_of_riemannExistence`, `LocalTopologySLSC.lean`). The stronger
`LocallyContractibleStatement` is not needed; it is proved for `X` smooth
(`SchemePoints.stronglyLocallyContractibleSpace_of_smooth`) and in dimension `≤ 1`
(`SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one`,
`LocalTopologyCurves.lean`), and open in dimension `≥ 2`.
-/

open AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

/-- The topological input of the proof of XII.5.2, first half: for `X` locally of finite type over
`ℂ`, the space `X(ℂ)` is locally path-connected. Proved for every `X`:
`locallyPathConnectedStatement` (`LocalTopologyLPC.lean`). -/
def LocallyPathConnectedStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))],
    LocallyPathConnectedSpace (SchemePoints ℂ X)

/-- The topological input of the proof of XII.5.2, second half: for `X` locally of finite type
over `ℂ`, the space `X(ℂ)` is semilocally simply connected. Proved for every `X`:
`semilocallySimplyConnectedStatement` (`LocalTopologySLSC.lean`: `X(ℂ)` is locally a real
algebraic set, and real algebraic sets are locally contractible in the classical sense). The
special cases `X` smooth and `dim X ≤ 1` also follow from strong local contractibility
(`SchemePoints.stronglyLocallyContractibleSpace_of_smooth`,
`SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one`). -/
def SemilocallySimplyConnectedStatement : Prop :=
  ∀ (X : Scheme.{0}) [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))],
    SemilocallySimplyConnectedSpace (SchemePoints ℂ X)

/-- Strong local contractibility of `X(ℂ)` implies its local path-connectedness. -/
theorem locallyPathConnectedStatement_of_locallyContractible
    (h : LocallyContractibleStatement) : LocallyPathConnectedStatement := fun X _ _ ↦
  have := h X
  inferInstance

/-- Strong local contractibility of `X(ℂ)` implies its semilocal simple connectedness. -/
theorem semilocallySimplyConnectedStatement_of_locallyContractible
    (h : LocallyContractibleStatement) : SemilocallySimplyConnectedStatement := fun X _ _ ↦
  have := h X
  inferInstance

/-- XII.5.2, proof: the comparison of fundamental groups follows from the Riemann existence
theorem XII.5.1 and the local path-connectedness and semilocal simple connectedness of `X(ℂ)`,
the input SGA uses ("every finite étale covering of `X^an` is a quotient of the universal
covering by a subgroup of finite index"), together with the connectedness comparison XII.2.4
(`SchemePoints.connectedComparison`). -/
theorem schemeFundamentalGroupComparison_of_lpc_slsc (H : SchemeRiemannExistenceStatement)
    (Hl : LocallyPathConnectedStatement) (Hs : SemilocallySimplyConnectedStatement) :
    SchemeFundamentalGroupComparisonStatement := by
  intro X _ _ hX x
  have := SchemePoints.connectedComparison X hX
  have := H X
  have := Hl X
  have := Hs X
  exact nonempty_etaleFundamentalGroup_continuousMulEquiv ℂ x

end SGA.SGA1.ExposeXII
