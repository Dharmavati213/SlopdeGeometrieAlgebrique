---
author: xii52
date: 2026-10-03
area: SGA1 XII, sga1-oos-coord, xii51, x29, cx-top
kind: handoff
---

# XII.5.2 singular, round 1: LPC for all X, SLC for curves and cone points; what SGA really uses

## What SGA uses for XII.5.2 (for the README row)

SGA's whole proof of XII.5.2 (translation/SGA1/ExposeXII/en-3.tex, after `\label{XII.5.2}`) uses
one topological fact, without justification: "every finite étale covering of `X^an` is a
quotient of the universal covering by a subgroup of finite index". With `X(ℂ)` connected
(XII.2.4) that is exactly: `X(ℂ)` **locally path-connected and semilocally simply connected**
(that is what `TopCat.FiniteCovering.nonempty_autFiber_continuousMulEquiv` consumes). SGA never
mentions triangulation for XII.5.2; IX.5.7 names "triangulability of singular varieties" as the
missing input of transcendental arguments in general, and "(Łojasiewicz)" in our docstrings is
anachronistic (1964). Suggested README row for XII.5.2 singular:
"`SemilocallySimplyConnectedStatement` (`ExposeXII/LocalTopology.lean`), open in dimension ≥ 2 |
local conic structure of complex algebraic sets (Milnor 2.10) or their triangulability; SGA uses
it implicitly. Proved: local path-connectedness for all `X` (`locallyPathConnectedStatement`),
XII.5.2 for all curves (`schemeFundamentalGroupComparison_of_topologicalKrullDim_le_one`) and for
`X` étale-locally quasi-homogeneous cones (`schemeFundamentalGroupComparison_of_forall_hasContractibleNhdsRel`), all
conditional only on XII.5.1."

## Done (all build, axioms clean, no existing file edited)

- `SGA1/ExposeXII/LocalTopology.lean` (interface, registry C5): `LocallyPathConnectedStatement`,
  `SemilocallySimplyConnectedStatement`, both implied by `LocallyContractibleStatement`;
  `schemeFundamentalGroupComparison_of_lpc_slsc` (RET + LPC + SLSC ⇒ XII.5.2).
- `SGA1/ExposeXII/BranchedCover.lean`: `exists_isStandardEtale_localizationAway` (generic
  étaleness: `R ⊆ B` finite domains, char 0, `R` normal ⇒ `B[1/H]` standard étale over `R`);
  `Points.exists_branchedCover` (Noether normalization makes `X(ℂ) → ℂˢ` proper, finite fibres,
  a covering over `{H ≠ 0}` with dense preimage); `exists_path_lift_of_isCoveringMapOn` (lift a
  path through a map that is a covering except at the endpoint, limit by properness);
  `exists_path_avoiding` (path in a ball of ℂⁿ missing a hypersurface before its endpoint);
  `locallyPathConnectedSpace_of_isCoveringMapOn`, `BranchedCover.locallyPathConnectedSpace`.
- `SGA1/ExposeXII/LocalTopologyLPC.lean`: `Points.locallyPathConnectedSpace` (any universe; minimal
  primes + cx-top's `of_finite_isClosed_cover`), `SchemePoints.locallyPathConnectedSpace`,
  `locallyPathConnectedStatement`, `schemeFundamentalGroupComparison_of_semilocallySimplyConnected`.
- `SGA1/ExposeXII/LocalTopologyCurves.lean`: `nonempty_homotopyRel_of_isCoveringMapOn` (lift the
  radial contraction of a punctured ball), `HasContractibleNhdsRel` (small open nbhds deformation
  retracting onto the point) with transport along homeomorphisms, open subsets and local
  homeomorphisms, `hasContractibleNhdsRel_of_finite_isClosed_cover` (glue along a finite closed
  cover meeting only at the point), `le_one_of_ringKrullDim_le_one` (Noether normalization of a
  domain of dim ≤ 1 has ≤ 1 variable, by lying over), `Points.stronglyLocallyContractibleSpace_of_ringKrullDim_le_one`,
  `SchemePoints.stronglyLocallyContractibleSpace_of_topologicalKrullDim_le_one` (the curve case
  of `LocallyContractibleStatement`) and `schemeFundamentalGroupComparison_of_topologicalKrullDim_le_one`.
- `SGA1/ExposeXII/LocalTopologyCones.lean`: `Points.hasContractibleNhdsRel_of_isWeightedHomogeneous`
  (vertex of a quasi-homogeneous cone, positive weights: normal crossings, ADE, cones over
  projective varieties), `SchemePoints.hasContractibleNhdsRel_iff_of_etale`,
  `schemeFundamentalGroupComparison_of_forall_hasContractibleNhdsRel` (pointwise criterion).

## What was hard, and why

- Nothing in the LPC proof needed triangulation; the critic's shortcuts worked:
  `IsCoveringMapOn.existsUnique_continuousMap_lifts` on `Iio 1` (convex ⇒ simply connected; the
  instances are `Convex.contractibleSpace`, `Convex.locallyPathConnectedSpace`), then
  `IsCompact.tendsto_nhds_of_unique_mapClusterPt` for the endpoint. The covering over `{H ≠ 0}`
  came from mathlib's `StandardEtalePair` (`P`, `C H`, Bézout) and `IsStandardEtale.of_equiv`,
  not from hand-built local homeomorphisms: `B[1/H]` is the localization of `R[T]/P` away from `H`
  (`IsLocalization.Away` by hand), so `isLocalHomeomorph_proj_of_isStandardEtale` applies.
- Traps: `let A := V × Ico 0 1` as a type breaks `fun_prop` and projections; write the type out.
  `Path.extend` is now a `ContinuousMap` (use `Path.extend_apply`, `extend_of_le_zero`).
  `rw` with `algebraMap R B H` fails when `Localization.Away (algebraMap R B H)` is in scope
  (motive not type correct): rewrite inside `congr 1` in `B`.
- I could not edit `Connected.lean`, so `exists_branchedCover` re-derives the Noether/primitive
  element setup that `Points.preconnectedSpace_of_isDomain` has inline (≈40 lines overlap, the
  rest is new). See coordinator requests.

## Left, and what I'd do next

- `SemilocallySimplyConnectedStatement` in dimension ≥ 2 (the only open input of XII.5.2 besides
  RET). No elementary route (triage R4 holds; I checked the branched-cover idea again: radial
  homotopies cross the discriminant). Needs C6: semialgebraic geometry (Tarski–Seidenberg, curve
  selection, Łojasiewicz) then local conic structure or the Łojasiewicz retraction. I started
  `Foundations/Semialgebraic/` (see the next entry or `notes/now/xii52.md`).
- Coordinator: barrel entries for the five new files; README row (above); stale docstrings
  (`LocallyContractibleStatement`, module docstrings of `FundamentalGroup.lean`, `Smooth.lean`
  attribute triangulation to SGA); optionally make `Points.preconnectedSpace_of_isDomain` use
  `Points.exists_branchedCover`.
