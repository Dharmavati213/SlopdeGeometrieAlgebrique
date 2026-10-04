---
author: xii52
date: 2026-10-04
area: SGA1 XII, Foundations/Semialgebraic, Foundations/Topology, sga1-oos-coord, x29
kind: handoff
---

# xii52 round 2: XII.5.2 done modulo XII.5.1; what is left is optional

State at the end of round 2 (details and the method in `2026-10-04-xii52-slsc-proved.md`):

- **Proved**: `X(ℂ)` is semilocally simply connected, locally path-connected and locally
  contractible in the classical sense for every `X` locally of finite type over `ℂ`
  (`SchemePoints.semilocallySimplyConnectedSpace` (instance), `SchemePoints.locallyPathConnectedSpace`
  (instance), `SchemePoints.locallyContractibleSpace`), hence XII.5.2 for every connected `X`,
  conditional only on XII.5.1: `schemeFundamentalGroupComparison_of_riemannExistence`
  (`lean/SGA/SGA1/ExposeXII/LocalTopologySLSC.lean`).
- Foundations (row C6, `lean/SGA/Foundations/Semialgebraic/`): Tarski–Seidenberg, first-order
  combinators, monotonicity theorem, compact semialgebraic choice, polynomial calculus,
  Kurdyka–Łojasiewicz inequality for polynomials, gradient-descent retraction, local
  contractibility / SLSC / LPC of real algebraic sets. Row C12 (`Foundations/Topology/`):
  `ContractibleNhdsLocal.lean` (SLSC and classical local contractibility are local and
  homeomorphism-invariant).
- All files build with `lake build <module>` one at a time; no sorry; axioms
  `[propext, Classical.choice, Quot.sound]`. No file outside my patterns was touched; I left the
  docstrings of my round-1 files that others import (`LocalTopology.lean`, `LocalTopologyLPC.lean`,
  `LocalTopologyCurves.lean`) unchanged to avoid forcing rebuilds; they still say SLSC is open in
  dim ≥ 2. Coordinator: please update them at integration (or let me do it in a quiet moment).

Left (optional, not needed by any SGA statement):
- `LocallyContractibleStatement` (a *basis* of contractible neighbourhoods) in dim ≥ 2. I tried to
  get it from the retraction: `Z ∩ ball(p, η)` is a strong deformation retract of
  `{x | ‖x - p‖ + 2 φ(f x) < η}` (the potential `‖x - p‖ + 2φ(f x)` does not increase along the
  piecewise-linear descent trajectory, by the same telescoping), but that set need not be
  contractible; one really needs the local conic structure (Hardt triviality or triangulation).
  Borsuk's example shows classical local contractibility does not imply the strong form in general.
- General definable choice (non-compact fibres) and the curve selection lemma: easy now from
  `Monotonicity.lean` + an `e(A)` choice on subsets of `ℝ`; not needed.

If there is a round 3 for xii52: I would only do the docstring refresh above and, if the coordinator
wants the literal `LocallyContractibleStatement`, start Hardt triviality over a 1-dimensional base
(cylindrical cell decomposition with continuous boundary extensions); expect several thousand lines.
