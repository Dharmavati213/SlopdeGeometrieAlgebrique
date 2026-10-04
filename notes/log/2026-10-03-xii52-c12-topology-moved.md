---
author: xii52
date: 2026-10-03
area: Foundations/Topology, cx-top, xii51, x29, sga1-oos-coord
kind: experience
---

# General topology from the XII.5.2 work moved to Foundations (row C12); LPC of `X(ℂ)` is an instance

The round-1 review asked that general topology not live in `SGA.SGA1.ExposeXII`. New registry row
C12 (owner `xii52`; cx-top, please don't reprove these):

- `lean/SGA/Foundations/Topology/CoveringMapOn.lean` (namespace `IsCoveringMapOn`):
  `exists_path_lift` (lift a path that is in `W` except at its end, through `p` covering over `W`,
  ending at the only point of `U` over the endpoint), `exists_mem_nhds_joinedIn`,
  `locallyPathConnectedSpace` (proper, finite fibres, covering over `W` with dense preimage),
  `nonempty_homotopyRel_id_const` / `exists_nonempty_homotopyRel_id_const` (radial contraction of a
  covering of a punctured ball of a real normed space).
- `lean/SGA/Foundations/Topology/ContractibleNhds.lean`: `HasContractibleNhdsRel x` (small open
  nbhds strongly deformation retracting onto `x`), `StronglyLocallyContractibleSpace.of_forall_hasContractibleNhdsRel`,
  `HasContractibleNhdsRel.{homeomorph, subtype, of_subtype, of_finite_isClosed_cover,
  of_isCoveringMapOn_ball}`, `IsLocalHomeomorph.hasContractibleNhdsRel_iff`.

The old names (`SGA.SGA1.ExposeXII.exists_path_lift_of_isCoveringMapOn`,
`nonempty_homotopyRel_of_isCoveringMapOn`, `hasContractibleNhdsRel_of_finite_isClosed_cover`, …) are
gone; nobody outside my files used them.

For xii51 and x29: `SchemePoints.locallyPathConnectedSpace X` and
`Points.locallyPathConnectedSpace A` are now **instances** (same names and explicit arguments, so
`have := SchemePoints.locallyPathConnectedSpace X` still works), in
`SGA/SGA1/ExposeXII/LocalTopologyLPC.lean`. Your `[LocallyPathConnectedSpace (SchemePoints ℂ X)]`
hypotheses can be dropped once you import it. There is also a per-`X` form of XII.5.2:
`schemeFundamentalGroupComparison_of_semilocallySimplyConnectedSpace (H : SchemeRiemannExistenceStatement)
X [SemilocallySimplyConnectedSpace (SchemePoints ℂ X)] (hc : ConnectedSpace X) x`. I checked that
`SGA/SGA1/ExposeX/TopologicallyFiniteComplex.lean` (x29) still compiles against the new files.
