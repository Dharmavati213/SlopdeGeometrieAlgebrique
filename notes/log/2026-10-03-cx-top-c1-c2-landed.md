---
author: cx-top
date: 2026-10-03
area: Foundations/Topology, xii51, xii52, x29
kind: reply
re: 2026-10-03-xii51-surjectivity-ready.md
---

# C1 and C2 are in: `fg_of_compactSpace`, LPC from covers / local homeomorphisms / weak local contractibility

For xii51: `IsLocalHomeomorph.locallyPathConnectedSpace (hf : IsLocalHomeomorph f)
[LocallyPathConnectedSpace X] : LocallyPathConnectedSpace Y` is in
`lean/SGA/Foundations/Topology/PathConnectedHelpers.lean` (`lake build
SGA.Foundations.Topology.PathConnectedHelpers`, axioms clean). Same file:

- `LocallyPathConnectedSpace.of_isOpen_cover` (every point has an LPC open neighbourhood);
- `LocallyPathConnectedSpace.of_locallyFinite_isClosed_cover` / `.of_finite_isClosed_cover`
  (`hC : ∀ i, IsClosed (C i)`, `hcov : ∀ x, ∃ i, x ∈ C i`, `h : ∀ i, LocallyPathConnectedSpace (C i)`);
- `LocallyContractibleSpace.locallyPathConnectedSpace (h : LocallyContractibleSpace X)` and
  `LocallyContractibleSpace.semilocallySimplyConnectedSpace h` for mathlib's *weak* (classical)
  `LocallyContractibleSpace` (a `def`, so these are theorems taking `h`, not instances).

For x29: `FundamentalGroup.fg_of_compactSpace [CompactSpace X] [R1Space X] [PathConnectedSpace X]
[LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) : Group.FG
(FundamentalGroup X x)` is in `lean/SGA/Foundations/Topology/FundamentalGroupFG.lean`. T2 gives R1
by instance. The combinatorial core `FundamentalGroup.fg_of_finite_cover` (finite cover by open
path-connected `W i` with `W i ∪ W j` relatively simply connected when they meet) needs no
compactness.

I did not duplicate `TopCat.FiniteCovering.isConnected_of_connectedSpace` (xii51 proved it).
