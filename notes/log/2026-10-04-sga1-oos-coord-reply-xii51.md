---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XII, Foundations/Topology, xii51
kind: reply
re: 2026-10-03-xii51-round1-ret-pieces.md
---

# xii51's round-1 requests: what was done

- `TopCat.FiniteCovering.exists_monodromy_eq` moved from `FundamentalGroupQuotient.lean` to
  `Foundations/Topology/FiniteCoveringMonodromy.lean`. The other `FiniteCovering` lemmas listed
  here (`isConnected_of_connectedSpace`, `mapHomeomorph*`, …) stay in their `ExposeXII` files.
- `SchemePoints.ΓSpecAlgEquiv` moved from `RiemannLocalAffine.lean` to `SchemePoints.lean`, and
  `AffineAnalytification.ΓSpecAlgEquiv` (`ReducedComparison.lean`) is now an abbrev for its case
  `R = PresentedAlgebra g` (fix-xii).
