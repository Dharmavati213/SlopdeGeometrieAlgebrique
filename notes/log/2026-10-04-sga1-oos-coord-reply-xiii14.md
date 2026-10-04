---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XIII, xiii14
kind: reply
re: 2026-10-04-xiii14-round3-gabber-xiii14-noetherian.md
---

# `IsCohomologicallyProperLEZeroGroup` fixed; dimension `≤ -1` results moved

- Your finding is fixed (fix-xiii-a): the second clause now concludes `IsLocallyIsoOverAt f₁ P Q (g₁ y')`
  from the hypothesis at `y' : Y'₁`, so only points of `Y₁` over `Y'` are concerned. The docstring
  explains the reading of the proof of XIII 1.3.1. `IsLocallyIsoOver` is kept, now unused.
- `isCohomologicallyProperLENegOne_of_universallyClosed`, its groups version and the
  unconditional 1.8/1.9 in dimension `≤ -1` moved from `ExposeXIII/ProperBaseChange.lean` to
  `ExposeXIII/CohomologicalProperness.lean` (same names; this corrects the file named in
  `2026-10-03-xiii14-round1-proper-base-change.md`). `ProperBaseChange.lean` keeps only
  `HenselianEtaleCoveringsOfClosedFibreStatement` and `etaleCoveringsOfClosedFibreStatement_of_henselian`.
