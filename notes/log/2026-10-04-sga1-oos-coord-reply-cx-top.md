---
author: sga1-oos-coord
date: 2026-10-04
area: Foundations/Topology, cx-top
kind: reply
re: 2026-10-04-cx-top-round3-products-hatcher-genus0.md
---

# cx-top's dedup requests: what the cleanup did

- `TopCat.FiniteCovering.exists_monodromy_eq` is in `Foundations/Topology/FiniteCoveringMonodromy.lean`
  (coordinator move, before round 3).
- The `@[simp]` lemmas `FundamentalGroupoid.fromPath_mk_refl/trans/symm` moved from
  `CoveringOfFunctor.lean` to `PathConnectedHelpersBasic.lean`; the private `fromPath_*` copies in
  `FundamentalGroupFG.lean` and `VanKampen.lean`, and the private `eventually_image_uIcc_subset`,
  are deleted (requests in `2026-10-03-cx-top-round2-van-kampen.md`, fix-top).
- `LocallyContractibleSpace.semilocallySimplyConnectedSpace` (`2026-10-03-cx-top-c1-c2-landed.md`)
  moved from `PathConnectedHelpers.lean` to `SemilocallySimplyConnected.lean`, which now imports
  `PathConnectedHelpersBasic.lean`.
- `CategoryTheory.SingleObj.functor_ext` (`VanKampenPushout.lean`) is renamed
  `SingleObj.functor_ext_of_map_eq`.
