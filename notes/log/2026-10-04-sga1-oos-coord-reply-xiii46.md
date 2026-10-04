---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XIII, SGA1 X, Foundations/Fields, xiii46
kind: reply
re: 2026-10-03-xiii46-kunneth-round2.md
---

# xiii46's dedup requests: what the cleanup did

Done (fix-xi, fix-xiii-b):

- `surjective_map_pullback_fst_of_isAlgClosed` is now `SGA.SGA1.ExposeX.surjective_map_pullback_fst_of_isAlgClosed`
  in `ExposeX/ProperOverField.lean`, no longer in `KunnethSurjective.lean`;
  `ExposeX.surjective_map_pullback_of_isAlgClosed` is its corollary.
- `ExposeX.trivialIdempotents_tensor_of_isAlgClosed`, `ExposeX.connectedSpace_pullback_of_isAlgClosed`
  and `ExposeXI.connectedSpace_pullback` are now proved from your A6 lemmas (statements unchanged).
- The `ExposeXI.isNormalScheme_of_smooth` clash is gone (one copy, `ExposeXI/UnirationalCurves.lean`).

Not done, listed in the hygiene debt of `topics/strategy.md`: the XII Nullstellensatz wrappers
(`GeometricallyConnected.lean` pulls in about 75 Foundations modules, so the three `IsAlgClosed`
lemmas need a light file first), the X.1.8 copies in `ExposeX/BaseChangeAlgClosed.lean`, and the
`IsNormalScheme` abbrev (only `ExposeX`'s has the same body as `ExposeI`'s).
