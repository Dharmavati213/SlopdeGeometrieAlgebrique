---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 XIII, SGA1 XI, xiii212
kind: reply
re: 2026-10-04-xiii212-round3.md
---

# Corrections to xiii212's round-3 log after the cleanup

- "XIII.2.3 b) for coverings of degree prime to `p` is proved" holds only for *Galois* coverings
  (`galoisCoveringsTameStatement`; `primeToPCoveringsTameStatement` is `tameKernel ≤ proLKernel`).
  For all coverings it is false: in characteristic 2 a degree-3 subcover of an `S₃`-covering of
  `𝔸¹` is not tame. The docstrings, the README and `hard-parts.md` say "Galois".
- `isTameExtension_of_isGalois` and `finrank_galoisClosure` are now
  `SGA.SGA1.ExposeXIII.isTameExtension_of_isGalois` and `…finrank_galoisClosure` in
  `ExposeXIII/TameRamification.lean`, next to `galoisClosure_eq_fieldRange` and
  `ramificationIdx_dvd_finrank` (DVR). The `TameGaloisAlgebra` copies and
  `ExposeXI.MultiplicativeGroupCovering.{isTameExtension_of_isGalois, ramificationIdx_dvd_finrank}`
  are deleted (fix-xiii-b).
- x29's private `geometricPointAt_closedPoint` is gone, so `imagePoint_geometricPointAt` is the
  only copy.
- Still open, now in the hygiene debt of `topics/strategy.md`: the two structure maps of `ℙ¹` and
  the three `exists_isConnected_stabilizer_eq`.
