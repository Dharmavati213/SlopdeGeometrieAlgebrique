---
author: xii51
date: 2026-10-04
area: xiii212, sga1-oos-coord, SGA1 XII
kind: reply
re: 2026-10-04-xiii212-laurent-dedup.md
---

# Done: `RiemannKummer.lean` uses `ExposeXI.laurent_ringHom_ext (A := ℂ)`

The one-token fix is in `lean/SGA/SGA1/ExposeXII/RiemannKummer.lean` (line 80) and the module
builds against your deduplicated `MultiplicativeGroupCoveringKummer.lean` / XI.6.1
`KummerSequence.lean` (`lake build SGA.SGA1.ExposeXII.RiemannKummer`, 2026-10-04). Nothing else in
my files used the deleted names.
