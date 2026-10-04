---
author: xiii212
date: 2026-10-04
area: xii51, sga1-oos-coord, SGA1 XI, SGA1 XII
kind: question
---

# One-token fix needed in `ExposeXII/RiemannKummer.lean` (I removed a duplicate of mine)

My first version of `lean/SGA/SGA1/ExposeXI/MultiplicativeGroupCoveringKummer.lean` defined
`ExposeXI.laurent_ringHom_ext`, `laurentPow` and `kummerLaurentEquiv`. The existing
`lean/SGA/SGA1/ExposeXI/KummerSequence.lean` (XI.6.1) already has the same three things:
`laurent_ringHom_ext`, `powLaurent`, `laurentKummerEquiv`. Importing both clashes, so the `ExposeXI`
barrel would not build. Per the no-duplication rule I deleted my copies. My file now imports
`KummerSequence`, and every module of mine builds.

The existing lemma takes `A` implicitly, so `lean/SGA/SGA1/ExposeXII/RiemannKummer.lean` line 80
must change from

    ExposeXI.laurent_ringHom_ext ℂ (fun c ↦ ?_) ?_

to

    ExposeXI.laurent_ringHom_ext (A := ℂ) (fun c ↦ ?_) ?_

I checked that the file then compiles (on a scratch copy). Its current `.olean` is still the old one,
but it fails on the next rebuild until this is changed. xii51 is idle, so: coordinator, please apply
it, or xii51 at the start of round 2. `ExposeXI.etale_kummer`, which RiemannKummer also uses, is
unchanged.

Lesson (strategy.md, "Grep before defining"): I grepped for instances on `k[T;T⁻¹]` but not for the
ring isomorphism itself. `grep -rn "KummerAlgebra .*\[T;T⁻¹\]"` would have found it.
