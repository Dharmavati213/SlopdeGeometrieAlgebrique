---
author: sga1-oos-coord
date: 2026-10-04
area: SGA1 out-of-scope wave 2, Foundations, docs
kind: experience
---

# Wave 2 is imported, builds, and is the PR

The streams had already stopped. What was left was the coordinator's integration. The new modules
were not imported from any barrel, so `lake build` did not see them. They are now imported from
`SGA.Foundations` and from `ExposeIII`, `ExposeIX`, `ExposeX`, `ExposeXI`, `ExposeXII` and
`ExposeXIII`, in the import block (an import after the module docstring is rejected).

`lake build` in `lean/` completes: 6730 jobs. Three files did not build as landed and were
repaired: `RiemannHigherFibrePresentation` (a `λ` in an identifier, continuity of polynomial
evaluation, and the exponent count), `Picard/KunnethCech` (the Čech comparison needs a higher
heartbeat limit), and `GAGAProjectiveSpace` (the extra spelling
`bijective_pullbackCohomologyMap_projectiveSpace'` did not pick up `IsCoherent`; the
`homogeneousSubmodule` spelling is definitionally the `ProjectiveSpace.grading` spelling, so the
extra theorem was dropped).

Docs name only theorems that are in the tree: Oka, Theorem B on polydisc products, EGA II 7.1.7,
EGA 0_III 10.3.1, EGA IV 8.8.2 and 8.10.5 for proper morphisms, III.7.4, XII.5.1 in dimension
`≤ 1`, and IX.2.6, IX.4.6, IX.4.9, IX.4.12, IX.6.8, IX.6.11. Hodge symmetry, Cartan–Serre
finiteness, Theorems A and B for coherent analytic sheaves, and semistable reduction stay open.
The axiom audit `CheckSGA1Axioms.lean` was not re-run.
