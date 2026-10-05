# Lean 4 library

A Lake project on mathlib `v4.34.0-rc2`; the Lean version is pinned in
[`lean-toolchain`](lean-toolchain).

```bash
lake exe cache get    # first time: download mathlib's compiled files
lake build
```

The root modules are `SGA.SGA1.ExposeI` … `SGA.SGA1.ExposeXIII` (no Exposé VII),
`SGA.Foundations` (prerequisites of SGA 1 that mathlib lacks), and `SGA.SGA2.ExposeI` …
`SGA.SGA2.ExposeVII`, all imported by [`SGA.lean`](SGA.lean). Each is a barrel: it imports the
files of its directory, and its module docstring lists them and what they prove. What is proved,
exposé by exposé and with declaration names, is in
[`../docs/formalization.md`](../docs/formalization.md).

Lean files are MIT-licensed, like the rest of the repository, and start with the MIT copyright
header; `lakefile.toml` sets mathlib's header linter to expect it. The exception is
`SGA/SGA2/ExposeII/ProjectiveComplexLift.lean`, adapted from mathlib and kept under Apache-2.0
(see [`../COPYRIGHT.md`](../COPYRIGHT.md)).

## SGA 1

Every exposé (I–VI, VIII–XIII) is formalized, following
[`SGA/SGA1/CONVENTIONS.md`](SGA/SGA1/CONVENTIONS.md): mathlib naming, and the SGA number at the
start of each docstring. In Exposés I, II, IV–VI, VIII and XI every numbered statement is
proved, up to the restrictions recorded in `docs/formalization.md`. III, IX, X and XIII are
mostly proved. XII covers §§1–2 and §3 on the spaces of points `X(ℂ)`, but not GAGA (§4) or the
comparisons that need coherent analytic sheaves. A statement that is not proved is kept as a
faithful `Prop`-valued `…Statement` definition, and the consequences SGA draws from it are
proved with it as a hypothesis.

Prerequisites that mathlib lacks are in [`SGA/Foundations/`](SGA/Foundations/), in mathlib's
namespaces and style. They include ampleness and quasi-projective morphisms, henselization and
étale stalks, differentials, the cohomology of proper morphisms, formal schemes, torsors and
étale sheaves, pro-objects, noetherian approximation and complex analytic spaces. The
Foundations [README](SGA/Foundations/README.md) lists the results that rest on theories SGA 1
quotes from elsewhere (Hodge theory, resolution of singularities, GAGA, SGA 4 étale cohomology)
and how far each is formalized.

`lake env lean CheckSGA1Axioms.lean` checks every declaration of the `SGA.SGA1.*` and
`SGA.Foundations.*` modules and allows only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## SGA 2

Exposés I–VII are partly formalized; VIII–XIV are not started. The SGA 2 files predate the
SGA 1 conventions and have their own naming and their own sheaf-cohomology infrastructure.

- **I.** Local cohomology `H_Z` of abelian sheaves, for closed and locally closed supports:
  SGA's derived-functor definition and the Ext definition of I.2.3 bis, compared in every
  degree; the exact sequences of §§1–2; the local-to-global spectral sequence I.2.6; flasque
  acyclicity.
- **II.** The affine comparisons II.(7.3)–(7.5), the Koszul comparison II.8, II.9 and II.11.
- **III.** Depth and the depth criteria for the vanishing of local cohomology; Hartogs-type
  extension and connectedness results (III.3.7–III.3.13).
- **IV.** Dualizing modules and functors, IV.1–IV.5, apart from parts of IV.5.5.
- **V.** Local duality over regular local rings, and the structure results of V.3.
- **VI.** Ext with supports: exact sequences, spectral sequences, VI.1.8–VI.1.9; VI.2.1 and
  VI.2.3 in degree 0 or in the affine case.
- **VII.** VII.1.3 on locally noetherian schemes.

`lake env lean CheckSGA2Axioms.lean` checks every imported `SGA.SGA2` declaration and its
transitive dependencies, and allows only `propext`, `Classical.choice` and `Quot.sound`.
