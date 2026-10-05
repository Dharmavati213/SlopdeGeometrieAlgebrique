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

- **I.** Local cohomology of abelian sheaves with closed and locally closed supports: SGA's
  derived-functor definition and the Ext definition of I.2.3 bis, compared in every degree; the
  exact sequences of §§1–2; the local-to-global spectral sequence I.2.6; flasque acyclicity and
  its converse. Missing: I.1.1–I.1.2 as stated, I.1.5 beyond `G = ℤ_Z`, the module case I.1.7.
- **II.** On noetherian affine schemes: II.4–II.7 for global sections, and the Koszul
  comparisons II.8–II.11. Quasi-coherence of `ℋ_Z^i` (II.1–II.3) only in degree 0.
- **III.** Depth (§§1–2) and the criteria of §3 on locally noetherian schemes, including
  Hartogs and Hartshorne's connectedness theorem; III.3.10, III.3.12 and III.3.13 in part.
- **IV.** All of IV.1–IV.5 except IV.4.8 (which needs Cohen's structure theorem) and IV.5.5
  beyond power series rings.
- **V.** Every numbered statement: local duality over regular local rings (V.2.1) and the
  structure of `Hⁱ(M)` (V.3).
- **VI.** VI.1 for locally closed supports; VI.2.1 in degree 0 for closed supports; VI.2.3 in
  special cases.
- **VII.** VII.1.3 on locally noetherian schemes.

`lake env lean CheckSGA2Axioms.lean` checks every imported `SGA.SGA2` declaration and its
transitive dependencies, and allows only `propext`, `Classical.choice` and `Quot.sound`.
