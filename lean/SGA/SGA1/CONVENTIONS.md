# SGA 1 Lean conventions

These rules apply to everything under `lean/SGA/SGA1/`. They deliberately
differ from the SGA 2 files: SGA 1 should read like mathlib.

## Layout

- One directory per exposé, `SGA/SGA1/Expose<Roman>/`, plus a barrel
  `SGA/SGA1/Expose<Roman>.lean` that imports every file of the exposé.
- Files are named by topic (`Smooth.lean`, `GaloisCategory.lean`), not by
  section number. The module docstring says which numbers of SGA 1 it covers.
- Namespace `SGA.SGA1.Expose<Roman>`.

## Statements

- Every declaration that corresponds to a numbered item of SGA 1 starts its
  docstring with the number: `/-- II.3.1: ... -/`. Parts are written
  `II.3.1 (ii)`; a direction is written `II.3.1, (i) ⇒ (ii)`.
- Names follow mathlib naming (`smooth_iff_flat_and_smooth_fibres`), never
  the SGA number and never words like *actual*, *genuine*, *original*.
- A statement must be the one in SGA 1, or say in its docstring exactly how
  it differs: extra hypotheses (noetherian, affine, separated, …), a special
  case, or one direction only. Do not give an SGA number to something weaker
  without saying so.
- Prefer mathlib's notions (`Smooth`, `Etale`, `Flat`, `Module.FaithfullyFlat`,
  `PreGaloisCategory`, `Functor.IsFibered`, …) over new definitions. Add a
  definition only when mathlib has none, and then prove it agrees with the
  expected notion when that is feasible.
- Do not restate mathlib theorems as new theorems with only a new name. If
  mathlib already proves an item, record it with a short `alias` or a
  one-line theorem whose docstring gives the SGA number. That is a legitimate
  entry and is how existing coverage is made visible.

## Proofs

- No `sorry`, `admit`, `axiom`, `native_decide`, or `implemented_by`.
  `lake env lean CheckSGA1Axioms.lean` from `lean/` must pass.
- When a result is out of reach (for example it needs the Grothendieck
  existence theorem, GAGA or étale cohomology that mathlib lacks), its precise
  statement may be recorded as a `Prop`-valued definition:

  ```lean
  /-- X.3.1 (statement only): ... -/
  def HomotopyExactSequenceStatement : Prop := ∀ ..., ...
  ```

  The name ends in `Statement`. It must be the faithful statement, not a
  vacuous one. Prove special cases or the formal part of the argument
  when possible, and use the statement as a hypothesis in theorems that
  deduce the consequences SGA draws from it.
- Keep proofs readable: short `have`s, no giant `simp only` dumps kept only
  because they happened to work, `set_option maxHeartbeats` only with a
  comment saying why.

## Missing prerequisites

If a numbered item needs something mathlib does not have, build that
prerequisite instead of stopping at a `Statement`:

- A small prerequisite used by one exposé goes in that exposé's directory,
  in its own file.
- A general theory used by several exposés (quasi-affine and quasi-projective
  morphisms, relative ampleness, formal schemes, torsors and non-abelian H¹,
  étale fundamental group of a scheme, …) goes in `lean/SGA/Foundations/`,
  barrel `SGA.Foundations`. These files are written as if for mathlib: mathlib
  namespaces (`AlgebraicGeometry`, `CategoryTheory`, …), mathlib naming, no SGA
  numbers in names, and a docstring citing the standard reference (EGA,
  Stacks Project tag).

A `Statement` is acceptable only while its prerequisite is being built;
once the prerequisite exists, prove it.

## Documentation

- Module docstrings are short: what SGA says, what is formalized, what is
  missing. Put coverage tables in `docs/formalization.md`, not in Lean files.
