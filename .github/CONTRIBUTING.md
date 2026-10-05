# Contributing

There are two tracks: **translation** (English TeX) and **formalization**
(Lean 4). They share numbering and terminology, not files.

Claim work by [opening an
issue](https://github.com/Dharmavati213/SlopdeGeometrieAlgebrique/issues/new/choose)
with the Translation or Formalization template, saying what you will do
(which SGA and exposé, and for Lean which section or statement). Check
[`docs/status.md`](../docs/status.md) and the open issues first, so that two
people do not take the same text. An exposé is translated before it is
formalized.

## Translation

1. Read [`translation/CONVENTIONS.md`](../translation/CONVENTIONS.md) (and, for
   SGA 3, [`translation/SGA3/CONVENTIONS.md`](../translation/SGA3/CONVENTIONS.md)).
2. Put a new exposé in `translation/SGA<n>/Expose<Roman>/`, with a `Makefile`
   like the existing ones.
3. Keep Grothendieck's numbering (`VI.6.1`, not a modern renumbering).
4. Do not add the French source (PDF or TeX) to the repository.
5. Translate misprints as printed and list them in the exposé's README.
6. Rebuild the PDF (`make tex`, or `make` in the exposé's directory) and tick
   the exposé in [`docs/status.md`](../docs/status.md).

## Lean

1. Change `lean/lean-toolchain` only together with the mathlib version.
2. After changing `lean/lakefile.toml`, run from `lean/`:
   `lake update && lake exe cache get && lake build`.
3. Put new files under `lean/SGA/SGA<n>/` and import them from `lean/SGA.lean`
   or from a barrel module that it imports. Prerequisites that mathlib lacks
   go under `lean/SGA/Foundations/`, in mathlib's namespaces and style.
4. Use mathlib's names (`Functor.IsFibered`, `IsCartesian`, …) and put the SGA
   number in the docstring. For SGA 1, follow
   [`lean/SGA/SGA1/CONVENTIONS.md`](../lean/SGA/SGA1/CONVENTIONS.md).
   New files start with the copyright header of the existing ones
   (`Released under MIT license as described in the file LICENSE.`).
5. No `sorry`, `admit` or new axioms. A statement that cannot be proved yet is
   recorded as a `Prop`-valued `…Statement` definition. Before opening a pull
   request, run `lake env lean CheckSGA1Axioms.lean` (or `CheckSGA2Axioms.lean`)
   from `lean/`.
6. Tick the matching box in [`docs/status.md`](../docs/status.md) and update
   [`docs/formalization.md`](../docs/formalization.md).

Mathlib already covers much of the language SGA uses (fibered categories,
descent, étale and smooth morphisms, …). Import it rather than copying it. If
you adapt mathlib code, keep its Apache-2.0 header and authors.

## Pull requests

Use the pull request template. One exposé, or one group of related lemmas, per
pull request. There is no CI, so run `make lean` (and `make tex` if you changed
TeX) before opening it.

## License

By contributing you agree that your contribution is licensed under the
[MIT License](../LICENSE), like the rest of the repository.

## Code of conduct

See [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md).
