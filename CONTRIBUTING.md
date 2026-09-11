# Contributing

Two tracks: **translation** (English TeX) and **formalization** (Lean 4).
They share numbering and terminology, not files.

## Translation

1. Read [`translation/CONVENTIONS.md`](translation/CONVENTIONS.md).
2. Put a new exposé at `translation/SGA<n>/Expose<Roman>/`.
3. Keep Grothendieck’s numbering (`VI.6.1`, not a modern rewrite).
4. Do not add the French source PDF/TeX to the repo.
5. Rebuild the PDF (`make` in that directory) and tick the exposé in
   [`CHECKLIST.md`](CHECKLIST.md) (and the row in [`STATUS.md`](STATUS.md)).

Open an issue with the `translation` label before starting a long exposé,
so two people do not take the same one.

## Lean

1. Pin stays in `lean-toolchain`; do not bump Lean independently of mathlib.
2. After `lakefile.toml` changes: `lake update && lake exe cache get && lake build`.
3. New files go under `SGA/SGA<n>/` and must be imported from `SGA.lean`
   (or a barrel module that `SGA.lean` already imports).
4. Prefer mathlib names (`Functor.IsFibered`, `IsCartesian`, …) and record
   the SGA number in the module docstring.
5. No `sorry` in `lake build` on the default branch unless the lemma is
   explicitly marked as a statement-only stub in the docstring.
6. Tick the matching box in [`CHECKLIST.md`](CHECKLIST.md).

Mathlib already covers much of SGA 1 VI. Do not copy those files; import
them and add only what the exposé still needs.

## Pull requests

Use the PR template. One exposé or one cluster of lemmas per PR is enough.
Run `lake build` (and `make` if you touched TeX) before opening the PR.

## Code of conduct

See [`CODE_OF_CONDUCT.md`](CODE_OF_CONDUCT.md).
