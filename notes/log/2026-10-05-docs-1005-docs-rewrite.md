---
author: docs-1005
date: 2026-10-05
area: docs, README, SGA1 IX X XIII, SGA2 I–VII, Foundations README, translation READMEs
kind: experience
---

# Docs rewrite: the prose was hiding overclaims and stale gaps

The owner asked for the docs to be made less sloppy (keeping the opening of `README.md`).
Rewritten: `README.md` below the opening, `docs/status.md`, `docs/formalization.md`,
`lean/README.md`, `lean/SGA/Foundations/README.md`, `translation/README.md`,
`translation/CONVENTIONS.md` (index and heading levels), every SGA 1 and SGA 2 exposé README,
`.github/CONTRIBUTING.md`, `COPYRIGHT.md`, `CITATION.cff`. No Lean or TeX changed.

The SGA 2 sections were the worst: ~700 uses of *actual/genuine/original/literal*, results listed
three times (table, "Remaining gaps", "Next dependencies"), and a status checklist of ~950 lines.
Each exposé now has a short modelling paragraph, a Proved table and an Open list in
`docs/formalization.md`, and a dozen sub-items in `docs/status.md`.

Reading the Lean while compressing found claims the old prose got wrong.

Overclaims (now listed as open or restricted):
- II.7 "the local-to-global spectral sequence degenerates": `II_7_affine_ordinary_vanishing` is
  only affine vanishing. `II_6_a_affine`, `II_6_b_affine`, `VI_2_3_structure`, `VI_2_3_sheaf` are
  aliases of global-section statements, not sheaf maps.
- III.2.11: flat base change gives `depth ≤` (`III_2_11_flat`); equality needs faithful flatness.
- III.3.12 (`III_3_12`) is only the range `i > m` for `Y = V(f₁…f_m)`, where both sides hold.
- II.10 is proved only where both sides hold outright.
- I.2.6 "identified with the Grothendieck spectral sequence":
  `grothendieckSpectralSequenceOfSupportedSheaf` is the same sequence under another name. The
  Leray and witness-change comparisons are on E₂ terms only.
- I.1.1–I.1.2, I.1.5 beyond `G = ℤ_Z`, and the module I.1.7 were ticked but are not formalized.

Understatements (now listed as proved):
- X.3.8 over every locally noetherian base (`tameSpecializationStatement`,
  `ExposeX/TameLiftingGeneral.lean`), hence X.3.9.
- `affineLineOpenInvarianceStatement`, so the XIII.4.6 results for normal `X`, `Y` in
  characteristic 0 are unconditional.
- X.2.10 in existence form (`exists_hyperplane_section`), so X.2.9 follows from the curve case
  alone (`topologicallyFiniteStatement_of_curve`).
- IV.5.5's residue pairing and `v` for power series rings.
- Oka and Theorem B (formalization.md called them "stated, not proved").
- SGA 2 VII.1.3 was shown as "—" in the status table. Every numbered statement of SGA 2 V is
  proved, so V is now ticked.

Left for someone else:
- Stale Lean docstrings, not edited:
  - `ExposeX/TameSpecialization.lean` (says X.3.8 is open in general);
  - `ExposeIX/ExactSequence.lean` (`ProperDescentStatement`, `GeometricFibresStatement`);
  - SGA 2 `DerivedFunctors.lean`, `LocalToGlobalSpectralSequence.lean`, `ExtensionByZero.lean`,
    `ExactSequences.lean`;
  - the alias docstrings above.
- The SGA 2 barrel docstrings have the same prose problems the docs had.
- Every SGA 2 TeX wrapper says retained misprints "are recorded in the accompanying README". None
  are; the READMEs now say so. Fixing the notice means rebuilding the PDFs.
- `notes/topics/priorities.md` item 4 is out of date (marked). `hard-parts.md` was already current
  on X.3.8.

What I'd do next: re-read the SGA 2 barrel docstrings against the new `docs/formalization.md`
and fix the overclaiming aliases. When a doc says "proved", grep for the theorem and read its
type. Several "proved" entries above were aliases or renamings.
