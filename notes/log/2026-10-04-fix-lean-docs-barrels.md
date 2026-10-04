---
author: fix-lean-docs
date: 2026-10-04
area: SGA1 IX, X, XI, XII, XIII (barrel docstrings), sga1-oos-coord
kind: handoff
---

# Docs fixes after the wave-1 checkers: barrels IX–XIII, stale docstrings, four XII corollaries

Applied the checker findings (`check_docs-*.json`) that concern the barrel docstrings, after
checking each against the Lean.

- IX barrel: IX.6.3, IX.6.6 (only the step over `Spec 𝒪̂_{S,s}`,
  `exists_isActAt_fromSpecCompletedStalk`), IX.6.10, IX.6.12 added to Not formalized; IX.5.2 in
  the connected case marked as the abstract Galois-category form.
- X barrel: new Not-formalized list (X.1.6, which the TeX labels `X.I.6`; the remarks X.2.5,
  2.7, 2.8, 2.13, 2.14, 3.5, 3.11; X.2.6; X.3.7 as a criterion; X.3.10); X.2.10 in the existence
  form used by `hH`; X.3.9 theorem names. `ExposeX/Purity.lean` no longer says X.3.8 is not
  formalized.
- XI barrel: the étale covering `A ⟶ A / K_n` is what is descended; uniqueness of the group law
  is with the marked point as origin; isogeny via `isFinite_coveringHom`/`surjective_coveringHom`;
  `exists_surjective_isMonHom_comp_eq_mulN_of_charZero` cited; Open names
  `SerreUnirationalSimplyConnectedStatement` and `UnirationalStructureSheafVanishingStatement`.
- XII barrel: (iii) read as flat and unramified, not shown to be a local isomorphism; Open and
  Not formalized now list `LocallyContractibleStatement`, XII.1.3.1, XII.2.5, `X^an` for
  non-separated `X`, XII.1.2 for analytic spaces, affine XII.2.2 in universes `≠ 0`.
- XIII barrel: "1-constructible stacks"; subsheaves need `f` universally closed; 1.4/1.8 for
  sheaves of groups in dimension `≤ 0` listed as not formalized; 4.6 hypotheses (k alg. closed,
  connected); the last sentence now names every open XIII `…Statement` in the barrel itself
  instead of claiming the other docs list them. `ExposeXIII/Abhyankar.lean`: 5.5 is stated,
  existence part only.
- New `ExposeXII/StatementCorollaries.lean` (in the barrel): `coveringFundamentalGroupStatement`
  (every universe), `fundamentalGroupComparison_of_riemannExistence` (affine XII.5.2 from XII.5.1
  alone), `separatingFunctionStatement`, `Points.closureComparisonStatement_zero` (universe 0
  only). `#print axioms`: propext, Classical.choice, Quot.sound. Statement docstrings in
  `RiemannExistence.lean`, `RiemannCurves.lean`, `Comparison.lean` point to them.
- `translation/SGA1/ExposeXIII/README.md`: elliptic-curve example now "of characteristic ≠ 2";
  the row now says SGA's statement (ii) is fine, the slip is in the proof's wording, and the
  over-strong Lean definition was this repo's.

Each barrel built on its own (`lake build SGA.SGA1.Expose<N>`). I did not run
`CheckSGA1Axioms.lean` (it needs the full `SGA` build).

For the coordinator: the open-statements drafts can drop the `CoveringFundamentalGroupStatement`
row and list `SeparatingFunctionStatement` as proved. The affine `Points.ClosureComparisonStatement`
is proved only in universe 0. docs/formalization.md and the Foundations README still have to name
the XIII statements the coordinator assigned to them.
