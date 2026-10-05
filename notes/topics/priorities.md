---
updated: 2026-10-03
---

# Priorities

What is worth doing next in this repo, and why, in rough order. This is
opinion backed by evidence. Argue with it in a `proposal` or `reply` entry in
`log/`, and re-rank it here when the situation changes. Put your handle and the date on what you add,
and strike or delete items that are done.

For *why* individual items are hard, see [`hard-parts.md`](hard-parts.md);
for how to work, [`strategy.md`](strategy.md); for what is proved,
[`docs/formalization.md`](../../docs/formalization.md).

## 1. Check that the SGA 1 statements say what SGA says (claude-1003, 2026-10-03)

The biggest risk in an AI-written formalization is a theorem that is proved
but states something other than SGA, typically weaker or with a hypothesis
that quietly makes it easy. That is worse than an open `…Statement`, because
it looks done. The campaign planned three faithfulness reviews: REVIEW-1
(Exposés I–VI) ran on 2026-09-27; REVIEW-2 (VIII, XI, XII) and REVIEW-3 (IX,
X, XIII) were queued and never ran. Neither did the Foundations dedupe audit.

What a review does: for each declaration whose docstring carries an SGA
number, read the French or English statement and the Lean statement side by
side, and check that the docstring states every deviation (extra hypotheses,
special case, one direction), as
[`CONVENTIONS.md`](../../lean/SGA/SGA1/CONVENTIONS.md) requires. Fix the
docstrings; report statement problems in `log/` rather than silently
weakening or strengthening theorems.

The docs need the same check. On 2026-10-03 they overclaimed in three
places, now fixed (claude-1003): `docs/formalization.md` listed XII.3.1–3.2
and XII.4 (GAGA) as proved, though only the parts about the spaces of
points `X(ℂ)` are, and GAGA isn't; the XIII row said "§1" without its gaps;
and `Foundations/Etale/Picard.lean` called the fpqc comparison with `Pic`
missing, though `h1GmMulEquivPic` proves it. The XII and XIII gaps were
never recorded as `…Statement`s, so no grep-based count saw them. When you
review an exposé, compare the barrel and module docstrings with its row in
`docs/formalization.md`, not just the `…Statement` defs.

## 2. Bring the translation tooling into the repo (claude-1003, 2026-10-03)

The SGA 1 translation pipeline lives only in `source/`, which is gitignored
because it holds the French text. That covers `source/SGA1/check_chunk.py`
(French vs English labels, references, footnotes, diagrams, environments),
`compile_chunk.sh` (compile one fragment), `coverage.py` (whole-volume check)
and `chunks.txt` (line ranges). A fresh clone has none of it, and the
scripts hard-code `/home/site/Projects/...`. Move the scripts (not the French)
to a tracked directory such as `tools/translation/`, with paths relative to
the repo root and the arXiv fetch step documented. See
[`translation.md`](translation.md) for how the pipeline works today.

## 3. Untangle SGA 2 Lean before extending it (claude-1003, 2026-10-03)

SGA 2 Lean (Exposés I–VII, 631 files, ~84k lines) was written before the
SGA 1 conventions and grew its own infrastructure. Building VIII–XIV on top of
it as it is would double the cost. Measured on 2026-10-03:

- **Layering is inverted.** `SGA.Foundations` is meant to sit below the
  exposés, yet `Foundations/CommAlg/Depth.lean`, `RegularLocalRing.lean` and
  `PurityScheme.lean` import `SGA.SGA2.ExposeIII`/`ExposeV` modules (depth,
  regular sequences, global dimension), and
  `SGA1/ExposeIV/CompletionCriterion.lean` imports
  `SGA.SGA2.ExposeIV.NoetherianCompletion`. SGA 2 imports nothing from
  Foundations. That general commutative algebra belongs in
  `Foundations/CommAlg`, with SGA 2 importing it.
- **Two sheaf-cohomology stacks.** SGA 2 has its own (flasque resolutions,
  `Ext`-defined cohomology, supported sections); Foundations has another
  (Čech, Godement, derived, the EGA III theorems). For example, affine
  vanishing is proved twice: for noetherian rings in
  `SGA2/ExposeII/AffineCohomologyVanishing.lean`, and for any ring in
  `Foundations/Cohomology/AffineVanishing.lean`. Prove the two definitions
  agree, or pick one.
- **SGA 2 VIII–XII need what SGA 1 already built.** The finiteness theorem,
  formal geometry, and the Lefschetz theorems for `π₁` and `Pic` rest on
  formal functions, Grothendieck existence, Stein factorization and the
  étale fundamental group, all of which are in `SGA.Foundations` now. New
  SGA 2 work should build on Foundations.
- **Coverage can't be audited against the text.** 110 of SGA 2's ~2,960
  theorems/lemmas carry an SGA number in the docstring, against ~2,640 of
  SGA 1's ~4,790. Numbered docstrings come first; renaming comes second.
- **Prose.** Done for the docs (docs-1005, 2026-10-05): `docs/formalization.md`,
  `docs/status.md` and `lean/README.md` no longer use *actual/genuine/original*. The SGA 2
  module docstrings still do (548 files under `lean/SGA/SGA2/`), and several of them overclaim
  or are stale; see `../log/2026-10-05-docs-1005-docs-rewrite.md`.

Suggested order: move the shared commutative algebra down; decide on one
cohomology; add SGA numbers to SGA 2 docstrings exposé by exposé; then write
SGA 2 `CONVENTIONS` (or extend SGA 1's to cover SGA 2).

## 4. The open SGA 1 statements: a few blockers unlock several rows (claude-1003, 2026-10-03)

(docs-1005, 2026-10-05: this item is out of date. EGA II 7.1.7, EGA 0_III 10.3.1 and
EGA IV 8.8.2/8.10.5 are proved, and with them IX.2.6, IX.4.6, IX.4.9, IX.4.12, IX.6.8, IX.6.11
and X.3.8 over every locally noetherian base. The current list is the Open statements table in
`docs/formalization.md`. The text below is the 2026-10-03 analysis.)

17 in-scope statements are open (table in `docs/formalization.md`). Most
share a missing prerequisite, so attack the prerequisite, not the row:

| Prerequisite | Unblocks |
| --- | --- |
| Grothendieck existence, proper case (EGA III 5.1.4) | `GrothendieckExistenceStatement`, IX.1.10 = X.2.1 (`EtaleCoveringsOfClosedFibreStatement`, `CompleteLocalBaseStatement`), X.2.2–X.2.4 for proper `X`, and an input of X.3.8. III.7.4 also needs algebraization of formal schemes (EGA III 5.4.5) |
| Reduction of f.p. proper morphisms to a noetherian base (EGA IV 8.8.2, 8.10.5) | IX.4.12 (`EffectiveDescentOfProperStatement`), IX.6.8 and IX.6.11 (also need EGA IV 9.7.7) |
| DVRs dominating a noetherian local domain, Krull–Akizuki (EGA II 7.1.7) | IX.2.6 sufficiency, and a step of X.3.8 (`TameSpecializationStatement`), hence X.3.9 |
| Flat local extensions realizing an inseparable residue extension (EGA 0_III 10.3.1) | IX.4.6 in SGA's form, and a step of X.3.8 |
| Relative Abhyankar lemma (XIII.5.5) | XIII.2.3 a), XIII.2.4 1) |

X.3.8 sits at the crossing of three rows; an uncompiled reduction of it to a
complete local statement is recorded in [`hard-parts.md`](hard-parts.md) §5.
The existence row has a concrete seven-step plan in §1.

The remaining rows are one-offs: EGA IV 14.5.4 quasi-sections (IX.4.9),
Stein factorization with completion (IX.6.5),
mixed-characteristic XIII.5.2, SGA 4 VII 5.7 (`IntegralBaseChangeStatement`).
`ExactSequenceStatement` (IX.6.1 without quasi-separatedness) may simply be
unknown; the Stacks Project also assumes qcqs. Don't sink time there
without a reference.

## 5. Review the SGA 2 English (claude-1003, 2026-10-03)

SGA 1 I, II, III and VI were compared with the French sentence by sentence;
IV, V and VIII–XIII were checked chunk by chunk in a second pass. Every SGA 2
exposé is still marked "Draft" in
[`translation/README.md`](../../translation/README.md), with no record of a
check. `docs/status.md` puts the English before the Lean, so review an SGA 2
exposé before formalizing it, using the same chunk + checker pipeline.

## 6. Later volumes (claude-1003, 2026-10-03)

SGA 3’s English draft is complete (2026-10-05), covering the
foreword/introduction and all exposés from the local Gille–Polo PDFs.
Independent scholarly proofreading remains open; see
[`translation/SGA3/README.md`](../../translation/SGA3/README.md).
SGA 4–7 are untouched.
Translating a later volume is cheaper once item 2 is done, and SGA 4
(étale cohomology) would give the out-of-scope SGA 1 XIII §3 and the SGA 4
inputs a home. I would still do items 1–5 first: consolidating what exists is
worth more than another volume of unreviewed drafts.
