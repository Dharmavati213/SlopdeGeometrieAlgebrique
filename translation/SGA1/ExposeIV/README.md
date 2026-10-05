# SGA 1, Exposé IV — Flat morphisms

Complete English draft of the exposé: the introduction and all six
sections, with proofs, footnotes, and both diagrams. Translated in two
chunks from the corrected SMF branch of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2); a second
reviewer checked each chunk against the French (2026-09-24). Scholarly
proofreading is outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-IV.tex`](SGA1-IV.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | Introduction; §1 Sorites on flat modules; §2 Faithfully flat modules; §3 Relations with completion; §4 Relations with free modules (IV.1–IV.4.4) |
| [`en-2.tex`](en-2.tex) | §5 Local criteria of flatness; §6 Flat morphisms and open sets (IV.5–IV.6.11) |
| [`SGA1-IV.pdf`](SGA1-IV.pdf) | Compiled English draft |

Build: `make -C translation/SGA1/ExposeIV` (TeX Live with `latexmk`,
`amsbook`, `xy`, `mathrsfs`, `enumitem`, `hyperref`); `make tex` builds
every exposé.

## Source and translation choices

`smf_doc-math_3_01.tex` (corrected branch, `orig = false`), lines
6269–7382: from `\chapter{Morphismes plats}` and `\label{IV}` up to, but
not including, the chapter of Exposé V; original page markers 87–104.
The French TeX and PDF are not in this repository.

The fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md), section
“SGA 1 — front matter and Exposés IV, V, VIII–XIII” (labels, reference
keys, page markers, omitted indexes), and use the shared package
[`sga1-en.sty`](../sga1-en.sty). Exposé IV has only internal references.
*n°* / *numéro* is rendered “no.” (`\No`), as in “the present no.”, and
*changement de base* is rendered “change of base”, the Exposé VI term.

Exposé IV terminology:

| French | English |
| --- | --- |
| plat; fidèlement plat | flat; faithfully flat |
| sorites (sur les modules plats) | sorites (on flat modules) |
| critères locaux de platitude | local criteria of flatness |
| complété | completion |
| module libre | free module |
| séparé pour la topologie … | separated for the … topology |
| universellement ouvert | universally open |
| constructible | constructible |
| foncteurs dérivés à droite | right derived functors (as printed; see below) |

## Source points for scholarly review

Apparent slips in the corrected French TeX, kept as printed per
[`CONVENTIONS.md`](../../CONVENTIONS.md).

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| IV.1, opening | `Tor^A_i` called the “right derived functors” | They are the left derived functors of `⊗`. |
| IV.1.2 (ii) | “if `M_n` is flat over `A_n` for every maximal ideal `n` of `B`, `M_n` is flat over `A` (or … over `A_m` …) then `M` is `A`-flat” | The statement is garbled: `A_n` is undefined, and the clauses are joined without a connective. |
| IV.2, opening | A category `𝒞` is used | Only “a functor from one category into another” has been introduced. |
| IV.2.4 | The prime `𝔭` | Not introduced in the statement; it is carried over from IV.2.3. |
| IV.2.6 (ii bis) | “every maximal ideal is induced by an ideal of `B`” | The surrounding arguments speak of a prime ideal of `B`. |
| Proof of IV.2.6 | “the second condition (iv bis)” | Condition (iv) may be meant. |
| Proof of IV.5.2 | The low-degree exact sequence has `Tor_1^A(M,B) ⊗_A N` | `⊗_B N` is expected. |
| Proof of IV.5.4 | `\eqref{IV.5.1}` | The key is a proposition, so the number prints in parentheses. |
| IV.5.8 | Conclusion “`M` is `Â`-flat” | Presumably `M̂` is meant. |
| Proof of IV.6.4 | “criterion IV.6.2” | IV.6.3 appears to be meant. |
| Proof of IV.6.5 | “`f(X)` constructible by IV.6.1” | Chevalley's theorem is IV.6.2. |
| Remarks after IV.6.6 | “conditions of IV.6.5”, “flatness hypothesis of IV.6.5” | IV.6.6 appears to be meant. |
| Proof of IV.6.8 | `A/\goth(q)` (prints `A/(q)`); the proof ends “which proves the corollary” | A typo for `\goth{q}`; the statement is a lemma. |
| Proof of IV.6.9 | `(A, B_{q'}, q, M_{q'})` | Localizations at `p'` are presumably meant. |

## Validation

`source/SGA1/check_chunk.py` (a local script, not in the repository)
compared each chunk with the corrected French and found the same
non-index labels, reference keys, footnotes, diagrams, displayed
formulas, list items, and statement environments. For the whole exposé
these are 45 labels, 59 references, 5 footnotes, 2 diagrams, and
47 displays. Statement numbers are 1.1–1.3, 2.1–2.6, 3.1–3.2, 4.1–4.4,
5.1–5.9, and 6.1–6.11, as in the source. The wrapper compiles to a
15-page PDF with no errors or undefined references.

The second reviewer made one fix, in `en-2.tex` (“present section” →
“present no.”), confirmed all the translator's source points, and added
the query on the proof of IV.2.6.

License: [`../../LICENSE`](../../LICENSE) (MIT for the translator's
contribution).
