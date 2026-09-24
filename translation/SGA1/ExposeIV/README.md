# SGA 1, Exposé IV — Flat morphisms

Full English draft of the whole exposé: the introduction and all six
sections, with proofs, footnotes, and both diagrams. It was translated
from the corrected SMF branch in two chunks. A second reviewer then
checked each chunk against the French (2026-09-24). Scholarly
proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-IV.tex`](SGA1-IV.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | Introduction; §1 Sorites on flat modules; §2 Faithfully flat modules; §3 Relations with completion; §4 Relations with free modules (IV.1–IV.4.4) |
| [`en-2.tex`](en-2.tex) | §5 Local criteria of flatness; §6 Flat morphisms and open sets (IV.5–IV.6.11) |
| [`SGA1-IV.pdf`](SGA1-IV.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeIV` from the repository root,
or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 6269–7382, from `\chapter{Morphismes plats}`
and `\label{IV}` up to, but not including, the chapter of Exposé V.
This covers original page markers 87–104.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and use the
shared package [`sga1-en.sty`](../sga1-en.sty). All non-index labels,
`\Ref`/`\eqref` keys, footnotes, and diagrams are kept. Exposé IV has
only internal references. The shared package would print a key from
another exposé with the source's number, as the SMF volume does:
`VIII~\Ref{VIII.6.2}` prints “VIII 6.2”. Original page numbers remain as
`% original p. N` comments. Indexes and SMF page-layout commands are
omitted.

House rules applied here as in the other new exposés: *n°* / *numéro*
is rendered “no.” (`\No`), as in “the present no.”, and *changement de
base* is rendered “change of base”, the Exposé VI term. After the
reviews, “base change” was replaced by “change of base” throughout
Exposés IV, V, VIII, IX, and X.

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

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

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

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, finds for each chunk the same non-index labels, reference
keys, footnotes, diagrams, displayed formulas, list items, and statement
environments as in the corrected French. For the whole exposé these are
45 labels, 59 references, 5 footnotes, 2 diagrams, and 47 displays.
Statement numbers are 1.1–1.3, 2.1–2.6, 3.1–3.2, 4.1–4.4, 5.1–5.9, and
6.1–6.11, as in the source. The wrapper compiles to a 15-page PDF with
no errors or undefined references.

A second reviewer checked both chunks against the French. There was one
fix, in en-2.tex (“present section” → “present no.”). The reviewer
confirmed all the translator's source points and added the query on the
proof of IV.2.6. These checks do not settle the mathematical questions
above; scholarly proofreading remains outstanding.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
