# SGA 1, Exposé XII — Algebraic geometry and analytic geometry

By Mme M. Raynaud, after unpublished notes of A. Grothendieck.

Full English draft of the whole exposé: the introduction, all five
sections, and the bibliography, with proofs, footnotes, and all diagrams.
It includes M. Raynaud's 2003 remark XII 5.6 (MR) and the 2003 starred
footnote in §1. It was translated from the corrected SMF branch in three
chunks. A second reviewer then checked each chunk against the French
(2026-09-24). Scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-XII.tex`](SGA1-XII.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | Author line and introduction; §1 Analytic space associated with a scheme; §2 Comparison of the properties of a scheme and of the associated analytic space (XII.1.1–XII.2.6) |
| [`en-2.tex`](en-2.tex) | §3 Comparison of the properties of morphisms; §4 Cohomological comparison theorems and existence theorems (XII.3.1–XII.4.6) |
| [`en-3.tex`](en-3.tex) | §5 Comparison theorems for étale coverings (XII.5.0–XII.5.5, and Remark 5.6 (MR)); bibliography |
| [`SGA1-XII.pdf`](SGA1-XII.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeXII` from the repository
root, or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 19357–20813, from
`\chapter{G\'eom\'etrie alg\'ebrique et~g\'eom\'etrie~analytique}` and
`\label{XII}` up to, but not including, the chapter of Exposé XIII.
This covers original page markers 311–343.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and use the
shared package [`sga1-en.sty`](../sga1-en.sty). All non-index labels,
`\Ref`/`\eqref`/`\cite` keys, footnotes, and diagrams are kept.
Optional `\cite` arguments keep the source's lower-case abbreviations
(th., cor., prop.). The bibliography keeps
`\begin{thebibliography}{10}{XII.6}` (numbered section 6), and its
entries are kept as printed. References to other exposés print the
source's numbers: `V~\Ref{V.6.10}` prints “V 6.10”, as in the SMF
volume. Original page numbers remain as `% original p. N` comments.
Indexes and SMF page-layout commands are omitted.

House rules applied here as in the other new exposés: *n°* / *numéro*
is rendered “no.” (`\No`), as in “In nos. 2 and 3”, and *changement de
base* is rendered “change of base”, the Exposé VI term. The
harmonization that replaced “base change” after the reviews concerned
Exposés IV, V, VIII, IX, and X; this exposé needed no change.

**Remark 5.6 (MR).** The SMF prints M. Raynaud's 2003 remark
(`remarqueMR`) between bold brackets and without a number. Here it is
printed as “Remark 5.6 (added in 2003 (MR))”, for three reasons: its
label `XII.5.6` names that number, the remark closes §5, and the
translated Preface refers to it as “XII 5.6”. The comment on `remarkMR`
in [`sga1-en.sty`](../sga1-en.sty) explains this. The 2003 footnote in
§1 keeps its `*` mark.

Grothendieck's calligraphic letters (`\cal`) and the second script
alphabet (`\othercal`) for analytic objects are kept as the source uses
them, including where the source mixes them (see below).

Exposé XII terminology:

| French | English |
| --- | --- |
| espace analytique (associé) | (associated) analytic space |
| schéma localement de type fini | scheme locally of finite type |
| « dictionnaire » | “dictionary” |
| théorèmes de comparaison; théorèmes d'existence | comparison theorems; existence theorems |
| revêtement étale fini | finite étale covering |
| adhérence schématique | scheme-theoretic closure |
| résolution des singularités | resolution of singularities |
| Module, Algèbre (cohérent(e)) | (coherent) Module, Algebra (capital kept) |

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| XII.1.3.1 and proof of XII.2.1 | `\eqref{XIII.1.1}`, which cites XIII 1.1 | Theorem XII.1.1 is meant. |
| XII.1.3.1 | “`O_{X^an}`-Module `F`” | An `O_X`-Module is required. |
| Proof of XII.2.4 | `\cal{F}` | Printed with `\cal` where `\othercal` would be expected (as in XII.2.5). |
| XII.2.5 | The lemma uses `\cal{P}`, `\cal{Y}`, `\cal{U}`, `\cal{E}^n` | `\othercal` letters are used elsewhere for analytic objects. |
| Proof of XII.2.5 | The lemma is called “the proposition” | Wrong statement type. |
| Proof of XII.3.1 (iv)–(vi) | Only regular fibers are cited as open (EGA IV 12.1.7) | No “resp. normal, resp. reduced”. |
| XII.3.2 (iv) | Factorization `X --i--> \overline T --j--> J`; `\overline T` called “scheme-theoretic closure of `f`” | The target should be `Y`; the closure of `X` in `Y` (or of `T`) is expected. |
| Proof of XII.4.4, 1) | Target `H^0(X^an, SheafHom_{O_X}(F, G))` | The superscript `an` is missing. |
| XII.4.4, display (*) | Condition “`q ≠ 1`”; `an` on a global Ext group; `\isomto` | The condition looks like a slip; `\isomto` is used for a map still to be shown bijective. |
| Proof of XII.5.1, 2) c) | `R'` “extends the étale covering `X'^an`” | `X'` is not yet built; `\othercal X'` is meant. |
| Proof of XII.5.3, last paragraph | “since `f` is finite”; `p` | No `f` is defined; `p` denotes both the projection and the number of coordinates. |
| Proof of XII.5.4 | “`F_1` the coherent Algebra defined by `F_1`” | Should be “defined by `X_1'`”. |
| Bibliography [8] (Hironaka) | “Ann. of Math. **39** (1964), p. 109–236” | The volume is 79; the pages are 109–203 and 205–326. |
| French slips | English “and” in the first line of the proof of XII.5.3; “que l'on muni”, “il est de même de” (§§1–2) | These do not affect the English. |

## Validation

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, finds for each chunk the same non-index labels, reference
and citation keys, footnotes, diagrams, displayed formulas, list items,
and statement environments as in the corrected French. For the whole
exposé these are 35 labels, 45 references, 38 citations, 3 footnotes,
6 diagrams, and 95 displays. The wrapper compiles to an 18-page PDF with
no errors or undefined references.

A second reviewer checked all three chunks against the French:

- en-1.tex: six fixes (five optional `\cite` arguments restored to the
  printed lower-case th./cor./prop., and “In nos. 2 and 3”);
- en-2.tex: one fix (“this section” → “this no.” at the start of §4);
- en-3.tex: no fixes.

The reviewer confirmed all the translator's source points and added the
`\cal{F}` in the proof of XII.2.4 and the French slips. These checks do
not settle the mathematical questions above; scholarly proofreading
remains outstanding.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
