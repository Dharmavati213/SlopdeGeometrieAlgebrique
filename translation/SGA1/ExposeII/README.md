# SGA 1, Exposé II — Smooth morphisms: generalities, differential properties

Full English draft: the opening convention, **all five sections**,
and the closing errata, including proofs, footnotes, and both diagrams.
Scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-II.tex`](SGA1-II.tex) | Standalone wrapper, macros, and translation notice |
| [`en-01-03.tex`](en-01-03.tex) | Opening convention; generalities; smoothness criteria; permanence |
| [`en-04-08.tex`](en-04-08.tex) | Differential properties: sequences of $\Omega^1$; 4.1–4.8 |
| [`en-04-09-13.tex`](en-04-09-13.tex) | Jacobian-type criteria 4.9–4.13 |
| [`en-04-14.tex`](en-04-14.tex) | Remarks 4.14 (regular immersions and regular sequences) |
| [`en-04-15-19.tex`](en-04-15-19.tex) | Regular immersions of a smooth subprescheme; principal parts; 4.15–4.19 |
| [`en-05.tex`](en-05.tex) | The case of a ground field; errata |
| [`SGA1-II.pdf`](SGA1-II.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeII` from the repository root,
or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, and `hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, from `\chapter{Morphismes lisses:...}` and
`\label{II}` up to, but not including, the chapter beginning
`\chapter{Morphismes lisses: propri\'et\'es de prolongement}` and
`\label{III}`.
This covers printed SMF pages 25–47 and original page markers 29–57.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md):
retain the corrected branch, all non-index labels, proofs, both diagrams, and translated
footnotes; omit indexes and source pagination machinery. Original page
numbers remain as comments. The standalone wrapper is separate from
the translation fragments.

Exposé II terminology:

| French | English |
| --- | --- |
| préschéma | prescheme |
| schéma | scheme (the source's distinction is retained) |
| lisse | smooth |
| essentiellement lisse | essentially smooth |
| simple (ancienne terminologie) | simple (old terminology) |
| net / non ramifié | net / unramified |
| étale | étale |
| plat | flat |
| dimension relative | relative dimension |
| immersion régulière | regular immersion |
| différentiablement lisse | differentially smooth |
| faisceau conormal | conormal sheaf |
| application tangente | tangent map |
| système régulier de générateurs | regular system of generators |
| suite régulière | regular sequence |
| profondeur / coprofondeur | depth / codepth |
| base de transcendance séparante | separating transcendence basis |

The historical synonym **simple** is retained where the source uses it
as the old name for smooth. The author's word *multiplodoque* is
retained. Informal asides and requests to supply arguments are
translated as part of the text.

The corrected source assigns **1.1** to both a definition and the next
proposition, and **4.18** to both a corollary and the next block of
remarks. Both numbers are retained, with the original labels
`II.1.1` / `prop:II.1.1` and `II.4.18` / `rem:II.4.18` and distinct
PDF destinations.

References within this draft use `\ref`. For references beyond its
scope, `\SourceRef{source-label}{printed-number}` preserves the source
key and prints the original number without inventing a destination;
it uses `\ref` if that label later becomes available.

## Source points for scholarly review

These apparent issues are present in the corrected French TeX and the
matching PDF. They have been retained in the translation, in accordance
with the convention against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| After II.1.3 | $Z[t_1,\dots,t_n][s_1,\dots,s_m]=Z[t_1,\dots,s_m]$ | The $t_i$ disappear on the right-hand side. |
| II.2.3 | The argument stops once $\mathcal{O}_{y'}\to\mathcal{O}_x$ is étale | Smoothness of $f$ is not restated. |
| II.2.4 | Fiber of $f$ “above $x$” | The point of the base would ordinarily be $y$. |
| II.4.5 | A point $s$, projection of $x$ and $y$ on $S$ | Unused in the statement that follows. |
| II.4.10, II.4.11 | Citations of “4.8 (i)” / neighborhood “of $X$” | Corollary 4.8 has no enumerated items; the neighborhood is of $x$ in the surrounding text. |
| II.4.13 | Smooth over $S$ “at $X$” | Compare the point $x$ in the setup. |
| II.4.14 | Relative dimension $n$, then a subprescheme of $S[t_1,\dots,t_n]$ “with $n=m+1$” | The integer $m$ is not introduced. |
| Proof of II.4.15 | `$g\colon X_1\to X$`; mixed indices $\cal{J}'_x$ / $\cal{J}'_{x'}$ | Compare $X'$ and $x'$ in the criterion being applied. |
| II.4.18 | “$S$ is a sheaf of $\mathbf{Q}$-algebras” | $S$ is the base prescheme in the surrounding text. |
| II.5.6 | Transcendence degree “over $K$ of its residue field”; $\it{\Omega}^1_{X/k}$ as a $K$-module | $X$ is not in the setup; the module is that of $K/k$. |
| II.5.7 | $\Omega^1_{K/k}$ a free $k$-module | The rank is as a $K$-module in 5.6. |
| II.5.10 | A point $x$ of a prescheme of finite type over $k$ | The prescheme $X$ is not named in the setup. |

Validation: `make tex` succeeds. All 65 non-index source labels
(including the numbered statements, the duplicate 1.1 and 4.18, the
equation tags, and the errata), ten footnotes, and both diagrams were
checked against the corrected source. Compiled statement numbers match
the original, including the repeated 1.1 and 4.18. Equation tags match
the source (`1.1`--`1.3`, `3.1`--`3.2`, `4.1`--`4.6` with bis tags,
`5.1`). The PDF build has no TeX warnings, unresolved references, or
duplicate destinations. Representative pages and the diagrams were
visually checked.

These checks do not settle the mathematical questions above;
scholarly proofreading remains outstanding.

## Continuation

The next untranslated exposé is **III — Smooth morphisms: extension
properties**. Keep source review of Exposé II distinct from
translation coverage. Lean for this exposé has not been started.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
