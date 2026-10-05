# SGA 1, Exposé II — Smooth morphisms: generalities, differential properties

Complete English draft of the exposé: the opening convention, all five
sections, and the closing errata, with proofs, footnotes, and both
diagrams. Translated from the corrected SMF branch of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2); compared
with the French sentence by sentence on 2026-09-24 (see
[Review against the French](#review-against-the-french-2026-09-24)).
Deeper scholarly proofreading is outstanding.

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

Build: `make -C translation/SGA1/ExposeII` (TeX Live with `latexmk`,
`amsbook`, `xy`, `hyperref`); `make tex` builds every exposé.
Lean: `lean/SGA/SGA1/ExposeII.lean`, with modules in
`lean/SGA/SGA1/ExposeII/`; coverage in
[`docs/formalization.md`](../../../docs/formalization.md).

## Source and translation choices

`smf_doc-math_3_01.tex` (corrected branch, `orig = false`), from
`\chapter{Morphismes lisses:...}` and `\label{II}` up to, but not
including, the chapter beginning
`\chapter{Morphismes lisses: propri\'et\'es de prolongement}` and
`\label{III}`: printed SMF pages 25–47, original page markers 29–57. The
French TeX and PDF are not in this repository.

The fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md): the
corrected branch, all non-index labels, proofs, both diagrams, and
translated footnotes are kept; indexes and source pagination machinery
are omitted; original page numbers remain as comments.

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

The historical synonym “simple” is kept where the source uses it as the
old name for smooth. The author's word *multiplodoque* is kept. Informal
asides and requests to supply arguments are translated as part of the
text.

The corrected source assigns 1.1 to both a definition and the next
proposition, and 4.18 to both a corollary and the next block of remarks.
Both numbers are kept, with the source labels `II.1.1` / `prop:II.1.1`
and `II.4.18` / `rem:II.4.18` and distinct PDF destinations.

References within the exposé use `\ref`. A reference beyond it is
written `\SourceRef{source-label}{printed-number}`, which keeps the
source key and prints the source's number without inventing a
destination; it becomes a `\ref` if that label is defined. The source's
own keys for this exposé's 4.8 and 4.9 are `\Ref{I.4.8}` and
`\Ref{I.4.9}`, which name Exposé I; the English uses `\ref{II.4.8}` and
`\ref{II.4.9}`, which print the numbers the source means.

## Review against the French (2026-09-24)

The whole exposé was compared with the corrected French, sentence by
sentence, in four parts: `en-01-03.tex`; `en-04-08.tex` and
`en-04-09-13.tex`; `en-04-14.tex` and `en-04-15-19.tex`; `en-05.tex`.
Changes made:

- two mistranslations in `en-01-03.tex`: the word order of “étale
  $k(y)$-morphism” in the proof of 2.1, and *considéraient abusivement*
  in 2.4, rendered “abusively regarded”;
- the comment `% original p. 36` moved to the position of the source's
  page marker;
- three capitalizations in II.4.14: *Idéal*, a sheaf of ideals, rendered
  “Ideal”;
- in the errata, “the present number” → “the present no.”.

The review found no omissions or formula errors. It confirmed that the
statement numbering matches the source, including the repeated 1.1. It
confirmed all twelve source points of the first table below in the
French and found the further points of the second.

## Source points for scholarly review

Apparent slips in the corrected French TeX and the matching PDF, kept as
printed per [`CONVENTIONS.md`](../../CONVENTIONS.md).

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

Further points found by the 2026-09-24 review, also kept as printed:

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Proof of II.2.1 | The $g_i$ are elements of $B\otimes_A k = BS^{-1}$ | Localization gives $B_{\mathfrak p}$, not the fiber ring. |
| Proof of II.2.1 | “up to multiplying the $g_i$ by one and the same nonzero element of $k$” | Clearing denominators in $BS^{-1}$ needs an element of $S$, not of $k$. |
| II.2.2 | “$X$ flat (or again: smooth) over $S$ at $x$” | Only $Y$ flat over $S$ is assumed, so the two conditions are not obviously equivalent. |
| After II.2.5 | An unclosed parenthesis after “excess component” | Typographic slip. |
| Proof of II.4.10 | “elements of the form $dg_i$ ($1\le i\le n$)” | $i\le p$ is meant. |
| Proof of II.4.12 | An unbalanced parenthesis | Typographic slip. |
| Proof of II.4.13 | $X$ and $X'$ | Used without $X$ being introduced. |
| II.4.14 | “there always exists a neighborhood of $Y$ isomorphic to …” | A neighborhood of $x$ is meant. |
| II.4.14 | “for $(x_i)$ to be a minimal system of generators of $J$, it already suffices that …” | “Regular system of generators” is meant. |
| II.4.14 | “the canonical homomorphism $S_{\mathcal O_Y}(\mathcal J/\mathcal J^2)\to\operatorname{gr}^{\mathcal J}(\mathcal O_X)$ be surjective” | “Isomorphism” is meant; the map is surjective in any case. |
| Proof of II.4.15 | “the fiber of $X'\to X$ at $x'$” | $X\to X'$ is meant. |
| Proof of II.4.15 | Polynomial rings “in $n-p$ indeterminates” | Check the number of indeterminates. |
| Remarks II.4.18 | $f\mapsto D(fg)-D(f)$ | The usual recursive definition uses $D(fg)-gD(f)$. |
| Proof of II.5.1 | “replacing $x$ by an open neighborhood” | $X$ is meant. |
| Proof of II.5.8 | “generate this vector space over $k$”; “corollary 5.6, criterion (iii)” | $k(x)$ is meant; the argument uses (ii)/(ii bis). |
| Proof of II.5.8 (`en-05.tex`) | `\eqref{II.4.8}`, `\eqref{II.5.1}` | The keys are statement labels, so the numbers print in parentheses. |
| French slip | “un voisinages $Y_1$” (proof of II.4.15) | No effect on the English. |

## Validation

`make tex` succeeds. All 65 non-index source labels (including the
numbered statements, the duplicate 1.1 and 4.18, the equation tags, and
the errata), ten footnotes, and both diagrams were checked against the
corrected source. Compiled statement numbers match the source, including
the repeated 1.1 and 4.18. Equation tags match the source
(`1.1`--`1.3`, `3.1`--`3.2`, `4.1`--`4.6` with bis tags, `5.1`). The
PDF build has no TeX warnings, unresolved references, or duplicate
destinations. Representative pages and the diagrams were checked
visually.

License: [`../../LICENSE`](../../LICENSE) (MIT for the translator's
contribution).
