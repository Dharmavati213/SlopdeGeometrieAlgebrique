# SGA 1, Exposé X — Theory of specialization of the fundamental group

Complete English draft of the exposé: the introduction, all three
sections, and the bibliography, with proofs, footnotes, the diagram, and
M. Raynaud's 2003 remark X 2.14 (MR). Translated in three chunks from the
corrected SMF branch of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2); a second
reviewer checked each chunk against the French (2026-09-24). Scholarly
proofreading is outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-X.tex`](SGA1-X.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | Introduction; §1 The homotopy exact sequence for a proper and separable morphism (X.1.1–X.1.10) |
| [`en-2.tex`](en-2.tex) | §2 Application of the existence theorem for sheaves: semicontinuity theorem for the fundamental groups of the fibers of a proper and separable morphism (X.2.1–X.2.13, and Remark 2.14 (MR)) |
| [`en-3.tex`](en-3.tex) | §3 Application of the purity theorem: continuity theorem for the fundamental groups of the fibers of a proper and smooth morphism (X.3.1–X.3.11); bibliography |
| [`SGA1-X.pdf`](SGA1-X.pdf) | Compiled English draft |

Build: `make -C translation/SGA1/ExposeX` (TeX Live with `latexmk`,
`amsbook`, `xy`, `mathrsfs`, `enumitem`, `hyperref`); `make tex` builds
every exposé.

## Source and translation choices

`smf_doc-math_3_01.tex` (corrected branch, `orig = false`), lines
16491–17843: from
`\chapter{Th\'eorie de la sp\'ecialisation du~groupe~fondamental}` and
`\label{X}` up to, but not including, the chapter of Exposé XI; original
page markers 261–284. The French TeX and PDF are not in this repository.

The fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md), section
“SGA 1 — front matter and Exposés IV, V, VIII–XIII” (labels, reference
and citation keys, page markers, omitted indexes), and use the shared
package [`sga1-en.sty`](../sga1-en.sty). The bibliography keeps
`\begin{thebibliography}{0}{X.4}` (numbered section 4). *n°* / *numéro*
is rendered “no.” (`\No`), and *changement de base* is rendered “change
of base”, the Exposé VI term.

Exposé-specific choices:

- **Remark 2.14 (MR).** The SMF prints M. Raynaud's 2003 remark
  (`remarqueMR`) between bold brackets and without a number. Here it is
  “Remark 2.14 (added in 2003 (MR))”: its label `X.2.14` names that
  number, it closes §2, and the translated Preface cites it as “X 2.14”
  (see the comment on `remarkMR` in [`sga1-en.sty`](../sga1-en.sty)).
- **Sums.** In X.1.5, *somme directe* and *somme de deux Algèbres* are
  translated literally (“direct sum”, “sum of two Algebras”). Products or
  disjoint sums are meant, which is ordinary usage in the source.
- **“normal closure”.** In §3 *clôture normale* `V'` is kept as “normal
  closure”, although the integral closure is meant.

Exposé X terminology:

| French | English |
| --- | --- |
| spécialisation | specialization |
| morphisme propre et séparable | proper and separable morphism |
| suite exacte d'homotopie | homotopy exact sequence |
| théorème d'existence (de faisceaux) | existence theorem (for sheaves) |
| théorème de pureté | purity theorem |
| semi-continuité; continuité | semicontinuity; continuity |
| modérément ramifié | tamely ramified |
| fibre géométrique | geometric fiber |
| clôture normale | normal closure (as printed) |
| changement de base | change of base |

## Source points for scholarly review

Apparent slips in the corrected French TeX, kept as printed per
[`CONVENTIONS.md`](../../CONVENTIONS.md).

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| X.1.3 | The statement defines `\overline X_y'` but uses `\overline{X'}_y` | Inconsistent notation. |
| X.1.6 | Label key `X.I.6` (letter I) | Kept as the source's key; the printed number is 1.6. |
| Proof of X.1.7 | “`Z` is separable over `k`” | Applying X.1.4 to `f: Z → Y` needs `Z` separable over `Y`. |
| Proof of X.1.7 | “1.4” as plain text | Not a `\Ref` in the source. |
| X.2.1 | `X_0 = X ⊗_A k` | The complete local ring `A` is never named (`Y = Spec A` is implicit). |
| Before X.2.2 and X.2.2 | `π_1(\overline X_0, \overline a)` | The point introduced is `\overline a_0`; `\overline a` comes from the SMF correction itself. |
| X.2.5 | Local system, projective limit of group schemes “over `X`” | `Y` is expected. |
| Before X.2.6 | “the fundamental group of `X`” (twice) | The curve is `X_0`. |
| Proof of X.2.11 | The generic hyperplane is called `H_1'` | The next formula uses `X' ×_{P^r} H_1`. |
| Remark after X.3.1 | “finite extension `R(Z)/R(X)`” | Presumably `R(X)/R(Y)`. |
| Proof of X.3.3 | “locally free coverings … of `X'`”; `X' = X ×_X U ≅ U'`; `U' = f^{-1}(U) = X' = f^{-1}(Z)` | Of `X`; `X' ×_X U`; `X' − f^{-1}(Z)`. |
| Before X.3.6 | “`n_i = [G_i : e]` is of order `p` prime to the characteristic of `k`” | Presumably “prime to the characteristic `p` of `k`”. |
| Proof of X.3.6 | `G_i, H_i, L_i'`; “cyclic of orders `m` and `n`” | `M_i` is meant; the orders are swapped. |
| X.3.7 | “`Z_K` its inverse image on `X_{K_s}`” | `Z_{K_s}` is meant. |
| Before X.3.8 | `K'' = K'[t]/(t^n − u)` | `u'` is meant. |
| §3, footnote 1 | “SGA 2 X `\Ref{X.3.4}`” | The key is this exposé's own, so the link goes to SGA 1 X.3.4, not to SGA 2. |
| French slips | “en topologies algébriques” (X.1.6); “les fibres géométrique”, “en droit à s'attendre” (§2); “d'autre applications” (X.3.5) | These do not affect the English. |

### Found during the Lean formalization (2026-09)

Found while formalizing the exposé in `lean/SGA/SGA1/`; the Lean
statements use the corrected forms.

| Location | Source wording | Point |
| --- | --- | --- |
| X.1.10 | “the coverings `x^p − x = ct` are pairwise non-isomorphic” | Not pairwise: `x ↦ jx` identifies `c` with `jc` for `j ∈ 𝔽_p^×` (`algEquivNeg` for `j = −1`). Infinitely many classes remain, so the counterexample stands. |

## Validation

`source/SGA1/check_chunk.py` (a local script, not in the repository)
compared each chunk with the corrected French and found the same
non-index labels, reference and citation keys, footnotes, diagrams,
displayed formulas, list items, and statement environments. For the
whole exposé these are 39 labels, 88 references, 7 citations,
8 footnotes, 1 diagram, and 42 displays. The wrapper compiles to a
16-page PDF with no errors or undefined references.

The second reviewer made no fixes in `en-1.tex` and `en-2.tex`, and four
in `en-3.tex` (renderings of *numéro* as “no.”, and ordinals “nth”). The
reviewer confirmed all the translator's source points, added the French
slips, and noted that `\overline a` in X.2.2 comes from the SMF
correction.

License: [`../../LICENSE`](../../LICENSE) (MIT for the translator's
contribution).
