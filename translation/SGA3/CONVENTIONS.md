# SGA 3 English conventions

Unofficial English of *Schémas en groupes* (SGA 3), from the recomposition
edited by Philippe Gille and Patrick Polo. The French PDFs live only in
`source/SGA3/` (gitignored). Do not copy them into the repository.

Translate from the PDF itself. A plain-text extract is a crib for the French
words only: it loses formulas, diagrams, accents and notation.

## Scope

Exposés I–XXVI and the foreword/introduction. Not the indexes, and not the
tables of contents (LaTeX builds the contents). Tome 1 is exposés I–VIIB
(PDFs of 13–14 October 2024). Tome 2 is VIII–XVIII (PDFs of 2008–2009).
Tome 3 is XIX–XXVI (PDFs of 13 October 2024).

## Fidelity

Translate every sentence, proof, footnote, diagram, and bibliography item.
Do not summarize, modernize an argument, or add a translator’s remark in
the body. Impersonal French *on* becomes *one*. Keep *I* where the French
is *je*.

*Préschéma* is *prescheme*. *Schéma* is *scheme*. Do not collapse the two.

The October 2024 PDFs already incorporate the errata lists
`typos_SGA31-oct24.pdf` and `typos_SGA33-oct24.pdf`. Translate the PDF.
Do not apply those lists a second time.

Correct a typographical slip (spelling, a duplicated word, a mismatched
parenthesis that is visibly a slip). Mark it with a comment
`% typo: <what was printed> -> <correction>`. Do not change a formula,
a hypothesis, or a number because it looks unlikely. If you are unsure,
leave the text as printed and mark `% typo?: kept as printed`.

## File shape

Each exposé directory has a standalone wrapper `SGA3-<id>.tex` and body
fragments `en-01.tex`, `en-02.tex`, … covering consecutive page ranges of the
French PDF (listed in the exposé README). A sentence belongs to the fragment
of the page where it begins. Fragments have no preamble. The first one starts
with `\exposetitle{I}{English title}` (or `\fronttitle{...}` for the
introduction) and `\label{I}`. Running headers and printed page numbers are
dropped.

## Numbering

Copy the source number. Do not use an automatic theorem counter.

| Printed French | LaTeX |
| --- | --- |
| `1. Généralités` (section) | `\sgasection{1}{Generalities}` |
| `1.1. ---` | `\numpara{1.1}` |
| `Proposition 1.5.1` | `\begin{proposition}{1.5.1} ... \end{proposition}` |
| `Définition 2.1.2` | `\begin{definition}{2.1.2}` |
| `Théorème` | `theorem` |
| `Lemme` | `lemma` |
| `Corollaire` / `Corollaires` | `corollary` / `corollaries` |
| `Remarque` / `Remarques` | `remark` / `remarks` |
| `Scholie` | `scholium` |
| `Exemple` | `example` |
| `Notation` | `notation` |
| `Variante` | `variant` |
| `Démonstration` | `\begin{proof}` |

Put `\label{I.1.5.1}` on a statement (the exposé id, then the printed
number). Leave cross-references in the prose as printed (`I 1.1`,
`4.6.2`, `EGA IV`). Do not replace them by `\ref`.

## Notes, quotes, diagrams

N.D.E. stays N.D.E., and the note is translated, via `\nde{...}`.
Ordinary footnotes use `\footnote`. Quotes are `` ... ''.
Diagrams are `xymatrix`. Lists that the source numbers (i), (ii)
use `enumeratei`.

## Words

Group scheme, group prescheme, algebraic group, diagonalizable group,
group of multiplicative type, reductive group, split group (*déployé*),
splitting (*déploiement*), pinned group (*épinglé*), pinning
(*épinglage*), root datum, root system, parabolic subgroup, Borel
subgroup, maximal torus, Weyl group, Cartan subgroup, reductive center,
unipotent rank, unipotent group, radicial group, height, Lie algebra,
restricted Lie \(p\)-algebra, tangent bundle, infinitesimal extension,
formal group, rational law, character, sheaf, functor, representable,
smooth, flat, quasi-compact, quasi-separated, faithfully flat, radicial,
base change, normalizer, centralizer, center, torus, fiber, bundle,
principal homogeneous space, torsor, arrow, universe.

Bold functor letters in the PDF are `\mathbf{F}`. The underlined
functors `Lie`, `Norm`, `Centr` are `\uLie`, `\uNorm`, `\uCentr`.
Categories are `\Ens`, `\Sch`, `\Abcat`, `\Grcat`.
`\Gm`, `\Ga`, `\Spec`, `\Hom`, `\Lie`, `\Aut`, `\Centr`, `\Norm` are
already defined. Do not redefine them.

## Build

`make -C translation/SGA3/ExposeI` runs `latexmk`. Undefined references
are expected: the prose keeps printed numbers, and a single exposé does
not contain the others.
