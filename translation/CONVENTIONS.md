# Translation conventions for SGA 1, Exposé VI

Translate the French LaTeX **exactly**, as a mathematical text, into English LaTeX.
Do **not** modernize, abridge, paraphrase, add commentary, or “fix” Grothendieck’s arguments.
Take the **corrected** SMF branch: whenever you see `\ifthenelse{\boolean{orig}}{A}{B}`, keep **B** only.

## Output

- Write **only** a LaTeX body fragment (no `\documentclass`, no preamble, no `\begin{document}`).
- Start at the first `\section` or `\chapter` of your chunk (translated).
- The fragment must cover **every sentence** of the assigned French chunk.

## Drop (do not copy)

- `\oldindexnot{...}` and `\label{indnot:...}`
- `\index{...}`
- `\marginpar{N}` (you may leave a comment `% original p. N`)
- `\enlargethispage{...}`
- `\ifthenelse{\boolean{orig}}{...}{...}` wrappers (keep the false/corrected branch)
- `\refstepcounter{chapter}` and the “VII n’existe pas” TOC line at the very end of the exposé (only the last chunk: omit those two lines)
- SMF page-break hacks

## Keep

- Every `\label{...}` that is **not** `indnot:*`
- Equation tags `(i)`, `(ii)`, `(I)`, `(II)`, … and `\eqref{...}`
- All `\xymatrix` diagrams (translate only surrounding words, not the math)
- Footnotes, translated
- Bibliography items, with English bibliographic punctuation as in the corrected branch

## Environments (English names, same numbering)

| French source | English |
|---|---|
| `\begin{definition}` | `\begin{definition}` |
| `\begin{proposition}` | `\begin{proposition}` |
| `\begin{corollaire}` | `\begin{corollary}` |
| `\begin{remarquesstar}` | `\begin{remarks}` |
| `\begin{remarquestar}` | `\begin{remark}` |
| `\begin{thebibliography}{0}{VI.13}` | `\begin{thebibliography}{9}` |

Keep the original `\label{VI.m.n}` on each statement.

## Terminology (mandatory)

| French | English |
|---|---|
| catégorie fibrée | fibered category |
| catégorie préfibrée | prefibered category |
| catégorie clivée | cloven category |
| clivage | cleavage |
| clivage normalisé | normalized cleavage |
| catégorie scindée | split category |
| catégorie-fibre | fiber-category |
| morphisme cartésien | cartesian morphism |
| morphisme cocartésien | cocartesian morphism |
| image inverse | inverse image |
| foncteur cartésien | cartesian functor |
| foncteur transportable | transportable functor |
| changement de base | change of base |
| descente | descent |
| recollement | gluing |
| univers | universe |
| flèche | arrow |
| foncteur | functor |
| équivalence de catégories | equivalence of categories |
| pleinement fidèle | fully faithful |
| essentiellement surjectif | essentially surjective |
| catégorie cofibrée / co-fibrée | cofibered category |
| catégorie bifibrée / bi-fibrée | bifibered category |
| pseudo-foncteur | pseudofunctor |
| préeschema / préschéma | prescheme |
| produit fibré | fibered product |
| somme | sum (coproduct) |
| accouplement | pairing |
| homomorphisme de foncteurs | homomorphism of functors (natural transformation) |
| noyau d’un couple de foncteurs | kernel of a pair of functors |
| cqfd | qed |
| sorite | sorites |
| scholie | scholium |
| No / numéro | no. |

Keep Grothendieck’s own notation: `\cal{E}`, `\cal{F}`, `\cal{G}`, `\SheafHom`, `\Hom_{\cal{E}}`, `\SheafHom_{\cal{E}/-}`, `\Ob`, `\Fl`, `\Ens`, `\Cat`, `\isomto`, `\id`, `\quoi`, `\cf`, `\resp`, `\ie`.

Use `\No` for “n°”. Quotes: use `` ... '' (English). Emphasis: keep `\emph`.

## Macros already defined in the master file

`\Hom`, `\SheafHom`, `\Ob`, `\Fl`, `\Ens`, `\Cat`, `\id`, `\isomto`, `\cart`, `\Fib`, `\Lim`, `\Isom`, `\Aut`, `\Univ`, `\Sch`, `\cf`, `\Cf`, `\ie`, `\resp`, `\loccit`, `\ptbl`, `\quoi`, `\mto`, `\to` (longrightarrow), `\No`, `\from`.

Do not redefine them.

## Style of English

Write in the same register as the original: slightly formal mid-century mathematical French rendered into clear mathematical English. Prefer “one” / passive over “we” when the French is impersonal (“on dit que” → “one says that” or “we say that”; either is fine if used consistently). Keep “I say that” where Grothendieck writes “Je dis que”.
