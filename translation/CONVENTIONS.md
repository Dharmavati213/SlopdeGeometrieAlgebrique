# Translation conventions

## SGA 1, Exposé VI

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

---

## SGA 2

Translate the French LaTeX **exactly**, as a mathematical text, into English LaTeX.
Do **not** modernize, abridge, paraphrase, add commentary, or “fix” Grothendieck’s arguments.
Take the **corrected** SMF branch: whenever you see `\sisi{A}{B}` or
`\ifthenelse{\boolean{orig}}{A}{B}`, keep **B** only.

### Output

- Write **only** a LaTeX body fragment (no `\documentclass`, no preamble, no `\begin{document}`).
- Start at the `\chapter` / `\chapter*` of the exposé (translated).
- The fragment must cover **every sentence** of the assigned French chunk,
  including proofs, original footnotes, and editor notes (N.D.E.).

### Drop (do not copy)

- `\oldindexnot{...}` and `\label{indnot:...}`
- `\index{...}`
- `\pageoriginale` / `\pageoriginaled` (you may leave a comment `% original p. N`)
- `\enlargethispage{...}`, `\chapterspace{...}`, `\danger`
- `\sisi{...}{...}` wrappers (keep the false/corrected branch)
- SMF page-break hacks
- The notation and terminology indexes at the end of the SMF file
- The SMF editor preface (already printed in English in the source)

### Keep

- Every `\label{...}` that is **not** `indnot:*`
- Equation tags and `\Ref` / `\eqref`
- All `\xymatrix` diagrams (translate only surrounding words, not the math)
- Original footnotes (`\sfootnote`), translated
- Editor notes (`\nde{...}`), translated, still wrapped in `\nde`
- Empty `\subsection{}` used for decimal numbering
- Bibliography items, with English bibliographic punctuation as in the corrected branch

### Environments (English names, same numbering)

SGA 2 numbers most statements by sharing the **subsection** counter
(decimal system). Exposé II uses the `sup*` environments numbered by
**section**. Keep those counters; do not renumber.

| French source | English |
|---|---|
| `\begin{theoreme}` | `\begin{theorem}` |
| `\begin{proposition}` | `\begin{proposition}` |
| `\begin{lemme}` | `\begin{lemma}` |
| `\begin{corollaire}` | `\begin{corollary}` |
| `\begin{definition}` | `\begin{definition}` |
| `\begin{remarque}` | `\begin{remark}` |
| `\begin{remarques}` | `\begin{remarks}` |
| `\begin{exemple}` | `\begin{example}` |
| `\begin{probleme}` | `\begin{problem}` |
| `\begin{conjecture}` | `\begin{conjecture}` |
| `\begin{remarquestar}` | `\begin{remarkstar}` |
| `\begin{supproposition}` | `\begin{supproposition}` |
| `\begin{suptheoreme}` | `\begin{suptheorem}` |
| `\begin{suplemme}` | `\begin{suplemma}` |
| `\begin{supcorollaire}` | `\begin{supcorollary}` |
| `\begin{enonce*}` | `\begin{enonce*}` (translate the heading) |
| `\begin{criteredenormalitedeserre}` | `\begin{serrenormality}` |

Macros live in `translation/SGA2/sga2-en.sty`. Do not redefine them.

### Terminology (mandatory)

| French | English |
|---|---|
| préschéma | prescheme |
| schéma | scheme (the source’s distinction is retained) |
| cohomologie locale | local cohomology |
| profondeur | depth |
| profondeur étale | étale depth |
| profondeur géométrique | geometric depth |
| profondeur homotopique | homotopical depth |
| module dualisant | dualizing module |
| foncteur dualisant | dualizing functor |
| parafactorialité / parafactoriel | parafactoriality / parafactorial |
| théorème de Lefschetz | Lefschetz theorem |
| théorème de finitude | finiteness theorem |
| théorème de comparaison | comparison theorem |
| théorème d’existence | existence theorem |
| théorème de pureté | purity theorem |
| faisceau cohérent / quasi-cohérent | coherent / quasi-coherent sheaf |
| faisceau flasque | flasque sheaf |
| suite spectrale | spectral sequence |
| foncteur dérivé | derived functor |
| catégorie dérivée | derived category |
| revêtement étale | étale covering |
| groupe fondamental | fundamental group |
| groupe de Picard | Picard group |
| intersection complète | complete intersection |
| morphisme propre | proper morphism |
| voisinage tubulaire | tubular neighbourhood |
| sorite | sorites |
| cqfd | qed |
| No / n° | no. |

Keep the source’s underlined sheafified functors (`\sheaf`, `\SheafH`,
`\SheafExt`, `\SheafGamma`). Quotes: `` ... ''. Emphasis: keep `\emph`.
