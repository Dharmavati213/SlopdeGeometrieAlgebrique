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

## SGA 1 — front matter and Exposés IV, V, VIII–XIII

These use the shared package [`SGA1/sga1-en.sty`](SGA1/sga1-en.sty) (loaded by
each wrapper `SGA1/Expose<N>/SGA1-<N>.tex`; body fragments are `en-<k>.tex`).
Exposés I, II, III and VI keep their own wrappers and the rules above.

Translate the French LaTeX **exactly**, as a mathematical text, into English LaTeX.
Do **not** modernize, abridge, paraphrase, add commentary, or “fix” the arguments.
Take the **corrected** SMF branch: `\ifthenelse{\boolean{orig}}{A}{B}` → keep **B** only
(B may be empty). A misprint that survives in the corrected branch is translated
as printed and reported (not repaired) in the exposé README.

### Output

- A LaTeX body fragment only (no preamble). Start exactly where the assigned
  French chunk starts (a `\chapter`, `\section`, or a statement) and stop where it stops.
- Every sentence, proof, footnote, diagram, table and bibliography item of the chunk.

### Drop

- `\index{...}`, `\oldindexnot{...}`, `\label{indnot:...}`
- `\marginpar{N}` and the `% page: N` comment: replace the pair by one comment `% original p. N`
- `\enlargethispage{...}`, `\chapterspace{...}`, `\skpt`, `\pagebreak`, `\nopagebreak`, other page-layout hacks
- `\ifthenelse{\boolean{orig}}{...}{...}` wrappers (keep the corrected branch)
- source-editing comments such as `% correction: ...` or `% remark: ...`
- the notation and terminology indexes at the end of the volume

### Keep verbatim

- every `\label{...}` except `indnot:*`; every `\Ref{...}`, `\eqref{...}`, `\ref{...}`, `\cite{...}`
  with the same keys (the package prints cross-exposé keys as the SMF volume does)
- `\setcounter`, `\addtocounter`, `\refstepcounter` that belong to the corrected branch
- `\subsection{}` / `\subsubsection{}` used for decimal numbering, `\Subsection*{...}` (translate the text)
- all mathematics, `\xymatrix` diagrams, `\tag`s; translate only words inside `\text{...}`
- footnotes (translated); the 2003 footnotes keep their `*` construction
  `{{\renewcommand{\thefootnote}{*}\addtocounter{footnote}{-1}\footnote{\lcrochetbf Added in 2003: ...\rcrochetbf}}}`
- `\begin{thebibliography}{D}{VIII.8}` with both arguments (it makes the numbered section “Bibliography”);
  bibliography entries keep authors and titles as printed; translate only connecting words

### Environments

| French | English |
|---|---|
| `theoreme` | `theorem` |
| `proposition` | `proposition` |
| `lemme` | `lemma` |
| `corollaire`, `corollaires` | `corollary`, `corollaries` |
| `theoremedefinition` | `theoremdefinition` |
| `theoremedepurete` | `puritytheorem` |
| `subproposition`, `sublemme` | `subproposition`, `sublemma` |
| `corollairestar`, `propositionstar`, `theoreme*` | `corollarystar`, `propositionstar`, `theoremstar` |
| `definition`, `definitions`, `subdefinition`, `definitionstar` | same names |
| `remarque`, `remarques`, `subremarque` | `remark`, `remarks`, `subremark` |
| `remarquestar`, `remarquesstar`, `scholiestar` | `remarkstar`, `remarksstar`, `scholiumstar` |
| `exemple`, `exemples` | `example`, `examples` |
| `remarqueMR` | `remarkMR` (the heading “Remark N (added in 2003 (MR))” is built in; N is the label's number) |
| `enonce*`{Name} | `enonce*`{translated name} |
| `enumerateb`, `enumerate`, `itemize`, math environments | unchanged |

Optional statement titles `[...]` are translated.

### Macros

All macros of `sga1-smf.sty` are available with the same names (`\cal`, `\goth`,
`\othercal`, `\Hom`, `\SheafHom`, `\Spec`, `\Ob`, `\Sch`, `\Ens`, `\H`, `\R`, `\an`,
`\tame`, `\et`, `\kres`, `\isomto`, `\lto`, `\mto`, `\To`, `\cf`, `\Cf`, `\ie`,
`\iev`, `\resp`, `\loccit`, `\ptbl`, `\quoi`, `\No`, `\bbmu`, `\leftexp`, …).
Keep them as used; do not define new macros in a body fragment. `\og ... \fg`
becomes `` ... ''. `\red` prints “red”, `\car` prints “char”.

### Terminology (mandatory; American spelling)

| French | English |
|---|---|
| préschéma / schéma | prescheme / scheme |
| revêtement (étale, principal) | (étale, principal) covering |
| morphisme étale, net, non ramifié, lisse, plat | étale, net, unramified, smooth, flat morphism |
| fidèlement plat | faithfully flat |
| radiciel | radicial |
| Module, Algèbre, Idéal (sheaves, capitalized) | Module, Algebra, Ideal (keep the capital) |
| fibre | fiber |
| voisinage | neighborhood |
| corps résiduel | residue field |
| groupe fondamental | fundamental group |
| point géométrique | geometric point |
| foncteur fibre | fiber functor |
| catégorie galoisienne | Galois category |
| groupe de décomposition / d'inertie | decomposition / inertia group |
| préschéma quotient | quotient prescheme |
| donnée de descente | descent datum (pl. descent data) |
| descente effective; morphisme de descente (stricte) | effective descent; (strict) descent morphism |
| (universellement) submersif | (universally) submersive |
| spécialisation | specialization |
| théorème d'existence (de faisceaux) | existence theorem (for sheaves) |
| théorème de pureté | purity theorem |
| modérément ramifié; ramification modérée | tamely ramified; tame ramification |
| diviseur à croisements normaux | divisor with normal crossings |
| cohomologiquement propre; propreté cohomologique | cohomologically proper; cohomological properness |
| champ; gerbe; torseur | stack; gerbe; torsor |
| localement acyclique | locally acyclic |
| suite exacte d'homotopie | homotopy exact sequence |
| géométriquement unibranche | geometrically unibranch |
| hensélien, strictement local | henselian, strictly local |
| anneau de valuation discrète | discrete valuation ring |
| clôture intégrale; normalisé | integral closure; normalization |
| espace analytique | analytic space |
| fibré principal | principal bundle |
| composante connexe | connected component |
| de type fini; de présentation finie | of finite type; of finite presentation |
| catégorie fibrée, cartésien, image inverse | fibered category, cartesian, inverse image (as in Exposé VI) |
| il faut et il suffit | it is necessary and sufficient |
| Je dis que | I say that |
| cqfd; sorite | qed; sorites |
| n° / No | no. (`\No`) |

Register: formal mathematical English in the voice of the original; keep “we”
or impersonal “one” as the French has it. Keep N.B., loc.\ cit., cf.

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
