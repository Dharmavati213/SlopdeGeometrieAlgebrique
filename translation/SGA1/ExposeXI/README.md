# SGA 1, Exposé XI — Examples and complements

Full English draft of the whole exposé: all six sections and the
bibliography, with proofs, footnotes, and all diagrams. It includes
M. Raynaud's 2003 addition (MR) in XI.1.4 and the 2003 starred footnote
in §3. It was translated from the corrected SMF branch in three chunks.
A second reviewer then checked each chunk against the French
(2026-09-24). Scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-XI.tex`](SGA1-XI.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | §1 Projective spaces, unirational varieties; §2 Abelian varieties; §3 Projecting cones, Zariski's example |
| [`en-2.tex`](en-2.tex) | §4 The exact cohomology sequence (XI.4.1–XI.4.9); §5 Special cases of principal bundles (XI.5.1–XI.5.3) |
| [`en-3.tex`](en-3.tex) | §6 Application to principal coverings: Kummer and Artin-Schreier theories (XI.6.1–XI.6.11); bibliography |
| [`SGA1-XI.pdf`](SGA1-XI.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeXI` from the repository root,
or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 17844–19356, from the chapter
`Exemples et compl\'ements` and `\label{XI}` up to, but not including,
the chapter of Exposé XII.
This covers original page markers 285–310.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and use the
shared package [`sga1-en.sty`](../sga1-en.sty). All non-index labels,
`\Ref`/`\eqref`/`\cite` keys, footnotes, and diagrams are kept. The
bibliography keeps `\begin{thebibliography}{10}{XI.7}` (numbered section
7). References to other exposés print the source's numbers:
`X~\Ref{X.1.7}` prints “X 1.7”, as in the SMF volume. Original page
numbers remain as `% original p. N` comments. Indexes and SMF
page-layout commands are omitted.

House rules applied here as in the other new exposés: *n°* / *numéro*
is rendered “no.” (`\No`), and *changement de base* is rendered “change
of base”, the Exposé VI term. This exposé already used “change of
base”. The harmonization that replaced “base change” after the reviews
concerned Exposés IV, V, VIII, IX, and X.

The 2003 material has the SMF form. The addition in XI.1.4 stays inline
between bold brackets, beginning “Added in 2003 (MR)”. The footnote in
§3 keeps its `*` mark (`\renewcommand{\thefootnote}{*}`).

Exposé XI terminology:

| French | English |
| --- | --- |
| variété unirationnelle | unirational variety |
| variété abélienne; isogénie | abelian variety; isogeny |
| cône projetant | projecting cone |
| suite exacte de cohomologie | exact cohomology sequence |
| fibré principal (homogène) | principal (homogeneous) bundle |
| revêtement principal | principal covering |
| groupe d'opérateurs | group of operators |
| théories de Kummer et d'Artin-Schreier | Kummer and Artin-Schreier theories |
| changement de base | change of base |

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Before XI.1.3 | “completely decomposed by virtue of `\Ref{X.1.1}`” | The key is Definition X.1.1; XI.1.1 seems meant. |
| XI.2 | “commutes with products (IX `\Ref{IX.1.7}`)” | IX.1.7 is about nilpotent immersions; the product formula is X.1.7. |
| XI.3, second paragraph | “`X` does not come by inverse image” | `X'` is meant. |
| XI.3, Zariski's example | The open set `U` in `X'\|f^{-1}(U)`; footnote “not separated over `S`” | `U` is undefined; apparently “over `Y`”. |
| XI.3, Serre's construction | “acts on `X` without fixed point, i.e. `X` is a principal covering of `X = X'/G`” | `X'` in both places. |
| XI.3, end | “`k(X_1) = k(X)` regular extension of `k(X)`” | Apparently an extension of `k(f)`; `X_1` is used without being introduced. |
| XI.4, opening | “preschemes over `X`”; “object `S'` of `Sch_{/S'}`” | “Over `S`”; `Sch_{/S}`. |
| After XI.4.3 | `P^{(H)}`; product written `E' × P'` | `H^{(P)}` is meant; the product was defined as `P × E`. |
| XI.4.4 | “principal homogeneous bundles over `S` with group `S`” | “With group `G`”. |
| XI.4.5, display | `H^0(X, G') →∂ H^1(X, G'')` | The primes are swapped relative to the statement above. |
| Before XI.4.5 to XI.4.8 | `H^i(X, ·)`, `O_X(G)` | The text has `S`, not `X`. |
| XI.5, cocycles | `Z^1(π_1, G)`; an unmatched “)” | `Z^1(π_1, 𝒢)` is meant. |
| XI.5 | “principal homogeneous bundles with group `G` in the category of finite sets” | `𝒢` may be meant. |
| XI.5, Weil and Lang | “commutative when `G` is” | `G` is not named in that sentence. |
| XI.6.3 | “sections of `O_S`” of order `n` | Units are meant. |
| After XI.6.9 | “at least when `A` is the spectrum of a field” | `S` is meant (or “`A` a field”). |
| XI.6.11 | `Pic_{S/K}` with capital `K`, in the text and the footnote | `Pic_{S/k}` elsewhere. |
| XI.6.11 | `T^•(Pic_{X/k})` | `Pic_{S/k}` is meant. |
| French slips | “plus faut” for “plus haut” (XI.4.6); “Soient `S` un préschéma, on a” (XI.6.4) | These do not affect the English. |

## Validation

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, finds for each chunk the same non-index labels, reference
and citation keys, footnotes, diagrams, displayed formulas, list items,
and statement environments as in the corrected French. For the whole
exposé these are 40 labels, 67 references, 17 citations, 9 footnotes,
4 diagrams, and 85 displays. The wrapper compiles to an 18-page PDF with
no errors or undefined references.

A second reviewer checked all three chunks against the French:

- en-1.tex: one fix (“this number” → “this no.”);
- en-2.tex: two fixes (“present number” → “present no.”, and the plural
  “groups of operators”);
- en-3.tex: no fixes.

The reviewer confirmed all the translator's source points and added the
query on `G`/`𝒢` in XI.5. These checks do not settle the mathematical
questions above; scholarly proofreading remains outstanding.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
