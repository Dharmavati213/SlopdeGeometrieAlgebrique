# SGA 1, Exposé VIII — Faithfully flat descent

Complete English draft of the exposé: all seven sections and the
bibliography, with proofs, footnotes, and all diagrams. Translated in
four chunks from the corrected SMF branch of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2); a second
reviewer checked each chunk against the French (2026-09-24). Scholarly
proofreading is outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-VIII.tex`](SGA1-VIII.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | §1 Descent of quasi-coherent Modules (VIII.1.1–VIII.1.12) |
| [`en-2.tex`](en-2.tex) | §2 Descent of preschemes affine over another one; §3 Descent of set-theoretic properties and of finiteness properties of morphisms; §4 Descent of topological properties (to VIII.4.10) |
| [`en-3.tex`](en-3.tex) | §5 Descent of morphisms of preschemes; §6 Application to finite and quasi-finite morphisms (to VIII.6.6) |
| [`en-4.tex`](en-4.tex) | §7 Effectiveness criteria for a descent datum (VIII.7.1–VIII.7.10); bibliography |
| [`SGA1-VIII.pdf`](SGA1-VIII.pdf) | Compiled English draft |

Build: `make -C translation/SGA1/ExposeVIII` (TeX Live with `latexmk`,
`amsbook`, `xy`, `mathrsfs`, `enumitem`, `hyperref`); `make tex` builds
every exposé.

## Source and translation choices

`smf_doc-math_3_01.tex` (corrected branch, `orig = false`), lines
12789–14730: from `\chapter{Descente fid\`element plate}` and
`\label{VIII}` up to, but not including, the chapter of Exposé IX
(Exposé VII was never written); original page markers 195–227. The
French TeX and PDF are not in this repository.

The fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md), section
“SGA 1 — front matter and Exposés IV, V, VIII–XIII” (labels, reference
and citation keys, page markers, omitted indexes), and use the shared
package [`sga1-en.sty`](../sga1-en.sty). The bibliography keeps
`\begin{thebibliography}{D}{VIII.8}`, so it is the numbered section 8.
*n°* / *numéro* is rendered “no.” (`\No`); *changement de base* is
rendered “change of base” and *produit fibré* “fibered product”, the
Exposé VI terms.

Exposé VIII terminology:

| French | English |
| --- | --- |
| descente fidèlement plate | faithfully flat descent |
| donnée(s) de descente | descent datum (descent data) |
| descente effective; morphisme de descente (effective) | effective descent; (effective) descent morphism |
| Module quasi-cohérent | quasi-coherent Module (capital kept) |
| changement de base | change of base |
| produit fibré | fibered product |
| propriétés ensemblistes | set-theoretic properties |
| (morphisme) fini, quasi-fini | finite, quasi-finite (morphism) |
| recollement | gluing |

## Source points for scholarly review

Apparent slips in the corrected French TeX, kept as printed per
[`CONVENTIONS.md`](../../CONVENTIONS.md).

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Proof of VIII.1.1 | “By virtue of VII, 8” | Exposé VII was never written. |
| Footnote before VIII.1.2 | “exposée exposée” (kept as “expounded expounded”) | Doubled word. |
| Before VIII.1.6 | “the two modules deduced from `N`” | `N'` appears to be meant. |
| VIII.1.6 | `φ(x ⊗_{A'} 1_{A'}) = 1_{A'} ⊗_{A'} x` | `⊗_A` is expected. |
| VIII.3.4 | “`B' = B ⊗_A A'` the `A`-algebra” | Presumably the `A'`-algebra. |
| End of VIII.3.6 | “this statement” | The statement meant is not specified. |
| Proof of VIII.4.6 | `Z' = f'^{-1}(g^{-1}(\overline{f(Z)})` | A closing parenthesis is missing. |
| VIII.4.9 | `(VI~\Ref{IV.6.6})`, printing “VI 6.6” | The key is in Exposé IV, so “IV 6.6” is meant. |
| VIII.4.9 | “if `f` is a faithfully flat quasi-compact morphism” | The morphism under discussion is `g`. |
| Proof of VIII.5.5 | “sub-objects of `Y''`” next to “projection of `S''` into `S'`” | Mixed notation (harmless, since `Y = S` here). |
| Proof of VIII.5.8, first sentence | “The hypothesis on `L` implies … `f'` separated” | In the sufficiency direction the hypothesis is on `L'`. |
| Proof of VIII.7.5 | `q_1, q_2` from `p_1, p_2` “by the change of base `X' → S''`” | `X' → S'` apparently. |
| Proof of VIII.7.5 | “`X'_i` affine over `S` since `S'` is separated” | Probably “over `S'`”, as VIII.2.1 requires. |
| After VIII.7.6 | “a fiber of `X'` over `S` is contained in an affine open set” | False as printed; presumably a finite subset of a fiber is meant. |
| Proof of VIII.7.6 | `q_2(q_1^*(Z(f)))`; `f'' = f'\|U_{f'}'` | Presumably `q_1^{-1}` and `f'\|U'_f`. |
| VIII.7.10 (ii) | `S' = T − s` | `T − t` presumably. |
| Proof of VIII.7.10 (i) | Corrected branch: “rational over `S`” | Only `k` appears in the context. The second review considers this acceptable, since `S = Spec k`. |
| French slip | “La donné de descente” | Spelling only; no effect on the English. |

## Validation

`source/SGA1/check_chunk.py` (a local script, not in the repository)
compared each chunk with the corrected French and found the same
non-index labels, reference and citation keys, footnotes, diagrams,
displayed formulas, list items, and statement environments. For the
whole exposé these are 63 labels, 124 references, 9 citations,
4 footnotes, 21 diagrams, and 92 displays. The wrapper compiles to a
21-page PDF with no errors or undefined references.

Fixes by the second reviewer:

- `en-1.tex`: one fix of register (“We shall simply call” → “One will
  simply call”);
- `en-2.tex` and `en-4.tex`: no fixes;
- `en-3.tex`: six fixes of terminology (“fibered products”, and “change
  of base” five times).

The reviewer confirmed the translator's source points and added the
spelling slip listed last.

License: [`../../LICENSE`](../../LICENSE) (MIT for the translator's
contribution).
