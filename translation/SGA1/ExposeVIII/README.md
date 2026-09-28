# SGA 1, Exposé VIII — Faithfully flat descent

Full English draft of the whole exposé: all seven sections and the
bibliography, with proofs, footnotes, and all diagrams. It was translated
from the corrected SMF branch in four chunks. A second reviewer then
checked each chunk against the French (2026-09-24). Scholarly
proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-VIII.tex`](SGA1-VIII.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | §1 Descent of quasi-coherent Modules (VIII.1.1–VIII.1.12) |
| [`en-2.tex`](en-2.tex) | §2 Descent of preschemes affine over another one; §3 Descent of set-theoretic properties and of finiteness properties of morphisms; §4 Descent of topological properties (to VIII.4.10) |
| [`en-3.tex`](en-3.tex) | §5 Descent of morphisms of preschemes; §6 Application to finite and quasi-finite morphisms (to VIII.6.6) |
| [`en-4.tex`](en-4.tex) | §7 Effectiveness criteria for a descent datum (VIII.7.1–VIII.7.10); bibliography |
| [`SGA1-VIII.pdf`](SGA1-VIII.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeVIII` from the repository
root, or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 12789–14730, from
`\chapter{Descente fid\`element plate}` and `\label{VIII}` up to, but
not including, the chapter of Exposé IX. (Exposé VII was never written.)
This covers original page markers 195–227.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and use the
shared package [`sga1-en.sty`](../sga1-en.sty). All non-index labels,
`\Ref`/`\eqref`/`\cite` keys, footnotes, and diagrams are kept. The
bibliography keeps `\begin{thebibliography}{D}{VIII.8}`, so it is the
numbered section 8. References to other exposés print the source's
numbers: `VI~\Ref{VI.11}` prints “VI 11”, as in the SMF volume. Original
page numbers remain as `% original p. N` comments. Indexes and SMF
page-layout commands are omitted.

House rules applied here as in the other new exposés: *n°* / *numéro*
is rendered “no.” (`\No`), and *changement de base* is rendered “change
of base”, the Exposé VI term. The second review of en-3.tex made this
change there, and the harmonization of Exposés IV, V, VIII, IX, and X
then made it in en-2.tex and en-4.tex. *Produit fibré* is “fibered
product”, as in Exposé VI.

The doubled word in the footnote before VIII.1.2 (“exposée exposée”) is
kept as “expounded expounded”.

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

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

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

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, finds for each chunk the same non-index labels, reference
and citation keys, footnotes, diagrams, displayed formulas, list items,
and statement environments as in the corrected French. For the whole
exposé these are 63 labels, 124 references, 9 citations, 4 footnotes,
21 diagrams, and 92 displays. The wrapper compiles to a 21-page PDF with
no errors or undefined references.

A second reviewer checked all four chunks against the French:

- en-1.tex: one fix of register (“We shall simply call” → “One will
  simply call”);
- en-2.tex and en-4.tex: no fixes;
- en-3.tex: six fixes of terminology (“fibered products”, and “change of
  base” five times).

The reviewer confirmed the translator's source points and added the
spelling slip listed last. These checks do not settle the mathematical
questions above; scholarly proofreading remains outstanding.

License: [`../../LICENSE`](../../LICENSE) (MIT for the
translator's contribution).
