# SGA 1, Exposé I — Étale morphisms

Full English draft: the opening convention and **all eleven sections**,
including proofs, footnotes, and the closing discussion of geometrically
unibranch schemes. Scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-I.tex`](SGA1-I.tex) | Standalone wrapper, macros, and translation notice |
| [`en-01-03.tex`](en-01-03.tex) | Opening convention; differential calculus; quasi-finite and unramified morphisms |
| [`en-04-06.tex`](en-04-06.tex) | Étale morphisms and coverings; the fundamental property; complete local rings |
| [`en-07.tex`](en-07.tex) | Local construction of unramified and étale morphisms |
| [`en-08.tex`](en-08.tex) | Infinitesimal lifting and formal schemes |
| [`en-09.tex`](en-09.tex) | Permanence properties, including both proofs of normality |
| [`en-10.tex`](en-10.tex) | Coverings of normal schemes and counting geometric fiber points |
| [`en-11.tex`](en-11.tex) | Examples and geometrically unibranch schemes |
| [`SGA1-I.pdf`](SGA1-I.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeI` from the repository root,
or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, and `hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, from `\chapter{Morphismes \'etales}` and
`\label{I}` up to, but not including, the chapter beginning
`\chapter{Morphismes lisses:...}` and `\label{II}`.
This covers printed SMF pages 1–23 and original page markers 1–28.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md):
retain the corrected branch, all non-index labels, proofs, the diagram, and translated
footnotes; omit indexes and source pagination machinery. Original page
numbers remain as comments. The standalone wrapper is separate from
the translation fragments.

Exposé I terminology:

| French | English |
| --- | --- |
| préschéma | prescheme |
| schéma | scheme (the source's distinction is retained) |
| net / non ramifié | net / unramified |
| étale | étale |
| revêtement | covering |
| radiciel (morphism) | radicial |
| extension résiduelle radicielle | purely inseparable residue field extension |
| idéal différente | different ideal |
| idéal de définition | ideal of definition |
| relèvement | lifting |
| intègre (ring / scheme) | integral domain / integral |
| rang (of a prime ideal) | height |
| clôture normale (of a ring) | integral closure |
| compactifié de Z | profinite completion of Z |

The historical synonym **net** is retained where the source uses it;
Definition 3.2 identifies it with **unramified**. The author's word
*multiplodoque* is retained. Informal asides and requests to supply
examples are translated as part of the text.

The corrected source assigns **9.2** to both a corollary and the next
proposition. Both numbers are retained, with the original labels
`I.9.2` and `prop:I.9.2` and distinct PDF destinations. The equation
tagged `(*)` retains its label `eq:I.9.5.*`.

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
| I.2.1(ii) | The residue field is an “extension” of `k` | The finiteness qualification appears to be missing. |
| After I.2.1 | The fiber is written `f^{-1}(x)` | The point on the base would ordinarily be `f(x)`. |
| I.3.4 | The graph has target `X ×_Y X`; the following map is `g ×_Y id_{X'}` | The graph target and the identity factor appear inconsistent with `g : X' → X`. |
| I.4.10 | The trace pairing gives an isomorphism of `B` onto `B` | The second occurrence appears to require the dual. |
| I.7.6 and its discussion | The statement does not explicitly require `F(u) = 0`; the paragraph after I.7.8 attributes the desired properties to `O` | Compare the polynomial relation and the use of `O` and `O'` throughout the proof. |
| I.7.9 | `B' = B[u]` and `n' = n B'` | These expressions appear inconsistent with the subalgebra and contracted ideal used in the proof. |
| Proof of I.8.1 | `B ⊗_A A_0 = A_0`, and a local ring identified with `C` | Compare the subsequent identifications with `B_0` and `B`. |
| Proof of I.9.3; proof of I.10.11 | The source names the two directions of the implication | Their names appear reversed relative to the arguments that follow. |
| I.9.7 | Matrix entries are printed without a trace | A trace appears to be missing; the corrected sign `(-1)^{n(n-1)/2}` is retained. |
| I.10.1 and its proof | Normalization of `X` in `K_i`, and a component described as finite over `Y` | Compare the base `Y` and the quasi-finite hypothesis in the surrounding text. |
| I.10.7 and I.10.9 | “Upper semicontinuous” | Check the direction of semicontinuity against the source's conventions and the case of an open immersion. |
| I.11(b) | A power series ring in the first example, a polynomial ring later | The corrected branch changes only the first occurrence; both forms are retained. |

Validation: `make tex` succeeds. All 82 non-index source labels
(including the 69 numbered statements), 91 reference targets, ten
footnotes, and twelve displayed formulas or diagrams were checked
against the corrected source. The displays include both diagrams
and the tagged equation. Compiled statement numbers match the original,
including the repeated 9.2. The PDF build has no TeX warnings,
unresolved references, or duplicate destinations. Representative pages
and the diagrams were visually checked.

These checks do not settle the mathematical questions above;
scholarly proofreading remains outstanding.

## Continuation

The next untranslated exposé is **II — Smooth morphisms: generalities,
differential properties**. Begin with its opening convention and
**II.1 — Generalities**. Keep source review of Exposé I distinct from
translation coverage; no Lean formalization of Exposé I is included yet.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
