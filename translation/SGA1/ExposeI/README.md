# SGA 1, Exposé I — Étale morphisms

Complete English draft of the exposé: the opening convention and all
eleven sections, with proofs, footnotes, and the closing discussion of
geometrically unibranch schemes. Translated from the corrected SMF
branch of [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2);
compared with the French sentence by sentence on 2026-09-24 (see
[Review against the French](#review-against-the-french-2026-09-24)).
Deeper scholarly proofreading is outstanding.

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

Build: `make -C translation/SGA1/ExposeI` (TeX Live with `latexmk`,
`amsbook`, `xy`, `hyperref`); `make tex` builds every exposé.

## Source and translation choices

`smf_doc-math_3_01.tex` (corrected branch, `orig = false`), from
`\chapter{Morphismes \'etales}` and `\label{I}` up to, but not including,
the chapter beginning `\chapter{Morphismes lisses:...}` and
`\label{II}`: printed SMF pages 1–23, original page markers 1–28. The
French TeX and PDF are not in this repository.

The fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md): the
corrected branch, all non-index labels, proofs, diagrams, and translated
footnotes are kept; indexes and source pagination machinery are omitted;
original page numbers remain as comments.

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

The historical synonym “net” is kept where the source uses it;
Definition 3.2 identifies it with “unramified”. The author's word
*multiplodoque* is kept. Informal asides and requests to supply examples
are translated as part of the text.

The corrected source assigns 9.2 to both a corollary and the next
proposition. Both numbers are kept, with the source labels `I.9.2` and
`prop:I.9.2` and distinct PDF destinations. The equation tagged `(*)`
keeps its label `eq:I.9.5.*`.

References within the exposé use `\ref`. A reference beyond it is
written `\SourceRef{source-label}{printed-number}`, which keeps the
source key and prints the source's number without inventing a
destination; it becomes a `\ref` if that label is defined.

## Review against the French (2026-09-24)

The whole exposé was compared with the corrected French, sentence by
sentence, in four parts: `en-01-03.tex` and `en-04-06.tex`; `en-07.tex`
and `en-08.tex`; `en-09.tex`; `en-10.tex` and `en-11.tex`. There was one
change: an omitted word was restored in `en-10.tex` (“we shall admit
*here* Proposition 10.7”). The review found no other omissions,
mistranslations, or formula errors. It confirmed that the statement
numbering of §9 matches the source (Proposition 9.1, Corollary 9.2,
Proposition 9.2, …) and that all sixteen labels of `en-09.tex` are
present. It confirmed all twelve source points of the first table below
in the French and found the further points of the second.

## Source points for scholarly review

Apparent slips in the corrected French TeX and the matching PDF, kept as
printed per [`CONVENTIONS.md`](../../CONVENTIONS.md).

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

Further points found by the 2026-09-24 review, also kept as printed:

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| I.2, definition of quasi-finite morphisms | “or the `Y`-prescheme `f` is said to be quasi-finite at `x`” | The `Y`-prescheme is `X`. |
| Proof of I.5.5 | “sections of `X/Y`”, after reducing to the case `Y = S` | The sections are those of `X` over `S`. |
| Proof of I.5.8 | “the two algebras over `k(g(x))`” | Queried by the review. The source writes a plain `k` here, not the `\kres` macro it uses for residue fields elsewhere (the two look the same in print). |
| After I.7.8 | “the jargon of 7.6” | This refers to the last sentence of I.7.6 (the étale case); the word is unexpected. |
| Proof of I.10.1 | “in the field `K_i` of `X`” | `K_i` is the field of the component `X_i` (see also the point on I.10.1 above). |
| Proof of I.10.2 | “`R/K` separable” | `L/K` is meant. |
| Before I.10.3; I.10.4(ii) | An algebra “unramified over `X`” | Arguably over `Y`. |
| I.10.9 | “over U” with `U` outside math mode | Typographic slip. |

### Found during the Lean formalization (2026-09)

Found while formalizing the exposé in `lean/SGA/SGA1/ExposeI.lean`
(modules in `lean/SGA/SGA1/ExposeI/`); the Lean statements use the
corrected forms.

| Location | Source wording | Point |
| --- | --- | --- |
| I.9.8 | The trace formula is stated for `F` monic separable with no restriction on its coefficients. | It needs `F ∈ A[t]`: for `F = t² + t/2` over `ℤ ⊆ ℚ` the conclusion fails. The Lean statement (`SGA.SGA1.ExposeI.forall_trace_mul_root_pow_mem_iff`) adds this hypothesis. |
| I.10.7 and I.10.9 | “upper semicontinuous” | With `n(y)` the number of geometric points of the fiber, the function is lower semicontinuous: `n(y) ≤ n(y')` for `y'` near `y` (an open immersion gives `n = 1` on the open set and `0` off it). The Lean statements use this direction (`SGA.SGA1.ExposeI.geometricFiberCard_upperSemicontinuous_Statement`). |

## Validation

`make tex` succeeds. All 82 non-index source labels (including the
69 numbered statements), 91 reference targets, ten footnotes, and twelve
displayed formulas or diagrams were checked against the corrected
source. The displays include both diagrams and the tagged equation.
Compiled statement numbers match the source, including the repeated 9.2.
The PDF build has no TeX warnings, unresolved references, or duplicate
destinations. Representative pages and the diagrams were checked
visually.

License: [`../../LICENSE`](../../LICENSE) (MIT for the translator's
contribution).
