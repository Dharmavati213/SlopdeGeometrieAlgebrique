# SGA 1, Exposé VI — Fibered categories and descent

Full English draft of the whole exposé: sections 0–12 and the
bibliography, with proofs, the footnote, and all diagrams. On 2026-09-24
the English was compared with the corrected French sentence by sentence
(see [Review against the French](#review-against-the-french-2026-09-24)).
Deeper scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-VI.tex`](SGA1-VI.tex) | Standalone wrapper (`amsart`): macros, theorem environments, title, and abstract |
| [`en-01.tex`](en-01.tex) | §0 Introduction; §1 Universes, categories, equivalence of categories; §2 Categories over another; §3 Change of base in categories over `𝓔` |
| [`en-02.tex`](en-02.tex) | §4 Fiber-categories; equivalence of `𝓔`-categories; §5 Cartesian morphisms, inverse images, cartesian functors; §6 Fibered categories and prefibered categories. Products and change of base therein |
| [`en-03.tex`](en-03.tex) | §7 Cloven categories over `𝓔`; §8 Cloven category defined by a pseudofunctor `𝓔° → Cat`; §9 Example: cloven category defined by a functor `𝓔° → Cat`; split categories over `𝓔` |
| [`en-04.tex`](en-04.tex) | §10 Cofibered categories, bifibered categories; §11 Various examples; §12 Functors on a cloven category; bibliography |
| [`SGA1-VI.pdf`](SGA1-VI.pdf) | Compiled English draft |

The body was formerly a single file, `SGA1-VI.tex`. It has been split
into the four fragments above with no change to the text; the wrapper
now `\input`s them.

Build with `make -C translation/SGA1/ExposeVI` from the repository root,
or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsart`, `amsthm`, `mathtools`, `xy`, and
`enumitem`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 9929–12788, from
`\chapter{Cat\'egories fibr\'ees et descente}` and `\label{VI}` up to,
but not including, the chapter of Exposé VIII. Following the
conventions, the source's closing `\refstepcounter{chapter}` and its
table-of-contents line saying that Exposé VII does not exist are
omitted. The source covers original pages 145–194. Page 145 begins at
the chapter heading, which the wrapper renders as the title, so the
`% original p. N` comments run from 146 to 194.
The French TeX and PDF are not included in this repository.

This exposé follows the rules in [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1, Exposé VI”. It does not use the shared package
`sga1-en.sty` of the later exposés. The wrapper sets
`\setcounter{section}{-1}`, so the Introduction is §0, and it numbers
statements on one counter per section, as in the source. The source's
starred remark environments (`remarquesstar`, `remarquestar`) become
unnumbered Remarks/Remark. Labels keep the source's keys (`VI.m.n`);
references use `\ref`.

Terminology follows the mandatory table in
[`CONVENTIONS.md`](../../CONVENTIONS.md), section “SGA 1, Exposé VI”.
In particular:

| French | English |
| --- | --- |
| catégorie fibrée / préfibrée | fibered / prefibered category |
| catégorie clivée; clivage (normalisé) | cloven category; (normalized) cleavage |
| catégorie scindée | split category |
| catégorie-fibre | fiber-category |
| morphisme cartésien / cocartésien; foncteur cartésien | cartesian / cocartesian morphism; cartesian functor |
| catégorie cofibrée / bifibrée | cofibered / bifibered category |
| pseudo-foncteur | pseudofunctor |
| changement de base | change of base |
| produit fibré | fibered product |
| univers | universe |

The later exposés also adopted “change of base” (see the READMEs of
Exposés IV, V, and VIII–XIII).

## Review against the French (2026-09-24)

The four fragments were compared with the corrected French, sentence by
sentence. Changes made:

- `en-01.tex`: the chapter label `\label{VI}` was added, and a small
  omission was restored (“l'espace somme des `X_i`” → “the sum space of
  the `X_i`”).
- `en-02.tex`: no changes. All 478 formulas were compared with the French
  and match.
- `en-03.tex`: one typographic fix (`\ie` before a colon).
- `en-04.tex`: two fixes. In §11 a), `\mathbf{\Delta}^1` is now
  `\mathbf{\Delta^1}` (four times). In the bibliography, “décembre” is
  now “December”.

The review found the source points below, all of them in the French.

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| §0 Introduction | “one says that `X` is ‘locally trivial’” | `E` is presumably meant. |
| §1, quasi-inverse | The quasi-inverse is defined only by `GF ≅ id_C` | The half `FG ≅ id_{C'}` is missing. |
| §1 | `φ: GF → id_{C'}` | Presumably `FG`. |
| §1 | `S ↦ G(S)`, `S ↦ φ(S)` | Presumably `S'`. |
| §2, after (IV) | “`v*f` or `u*g`” | Presumably `g*u`. |
| §3 | `E' → SheafHom_{E''/-}(F', G')` | A stray double prime. |
| §5, after the proof of VI.5.4 | “It follows from 5.4 (iii)” | 5.4 has no (iii); 5.3 (iii) is meant. |
| §5, before VI.5.5 | “especially for the case where `𝓕 = 𝓖`” | `𝓕 = 𝓔` is meant. |
| §6, after VI.6.11 | “cartesian diagrams are characterized” | Probably “cartesian morphisms” (uncertain). |
| §7 | “if a category over `𝓔` is a product … then `F` is endowed” | `F` is not introduced. |
| Proof of VI.7.4 B) | “`(fgh)`-morphisms `h^*g^*f^*(ξ) → (fgh)^*(ξ)`”; “by applying `h`” | Both objects lie over the same base, so these are morphisms of the fiber (`V`-morphisms); `h^*` is meant. |
| §8, composite after `u∘v = c_{f,g}(ξ)·g^*(u)·v` | The first arrow is labeled `u` | It should be `v`. |
| §8, item 2) | `\bar ξ = (ξ, S)` | Written `(S, ξ)` elsewhere. |
| §9, last sentence | `φ(S)` are “rigid and discrete” categories | The argument gives “rigid and reduced”. |
| §10 | “if `𝓕°` is prefibered, resp. fibered, over `𝓔`” | `𝓔°` is expected. |
| §11 b) | `(gf)_* = g_* f_*` with `g: U → T` | `(fg)_* = f_* g_*`. |
| §11 c) | “section of `𝓔'` over `𝓕'`” | The order is reversed. |
| §11 e) | `∏ 𝓔_i` | `∏ 𝓕_i`. |
| §12 | `ψ_f: G_T f → G_S` | `^*` is missing on `f`. |
| §12, diagram c) | `\phi_f` next to `\varphi_f` | Inconsistent notation. |
| VI.12.1 | `S ∈ Ob(𝓕)`, `f ∈ Fl(𝓕)` | `𝓔` is meant. |
| §12 | `u(ξ): F(S) = F_S(ξ)`; `v: ζ → ν`; `u': ξ → f(η)` | `F(ξ)`; `ζ → η`; `η → f^*(ξ)`. |
| §12, large diagram | `F_u` | `F_U` is meant. |
| §12, diagram b') | `φ_{g^*} f^*_F`, and subscripts `_F` for `_{𝓕}` | Inconsistent notation. |
| §12 | “(where `f: T → S` is a morphism in `𝓔` is in a unique way)” | The parenthesis is garbled. |

### Found during the Lean formalization (2026-09)

These points were found while formalizing the exposé in `lean/SGA/SGA1/`; the Lean statements use the corrected forms.

| Location | Source wording | Point |
| --- | --- | --- |
| VI.9, rigid fibres | “the existence of a splitting is unchanged when passing to an `𝓔`-equivalent category” | False for normalized splittings: the fibered category `threeToTwo` (`SGA.SGA1.ExposeVI.not_exists_isSplitting_threeToTwo`) has rigid fibres and no splitting. The version up to `𝓔`-equivalence holds and is formalized (`exists_isSplitting_of_rigid`). |
| Remarks after VI.6.1 | Condition (i): “every arrow of `F` is cartesian” | The equivalence with “`F` is fibered in groupoids” needs `F` to be prefibered; without the lifting condition it fails. The Lean statements (`SGA.SGA1.ExposeVI.allMorphismsCartesian_iff_fiberedInGroupoids`, `allMorphismsCartesian_and_isPreFibered_iff`) assume it. |

## Validation

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, was run on the four fragments against source lines
9929–12788. It finds the same 53 non-index labels, 37 references,
4 citations, 1 footnote, 15 diagrams, 311 displays, and 25 list items as
in the corrected French. The differences it reports are the ones the
Exposé VI conventions require:

- the chapter heading is the wrapper's title;
- the starred remark environments become `remark`/`remarks`;
- `\setcounter{section}{-1}` is set in the wrapper;
- the closing `\refstepcounter{chapter}` is dropped.

The wrapper compiles to a 25-page PDF with no errors, LaTeX warnings, or
undefined references. These checks, and the review above, do not settle
the mathematical questions listed; deeper scholarly proofreading remains
outstanding.

## Continuation

All of SGA 1 is now translated (see
[`../../README.md`](../../README.md)). Lean for this exposé lives at
`lean/SGA/SGA1/ExposeVI.lean`, with modules in `lean/SGA/SGA1/ExposeVI/`.

License: [`../../LICENSE`](../../LICENSE) (MIT for the
translator's contribution).
