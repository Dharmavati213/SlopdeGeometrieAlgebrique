# SGA 1, Exposé V — The fundamental group: generalities

Full English draft of the whole exposé: sections 0–9, with proofs,
footnotes, and all diagrams. It was translated from the corrected SMF
branch in five chunks. A second reviewer then checked each chunk against
the French (2026-09-24). Scholarly proofreading remains outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-V.tex`](SGA1-V.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-1.tex`](en-1.tex) | §0 Introduction; §1 Prescheme with a finite group of operators, quotient prescheme |
| [`en-2.tex`](en-2.tex) | §2 Decomposition and inertia groups. Étale case; §3 Automorphisms and morphisms of étale coverings |
| [`en-3.tex`](en-3.tex) | §4 Axiomatic conditions for a Galois theory (conditions a)–n), V.4.1, V.4.2) |
| [`en-4.tex`](en-4.tex) | §5 Galois categories (V.5.1–V.5.11) |
| [`en-5.tex`](en-5.tex) | §6 Exact functors from one Galois category into another; §7 The case of preschemes; §8 The case of a normal base prescheme; §9 The case of non-connected preschemes: multi-Galois categories |
| [`SGA1-V.pdf`](SGA1-V.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/ExposeV` from the repository root,
or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 7383–9928, from
`\chapter{Le groupe fondamental: g\'en\'eralit\'es}` and `\label{V}` up
to, but not including, the chapter of Exposé VI.
This covers original page markers 105–144.
The French TeX and PDF are not included in this repository.

The body fragments follow [`CONVENTIONS.md`](../../CONVENTIONS.md),
section “SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and use the
shared package [`sga1-en.sty`](../sga1-en.sty). All non-index labels,
`\Ref`/`\eqref` keys, footnotes, and diagrams are kept. References to
other exposés print the source's numbers: `I~\Ref{I.9.7}` prints
“I 9.7”, as in the SMF volume. Original page numbers remain as
`% original p. N` comments. Indexes and SMF page-layout commands are
omitted.

House rules applied here as in the other new exposés: *n°* / *numéro*
is rendered “no.” (`\No`), and *changement de base* is rendered “change
of base”, the Exposé VI term. After the reviews, “base change” was
replaced by “change of base” throughout Exposés IV, V, VIII, IX, and X.

Exposé-specific choices:

- **Repeated numbers 1.7 and 1.8.** The corrected source has
  `\setcounter{subsection}{6}` after Proposition 1.8. The two following
  corollaries are therefore numbered 1.7 and 1.8 again, after
  Definition 1.7 and Proposition 1.8. The counter command is kept, so the
  English repeats both numbers as the source does. The labels stay
  distinct (`V.1.7`/`cor:V.1.7`, `V.1.8`/`cor:V.1.8`). hyperref reports
  duplicate PDF destinations for these two numbers.
- **“fiber-functor” and “fiber functor”.** The source writes
  *foncteur-fibre* (with a hyphen) once, for the functor `E_X` associated
  with `X`, and *foncteur fibre* elsewhere. The English keeps the
  distinction: “fiber-functor” and “fiber functor”.
- **“Âne qui trotte.”** This phrase follows item m) of the list in §4,
  in place of a proof. The translator reads it as a colloquial sign that
  the verification is routine, and renders it literally: “A trotting
  donkey.”

Exposé V terminology:

| French | English |
| --- | --- |
| catégorie galoisienne; catégorie multigaloisienne | Galois category; multi-Galois category |
| foncteur fondamental | fundamental functor |
| foncteur fibre; foncteur-fibre (`E_X`) | fiber functor; fiber-functor |
| pro-objet; pro-groupe (fondamental) | pro-object; (fundamental) pro-group |
| objet ponctué | pointed object |
| épimorphisme strict | strict epimorphism |
| groupe (fini) d'opérateurs | (finite) group of operators |
| préschéma quotient | quotient prescheme |
| groupe de décomposition; groupe d'inertie | decomposition group; inertia group |
| revêtement principal | principal covering |

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| V.0 | “As in 1961, we shall confine ourselves” | The previous seminar was that of 1960. |
| Proof of V.1.2 | Flat “change of base `A → A'`” | `B → B'` may be meant. |
| V.1.3 | “groupe d'automorphismes finis” (plural *finis*) | “Finite group of automorphisms” appears to be meant. |
| Proof of V.1.5 | “`Y` as `Spec(A)^G`” | `Spec(A^G)` is meant. |
| Proof of Proposition V.1.8 | “Ces transformés” | Probably *Ses* (its transforms). |
| After Corollary 1.7 (the second 1.7) | “et les `s ∈ G` opèrent” | The sentence is ungrammatical. |
| V.1.9 | `\cal{O}_Y'` | `\cal{O}_{Y'}` is meant. |
| End of §1 | “finite over `Y` if `Y` is” | Presumably “if `G` is”. |
| Proof of V.2.2 | Local rings `A_x` corresponding to the points `x_i`; “finite flat extension of `A`” | `A_i` is meant; `B` may be meant in the second phrase. |
| Proof of V.2.4 | “`s` acts trivially on `G`”; residue homomorphism written `k(x)/k(x')` | `X` is meant; `x'` is undefined (`u(x)` is meant). |
| Before V.2.6 | `T_e = id_x` | Lower-case `x` for `X`. |
| Proof of V.2.7 | `G`-morphism `X × G → X` | `Y × G → X` seems meant. |
| V.3.6 | Statement: `X → X'` a strict epimorphism and `X' → X''` a monomorphism | The proof shows that `X → X''` and `X'' → X'` are meant. |
| V.3.7 | `\mathit{\Omega}` next to `\Omega` | Inconsistent notation. |
| V.4 c) | “loc. cit. prop. 3.1”, encoded as `\Ref{V.3.1}` | The reference is to Bourbaki exposé 195, Prop. 3.1, but the key prints and links as this exposé's 3.1. |
| V.4 g) | Factorization written `P --j--> P_j` | The arrow should be `φ_j`. |
| V.4 i) | “Then `G ×_G E` exists” | `Q ×_G E` is meant. |
| V.5.1 | “the canonical functor of `C(π)_x`” | The subscript `x` looks stray. |
| Proof of V.5.2 | Functor category written `C → Ens`; “compactness of `π`” | `C(π) → Ens` seems meant; compactness of `X` is what is needed. |
| V.5.6 (iii) | “implies `F(X) ≠ ∅`” | Presumably `F'(X)`. |
| After V.5.9 | “on peut vérifier … il suffit” | “Pour vérifier” is meant. |
| After V.5.10 | “the condition considered in V.5.8” | V.5.9 (topological spaces) seems meant. |
| After V.5.10 and V.5.11 | The fundamental pro-group `Π` called `G` in three places; `Π(F)`, `X(F)` next to `F(Π)` | Inconsistent notation. |
| Proof of V.6.1 | “`F`, assumed left exact, transforms `e_C` into `e_{C'}`”; in (iii) ⇒ (i), “`F` exact and conservative” | `H` is meant in the first; probably `F'` in the second. |
| After V.6.1 | Notation `F(X) = E_X(F)` “introduced in no. V.6” | It was introduced in V.5. |
| Display before “pointed object” | “(where `F' = F'∘H`)” | Should read `F = F'∘H`. |
| V.6.6 | “`X` isomorphic as a pointed object to a quotient”, “`X` isomorphic to an `H(X)`” | `X'` in both places. |
| Remark after V.6.6 | “replacing `U` by a conjugate subgroup of `U`” | `U'` is meant. |
| V.6.11 | `H': C → C''`; `Ker u ⊂ Im u'` | `C' → C''` is meant; the inclusions look swapped. |
| V.6.12 | “right inverse of `u`” | A left inverse would be usual (uncertain). |
| V.6.13 | “stabilizer of the marked element `a` of `F(X)`” | `F(S)` is meant. |
| V.7 | “the fiber of `G` at `s`”; “ces points” | `Π_1^S` is meant; presumably *ses points*. |
| V.7 | “`(a' = f(a))`”; `π_1(S; A)` with capital `A`; last paragraph “pro-groups over `S`” | Should be `a = f(a')`, lower-case `a`, and over `S'`. |
| V.7 | `π_1(S; a', a)` called the paths from `a` to `a'` | The direction may be reversed (uncertain). |
| French slips | “il suffit `F(u)` le soit” (V.4 a)); “pout tout j” (after V.4 j)); “n'est évidemment par surabondante” (V.2.5); missing period before “`F(X) = E_X(F)` peut être appelé” (before V.5.8); “`X`” outside math mode in V.2.3 | These do not affect the English. |

## Validation

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, finds for each chunk the same non-index labels, reference
keys, footnotes, diagrams, displayed formulas, list items, statement
environments, and counter commands as in the corrected French. For the
whole exposé these are 66 labels, 104 references, 6 footnotes,
4 diagrams, and 164 displays. The wrapper compiles to a 28-page PDF with
no errors or undefined references. The only warnings are the two
duplicate destinations noted above.

A second reviewer checked all five chunks against the French and made
six fixes:

- punctuation in the proof of V.1.5;
- a mistranslated direction of a correspondence (`Q ↦ X`) in the proof
  after V.5.2;
- four renderings of *numéro* (“this number” and similar) changed to
  “no.”.

The reviewer confirmed the translator's source points and added the
points on V.1.3, V.3.7, the proof of V.5.2 (compactness), and the
paragraph after V.5.9. These checks do not settle the mathematical
questions above; scholarly proofreading remains outstanding.

License: [`../../LICENSE`](../../LICENSE) (CC BY-SA 4.0 for the
translator's contribution).
