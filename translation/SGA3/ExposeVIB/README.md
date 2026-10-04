# SGA 3, VIB

Generalities on group schemes.

Author of the exposé: J.-E. Bertin.

French source (local only): `source/SGA3/Exp6B-13oct24.pdf` (112 pages),
the Gille–Polo recomposition.

| | |
| --- | --- |
| Status | Complete English draft: en-01.tex–en-18.tex translated and checked against the source PDF. Independent scholarly proofreading remains outstanding. |
| Chunks | en-01.tex (pp. 1–8), en-02.tex (pp. 9–16), en-03.tex (pp. 17–21), en-04.tex (pp. 22–26), en-05.tex (pp. 27–32), en-06.tex (pp. 33–38), en-07.tex (pp. 39–46), en-08.tex (pp. 47–54), en-09.tex (pp. 55–60), en-10.tex (pp. 61–66), en-11.tex (pp. 67–72), en-12.tex (pp. 73–78), en-13.tex (pp. 79–84), en-14.tex (pp. 85–90), en-15.tex (pp. 91–96), en-16.tex (pp. 97–102), en-17.tex (pp. 103–108), en-18.tex (pp. 109–112) |

All eighteen fragments contain every sentence, formula, proof, diagram, bibliography item and
footnote assigned to source pp. 1–112 (p. 112 is blank). Editor notes 0–140, reused notes 56 and 117, the
original starred notes, and the embedded Theorem 5.3A in editor note 34 are
retained. Underlining distinguishes the underlying identity-component sets
from the group functors. Formula closures and diagrams were inspected in the
source PDF, and representative English pages were rendered and inspected.

Page-boundary assignments follow the sentence rule. The sentence defining the multiplication morphism in
2.0, begun on p. 8, is completed in en-01.tex, while the next sentence begun on
p. 9 starts en-02.tex. Corollary 5.6.2 is opened at the end of en-05.tex and
completed in en-06.tex. Remark 6.1.1, begun on p. 38, is completed with its
sentence and display from p. 39 in en-06.tex. The first-case sentence of the
proof of 7.4 begun on p. 54 is completed on p. 55 in en-08.tex. en-09.tex therefore starts with the sentence saying that the sequence is stationary.
No environment remains open at the en-08.tex boundary. The last sentence of
10.11, begun on p. 72, is completed in en-11.tex; en-12.tex starts Corollary
10.11.1. The final sentence begun on p. 84 in the proof of 11.8.1 is completed
in en-13.tex, with the proof closed in en-14.tex. The invariance criterion
begun on p. 96 in the proof of 11.17 is completed through the definition of
m_13 on p. 97 in en-15.tex. Remark 13.6 opens in en-17.tex and closes in
en-18.tex; its final sentence begun on p. 108 is completed in en-17.tex.

`make -C translation/SGA3/ExposeVIB` builds the complete draft (89 pages).
`python3 translation/SGA3/check_coverage.py --expose VIB --source-dir source/SGA3 --require-pdf`
passes: 18/18 populated fragments, all extracted statement headings labelled,
no duplicate labels, and no missing source editor-note markers.
There are 197 labels, 141 editor-note bodies (139 `nde`, 2 `ndetext`),
and 26 bibliography entries. `git diff --check` passes for this directory.
Every source page in the second half was inspected as an image; representative
English physical PDF pages 47, 55, 65, 67, 72, 77, 84, 88 and 89 were inspected.
The build has only small layout warnings (overfull boxes below 3.2pt), with
no substantial clipping. These structural and layout checks do not certify
independent scholarly proofreading.

Clear source slips corrected in the English, marked `% typo:`:

- 1.4 proof: `limitive` → limit.
- 2.10: `quel soit` → `quel que soit`.
- 4.2 proof: `composante irréductibles` → `composantes irréductibles`.
- Editor note 34: `exemples du` → `exemples dus`.
- 5.6.1.0 proof: duplicated `le` before `changement` removed.
- 5.8.4: extra closing parenthesis in the equivalence relation removed;
  missing period after the openness assertion supplied.
- 6.5: missing `est` supplied in `lorsque H un`.
- 6.5.2 proof: `S et noethérien` → `S est noethérien`.
- Editor note 69: `sous l'hypothèses` and `peut-être omise` corrected
  grammatically.

- 8.4 proof: `Nous somme` → `Nous sommes`.
- 11.0: `aux limite inductives` → `aux limites inductives`.
- 11.8.0, 11.10.1, 11.12 and bibliography: visible encoding corruption
  in “counit” and the name Lütkebohmert corrected.
- 11.9.1: `des morphisme` → `des morphismes`.
- 11.17 proof (d): duplicated `est` removed.
- 12.10 proof: `toplogie` → `topologie`; final period supplied before
  Corollary 12.10.1.

Source anomalies retained as printed, marked `% typo?:`:

- 1.2 proof calls the closure image a reduced subgroup scheme of G.
- 1.3.0 proof writes B/n, and 1.4.2 writes the unit k-group for an artinian A.
- 2.1 display omits b before (h,v); 2.5 uses W_X for the flatness locus,
  cites EGA IV_2 11.3.10, and uses G rather than u in two concluding hypotheses.
- 3.8 proof says “over S” and cites EGA IV_2 8.14.2.
- 4.2 proof changes the generic-point letter x to ξ in the next sentence.
- 5.6.1.0 proof says f is universally open at x and f′ at x′; 5.6.1 uses
  O_{S′,s}; 5.6.2.0 (iii) uses products over S although the base is k.
- Editor note 44 uses an undefined B_x.
- 5.8.4 uses f:X→k instead of X′ and calls the pointed homeomorphism q_F.
- 6.2.3 proof omits `plat` in “fidèlement et quasi-compact”.
- 6.5 (i′) refers to the nonexistent 6.2 (iv).
- 7.1 (iii) writes X_S instead of X_{i,S}.
- 7.3 proof says X_S is reduced for arbitrary S and ends (iii) with Γ_G(f)
  rather than Γ_G(φ).

- 7.4 proof uses g′ⁿ(Yⁿ), without a prime on Y, in the second-case inclusion.
- 7.6.0 calls the subgroup functor a k-functor although the base is S.
- 7.6 proof omits the target of μ and asserts finite presentation; 7.8 repeats
  the same two commutator factors in its base-change surjectivity argument.
- 7.9 proof (i) ends with (A,B)₀ rather than (A·B)₀, and (ii) cites EGA IV₄.
- 8.4 and 10.12.1 use G rather than G_s or G_η in nilpotent recurrences;
  8.4 says G′_α is flat and separated over A.
- 9.2 (vii) uses S′ rather than S.
- 10.7 cites EGA IV₂ for the limit results; 10.9 uses H_i → S rather than S_i;
  10.14 (ii) ends with (G,X) rather than (G,H).
- 11.0 uses U rather than U′ in q′⁻¹(U); 11.7 refers to a restriction of μ.
- 11.10.bis writes δ = θ ∘ τ with θ on f*(E), labels the lower diagram arrow
  τ rather than δ, and uses π rather than π_α in its final diagram.
- 11.12 writes ε(a_j) rather than ε(a_i) in the final summation.
- 11.16 sums ρ(e_j) from i = 1 despite a basis starting at e₀, and announces
  H′ = H in the proof although the final conclusion is H′ ⊂ H.
- 11.17 proof (c) cites (a), rather than (b); 11.18.1 drops primes on G_i;
  11.18.2 prints G/N as the target of the limit exact sequence and uses G′
  for the identity-section square while referring to augmentation B → k.
- 13.1 (i) writes U ↪ X rather than U ↪ S; 13.5 (ii) says “some n” while
  the exponent and general linear group use d; 13.7 calls id_F ⊗ ε a section.
