# SGA 1, Exposé III — Smooth morphisms: extension properties

English translation of the complete Exposé III, including all seven
sections, proofs, footnotes, diagrams, and the application to formal and
ordinary smooth schemes over a complete local ring. On 2026-09-24 the
English was compared with the corrected French sentence by sentence (see
[Review against the French](#review-against-the-french-2026-09-24)).
Deeper scholarly proofreading remains outstanding.

## Source

The source is the corrected SMF recomposition of:

> A. Grothendieck and M. Raynaud, *Revêtements étales et groupe fondamental*
> (SGA 1), Séminaire de géométrie algébrique du Bois Marie, 1960–61,
> Documents Mathématiques 3, Société Mathématique de France.

- arXiv record: <https://arxiv.org/abs/math/0206203v2>
- corrected PDF: <https://arxiv.org/pdf/math/0206203v2>
- source archive: <https://arxiv.org/e-print/math/0206203v2>
- SMF publication page: <https://smf.emath.fr/publications/revetements-etales-et-groupe-fondamental-sga-1-seminaire-de-geometrie-algebrique-du>
- navigable bilingual edition: <https://grothendiecksga.com/read/sga1/III.html>

In the corrected source, Exposé III is the chapter beginning with
`\chapter{Morphismes lisses: propri\'et\'es~de~prolongement}` and ending
before `\chapter{Morphismes plats}`. It corresponds to printed pages 58–86
of the recomposed volume (approximately PDF pages 65–86).

The French source is not included in this repository. Source-specific
pagination, index entries, and corrected-branch conditionals are omitted
according to [`../../CONVENTIONS.md`](../../CONVENTIONS.md); where a
conditional is present, the corrected (`orig = false`) branch is retained.

## Files

- [`SGA1-III.tex`](SGA1-III.tex) — standalone wrapper and preamble
- `sections/en-01.tex` through `sections/en-07.tex` — translated sections
- [`SGA1-III.pdf`](SGA1-III.pdf) — compiled English draft

Build from the repository root with:

```bash
make -C translation/SGA1/ExposeIII
```

or build all translated exposés with `make tex`.

## Review against the French (2026-09-24)

The whole exposé was compared with the corrected French, sentence by
sentence, in three parts: `en-01`–`en-02`, `en-03`–`en-05`, and
`en-06`–`en-07`.

**Numbering.** Before the review, the wrapper typeset the source's
numbered remarks without numbers. Remarks 1.2, Remark 1.8, Remark 4.3,
and Remarks 6.4 therefore printed unnumbered, and every later statement
in their sections was numbered one too low. In §6 the numbered
subsections 6.5 and 6.6 also printed as 6.1 and 6.2, because they used a
separate counter, and Corollaries 6.7–6.10 printed as 6.4–6.7.

The wrapper now defines numbered `remark` and `remarks` environments on
the shared theorem counter, and unnumbered `remarkstar` and
`remarksstar` for the source's starred forms. The remark after 2.1 is
now a `remarkstar`. The earlier per-statement workarounds were removed,
and the §6 counters are synchronized. Remarks are now numbered as in the
French, and the compiled statement numbers were checked against the
source.

**Text.** The other changes were:

- **Mistranslations (eight).** In 1.4, *de sorte que* is now “so that”.
  In the proof of 2.1, the causal structure of (v) ⇒ (i) is restored, and
  so is *comme* in (iii) ⇒ (ii). In 5.2, “libre de type fini” had been
  rendered “locally free” and is now “free”, as printed. In 6.6,
  *théorie des modules* is now “theory of moduli”, no longer “module
  theory”. Further fixes: the introduction to §6 (“over `f^{-1}(O)`”),
  the emphasis in Serre's footnote in §7, and “Then” in §7 a).
- **Formulas restored as printed (three).** 1.4 (i) is back to the
  printed `B`. The translator had silently corrected `Y' → Y'_0` in the
  proof of 3.1 and `A_0` in the proof of 5.1; both now read as printed.
- **Other formula fixes.** `\Im` had printed in Fraktur and is now
  `\operatorname{Im}`. Doubled prefixes such as “I I.3.2” are now
  “I 3.2”. `\gr` was fixed, and a stray `\goth X` was removed.
- **Omissions restored.** The second “(for example)” before 5.7, and the
  quotation marks around “glue”.
- **Typographic fixes.** Emphasis, word order, spacing, double periods,
  `\No`, ties, and the bold brackets of the 2003 note.

Two stylistic inconsistencies remain for proofreading. Exposé III writes
sheaves of ideals and modules in lower case. The conventions for the
front matter and Exposés IV, V, VIII–XIII keep the capitals (Module,
Algebra, Ideal), and so does Exposé II 4.14 since its review. Both
“sub-prescheme” and “subprescheme” occur.

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They were
found by the 2026-09-24 review and have been retained in the
translation, in accordance with the convention against silently
repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Introduction | `O_x` | Presumably `O_y`. |
| After III.1.3 | “`L`, `k`, `k'` are the residue fields of `A`, `B`, `A'`” | Presumably of `B`, `A`, `A'`. |
| III.1.4 (i) | “localizations of `B`” | Presumably `B'`. |
| Proof of III.1.9 | The two references of a “resp.” construction | They appear swapped (III.1.5 and II.5.2). |
| III.2.1 (iii) | “continuous `A`-homomorphism `B → C`” | Presumably `B → C/J`. |
| Proof of III.2.1 | `g(x, y)` | Presumably `g(xy)`. |
| Proof of III.2.1, (iv) ⇒ (i) | “un peu précis” (rendered “slightly more precise”) | *Plus* appears to be missing in the French. |
| Proof of III.3.1 | “`Y`-morphism `Y' → Y'_0`” | `Y' → Y[t_1, …, t_n]` is meant. |
| Comment after III.4.1 (a) | Isomorphism to `O_{Y_0}`; `f^{-1}` | `O_{U_0}` and `f_0^{-1}` are meant. |
| Proof of III.4.1 | `X ×_{Y'} Y'_0 ≅ X'` | The right-hand side should be `X_0`. |
| §5, opening | “`G` a sheaf of groups on `X`” | `T` is meant. |
| Proof of III.5.1 | `A_0`; “homomorphisms of Modules `M → A`”; “`Y'_0` … the sheaf of algebras `A_0`” | `\cal A_0`; `M → O_Y`; the spectrum of `\cal A_0` is meant. |
| III.5.2 | “free of finite type” | Locally free is meant. |
| §6, introduction | “a subprescheme `X_n` smooth over `S_n`” | Probably “prescheme”. |
| Before III.6.3 | “the gluing condition being none other than (3)” | Probably (4) or (1). |
| §7 b) | “reducing along `k`” | Probably `X_0`. |

Validation: the wrapper compiles with `make -C translation/SGA1/ExposeIII`
to a 20-page PDF with no errors or undefined references. These checks,
and the review above, do not settle the mathematical questions listed;
deeper scholarly proofreading remains outstanding.

## Continuation

All of SGA 1 is now translated (see
[`../../README.md`](../../README.md)). Lean for this exposé does not
exist yet; `lean/SGA/SGA1/` covers Exposés I and VI.

The English translation is an unofficial derivative work. The translator's
contribution is licensed under CC BY-SA 4.0; see [`../../LICENSE`](../../LICENSE)
and [`../../../COPYRIGHT.md`](../../../COPYRIGHT.md).
