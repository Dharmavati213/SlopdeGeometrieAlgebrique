# SGA 1, Exposé III — Smooth morphisms: extension properties

Complete English draft of the exposé: all seven sections, with proofs,
footnotes, and diagrams, ending with the application to formal and
ordinary smooth schemes over a complete local ring. Translated from the
corrected SMF branch of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2); compared
with the French sentence by sentence on 2026-09-24 (see
[Review against the French](#review-against-the-french-2026-09-24)).
Deeper scholarly proofreading is outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-III.tex`](SGA1-III.tex) | Standalone wrapper and preamble |
| [`sections/en-01.tex`](sections/en-01.tex) – [`sections/en-07.tex`](sections/en-07.tex) | Translated sections |
| [`SGA1-III.pdf`](SGA1-III.pdf) | Compiled English draft |

Build: `make -C translation/SGA1/ExposeIII`; `make tex` builds every
exposé. Lean: `lean/SGA/SGA1/ExposeIII.lean`, with modules in
`lean/SGA/SGA1/ExposeIII/`; coverage in
[`docs/formalization.md`](../../../docs/formalization.md).

## Source and translation choices

Source: the corrected SMF recomposition of

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
before `\chapter{Morphismes plats}`: printed pages 58–86 of the
recomposed volume (approximately PDF pages 65–86).

The French source is not in this repository. Following
[`../../CONVENTIONS.md`](../../CONVENTIONS.md), source pagination, index
entries, and corrected-branch conditionals are omitted; where a
conditional is present, the corrected (`orig = false`) branch is kept.

The wrapper numbers remarks as the source does: numbered `remark` and
`remarks` share the theorem counter, and the source's starred forms use
unnumbered `remarkstar` and `remarksstar` (the remark after 2.1 is a
`remarkstar`). The §6 counters follow the source.

Open stylistic points for proofreading: Exposé III writes sheaves of
ideals and modules in lower case, whereas Exposé II 4.14 and the
conventions for the front matter and Exposés IV, V, VIII–XIII keep the
capitals (Module, Algebra, Ideal); both “sub-prescheme” and
“subprescheme” occur.

## Review against the French (2026-09-24)

The whole exposé was compared with the corrected French, sentence by
sentence, in three parts: `en-01`–`en-02`, `en-03`–`en-05`, and
`en-06`–`en-07`. Changes made:

- **Numbering.** The wrapper had typeset the source's numbered remarks
  without numbers, so Remarks 1.2, Remark 1.8, Remark 4.3, and
  Remarks 6.4 printed unnumbered and every later statement in their
  sections was numbered one too low. In §6 the numbered subsections 6.5
  and 6.6 printed as 6.1 and 6.2, because they used a separate counter,
  and Corollaries 6.7–6.10 printed as 6.4–6.7. The review introduced the
  remark environments described above, removed the earlier
  per-statement workarounds, and synchronized the §6 counters; the
  compiled statement numbers were checked against the source.
- **Mistranslations (eight).** In 1.4, *de sorte que* → “so that”. In the
  proof of 2.1, the causal structure of (v) ⇒ (i) is restored, and so is
  *comme* in (iii) ⇒ (ii). In 5.2, “libre de type fini” is rendered
  “free”, as printed (was “locally free”). In 6.6, *théorie des modules*
  is rendered “theory of moduli” (was “module theory”). Further fixes: the
  introduction to §6 (“over `f^{-1}(O)`”), the emphasis in Serre's
  footnote in §7, and “Then” in §7 a).
- **Formulas restored as printed (three).** 1.4 (i) is back to the
  printed `B`. The translator had silently corrected `Y' → Y'_0` in the
  proof of 3.1 and `A_0` in the proof of 5.1; both read as printed.
- **Other formula fixes.** `\Im` (which printed in Fraktur) →
  `\operatorname{Im}`. Doubled prefixes such as “I I.3.2” → “I 3.2”.
  `\gr` was fixed, and a stray `\goth X` was removed.
- **Omissions restored.** The second “(for example)” before 5.7, and the
  quotation marks around “glue”.
- **Typographic fixes.** Emphasis, word order, spacing, double periods,
  `\No`, ties, and the bold brackets of the 2003 note.

## Source points for scholarly review

Apparent slips in the corrected French TeX, found by the 2026-09-24
review and kept as printed per [`CONVENTIONS.md`](../../CONVENTIONS.md).

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

## Validation

The wrapper compiles with `make -C translation/SGA1/ExposeIII` to a
20-page PDF with no errors or undefined references.

## License

The English translation is an unofficial derivative work. The translator's
contribution was made under CC BY-SA 4.0 and, unlike the rest of the repository
(MIT), stays under it; see [`LICENSE`](LICENSE) and
[`../../../COPYRIGHT.md`](../../../COPYRIGHT.md).
