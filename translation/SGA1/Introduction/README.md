# SGA 1 — Preface, Introduction, Foreword

Full English draft of the front matter of SGA 1: the abstract, the
preface of the SMF edition, Grothendieck's Introduction (Massy, August
1970) and the Foreword (*Avertissement*, Bures, June 1963) to the
mimeographed notes, with all footnotes. It was translated from the
corrected SMF branch, and the translation was then checked against the
French by a second reviewer (2026-09-24). Scholarly proofreading remains
outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-Intro.tex`](SGA1-Intro.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-front.tex`](en-front.tex) | Abstract (with subject classification and keywords); Preface; Introduction; Foreword |
| [`SGA1-Intro.pdf`](SGA1-Intro.pdf) | Compiled English draft |

Build with `make -C translation/SGA1/Introduction` from the repository
root, or `make tex` to build all translated exposés. The build requires
TeX Live with `latexmk`, `amsbook`, `xy`, `mathrsfs`, `enumitem`, and
`hyperref`.

## Source and translation choices

Source: the corrected SMF branch (`orig = false`) of
[arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2),
`smf_doc-math_3_01.tex`, lines 1–545: from the title page up to, but not
including, `\chapter{Morphismes \'etales}` (Exposé I).
The French TeX and PDF are not included in this repository.

The fragment follows [`CONVENTIONS.md`](../../CONVENTIONS.md), section
“SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and uses the shared
package [`sga1-en.sty`](../sga1-en.sty). References to exposés print the
source's numbers (for example “Exp. XII”).

- The source prints the abstract and the preface twice, in French and in
  English. The English here is translated from the French versions, and
  each text appears once, as an unnumbered chapter.
- The Preface refers to M. Raynaud's 2003 remarks by SMF page numbers
  (`\pageref`). These page references are replaced by statement numbers
  (Remarks X 2.14, XI 1.4, XII 5.6, XIII 2.13, and the footnote to
  III 6.6). A translator's footnote at the end of the Preface says so.
  This is the only footnote not in the source.
- The French title-page author line (“Un séminaire dirigé par
  A. Grothendieck / Augmenté de deux exposés de Mme M. Raynaud”) is not
  reproduced in the English wrapper.
- Bibliographic titles are kept as printed, including the inconsistent
  ones listed below.

Front-matter terminology:

| French | English |
| --- | --- |
| Avertissement | Foreword |
| version multigraphiée | mimeographed version / notes |
| exposé (oral, rédigé) | (oral, written-up) exposé |
| point de vue « kroneckerien » | “Kroneckerian” point of view |
| Revêtements étales et groupe fondamental | Étale coverings and the fundamental group |
| Séminaire de Géométrie Algébrique du Bois-Marie | kept in French |

## Source points for scholarly review

These apparent issues are present in the corrected French TeX. They have
been retained in the translation, in accordance with the convention
against silently repairing the source.

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Introduction, Giraud reference | *Méthode de la Descente* | The Foreword footnote gives the title as *Méthodes de la descente*. |
| Foreword, footnote to Giraud | “Société mathématiques de France” | The society's name is Société mathématique de France. |
| Foreword, footnote on SGA 2 | SGA 2 cited as “Cohomologie étale des faisceaux cohérents …” (English: “Étale cohomology of coherent sheaves …”) | The published title of SGA 2 begins “Cohomologie locale des faisceaux cohérents”. |
| Foreword, on the 1963/64 seminar | “dans la parution de plusieurs résultats clefs”, rendered “in the appearance of several key results” | *Parution* may stand for *démonstration* (the proof of several key results). |
| Introduction and Foreword, French slips | “importance croissance” (for *croissante*), “dans le mesure”, “la paragraphe 9”, “dans le série”, “d'êtres prises”, “destruction massives”, “logiquement indépendants”, “aux prix de” | Grammar or spelling slips in the French only; they do not affect the English. |

## Validation

The local checker `source/SGA1/check_chunk.py`, which is not in the
repository, compares the fragment with the corrected French. All five
labels (including `I.avertissement` and `footnotegiraud`) are present.
The differences it reports are the deliberate ones described above: the
page references replaced by statement numbers; the added translator's
footnote (10 footnotes against 9); and the abstract and preface rendered
once, as chapters. The wrapper compiles to an 11-page PDF with no errors
or undefined references.

A second reviewer checked the translation against the French and made
two fixes. The Foreword now keeps the plural of “Les premiers de ces
exposés oraux”. The translator's footnote now tells the reader that page
references were replaced by statement numbers. The reviewer also found
the French slips listed above. These checks do not replace scholarly
proofreading.

License: [`../../LICENSE`](../../LICENSE) (MIT for the
translator's contribution).
