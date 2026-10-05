# SGA 1 — Preface, Introduction, Foreword

Complete English draft of the front matter of SGA 1: the abstract, the
preface of the SMF edition, Grothendieck's Introduction (Massy, August
1970) and the Foreword (*Avertissement*, Bures, June 1963) to the
mimeographed notes, with all footnotes. Translated from the corrected SMF
branch of [arXiv:math/0206203v2](https://arxiv.org/abs/math/0206203v2);
a second reviewer checked it against the French (2026-09-24). Scholarly
proofreading is outstanding.

| File | Contents |
| --- | --- |
| [`SGA1-Intro.tex`](SGA1-Intro.tex) | Standalone wrapper (loads [`../sga1-en.sty`](../sga1-en.sty)) and translation notice |
| [`en-front.tex`](en-front.tex) | Abstract (with subject classification and keywords); Preface; Introduction; Foreword |
| [`SGA1-Intro.pdf`](SGA1-Intro.pdf) | Compiled English draft |

Build: `make -C translation/SGA1/Introduction` (TeX Live with `latexmk`,
`amsbook`, `xy`, `mathrsfs`, `enumitem`, `hyperref`); `make tex` builds
every exposé.

## Source and translation choices

`smf_doc-math_3_01.tex` (corrected branch, `orig = false`), lines 1–545:
from the title page up to, but not including, `\chapter{Morphismes \'etales}`
(Exposé I). The French TeX and PDF are not in this repository.

The fragment follows [`CONVENTIONS.md`](../../CONVENTIONS.md), section
“SGA 1 — front matter and Exposés IV, V, VIII–XIII”, and uses the shared
package [`sga1-en.sty`](../sga1-en.sty). References to exposés print the
source's numbers (for example “Exp. XII”).

- The source prints the abstract and the preface twice, in French and in
  English. The English here is translated from the French versions, and
  each text appears once, as an unnumbered chapter.
- The Preface refers to M. Raynaud's 2003 remarks by SMF page numbers
  (`\pageref`). These are replaced by statement numbers (Remarks X 2.14,
  XI 1.4, XII 5.6, XIII 2.13, and the footnote to III 6.6), and a
  translator's footnote at the end of the Preface says so. It is the only
  footnote not in the source.
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

Apparent slips in the corrected French TeX, kept as printed per
[`CONVENTIONS.md`](../../CONVENTIONS.md).

| Location | Source wording or notation retained | Point to review |
| --- | --- | --- |
| Introduction, Giraud reference | *Méthode de la Descente* | The Foreword footnote gives the title as *Méthodes de la descente*. |
| Foreword, footnote to Giraud | “Société mathématiques de France” | The society's name is Société mathématique de France. |
| Foreword, footnote on SGA 2 | SGA 2 cited as “Cohomologie étale des faisceaux cohérents …” (English: “Étale cohomology of coherent sheaves …”) | The published title of SGA 2 begins “Cohomologie locale des faisceaux cohérents”. |
| Foreword, on the 1963/64 seminar | “dans la parution de plusieurs résultats clefs”, rendered “in the appearance of several key results” | *Parution* may stand for *démonstration* (the proof of several key results). |
| Introduction and Foreword, French slips | “importance croissance” (for *croissante*), “dans le mesure”, “la paragraphe 9”, “dans le série”, “d'êtres prises”, “destruction massives”, “logiquement indépendants”, “aux prix de” | Grammar or spelling slips in the French only; they do not affect the English. |

## Validation

`source/SGA1/check_chunk.py` (a local script, not in the repository)
compared the fragment with the corrected French. All five labels
(including `I.avertissement` and `footnotegiraud`) are present. The
differences it reports are the deliberate ones described above: page
references replaced by statement numbers; the added translator's
footnote (10 footnotes against 9); the abstract and preface rendered
once, as chapters. The wrapper compiles to an 11-page PDF with no errors
or undefined references.

The second reviewer made two fixes: the Foreword keeps the plural of
“Les premiers de ces exposés oraux”, and the translator's footnote says
that page references were replaced by statement numbers. The reviewer
also found the French slips listed above.

License: [`../../LICENSE`](../../LICENSE) (MIT for the translator's
contribution).
