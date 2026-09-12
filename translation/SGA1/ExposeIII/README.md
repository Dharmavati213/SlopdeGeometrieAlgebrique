# SGA 1, Exposé III — Smooth morphisms: extension properties

English translation of the complete Exposé III, including all seven
sections, proofs, footnotes, diagrams, and the application to formal and
ordinary smooth schemes over a complete local ring.

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

The English translation is an unofficial derivative work. The translator's
contribution is licensed under CC BY-SA 4.0; see [`../../LICENSE`](../../LICENSE)
and [`../../../COPYRIGHT.md`](../../../COPYRIGHT.md). Scholarly proofreading
remains outstanding.
