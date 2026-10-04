# SGA 3 English

Unofficial English of *Schémas en groupes*, from the Gille–Polo
recomposition. French PDFs stay in `source/SGA3/` and are not committed.
Conventions: [`CONVENTIONS.md`](CONVENTIONS.md).
Macros: [`sga3-en.sty`](sga3-en.sty).
The foreword/introduction and all exposés I–XXVI, including the A and B parts,
have complete English drafts: 222 fragments covering the 1,351 mapped source
PDF pages. Every individual PDF and the combined volume compile. Translator
checks and retained source slips are recorded in the per-exposé READMEs;
independent scholarly proofreading remains open.

Indexes and the printed tables of contents are not part of this pass.

| Id | Directory | Title | Pages | Chunks |
| --- | --- | --- | --- | --- |
| Intro | [`Introduction/`](Introduction/) | Foreword and introduction | 6 | 1 |
| I | [`ExposeI/`](ExposeI/) | Algebraic structures. Cohomology of groups | 48 | 9 |
| II | [`ExposeII/`](ExposeII/) | Tangent bundles. Lie algebras | 52 | 8 |
| III | [`ExposeIII/`](ExposeIII/) | Infinitesimal extensions | 78 | 11 |
| IV | [`ExposeIV/`](ExposeIV/) | Topologies and sheaves | 74 | 12 |
| V | [`ExposeV/`](ExposeV/) | Construction of quotient schemes | 41 | 7 |
| VIA | [`ExposeVIA/`](ExposeVIA/) | Generalities on algebraic groups | 38 | 5 |
| VIB | [`ExposeVIB/`](ExposeVIB/) | Generalities on group schemes | 112 | 18 |
| VIIA | [`ExposeVIIA/`](ExposeVIIA/) | Infinitesimal study of group schemes | 60 | 10 |
| VIIB | [`ExposeVIIB/`](ExposeVIIB/) | Infinitesimal study of group schemes. Formal groups | 99 | 15 |
| VIII | [`ExposeVIII/`](ExposeVIII/) | Diagonalizable groups | 30 | 5 |
| IX | [`ExposeIX/`](ExposeIX/) | Groups of multiplicative type: homomorphisms into a group scheme | 32 | 5 |
| X | [`ExposeX/`](ExposeX/) | Characterization and classification of groups of multiplicative type | 44 | 8 |
| XI | [`ExposeXI/`](ExposeXI/) | Representability criteria. Applications to subgroups of multiplicative type of affine group schemes | 34 | 6 |
| XII | [`ExposeXII/`](ExposeXII/) | Maximal tori, the Weyl group, Cartan subgroups, the reductive center of smooth affine group schemes | 48 | 8 |
| XIII | [`ExposeXIII/`](ExposeXIII/) | Regular elements of algebraic groups and of Lie algebras | 30 | 5 |
| XIV | [`ExposeXIV/`](ExposeXIV/) | Regular elements, continued. Application to algebraic groups | 36 | 6 |
| XV | [`ExposeXV/`](ExposeXV/) | Complements on the subtori of a group prescheme. Application to smooth groups | 68 | 12 |
| XVI | [`ExposeXVI/`](ExposeXVI/) | Groups of unipotent rank zero | 24 | 5 |
| XVII | [`ExposeXVII/`](ExposeXVII/) | Unipotent algebraic groups. Extensions between unipotent groups and groups of multiplicative type | 50 | 8 |
| XVIII | [`ExposeXVIII/`](ExposeXVIII/) | Weil's theorem on the construction of a group from a rational law | 18 | 3 |
| XIX | [`ExposeXIX/`](ExposeXIX/) | Reductive groups: generalities | 25 | 4 |
| XX | [`ExposeXX/`](ExposeXX/) | Reductive groups of semisimple rank 1 | 35 | 6 |
| XXI | [`ExposeXXI/`](ExposeXXI/) | Root data | 46 | 8 |
| XXII | [`ExposeXXII/`](ExposeXXII/) | Reductive groups: splittings, subgroups, quotient groups | 68 | 12 |
| XXIII | [`ExposeXXIII/`](ExposeXXIII/) | Reductive groups: uniqueness of pinned groups | 37 | 6 |
| XXIV | [`ExposeXXIV/`](ExposeXXIV/) | Automorphisms of reductive groups | 54 | 8 |
| XXV | [`ExposeXXV/`](ExposeXXV/) | The existence theorem | 11 | 2 |
| XXVI | [`ExposeXXVI/`](ExposeXXVI/) | Parabolic subgroups of reductive groups | 53 | 9 |

```bash
make -C translation/SGA3/Introduction
make -C translation/SGA3/ExposeI
```

The root `make tex` target builds the individual PDFs and combined SGA 3 volume.

The local source-page inventory is preserved in [manifest.json](manifest.json),
without French body text or absolute paths. Check the current draft inventory:

```bash
python3 translation/SGA3/check_coverage.py
python3 translation/SGA3/check_coverage.py --expose IV --source-dir source/SGA3 --require-pdf
```

The checker fails for pending fragments, duplicate labels, mismatched
environments, wrapper or book input mismatches, and optionally missing source statement
headings or stale PDFs. These structural checks do not certify translation
fidelity. Per-exposé READMEs distinguish translator checks from independent review.

`make -C translation/SGA3` builds and checks all
exposés, and `make -C translation/SGA3 book` compiles the combined
[SGA3-English.tex](SGA3-English.tex) in source order as SGA3-English.pdf.
Chapter-local bibliographies keep repeated citation keys separate. The book
build is gated on complete fragment coverage; per-exposé targets also remain
available.
Footnotes retain their printed source markers, including repeated and starred
markers. Footnote hyperlinks are disabled to avoid ambiguous destinations;
contents, section and citation links remain active.
