# SGA 3 English

Unofficial English translation of *Schémas en groupes* (SGA 3), from the
recomposition edited by P. Gille and P. Polo. The French PDFs are not in this
repository. Conventions: [`CONVENTIONS.md`](CONVENTIONS.md). Macros:
[`sga3-en.sty`](sga3-en.sty).

The foreword, the introduction and Exposés I–XXVI (including the A and B
parts) are translated in full; the indexes are not. The drafts have not yet
been independently reviewed against the French. Typographical corrections and
apparent slips kept as printed are listed in each exposé's README.

| Id | Directory | Title | Pages | Files |
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
| XVI | [`ExposeXVI/`](ExposeXVI/) | Groups of unipotent rank zero | 24 | 4 |
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

Build one exposé, or everything plus the combined volume
[`SGA3-English.pdf`](SGA3-English.pdf):

```bash
make -C translation/SGA3/ExposeI
make -C translation/SGA3 book
```

The root `make tex` target runs the second command.
