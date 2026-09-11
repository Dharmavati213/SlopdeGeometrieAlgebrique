# Status

Track what is in the tree. Update this file when an exposé is added.

## SGA 1 — *Revêtements étales et groupe fondamental*

| Exposé | Title | Translation | Lean |
| --- | --- | --- | --- |
| I | Étale morphisms | — | — |
| II | Smooth morphisms: generalities | — | — |
| III | Smooth morphisms: lifting | — | — |
| IV | Unramified morphisms, étale morphisms | — | — |
| V | The fundamental group | — | — |
| **VI** | **Fibered categories and descent** | **done** | **scaffold** |
| VII | *(does not exist in SGA 1)* | | |
| VIII | Vanishing cycles | — | — |
| IX | Descent of étale morphisms | — | — |
| X | Specialization of the fundamental group | — | — |
| XI | Examples and complements | — | — |
| XII | Geometric fundamental group | — | — |
| XIII | Projective space, fundamental group of the line | — | — |

SGA 1 VI translation lives in `translation/SGA1/ExposeVI/`.

Lean for VI is `SGA/SGA1/ExposeVI.lean`: it imports mathlib’s fibered-category
and descent APIs so a later formalization can start from Grothendieck’s
numbering. It does **not** claim a complete formalization of the exposé.

## Later SGA

SGA 2–7 are out of scope until SGA 1 has more than one exposé.
