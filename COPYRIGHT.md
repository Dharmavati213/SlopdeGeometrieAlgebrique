# Copyright and sources

Everything in this repository that is original to the project — the Lean 4
formalization, the English translation, documentation, and repository
tooling — is licensed under the MIT License. See `LICENSE`.

Two parts keep the license under which they were contributed:

1. `translation/SGA1/ExposeIII/` — the English translation of SGA 1,
   Exposé III, contributed by [niclasrst](https://github.com/niclasrst)
   under CC BY-SA 4.0 and later revised in this repository. Its ShareAlike
   condition also covers the revisions. See
   `translation/SGA1/ExposeIII/LICENSE`.
2. `lean/SGA/SGA2/ExposeII/ProjectiveComplexLift.lean` — adapted from
   mathlib's projective-resolution comparison (Apache-2.0, with the mathlib
   authors named in its header). See `LICENSES/Apache-2.0.txt`.

The Lean library depends on
[mathlib4](https://github.com/leanprover-community/mathlib4) (Apache-2.0),
which is not redistributed here.

## Original SGA

The *Séminaire de Géométrie Algébrique du Bois Marie* (SGA) was written
by Alexander Grothendieck and collaborators. The texts used for the
English translations are the slightly corrected SMF recompositions:

- A. Grothendieck, M. Raynaud, *Revêtements étales et groupe fondamental*
  (SGA 1), Séminaire de géométrie algébrique du Bois Marie 1960–61,
  recomposed edition, [arXiv:math/0206203](https://arxiv.org/abs/math/0206203).
- A. Grothendieck (notes by a group of auditors), with an exposé by
  M. Raynaud, *Cohomologie locale des faisceaux cohérents et théorèmes
  de Lefschetz locaux et globaux* (SGA 2), Séminaire de géométrie
  algébrique du Bois Marie 1962, recomposed edition,
  [arXiv:math/0511279](https://arxiv.org/abs/math/0511279).

- M. Demazure, A. Grothendieck, *Schémas en groupes* (SGA 3),
  Séminaire de géométrie algébrique du Bois Marie 1962–64.
  The English follows the recomposition edited by P. Gille and P. Polo
  (Société Mathématique de France, Documents Mathématiques;
  corrected PDFs of 2008–2024). The French PDFs are not in this
  repository.

Those French texts are **not** redistributed in this repository. The original
remains copyright of the authors and of the original publishers
(IHÉS / Springer / Société Mathématique de France, as applicable).

This project is an unofficial scholarly companion. It does not claim
endorsement by the original authors or publishers.

## English translation

The English translation in `translation/` is an original derivative work
of the SMF recompositions, prepared for this project. Numbering of
statements follows the original exposés. The translator’s contribution
is offered under the MIT License, except SGA 1, Exposé III (CC BY-SA 4.0,
see above). See `translation/LICENSE`.

No license in this repository grants any rights in the French original.
If you are a rights holder and believe this use is not appropriate,
open a GitHub issue or contact the repository owner.

## Lean formalization

Lean source in `lean/SGA/` is original work of this project, apart from the
Apache-2.0 file listed above, building on
[mathlib4](https://github.com/leanprover-community/mathlib4). It covers
SGA 1 (every exposé, with the open items listed in `docs/formalization.md`)
and parts of SGA 2, Exposés I–VII. Prerequisites that mathlib lacks are in
`lean/SGA/Foundations/`, written in mathlib's style.
