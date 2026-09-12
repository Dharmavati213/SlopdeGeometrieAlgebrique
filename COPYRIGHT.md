# Copyright and sources

This repository contains two kinds of work, under two licenses.

1. Lean 4 formalization, documentation, and repository infrastructure
   are licensed under the Apache License, Version 2.0. See `LICENSE`.
   They depend on mathlib4 (Apache-2.0),
   https://github.com/leanprover-community/mathlib4
2. The English translation in `translation/` is an unofficial scholarly
   translation of Grothendieck–Raynaud, *SGA 1*, SMF recomposition
   arXiv:math/0206203, and of Grothendieck–Raynaud, *SGA 2*, SMF
   recomposition arXiv:math/0511279. The translator’s original
   contribution is licensed under CC BY-SA 4.0; the French original
   remains copyright of the original authors and publishers and is not
   redistributed here. See `translation/LICENSE`.

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

Those French texts are **not** redistributed in this repository. The original
remains copyright of the authors and of the original publishers
(IHÉS / Springer / Société Mathématique de France, as applicable).

This project is an unofficial scholarly companion. It does not claim
endorsement by the original authors or publishers.

## English translation

The English translation in `translation/` is an original derivative work
of the SMF recomposition, prepared for this project. Numbering of
statements follows the original exposé. The translator’s contribution
is offered under [CC BY-SA 4.0](https://creativecommons.org/licenses/by-sa/4.0/).
See `translation/LICENSE`.

If you are a rights holder and believe this use is not appropriate,
open a GitHub issue or contact the repository owner.

## Lean formalization

Lean source in `lean/SGA/` is original work of this project, building on
[mathlib4](https://github.com/leanprover-community/mathlib4) (Apache-2.0).
Mathlib already contains the language of fibered categories as in
SGA 1 VI (cartesian morphisms, (pre)fibered categories, fibers, the
Grothendieck construction) and the language of descent data / (pre)stacks.
This repository records the correspondence with Grothendieck’s numbering
and adds statements that mathlib does not yet name (in particular
categories fibered in groupoids, and cofibered / bifibered categories
as in SGA 1 VI.10).
