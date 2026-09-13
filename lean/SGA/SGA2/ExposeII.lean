/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.Torsion
import SGA.SGA2.ExposeII.PrincipalSystem

/-!
# SGA 2, Exposé II — Algebraic foundations for local cohomology

English translation: `translation/SGA2/ExposeII/` (repo root).

This is a partial formalization of the module arguments in II.(7.5), II.9,
and II.11:

* `Torsion`: ideal-power torsion, functoriality, radical invariance, and
  `Hom(R/I, M)` identified with the submodule annihilated by `I`;
* `EssentiallyZero`: the diagram argument of II.9(c) ⇒ (b) and closure under
  subobjects, quotients, and extensions used in II.11;
* `Principal`: the one-generator annihilator argument of II.11;
* `PrincipalSystem`: the annihilator system as a functor and its Hom colimits.

The affine sheaf comparison, the comparison with Koszul cohomology, and the
multiple-generator induction remain open. See `docs/formalization.md`.
-/
