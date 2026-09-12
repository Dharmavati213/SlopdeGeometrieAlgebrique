/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.GammaZ
import SGA.SGA2.ExposeI.Flasque
import SGA.SGA2.ExposeI.LocalCohomology
import SGA.SGA2.ExposeI.UnderlineGammaZ
import SGA.SGA2.ExposeI.LocallyClosed
import SGA.SGA2.ExposeI.ExtensionByZero
import SGA.SGA2.ExposeI.DerivedFunctors
import SGA.SGA2.ExposeI.ExactSequences

/-!
# SGA 2, Exposé I — Global and local cohomological invariants relative to a closed subspace

English translation: `translation/SGA2/ExposeI/` (repo root).
This module is the barrel for the Lean formalization of the exposé.

## Coverage (I.1–I.2)

* **I.1** `Γ_Z` closed — `GammaZ.lean`
* **I.1** sheaf `Γ̲_Z` — `UnderlineGammaZ.lean`
* **I.1** locally closed + independence of open — `LocallyClosed.lean`
  (`gammaZSections_restrict_addEquiv`)
* **I.1.1–I.1.7** `i_!` / `i^!` / `ℤ_{Z,X}` — `ExtensionByZero.lean`
  (closed/open/locally closed factorization)
* **I.1.8–I.1.9** — `ExactSequences.lean`, `Flasque.lean`
* **I.2.1 / I.2.3 bis** `H_Z^*` — `DerivedFunctors.lean` as `Ext(ℤ_{Z,X}, −)`
* **I.2.1** algebraic — `LocalCohomology.lean`
* **I.2.2** excision — `I_2_2_degree_zero`, `I_2_2_excision`
* **I.2.4–I.2.5 / I.2.11** `ℋ_Z^n` for all `n` — `sheafH_Z_n`
* **I.2.6** local-to-global SS — packaged (`I_2_6_*`)
* **I.2.8–I.2.14** LES / vanishing — `ExactSequences.lean`

Exposé II handles topological↔algebraic comparison on affines.

Mathlib supplies: flasque sheaves, algebraic local cohomology, `Ext` /
`HasExt` for Grothendieck abelian sheaf categories, pushforward/pullback,
`Functor.rightDerived`.

Numbering follows Grothendieck (`I.1.1`, `I.2.1`, …). See `docs/formalization.md`.
-/
