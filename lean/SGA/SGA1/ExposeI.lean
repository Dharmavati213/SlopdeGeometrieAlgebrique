/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeI.Differentials
import SGA.SGA1.ExposeI.QuasiFinite
import SGA.SGA1.ExposeI.Unramified
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeI.Fundamental
import SGA.SGA1.ExposeI.CompleteLocal
import SGA.SGA1.ExposeI.StandardEtale
import SGA.SGA1.ExposeI.Infinitesimal
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeI.NormalCoverings
import SGA.SGA1.ExposeI.Unibranch

/-!
# SGA 1, Exposé I — Étale morphisms

English translation: `translation/SGA1/ExposeI/` (repo root).
This module is the barrel for the Lean formalization of the exposé.
Mathlib already supplies the language:

* Kähler differentials `Ω[S⁄R]` (I.1)
* quasi-finite algebras and morphisms (`Algebra.QuasiFinite`, `LocallyQuasiFinite`) (I.2)
* formally unramified morphisms (`FormallyUnramified`, `Algebra.Unramified`) (I.3)
* étale morphisms (`Etale`, `Algebra.Etale`) (I.4)
* flat monomorphisms of finite presentation are open immersions (I.5.1)
* standard étale algebras (`StandardEtalePair`, `IsStandardEtale`) (I.7)
* finite étale algebras (`CommAlgCat.FiniteEtale`) (I.6)
* relative normalisation (`Scheme.Hom.toNormalization`) (I.10)

Numbering follows Grothendieck (`I.3.1`, `I.5.1`, …). See
`docs/formalization.md`.

The exposé works throughout with locally noetherian schemes (after no. I.2).
Mathlib's étale morphisms are locally of finite presentation; this agrees
with SGA's finite-type definition on a locally noetherian base
(`etale_of_flat_unramified_locallyNoetherian`).
-/
