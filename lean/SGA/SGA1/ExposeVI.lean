/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean
-/
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Sites.Descent.IsStack
import SGA.SGA1.ExposeVI.Equivalences
import SGA.SGA1.ExposeVI.OverCategories
import SGA.SGA1.ExposeVI.BaseChange
import SGA.SGA1.ExposeVI.Fibers
import SGA.SGA1.ExposeVI.BasedEquivalences
import SGA.SGA1.ExposeVI.Cartesian
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import SGA.SGA1.ExposeVI.FiberedProducts
import SGA.SGA1.ExposeVI.Cleavage
import SGA.SGA1.ExposeVI.Split
import SGA.SGA1.ExposeVI.Cofibered
import SGA.SGA1.ExposeVI.ClovenFunctors
import SGA.SGA1.ExposeVI.Groupoids
import SGA.SGA1.ExposeVI.BaseExamples
import SGA.SGA1.ExposeVI.Examples

/-!
# SGA 1, Exposé VI — Fibered categories and descent

English translation: `translation/SGA1/ExposeVI/` (repo root).
This module is the barrel for the Lean formalization of the exposé.
Mathlib already supplies the language:

* cartesian / strongly cartesian morphisms (`IsCartesian`, `IsStronglyCartesian`)
* prefibered / fibered categories (`IsPreFibered`, `IsFibered`)
* fibers (`Fiber`, `HasFibers`)
* Grothendieck construction (`∫ᶜ`, `forget`)
* cocartesian morphisms (`IsCocartesian`)
* descent data, prestacks, stacks (`DescentData`, `IsPrestack`, `IsStack`)

Numbering follows Grothendieck (`VI.5.1`, `VI.6.1`, …). See
`docs/formalization.md`.
-/
