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

/-!
# SGA 1, Exposé VI — Lean scaffold

English translation: `translation/SGA1/ExposeVI/`.
Formalization of this exposé is **not** done here; this file is a
starting point. Mathlib already has the language of the exposé:

* cartesian / strongly cartesian morphisms (`IsCartesian`, `IsStronglyCartesian`)
* prefibered / fibered categories (`IsPreFibered`, `IsFibered`)
* fibers (`Fiber`, `HasFibers`)
* Grothendieck construction (`∫ᶜ`, `forget`)
* cocartesian morphisms (`IsCocartesian`)
* descent data, prestacks, stacks (`DescentData`, `IsPrestack`, `IsStack`)

Add lemmas in this folder following Grothendieck's numbering
(`VI.5.1`, `VI.6.1`, …). See `docs/FORMALIZATION.md`.
-/
