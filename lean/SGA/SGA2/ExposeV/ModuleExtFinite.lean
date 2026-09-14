/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ModuleExtPairing
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite

/-!
# Finiteness of original module-valued Ext

The canonical linear comparison carries the proved finiteness of derived
Ext to the original Ext modules used in the local-cohomology construction.
-/

noncomputable section
universe u
open CategoryTheory
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Original module-valued Ext of two finite modules is finite. -/
instance moduleExt_finite (N M : ModuleCat.{u} R)
    [Module.Finite R N] [Module.Finite R M] (i : ℕ) :
    Module.Finite R (moduleExtValue N M i) :=
  Module.Finite.equiv (moduleExtLinearEquivAbelianExt N M i).symm

end SGA.SGA2.ExposeV
