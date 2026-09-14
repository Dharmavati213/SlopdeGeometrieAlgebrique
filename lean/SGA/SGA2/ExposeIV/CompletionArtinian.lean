/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.CompletionSubmodules
import Mathlib.RingTheory.Artinian.Module

/-!
# Actual Artinian modules under supported completion restriction

Every original-ring submodule of a supported completed-ring module is
already stable under completed scalars. The full submodule lattices are
therefore identified, and the actual descending-chain condition descends
along restriction, even when the original ring is not complete.
-/

noncomputable section
universe u
open CategoryTheory ModuleCat

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
variable (M : ModuleCat.{u} (AdicCompletion J R))
variable (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M)

local instance completionArtinianRestrictModule : Module R M :=
  Module.compHom M (algebraMap R (AdicCompletion J R))

/-- The original submodule lattice is exactly the completed-ring submodule
lattice for a supported module. -/
def completionSubmoduleOrderIso :
    Submodule R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M) ≃o
      Submodule (AdicCompletion J R) M where
  toFun := completionSubmodule J M hM
  invFun N :=
    { carrier := {x | x ∈ N}
      zero_mem' := N.zero_mem
      add_mem' := N.add_mem
      smul_mem' := fun r x hx => N.smul_mem (algebraMap R (AdicCompletion J R) r) hx }
  left_inv N := by ext x; rfl
  right_inv N := by ext x; rfl
  map_rel_iff' := Iff.rfl

include hM in
/-- Full Artinianity, not just local Artinianity, descends by the actual
submodule comparison under supported scalar restriction. -/
theorem completion_restrictScalars_isArtinian [IsArtinian (AdicCompletion J R) M] :
    IsArtinian R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M) := by
  let e := completionSubmoduleOrderIso J M hM
  apply (isArtinian_iff R _).mpr
  exact (InvImage.wf e wellFounded_lt).mono (fun _ _ h => e.strictMono h)

end SGA.SGA2.ExposeIV
