/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.AdditiveFunctorModules

/-!
# Recovering an original linear functor after the canonical module lift

For a genuinely linear module-valued functor, the scalar action reconstructed
from its underlying additive functor is its original action. The identity
on the original elements supplies the natural module-valued comparison.
-/

noncomputable section
universe u v
open CategoryTheory

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]
variable {C : Type v} [Category.{u} C] [Preadditive C] [Linear R C]

/-- The canonical scalar reconstruction agrees with the existing module
structure of a linear functor, by the identity on underlying elements. -/
def additiveFunctorModuleLiftIsoOfLinear (F : C ⥤ ModuleCat.{u} R)
    [F.Additive] [F.Linear R] :
    additiveFunctorModuleLift (R := R) (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat) ≅ F := by
  let e (X : C) :
      (additiveFunctorModuleLift (R := R) (F ⋙ forget₂ (ModuleCat R) AddCommGrpCat)).obj X ≃ₗ[R]
        F.obj X :=
    { toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => by
        change F.map (r • 𝟙 X) x = (r • 𝟙 (F.obj X)) x
        rw [F.map_smul, F.map_id] }
  exact NatIso.ofComponents (fun X => (e X).toModuleIso) (fun f => by ext x; rfl)

end SGA.SGA2.ExposeIV
