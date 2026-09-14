/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteModuleEvaluation

/-!
# Canonical evaluation on arbitrary modules

The evaluation map of IV.1.2 uses the actual value on the ring, with no
finiteness assumption on its argument. Its restriction to finite modules
is the already constructed evaluation of IV.1.1.
-/

noncomputable section

universe u

open CategoryTheory Opposite Functor

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- The actual linear map from the ring determined by an element. -/
def modulePoint (M : ModuleCat.{u} R) (x : M) : ModuleCat.of R R ⟶ M :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp] theorem modulePoint_add (M : ModuleCat.{u} R) (x y : M) :
    modulePoint M (x + y) = modulePoint M x + modulePoint M y := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact smul_add r x y

@[simp] theorem modulePoint_smul (M : ModuleCat.{u} R) (r : R) (x : M) :
    modulePoint M (r • x) = r • modulePoint M x := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact smul_comm s r x

@[simp] theorem modulePoint_comp {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (x : M) : modulePoint M x ≫ f = modulePoint N (f x) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact f.hom.map_smul r x

variable (T : (ModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R) [T.Additive] [T.Linear R]

instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).op.Linear R where
  map_smul _ _ := rfl

/-- The actual canonical pairing, curried as a linear evaluation map. -/
def moduleEvaluation (M : ModuleCat.{u} R) :
    T.obj (op M) →ₗ[R] (M ⟶ T.obj (op (ModuleCat.of R R))) where
  toFun t := ModuleCat.ofHom
    { toFun x := T.map (modulePoint M x).op t
      map_add' x y := by simp
      map_smul' r x := by simp }
  map_add' t s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (T.map (modulePoint M x).op).hom.map_add t s
  map_smul' r t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (T.map (modulePoint M x).op).hom.map_smul r t

@[simp] theorem moduleEvaluation_apply (M : ModuleCat.{u} R)
    (t : T.obj (op M)) (x : M) :
    moduleEvaluation T M t x = T.map (modulePoint M x).op t := rfl

theorem moduleEvaluation_naturality {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (t : T.obj (op N)) (x : M) :
    moduleEvaluation T M (T.map f.op t) x = moduleEvaluation T N t (f x) := by
  change (T.map f.op ≫ T.map (modulePoint M x).op) t = _
  rw [← T.map_comp, ← op_comp, modulePoint_comp]
  rfl

/-- The canonical natural transformation on all modules. -/
def moduleEvaluationNatTrans : T ⟶ (linearYoneda R (ModuleCat R)).obj
    (T.obj (op (ModuleCat.of R R))) where
  app M := ModuleCat.ofHom (moduleEvaluation T M.unop)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact moduleEvaluation_naturality T f.unop t x

/-- Restriction does not change the canonical map of IV.1.1. -/
theorem moduleEvaluationNatTrans_restrict :
    whiskerLeft (forget₂ (FGModuleCat R) (ModuleCat R)).op
      (moduleEvaluationNatTrans T) =
    finiteModuleEvaluationNatTrans ((forget₂ (FGModuleCat R) (ModuleCat R)).op ⋙ T) := rfl

end SGA.SGA2.ExposeIV
