/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.AdditiveFunctorModules
import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# The canonical evaluation map for contravariant functors on finite modules

This is the map `φ_T` of SGA 2, IV.1.1, constructed from the actual functor
and maps `R → M`. The target module is the functor's actual value on `R`.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- The linear Yoneda functor restricted to finitely generated modules. -/
def finiteModuleHomFunctor (H : ModuleCat.{u} R) :
    (FGModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (forget₂ (FGModuleCat R) (ModuleCat R)).op ⋙ (linearYoneda R (ModuleCat R)).obj H

/-- The map from the rank-one free module determined by a coefficient. -/
def finiteModulePoint (M : FGModuleCat.{u} R) (x : M) : FGModuleCat.of R R ⟶ M :=
  FGModuleCat.ofHom (LinearMap.toSpanSingleton R M x)

@[simp] theorem finiteModulePoint_add (M : FGModuleCat.{u} R) (x y : M) :
    finiteModulePoint M (x + y) = finiteModulePoint M x + finiteModulePoint M y := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact smul_add r x y

@[simp] theorem finiteModulePoint_smul (M : FGModuleCat.{u} R) (r : R) (x : M) :
    finiteModulePoint M (r • x) = r • finiteModulePoint M x := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro s
  exact smul_comm s r x

@[simp] theorem finiteModulePoint_comp {M N : FGModuleCat.{u} R}
    (f : M ⟶ N) (x : M) : finiteModulePoint M x ≫ f = finiteModulePoint N (f.hom x) := by
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  exact f.hom.hom.map_smul r x

variable (T : (FGModuleCat.{u} R)ᵒᵖ ⥤ ModuleCat.{u} R) [T.Additive] [T.Linear R]

/-- The bilinear evaluation pairing, curried in its functor-valued argument. -/
def finiteModuleEvaluation (M : FGModuleCat.{u} R) :
    T.obj (op M) →ₗ[R]
      (M.obj ⟶ T.obj (op (FGModuleCat.of R R))) where
  toFun t := ModuleCat.ofHom
    { toFun x := T.map (finiteModulePoint M x).op t
      map_add' x y := by simp
      map_smul' r x := by simp }
  map_add' t s := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (T.map (finiteModulePoint M x).op).hom.map_add t s
  map_smul' r t := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (T.map (finiteModulePoint M x).op).hom.map_smul r t

@[simp] theorem finiteModuleEvaluation_apply (M : FGModuleCat.{u} R)
    (t : T.obj (op M)) (x : M) :
    finiteModuleEvaluation T M t x = T.map (finiteModulePoint M x).op t := rfl

/-- Naturality is with respect to the original coefficient-module map. -/
theorem finiteModuleEvaluation_naturality {M N : FGModuleCat.{u} R}
    (f : M ⟶ N) (t : T.obj (op N)) (x : M) :
    finiteModuleEvaluation T M (T.map f.op t) x =
      finiteModuleEvaluation T N t (f.hom x) := by
  change (T.map f.op ≫ T.map (finiteModulePoint M x).op) t = _
  rw [← T.map_comp, ← op_comp, finiteModulePoint_comp]
  rfl

/-- The canonical natural transformation `φ_T : T → Hom(-, T(R))`. -/
def finiteModuleEvaluationNatTrans :
    T ⟶ finiteModuleHomFunctor (T.obj (op (FGModuleCat.of R R))) where
  app M := ModuleCat.ofHom (finiteModuleEvaluation T M.unop)
  naturality {M N} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact finiteModuleEvaluation_naturality T f.unop t x

/-- On the ring, evaluation at `1` recovers the original argument. -/
@[simp] theorem finiteModuleEvaluation_ring_one
    (t : T.obj (op (FGModuleCat.of R R))) :
    finiteModuleEvaluation T (FGModuleCat.of R R) t 1 = t := by
  have h : finiteModulePoint (FGModuleCat.of R R) 1 = 𝟙 _ := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    exact mul_one r
  change T.map (finiteModulePoint (FGModuleCat.of R R) 1).op t = t
  simp [h]

end SGA.SGA2.ExposeIV
