/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# SGA 1, Exposé VI, §11: discrete bases

VI.11(e): over a discrete category every based category is fibered and every
based functor is cartesian.
-/

universe v u v₁ u₁

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {I : Type u} {C : Type u₁} [Category.{v₁} C] (p : C ⥤ Discrete I)

/-- VI.11(e): any category over a discrete base is fibered. -/
instance discrete_isFibered : IsFibered p :=
  IsFibered.of_exists_isStronglyCartesian fun a i f => by
    have : i = p.obj a := Discrete.ext (Discrete.eq_of_hom f)
    subst this
    obtain rfl : f = 𝟙 (p.obj a) := Subsingleton.elim _ _
    exact ⟨a, 𝟙 a, inferInstance⟩

/-- VI.11(e): every based functor over a discrete base is cartesian. -/
instance discrete_isCartesianFunctor {X Y : BasedCategory.{v₁, u₁} (Discrete I)}
    (F : BasedFunctor X Y) : IsCartesianFunctor F where
  map_isCartesian {R S a b} f φ hφ := by
    have hRS : R = S := Discrete.ext (Discrete.eq_of_hom f)
    subst hRS
    obtain rfl : f = 𝟙 R := Subsingleton.elim _ _
    have : IsCartesian X.p (𝟙 R) φ := hφ
    have : IsIso φ := isIso_of_vertical_isCartesian X.p (S := R) φ
    have : IsIso (F.map φ) := inferInstance
    infer_instance

end SGA.SGA1.ExposeVI
