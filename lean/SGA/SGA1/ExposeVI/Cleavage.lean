/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Cartesian
import SGA.SGA1.ExposeVI.Fibered
import SGA.SGA1.ExposeVI.Fibers

/-!
# SGA 1, Exposé VI, VI.7: cloven categories

A cleavage chooses cartesian inverse-image functors. The comparison
`c_{f,g}` measures the failure of `f ↦ f^*` to be a strict functor.
VI.7.2: the category is fibered iff every comparison is an isomorphism.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u₁} {C : Type u₂} [Category.{v₁} E] [Category.{v₂} C]

/-- VI.7.1: a cleavage of `p : C ⥤ E`. -/
structure Cleavage (p : C ⥤ E) where
  pullback {R S : E} (f : R ⟶ S) : Fiber p S ⥤ Fiber p R
  transport {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    ((pullback f).obj ξ).val ⟶ ξ.val
  transport_isCartesian {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    IsCartesian p f (transport f ξ)
  transport_natural {R S : E} (f : R ⟶ S) {ξ η : Fiber p S} (u : ξ ⟶ η) :
    ((pullback f).map u).val ≫ transport f η = transport f ξ ≫ u.val

namespace Cleavage

variable {p : C ⥤ E} (K : Cleavage p)

include K

instance transport_isCartesian_inst {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    IsCartesian p f (K.transport f ξ) :=
  K.transport_isCartesian f ξ

/-- A cleavage supplies cartesian lifts, so `p` is prefibered. -/
theorem toIsPreFibered : IsPreFibered p where
  exists_isCartesian' {a _} f :=
    ⟨((K.pullback f).obj ⟨a, rfl⟩).val, K.transport f ⟨a, rfl⟩,
      K.transport_isCartesian f ⟨a, rfl⟩⟩

/-- The comparison `c_{f,g}(ξ) : g^* f^* ξ ⟶ (g ≫ f)^* ξ`. -/
noncomputable def comparison {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    (K.pullback g).obj ((K.pullback f).obj ξ) ⟶ (K.pullback (g ≫ f)).obj ξ :=
  ⟨IsCartesian.map p (g ≫ f) (K.transport (g ≫ f) ξ)
      (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ),
    by
      have := K.transport_isCartesian (g ≫ f) ξ
      have := K.transport_isCartesian g ((K.pullback f).obj ξ)
      have := K.transport_isCartesian f ξ
      infer_instance⟩

@[reassoc]
theorem comparison_fac {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    (K.comparison f g ξ).val ≫ K.transport (g ≫ f) ξ =
      K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ := by
  have := K.transport_isCartesian (g ≫ f) ξ
  exact IsCartesian.fac p (g ≫ f) (K.transport (g ≫ f) ξ)
    (K.transport g ((K.pullback f).obj ξ) ≫ K.transport f ξ)

end Cleavage

end SGA.SGA1.ExposeVI
