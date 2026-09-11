/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Fibers
import Mathlib.CategoryTheory.FiberedCategory.Fibered

/-!
# SGA 1, Exposé VI, §12: functors on a cloven category

A functor `F : 𝒳 ⥤ D` on a prefibered category is recorded by its
restrictions `F_S` to the fibers and the constraints
`φ_f(ξ) = F(α_f(ξ))` coming from chosen cartesian transports (VI.12).
We use mathlib's chosen cartesian lifts as the cleavage.
-/

universe v v₁ v₂ u u₁ u₂

set_option linter.unusedSectionVars false

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} {C : Type u₁} [Category.{v} E] [Category.{v₁} C]
  (p : C ⥤ E) [IsPreFibered p]

/-- Inverse image of an object, using a chosen cartesian lift. -/
noncomputable def fiberPullbackObj {R S : E} (f : R ⟶ S) (ξ : Fiber p S) : Fiber p R :=
  ⟨IsPreFibered.pullbackObj ξ.property f, IsPreFibered.pullbackObj_proj ξ.property f⟩

/-- The chosen cartesian transport `α_f(ξ) : f^*(ξ) ⟶ ξ`. -/
noncomputable def transport {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    (fiberPullbackObj p f ξ).val ⟶ ξ.val :=
  IsPreFibered.pullbackMap ξ.property f

instance transport_isCartesian {R S : E} (f : R ⟶ S) (ξ : Fiber p S) :
    IsCartesian p f (transport p f ξ) :=
  IsPreFibered.pullbackMap.IsCartesian ξ.property f

/-- VI.12: restriction of a functor on the total category to a fiber. -/
def onFiber {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (S : E) : Fiber p S ⥤ D :=
  Fiber.fiberInclusion ⋙ F

/-- VI.12: the component `φ_f(ξ) : F(f^*(ξ)) ⟶ F(ξ)` of the constraint. -/
noncomputable def constraintApp {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    F.obj (fiberPullbackObj p f ξ).val ⟶ F.obj ξ.val :=
  F.map (transport p f ξ)

/-- VI.12(a): the identity constraint is `F` of the chosen lift of an identity. -/
theorem constraintApp_id {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D) (S : E) (ξ : Fiber p S) :
    constraintApp p F (𝟙 S) ξ = F.map (transport p (𝟙 S) ξ) :=
  rfl

/-- VI.12(b): `F` of the composite of transports equals the composite of constraints
after factoring through the chosen lift of the composite base arrow. -/
theorem constraintApp_comp {D : Type u₂} [Category.{v₂} D] (F : C ⥤ D)
    {U T S : E} (g : U ⟶ T) (f : T ⟶ S) (ξ : Fiber p S) :
    F.map (transport p g (fiberPullbackObj p f ξ) ≫ transport p f ξ) =
      constraintApp p F g (fiberPullbackObj p f ξ) ≫ constraintApp p F f ξ :=
  F.map_comp _ _

/-- VI.12(c): a natural transformation of total functors is compatible with constraints. -/
theorem constraintApp_naturality {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D}
    (α : F ⟶ G) {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    constraintApp p F f ξ ≫ α.app ξ.val =
      α.app (fiberPullbackObj p f ξ).val ≫ constraintApp p G f ξ :=
  α.naturality (transport p f ξ)

/-- VI.12.1, faithfulness: a natural transformation of total functors is recovered
from its values on objects of fibers. -/
theorem natTrans_ext_onFiber {D : Type u₂} [Category.{v₂} D] {F G : C ⥤ D} {α β : F ⟶ G}
    (h : ∀ (S : E) (ξ : Fiber p S), α.app ξ.val = β.app ξ.val) : α = β := by
  apply NatTrans.ext
  funext x
  exact h (p.obj x) ⟨x, rfl⟩

end SGA.SGA1.ExposeVI
