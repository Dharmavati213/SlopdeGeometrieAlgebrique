/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.ClovenFunctors

/-!
# SGA 1, Exposé VI, VI.12.1: isomorphism of functor categories

`FiberFunctorData p D` records fiber functors and pointwise constraints. Morphisms of
data recover natural transformations injectively. Objectwise, every total functor
`F` yields data `ofFunctor F`, and conversely any data whose `mapApp` is functorial
(`Assembled`) assembles to a total functor `toFunctor`, recovering `F` on the nose.
-/

universe v v₁ v₂ u u₁ u₂

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} {C : Type u₁} [Category.{v} E] [Category.{v₁} C]

/-- Vertical factor of an arrow through the chosen cartesian transport (VI.12.1). -/
noncomputable def verticalMap (p : C ⥤ E) [IsPreFibered p] {x y : C} (α : x ⟶ y) :
    x ⟶ (fiberPullbackObj p (p.map α) ⟨y, rfl⟩).val :=
  haveI : IsCartesian p (p.map α) (transport p (p.map α) ⟨y, rfl⟩) :=
    transport_isCartesian p (p.map α) ⟨y, rfl⟩
  IsCartesian.map p (p.map α) (transport p (p.map α) ⟨y, rfl⟩) α

instance verticalMap_isHomLift (p : C ⥤ E) [IsPreFibered p] {x y : C} (α : x ⟶ y) :
    IsHomLift p (𝟙 (p.obj x)) (verticalMap p α) := by
  haveI : IsCartesian p (p.map α) (transport p (p.map α) ⟨y, rfl⟩) :=
    transport_isCartesian p (p.map α) ⟨y, rfl⟩
  dsimp [verticalMap]
  infer_instance

@[reassoc]
theorem verticalMap_fac (p : C ⥤ E) [IsPreFibered p] {x y : C} (α : x ⟶ y) :
    verticalMap p α ≫ transport p (p.map α) ⟨y, rfl⟩ = α := by
  haveI : IsCartesian p (p.map α) (transport p (p.map α) ⟨y, rfl⟩) :=
    transport_isCartesian p (p.map α) ⟨y, rfl⟩
  exact IsCartesian.fac p (p.map α) (transport p (p.map α) ⟨y, rfl⟩) α

/-- VI.12.1: fiber functors with pointwise constraints. -/
structure FiberFunctorData (p : C ⥤ E) [IsPreFibered p] (D : Type u₂) [Category.{v₂} D] where
  onFiber (S : E) : Fiber p S ⥤ D
  constraint {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
      (onFiber T).obj (fiberPullbackObj p f ξ) ⟶ (onFiber S).obj ξ

namespace FiberFunctorData

variable {p : C ⥤ E} [IsPreFibered p] {D : Type u₂} [Category.{v₂} D]

/-- VI.12.1: extract fiber data from a total functor. -/
noncomputable def ofFunctor (F : C ⥤ D) : FiberFunctorData p D where
  onFiber := SGA.SGA1.ExposeVI.onFiber p F
  constraint f ξ := SGA.SGA1.ExposeVI.constraintApp p F f ξ

/-- Morphisms of fiber data (VI.12(c)). -/
structure Hom (Φ Ψ : FiberFunctorData p D) where
  app (S : E) : Φ.onFiber S ⟶ Ψ.onFiber S
  natural {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
      Φ.constraint f ξ ≫ (app S).app ξ =
        (app T).app (fiberPullbackObj p f ξ) ≫ Ψ.constraint f ξ

/-- VI.12.1: natural transformations induce morphisms of fiber data. -/
def Hom.ofNatTrans {F G : C ⥤ D} (α : F ⟶ G) :
    Hom (ofFunctor (p := p) F) (ofFunctor (p := p) G) where
  app _S :=
    { app := fun ξ => α.app ξ.val
      naturality := fun {_ _} u => α.naturality u.val }
  natural f ξ := constraintApp_naturality p α f ξ

/-- VI.12.1: the map on morphisms is injective. -/
theorem Hom.ofNatTrans_injective {F G : C ⥤ D} {α β : F ⟶ G}
    (h : Hom.ofNatTrans (p := p) (D := D) α = Hom.ofNatTrans (p := p) (D := D) β) :
    α = β := by
  apply natTrans_ext_onFiber (p := p)
  intro S ξ
  exact congrArg (fun H : Hom (ofFunctor (p := p) F) (ofFunctor (p := p) G) =>
    (H.app S).app ξ) h

theorem ofFunctor_obj (F : C ⥤ D) (S : E) (ξ : Fiber p S) :
    ((ofFunctor (p := p) F).onFiber S).obj ξ = F.obj ξ.val :=
  rfl

theorem ofFunctor_constraint_id (F : C ⥤ D) (S : E) (ξ : Fiber p S) :
    (ofFunctor (p := p) F).constraint (𝟙 S) ξ = F.map (transport p (𝟙 S) ξ) :=
  constraintApp_id p F S ξ

theorem ofFunctor_constraint_comp (F : C ⥤ D)
    {U T S : E} (g : U ⟶ T) (f : T ⟶ S) (ξ : Fiber p S) :
    F.map (transport p g (fiberPullbackObj p f ξ) ≫ transport p f ξ) =
      (ofFunctor (p := p) F).constraint g (fiberPullbackObj p f ξ) ≫
        (ofFunctor (p := p) F).constraint f ξ :=
  constraintApp_comp p F g f ξ

theorem hom_ext {F G : C ⥤ D}
    {α β : Hom (ofFunctor (p := p) F) (ofFunctor (p := p) G)}
    (h : ∀ S ξ, (α.app S).app ξ = (β.app S).app ξ) : α = β := by
  rcases α with ⟨appα, _⟩
  rcases β with ⟨appβ, _⟩
  have happ : appα = appβ := by
    funext S
    apply NatTrans.ext
    funext ξ
    exact h S ξ
  subst happ
  rfl

/-- VI.12.1: candidate action on morphisms via the vertical cartesian factor. -/
noncomputable def mapApp (Φ : FiberFunctorData p D) {x y : C} (α : x ⟶ y) :
    (Φ.onFiber (p.obj x)).obj ⟨x, rfl⟩ ⟶ (Φ.onFiber (p.obj y)).obj ⟨y, rfl⟩ :=
  (Φ.onFiber (p.obj x)).map ⟨verticalMap p α, verticalMap_isHomLift p α⟩ ≫
    Φ.constraint (p.map α) ⟨y, rfl⟩

/-- VI.12.1: `mapApp` of extracted data is the original functor on morphisms. -/
theorem ofFunctor_mapApp (F : C ⥤ D) {x y : C} (α : x ⟶ y) :
    (ofFunctor (p := p) F).mapApp α = F.map α := by
  haveI : IsCartesian p (p.map α) (transport p (p.map α) ⟨y, rfl⟩) :=
    transport_isCartesian p (p.map α) ⟨y, rfl⟩
  change F.map (verticalMap p α) ≫ F.map (transport p (p.map α) ⟨y, rfl⟩) = F.map α
  rw [← F.map_comp, verticalMap_fac]

/-- Data whose candidate morphism action is functorial. -/
structure Assembled (Φ : FiberFunctorData p D) : Prop where
  map_id : ∀ (x : C), Φ.mapApp (𝟙 x) = 𝟙 ((Φ.onFiber (p.obj x)).obj ⟨x, rfl⟩)
  map_comp : ∀ {x y z : C} (f : x ⟶ y) (g : y ⟶ z),
    Φ.mapApp (f ≫ g) = Φ.mapApp f ≫ Φ.mapApp g

theorem ofFunctor_assembled (F : C ⥤ D) : (ofFunctor (p := p) F).Assembled where
  map_id x := by
    rw [ofFunctor_mapApp, F.map_id]
    rfl
  map_comp f g := by
    rw [ofFunctor_mapApp, ofFunctor_mapApp, ofFunctor_mapApp, F.map_comp]

/-- VI.12.1: assemble a total functor from compatible fiber data. -/
noncomputable def toFunctor (Φ : FiberFunctorData p D) (h : Φ.Assembled) : C ⥤ D where
  obj x := (Φ.onFiber (p.obj x)).obj ⟨x, rfl⟩
  map α := Φ.mapApp α
  map_id := h.map_id
  map_comp := h.map_comp

/-- VI.12.1: assembling extracted data recovers the original functor. -/
theorem toFunctor_ofFunctor (F : C ⥤ D) :
    toFunctor (ofFunctor (p := p) F) (ofFunctor_assembled (p := p) F) = F := by
  refine Functor.ext (fun _ => rfl) ?_
  intro x y α
  simp [toFunctor, ofFunctor_mapApp]

end FiberFunctorData

end SGA.SGA1.ExposeVI
