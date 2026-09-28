/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.Cleavage
import Mathlib.CategoryTheory.IsoCat

/-!
# SGA 1, Exposé VI, §12: functors on a cloven category

Let `K` be a cleavage of `p : 𝒳 ⥤ E`. A functor `F : 𝒳 ⥤ D` gives functors
`F_S = F ∘ i_S : 𝒳_S ⥤ D` on the fibers and homomorphisms `φ_f = F * α_f : F_T f^* ⟶ F_S`,
satisfying a) and b); a natural transformation gives a family `u_S` satisfying c).
VI.12.1: this is an isomorphism of categories `Hom(𝒳, D) ≅ H(𝒳, D)`.

SGA assumes the cleavage normalized and writes a) as `φ_{𝟙_S} = id`. We allow any cleavage;
a) then reads `φ_{𝟙_S} = F_S * α_{𝟙_S}`, which is SGA's a) when `K` is normalized
(`FiberFunctorSystem.φ_id_of_isNormalized`).
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} {C : Type u₁} [Category.{v} E] [Category.{v₁} C] {p : C ⥤ E}
  (K : Cleavage p) (D : Type u₂) [Category.{v₂} D]

/-- VI.12: the objects of `H(𝒳, D)`: functors `F_S` on the fibers and homomorphisms
`φ_f : F_T f^* ⟶ F_S`, satisfying a) and b). -/
structure FiberFunctorSystem where
  /-- The functor `F_S : 𝒳_S ⥤ D`. -/
  obj (S : E) : Fiber p S ⥤ D
  /-- The homomorphism `φ_f : F_T f^* ⟶ F_S`. -/
  φ {T S : E} (f : T ⟶ S) : K.pullback f ⋙ obj T ⟶ obj S
  /-- VI.12 a), for an arbitrary cleavage: `φ_{𝟙_S} = F_S * α_{𝟙_S}`. -/
  φ_id (S : E) (ξ : Fiber p S) : (φ (𝟙 S)).app ξ = (obj S).map (K.transportId S ξ)
  /-- VI.12 b): `φ_{fg} ∘ (F_U * c_{f,g}) = φ_f ∘ (φ_g * f^*)`. -/
  φ_comp {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    (obj U).map (K.comparison f g ξ) ≫ (φ (g ≫ f)).app ξ =
      (φ g).app ((K.pullback f).obj ξ) ≫ (φ f).app ξ

namespace FiberFunctorSystem

variable {K D}

/-- VI.12: morphisms of `H(𝒳, D)`: families `u_S : F_S ⟶ G_S` satisfying c). -/
@[ext]
structure Hom (Φ Ψ : FiberFunctorSystem K D) where
  /-- The component `u_S : F_S ⟶ G_S`. -/
  app (S : E) : Φ.obj S ⟶ Ψ.obj S
  /-- VI.12 c). -/
  comm {T S : E} (f : T ⟶ S) (ξ : Fiber p S) :
    (Φ.φ f).app ξ ≫ (app S).app ξ = (app T).app ((K.pullback f).obj ξ) ≫ (Ψ.φ f).app ξ

attribute [reassoc] Hom.comm

instance : Category (FiberFunctorSystem K D) where
  Hom := Hom
  id Φ := ⟨fun S ↦ 𝟙 (Φ.obj S), fun f ξ ↦ by simp⟩
  comp {Φ Ψ Χ} α β := ⟨fun S ↦ α.app S ≫ β.app S, fun f ξ ↦ by
    simp [α.comm_assoc, β.comm]⟩

@[simp] theorem id_app (Φ : FiberFunctorSystem K D) (S : E) :
    (𝟙 Φ : Φ ⟶ Φ).app S = 𝟙 (Φ.obj S) := rfl

@[simp] theorem comp_app {Φ Ψ Χ : FiberFunctorSystem K D} (α : Φ ⟶ Ψ) (β : Ψ ⟶ Χ) (S : E) :
    (α ≫ β).app S = α.app S ≫ β.app S := rfl

@[ext] theorem hom_ext {Φ Ψ : FiberFunctorSystem K D} {α β : Φ ⟶ Ψ}
    (h : ∀ S, α.app S = β.app S) : α = β :=
  Hom.ext (funext h)

/-- Systems are equal when their fiber functors are equal and their `φ_f` agree up to the
resulting identifications. -/
theorem ext' {Φ Ψ : FiberFunctorSystem K D} (h : ∀ S, Φ.obj S = Ψ.obj S)
    (hφ : ∀ {T S : E} (f : T ⟶ S) (ξ : Fiber p S), (Φ.φ f).app ξ =
      eqToHom (Functor.congr_obj (h T) _) ≫ (Ψ.φ f).app ξ ≫
        eqToHom (Functor.congr_obj (h S) ξ).symm) : Φ = Ψ := by
  obtain ⟨obj, φ, _, _⟩ := Φ
  obtain ⟨obj', φ', _, _⟩ := Ψ
  obtain rfl : obj = obj' := funext h
  obtain rfl : @φ = @φ' := by
    funext T S f
    ext ξ
    simpa using hφ f ξ
  rfl

/-! ### From a functor to a system -/

/-- VI.12: the system `((F_S), (φ_f))` attached to a functor `F : 𝒳 ⥤ D`. -/
@[simps]
def ofFunctorObj (F : C ⥤ D) : FiberFunctorSystem K D where
  obj S := Fiber.fiberInclusion ⋙ F
  φ f :=
    { app := fun ξ ↦ F.map (K.transport f ξ)
      naturality := fun _ _ u ↦ by
        simp only [Functor.comp_map, Fiber.fiberInclusion]
        rw [← F.map_comp, ← F.map_comp, K.transport_natural] }
  φ_id S ξ := rfl
  φ_comp f g ξ := by
    simp only [Functor.comp_map, Fiber.fiberInclusion]
    rw [← F.map_comp, ← F.map_comp, Cleavage.comparison_fac]

/-- VI.12.1: the functor `K : Hom(𝒳, D) ⥤ H(𝒳, D)`. -/
@[simps]
def ofFunctor : (C ⥤ D) ⥤ FiberFunctorSystem K D where
  obj := ofFunctorObj
  map {F G} α :=
    { app := fun S ↦ Functor.whiskerLeft Fiber.fiberInclusion α
      comm := fun f ξ ↦ α.naturality (K.transport f ξ) }

/-- VI.12, a) for a normalized cleavage: `φ_{𝟙_S}` is the identity (up to the
identification `(𝟙_S)^* ξ = ξ`). -/
theorem φ_id_of_isNormalized (hK : K.IsNormalized) (Φ : FiberFunctorSystem K D) (S : E)
    (ξ : Fiber p S) :
    (Φ.φ (𝟙 S)).app ξ = eqToHom (congrArg (Φ.obj S).obj (hK.pullback_obj ξ)) := by
  have : K.transportId S ξ = eqToHom (hK.pullback_obj ξ) :=
    Subtype.ext (by obtain ⟨h, ht⟩ := hK S ξ; simpa [Cleavage.transportId] using ht)
  rw [Φ.φ_id, this, eqToHom_map]

/-! ### From a system to a functor -/

variable (Φ : FiberFunctorSystem K D)

/-- The vertical part of an arrow `φ` over `f`, relative to the transport `α_f`. -/
noncomputable def verticalPart {X Y : E} (ξ : Fiber p X) (η : Fiber p Y) (f : X ⟶ Y)
    (φ : ξ.val ⟶ η.val) [IsHomLift p f φ] : ξ ⟶ (K.pullback f).obj η :=
  ⟨IsCartesian.map p f (K.transport f η) φ, inferInstance⟩

@[reassoc (attr := simp)]
theorem verticalPart_fac {X Y : E} (ξ : Fiber p X) (η : Fiber p Y) (f : X ⟶ Y)
    (φ : ξ.val ⟶ η.val) [IsHomLift p f φ] :
    (verticalPart ξ η f φ).val ≫ K.transport f η = φ :=
  IsCartesian.fac p f _ φ

/-- VI.12.1: the value `F(α_f(η) u') = φ_f(η) F_X(u')` on an `f`-arrow `α_f(η) u'`. -/
noncomputable def mapAux {X Y : E} (ξ : Fiber p X) (η : Fiber p Y) (f : X ⟶ Y)
    (φ : ξ.val ⟶ η.val) [IsHomLift p f φ] : (Φ.obj X).obj ξ ⟶ (Φ.obj Y).obj η :=
  (Φ.obj X).map (verticalPart ξ η f φ) ≫ (Φ.φ f).app η

theorem mapAux_congr {X Y : E} (ξ : Fiber p X) (η : Fiber p Y) {f f' : X ⟶ Y} (h : f = f')
    (φ : ξ.val ⟶ η.val) [IsHomLift p f φ] [IsHomLift p f' φ] :
    Φ.mapAux ξ η f φ = Φ.mapAux ξ η f' φ := by
  subst h
  rfl

theorem mapAux_id {S : E} {ξ η : Fiber p S} (u : ξ ⟶ η) :
    Φ.mapAux ξ η (𝟙 S) u.val = (Φ.obj S).map u := by
  rw [mapAux, Φ.φ_id, ← Functor.map_comp]
  congr 1
  exact Subtype.ext (verticalPart_fac ξ η (𝟙 S) u.val)

theorem mapAux_comp {X Y Z : E} (ξ : Fiber p X) (η : Fiber p Y) (ζ : Fiber p Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) (φ : ξ.val ⟶ η.val) (ψ : η.val ⟶ ζ.val)
    [IsHomLift p f φ] [IsHomLift p g ψ] :
    Φ.mapAux ξ ζ (f ≫ g) (φ ≫ ψ) = Φ.mapAux ξ η f φ ≫ Φ.mapAux η ζ g ψ := by
  -- The vertical part of `φ ≫ ψ` is `w ≫ f^*(v) ≫ c_{g,f}`.
  have hvert : verticalPart ξ ζ (f ≫ g) (φ ≫ ψ) = verticalPart ξ η f φ ≫
      (K.pullback f).map (verticalPart η ζ g ψ) ≫ K.comparison g f ζ := by
    apply Subtype.ext
    refine (IsCartesian.map_uniq p (f ≫ g) (K.transport (f ≫ g) ζ) (φ ≫ ψ) _ ?_).symm
    simp only [fiber_comp_val, Category.assoc, Cleavage.comparison_fac,
      Cleavage.transport_naturality_assoc, verticalPart_fac, verticalPart_fac_assoc]
  simp only [mapAux, hvert, Functor.map_comp, Category.assoc, Φ.φ_comp]
  have := (Φ.φ f).naturality_assoc (verticalPart η ζ g ψ) ((Φ.φ g).app ζ)
  simp only [Functor.comp_map] at this
  rw [this]

/-- An object `x` of `𝒳` as an object of its own fiber. -/
abbrev fiberOf (x : C) : Fiber p (p.obj x) := ⟨x, rfl⟩

/-- VI.12.1: the functor `F : 𝒳 ⥤ D` reconstructed from a system satisfying a) and b). -/
@[simps!]
noncomputable def toFunctor : C ⥤ D where
  obj x := (Φ.obj (p.obj x)).obj (fiberOf x)
  map {x y} φ := Φ.mapAux (fiberOf x) (fiberOf y) (p.map φ) φ
  map_id x := (Φ.mapAux_congr _ _ (p.map_id x) _).trans
    ((Φ.mapAux_id (𝟙 (fiberOf x))).trans ((Φ.obj _).map_id _))
  map_comp {x y z} φ ψ := (Φ.mapAux_congr _ _ (p.map_comp φ ψ) _).trans
    (Φ.mapAux_comp (fiberOf x) (fiberOf y) (fiberOf z) (p.map φ) (p.map ψ) φ ψ)

/-- Changing the representation `ξ = ⟨ξ.val, rfl⟩` of objects of fibers. -/
theorem mapAux_rep {X Y : E} (ξ : Fiber p X) (η : Fiber p Y) (f : X ⟶ Y)
    (φ : ξ.val ⟶ η.val) [IsHomLift p f φ] :
    Φ.mapAux (fiberOf ξ.val) (fiberOf η.val) (p.map φ) φ =
      eqToHom (by obtain ⟨x, rfl⟩ := ξ; rfl) ≫ Φ.mapAux ξ η f φ ≫
        eqToHom (by obtain ⟨y, rfl⟩ := η; rfl) := by
  obtain ⟨x, rfl⟩ := ξ
  obtain ⟨y, rfl⟩ := η
  have : f = p.map φ := IsHomLift.eq_of_isHomLift p f φ
  subst this
  simp

theorem toFunctor_obj_eq {S : E} (ξ : Fiber p S) :
    (Φ.toFunctor).obj ξ.val = (Φ.obj S).obj ξ := by
  obtain ⟨x, rfl⟩ := ξ
  rfl

theorem ofFunctorObj_toFunctor : ofFunctorObj (Φ.toFunctor) = Φ := by
  refine ext' (fun S ↦ Functor.ext (fun ξ ↦ Φ.toFunctor_obj_eq ξ) fun ξ η u ↦ ?_)
    fun {T S} f ξ ↦ ?_
  · change Φ.mapAux (fiberOf ξ.val) (fiberOf η.val) (p.map u.val) u.val = _
    rw [Φ.mapAux_rep ξ η (𝟙 S) u.val, Φ.mapAux_id]
    rfl
  · change Φ.mapAux (fiberOf _) (fiberOf ξ.val) (p.map (K.transport f ξ))
      (K.transport f ξ) = _
    rw [Φ.mapAux_rep ((K.pullback f).obj ξ) ξ f (K.transport f ξ)]
    have : verticalPart ((K.pullback f).obj ξ) ξ f (K.transport f ξ) = 𝟙 _ :=
      Subtype.ext (IsCartesian.map_self p f _)
    simp only [mapAux, this, Functor.map_id, Category.id_comp]
    rfl

variable {Φ}

theorem toFunctor_ofFunctorObj (F : C ⥤ D) : (ofFunctorObj (K := K) F).toFunctor = F := by
  refine Functor.hext (fun _ ↦ rfl) fun x y φ ↦ heq_of_eq ?_
  change F.map (verticalPart (K := K) (fiberOf x) (fiberOf y) (p.map φ) φ).val ≫
    F.map (K.transport (p.map φ) (fiberOf y)) = F.map φ
  rw [← F.map_comp, verticalPart_fac]

end FiberFunctorSystem

open FiberFunctorSystem

instance : (ofFunctor (K := K) (D := D)).Faithful where
  map_injective {F G} {α β} h := by
    ext x
    exact congrArg
      (fun γ : ofFunctorObj F ⟶ ofFunctorObj G ↦ (γ.app (p.obj x)).app (fiberOf x)) h

instance : (ofFunctor (K := K) (D := D)).Full where
  map_surjective {F G} u := by
    refine ⟨
      { app := fun x ↦ (u.app (p.obj x)).app (fiberOf x)
        naturality := fun x y φ ↦ ?_ }, ?_⟩
    · -- write `φ` as its vertical part followed by a transport
      let v := verticalPart (K := K) (fiberOf x) (fiberOf y) (p.map φ) φ
      have hv : v.val ≫ K.transport (p.map φ) (fiberOf y) = φ :=
        verticalPart_fac (K := K) (fiberOf x) (fiberOf y) (p.map φ) φ
      let t := K.transport (p.map φ) (fiberOf y)
      let uy : F.obj y ⟶ G.obj y := (u.app (p.obj y)).app (fiberOf y)
      let ux : F.obj x ⟶ G.obj x := (u.app (p.obj x)).app (fiberOf x)
      let uT : F.obj ((K.pullback (p.map φ)).obj (fiberOf y)).val ⟶
          G.obj ((K.pullback (p.map φ)).obj (fiberOf y)).val :=
        (u.app (p.obj x)).app ((K.pullback (p.map φ)).obj (fiberOf y))
      have hc : F.map t ≫ uy = uT ≫ G.map t := u.comm (p.map φ) (fiberOf y)
      have hn : F.map v.val ≫ uT = ux ≫ G.map v.val := (u.app (p.obj x)).naturality v
      change F.map φ ≫ uy = ux ≫ G.map φ
      calc F.map φ ≫ uy = F.map v.val ≫ F.map t ≫ uy := by
            rw [← Category.assoc, ← F.map_comp, hv]
        _ = (F.map v.val ≫ uT) ≫ G.map t := by rw [hc, Category.assoc]
        _ = ux ≫ G.map φ := by rw [hn, Category.assoc, ← G.map_comp, hv]
    · ext S ξ
      obtain ⟨x, rfl⟩ := ξ
      rfl

instance : (ofFunctor (K := K) (D := D)).IsIso where
  bijective_obj := by
    constructor
    · intro F G h
      rw [← toFunctor_ofFunctorObj (K := K) F, ← toFunctor_ofFunctorObj (K := K) G]
      exact congrArg FiberFunctorSystem.toFunctor h
    · intro Φ
      exact ⟨Φ.toFunctor, Φ.ofFunctorObj_toFunctor⟩

/-- VI.12.1: `F ↦ ((F_S), (φ_f))` is an isomorphism of categories
`Hom(𝒳, D) ≅ H(𝒳, D)`. -/
noncomputable def functorIsoFiberFunctorSystem : IsoCat (C ⥤ D) (FiberFunctorSystem K D) :=
  (ofFunctor (K := K) (D := D)).asIsomorphism

end SGA.SGA1.ExposeVI

/-! ### `E`-functors between cloven categories -/

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {X : BasedCategory.{v₁, u₁} E}
  {Y : BasedCategory.{v₂, u₂} E} (K : Cleavage X.p) (K' : Cleavage Y.p) (F : BasedFunctor X Y)

/-- VI.12: the `T`-morphism `φ_f(ξ) : F_T(f^* ξ) ⟶ f^*(F_S ξ)` through which `F(α_f(ξ))`
factors. -/
noncomputable def basedConstraintApp {T S : E} (f : T ⟶ S) (ξ : Fiber X.p S) :
    F.obj ((K.pullback f).obj ξ).val ⟶ ((K'.pullback f).obj ((fiberMap F S).obj ξ)).val :=
  IsCartesian.map Y.p f (K'.transport f ((fiberMap F S).obj ξ)) (F.map (K.transport f ξ))

instance {T S : E} (f : T ⟶ S) (ξ : Fiber X.p S) :
    IsHomLift Y.p (𝟙 T) (basedConstraintApp K K' F f ξ) :=
  IsCartesian.map_isHomLift Y.p f _ _

@[reassoc (attr := simp)]
theorem basedConstraintApp_fac {T S : E} (f : T ⟶ S) (ξ : Fiber X.p S) :
    basedConstraintApp K K' F f ξ ≫ K'.transport f ((fiberMap F S).obj ξ) =
      F.map (K.transport f ξ) :=
  IsCartesian.fac Y.p f _ _

/-- VI.12: `φ_f : F_T f^* ⟶ f^* F_S`, a homomorphism of functors `𝒳_S ⥤ 𝒴_T`. -/
noncomputable def basedConstraint {T S : E} (f : T ⟶ S) :
    K.pullback f ⋙ fiberMap F T ⟶ fiberMap F S ⋙ K'.pullback f where
  app ξ := ⟨basedConstraintApp K K' F f ξ, inferInstance⟩
  naturality {ξ η} u := by
    apply Subtype.ext
    apply IsCartesian.ext Y.p f (K'.transport f ((fiberMap F S).obj η))
    change (F.map ((K.pullback f).map u).val ≫ basedConstraintApp K K' F f η) ≫
        K'.transport f ((fiberMap F S).obj η) =
      (basedConstraintApp K K' F f ξ ≫ ((K'.pullback f).map ((fiberMap F S).map u)).val) ≫
        K'.transport f ((fiberMap F S).obj η)
    rw [Category.assoc, Category.assoc, basedConstraintApp_fac, K'.transport_naturality,
      basedConstraintApp_fac_assoc, ← F.map_comp, K.transport_naturality, F.map_comp]

theorem basedConstraint_app_val {T S : E} (f : T ⟶ S) (ξ : Fiber X.p S) :
    ((basedConstraint K K' F f).app ξ).val = basedConstraintApp K K' F f ξ := rfl

/-- VI.12 a′): for normalized cleavages, `φ_{𝟙_S}` is the identity (up to the identification
`(𝟙_S)^* = 𝟭`). -/
theorem basedConstraint_id (hK : K.IsNormalized) (hK' : K'.IsNormalized) (S : E)
    (ξ : Fiber X.p S) : ∃ h, ((basedConstraint K K' F (𝟙 S)).app ξ).val = eqToHom h := by
  obtain ⟨h₁, ht₁⟩ := hK S ξ
  obtain ⟨h₂, ht₂⟩ := hK' S ((fiberMap F S).obj ξ)
  refine ⟨congrArg F.obj h₁ |>.trans h₂.symm, ?_⟩
  have := isHomLift_eqToHom_id (p := Y.p) (congrArg F.obj h₁ |>.trans h₂.symm)
    ((F.w_obj _).trans ((K.pullback (𝟙 S)).obj ξ).property)
  apply IsCartesian.ext Y.p (𝟙 S) (K'.transport (𝟙 S) ((fiberMap F S).obj ξ))
  rw [basedConstraint_app_val, basedConstraintApp_fac, ht₁, ht₂, eqToHom_map]
  simp

/-- VI.12 b′): the compatibility of `φ` with the comparisons `c_{f,g}` of the two cleavages:
`φ_{fg} ∘ F_U(c_{f,g}) = c'_{f,g}(F_S) ∘ g^*(φ_f) ∘ φ_g(f^*)`. -/
theorem basedConstraint_comp {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber X.p S) :
    F.map (K.comparison f g ξ).val ≫ ((basedConstraint K K' F (g ≫ f)).app ξ).val =
      ((basedConstraint K K' F g).app ((K.pullback f).obj ξ)).val ≫
        ((K'.pullback g).map ((basedConstraint K K' F f).app ξ)).val ≫
          (K'.comparison f g ((fiberMap F S).obj ξ)).val := by
  have : IsHomLift Y.p (𝟙 U) (F.map (K.comparison f g ξ).val) :=
    F.preserves_isHomLift (𝟙 U) _
  have h₁ : F.map (K.comparison f g ξ).val ≫ basedConstraintApp K K' F (g ≫ f) ξ ≫
      K'.transport (g ≫ f) ((fiberMap F S).obj ξ) =
        F.map (K.transport g ((K.pullback f).obj ξ)) ≫ F.map (K.transport f ξ) := by
    rw [basedConstraintApp_fac, ← F.map_comp, ← F.map_comp, K.comparison_fac]
  have h₂ : basedConstraintApp K K' F g ((K.pullback f).obj ξ) ≫
      ((K'.pullback g).map ((basedConstraint K K' F f).app ξ)).val ≫
        (K'.comparison f g ((fiberMap F S).obj ξ)).val ≫
          K'.transport (g ≫ f) ((fiberMap F S).obj ξ) =
        F.map (K.transport g ((K.pullback f).obj ξ)) ≫ F.map (K.transport f ξ) := by
    have hn := K'.transport_naturality g ((basedConstraint K K' F f).app ξ)
    rw [K'.comparison_fac]
    erw [reassoc_of% hn]
    rw [basedConstraintApp_fac_assoc, basedConstraint_app_val, basedConstraintApp_fac]
  apply IsCartesian.ext Y.p (g ≫ f) (K'.transport (g ≫ f) ((fiberMap F S).obj ξ))
  simp only [basedConstraint_app_val, Category.assoc]
  exact h₁.trans h₂.symm

/-- VI.12: an `E`-functor between cloven categories is cartesian iff all the `φ_f` are
isomorphisms. -/
theorem isCartesianFunctor_iff_basedConstraint_isIso :
    IsCartesianFunctor F ↔ ∀ {T S : E} (f : T ⟶ S) (ξ : Fiber X.p S),
      IsIso ((basedConstraint K K' F f).app ξ) := by
  constructor
  · intro hF T S f ξ
    have : IsCartesian Y.p f (F.map (K.transport f ξ)) := hF.map_isCartesian f _
    have : IsIso ((basedConstraint K K' F f).app ξ).val :=
      (IsCartesian.domainUniqueUpToIso Y.p f (K'.transport f ((fiberMap F S).obj ξ))
        (F.map (K.transport f ξ))).isIso_hom
    exact fiber_isIso_of_isIso_val _
  · intro h
    refine isCartesianFunctor_of_map_transport K F fun {T S} f ξ ↦ ?_
    have := h f ξ
    have : IsIso ((basedConstraint K K' F f).app ξ).val :=
      inferInstanceAs (IsIso (Fiber.fiberInclusion.map ((basedConstraint K K' F f).app ξ)))
    have : IsHomLift Y.p (𝟙 T) (asIso ((basedConstraint K K' F f).app ξ).val).hom :=
      ((basedConstraint K K' F f).app ξ).property
    rw [← basedConstraintApp_fac]
    exact IsCartesian.of_iso_comp Y.p f _ (asIso ((basedConstraint K K' F f).app ξ).val)

end SGA.SGA1.ExposeVI
