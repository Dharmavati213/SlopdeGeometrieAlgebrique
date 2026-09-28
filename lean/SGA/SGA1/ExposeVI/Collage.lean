/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.VariousExamples
import SGA.SGA1.ExposeVI.FamilyProducts

/-!
# SGA 1, Exposé VI, VI.11 f): categories over the walking arrow

Let `E` have two objects `T = 0`, `S = 1` and one non-identity arrow `f : T ⟶ S` (the ordered set
`Fin 2`). SGA: a category `𝒳` over `E` is determined, up to unique `E`-isomorphism, by the fibers
`𝒳_S`, `𝒳_T` and the bifunctor `H(η, ξ) = Hom_f(η, ξ)` on `𝒳_Tᵒᵖ × 𝒳_S`, and "one leaves to the
reader the task of making explicit the construction in the opposite direction". This file makes
it explicit: `Collage H` is the category over `Fin 2` with fibers `B` (over `T`) and `A` (over
`S`) and with `Hom_f(η, ξ) = H(η, ξ)`.

* `Collage.fiberIsoTarget`, `Collage.fiberIsoSource`: its fibers are isomorphic to `A` and `B`;
* `Collage.homOverEquiv`: `Hom_f(η, ξ) ≃ H(η, ξ)`.

* `collageIso`, `collageToSelf_comp`: conversely every category `𝒳` over `E` is isomorphic over `E`
  to the collage of `(𝒳_S, 𝒳_T, Hom_f)`.

The uniqueness of this isomorphism (SGA's "up to unique `E`-isomorphism") is not formalized.
-/

universe v u

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite

variable {A B : Type u} [Category.{v} A] [Category.{v} B]

/-- VI.11 f): the category over the walking arrow defined by two categories `B = 𝒳_T`,
`A = 𝒳_S` and a bifunctor `H : Bᵒᵖ ⥤ A ⥤ Type`. Its objects are those of `B` (over `T`) and of
`A` (over `S`). -/
@[nolint unusedArguments]
def Collage (_H : Bᵒᵖ ⥤ A ⥤ Type v) : Type u := B ⊕ A

namespace Collage

variable {H : Bᵒᵖ ⥤ A ⥤ Type v}

/-- An object of `𝒳_T = B`. -/
def ofSource (b : B) : Collage H := Sum.inl b

/-- An object of `𝒳_S = A`. -/
def ofTarget (a : A) : Collage H := Sum.inr a

/-- Arrows of the collage: those of `B`, those of `A`, the elements of `H(b, a)` from `b` to `a`,
and none from `A` to `B`. -/
def Hom : Collage H → Collage H → Type v
  | Sum.inl b, Sum.inl b' => b ⟶ b'
  | Sum.inr a, Sum.inr a' => a ⟶ a'
  | Sum.inl b, Sum.inr a => (H.obj (op b)).obj a
  | Sum.inr _, Sum.inl _ => PEmpty

/-- Identities of the collage. -/
def id : ∀ x : Collage H, Hom x x
  | Sum.inl b => 𝟙 b
  | Sum.inr a => 𝟙 a

/-- Composition in the collage, using the bifunctoriality of `H`. -/
def comp : ∀ {x y z : Collage H}, Hom x y → Hom y z → Hom x z
  | Sum.inl _, Sum.inl _, Sum.inl _, u, u' => (u ≫ u' : _ ⟶ _)
  | Sum.inl _, Sum.inl _, Sum.inr a, u, h => (H.map (u : _ ⟶ _).op).app a h
  | Sum.inl b, Sum.inr _, Sum.inr _, h, v => (H.obj (op b)).map (v : _ ⟶ _) h
  | Sum.inr _, Sum.inr _, Sum.inr _, v, v' => (v ≫ v' : _ ⟶ _)
  | Sum.inl _, Sum.inr _, Sum.inl _, _, e => PEmpty.elim e
  | Sum.inr _, Sum.inr _, Sum.inl _, _, e => PEmpty.elim e
  | Sum.inr _, Sum.inl _, _, e, _ => PEmpty.elim e

instance category : Category (Collage H) where
  Hom := Hom
  id := id
  comp := comp
  id_comp {x y} f := by
    rcases x with b | a <;> rcases y with b' | a'
    · exact Category.id_comp (obj := B) _
    · change (H.map (𝟙 b).op).app a' f = f
      rw [op_id, H.map_id]
      rfl
    · exact PEmpty.elim f
    · exact Category.id_comp (obj := A) _
  comp_id {x y} f := by
    rcases x with b | a <;> rcases y with b' | a'
    · exact Category.comp_id (obj := B) _
    · change (H.obj (op b)).map (𝟙 a') f = f
      rw [(H.obj (op b)).map_id]
      rfl
    · exact PEmpty.elim f
    · exact Category.comp_id (obj := A) _
  assoc {w x y z} f g h := by
    rcases w with b | a <;> rcases x with b₁ | a₁ <;> rcases y with b₂ | a₂ <;>
      rcases z with b₃ | a₃
    all_goals first
      | exact PEmpty.elim f
      | exact PEmpty.elim g
      | exact PEmpty.elim h
      | skip
    · exact Category.assoc (obj := B) _ _ _
    · change b ⟶ b₁ at f
      change b₁ ⟶ b₂ at g
      change (H.map (f ≫ g : b ⟶ b₂).op).app a₃ h = (H.map f.op).app a₃ ((H.map g.op).app a₃ h)
      rw [op_comp, H.map_comp]
      rfl
    · change (H.obj (op b)).map h ((H.map f.op).app a₂ g) =
        (H.map f.op).app a₃ ((H.obj (op b₁)).map h g)
      exact (NatTrans.naturality_apply (H.map f.op) h g).symm
    · change a₁ ⟶ a₂ at g
      change a₂ ⟶ a₃ at h
      change (H.obj (op b)).map h ((H.obj (op b)).map g f) = (H.obj (op b)).map (g ≫ h : a₁ ⟶ a₃) f
      rw [(H.obj (op b)).map_comp]
      rfl
    · exact Category.assoc (obj := A) _ _ _

/-- The position of an object over the walking arrow `0 ⟶ 1`. -/
def projObj : Collage H → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

theorem projObj_le : ∀ {x y : Collage H} (_ : x ⟶ y), projObj x ≤ projObj y
  | Sum.inl _, Sum.inl _, _ => le_refl _
  | Sum.inl _, Sum.inr _, _ => show (0 : Fin 2) ≤ 1 by decide
  | Sum.inr _, Sum.inr _, _ => le_refl _
  | Sum.inr _, Sum.inl _, e => PEmpty.elim e

variable (H) in
/-- VI.11 f): the projection of the collage onto the walking arrow `T = 0 ⟶ S = 1`. -/
def proj : Collage H ⥤ Fin 2 where
  obj := projObj
  map φ := homOfLE (projObj_le φ)

variable (H) in
/-- The inclusion of `𝒳_S = A` into the collage. -/
def inclTarget : A ⥤ Collage H where
  obj a := Sum.inr a
  map v := (v : Hom (H := H) (Sum.inr _) (Sum.inr _))
  map_id _ := rfl
  map_comp _ _ := rfl

variable (H) in
/-- The inclusion of `𝒳_T = B` into the collage. -/
def inclSource : B ⥤ Collage H where
  obj b := Sum.inl b
  map u := (u : Hom (H := H) (Sum.inl _) (Sum.inl _))
  map_id _ := rfl
  map_comp _ _ := rfl

theorem inclTarget_comp_proj :
    inclTarget H ⋙ proj H = (Functor.const A).obj (1 : Fin 2) :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _

theorem inclSource_comp_proj :
    inclSource H ⋙ proj H = (Functor.const B).obj (0 : Fin 2) :=
  CategoryTheory.Functor.ext (fun _ ↦ rfl) fun _ _ _ ↦ Subsingleton.elim _ _

variable (H) in
/-- VI.11 f): `A ⥤ 𝒳_S`, the identification of the fiber over `S` of the collage. -/
def fiberFunctorTarget : A ⥤ Fiber (proj H) 1 := Fiber.inducedFunctor inclTarget_comp_proj

variable (H) in
/-- VI.11 f): `B ⥤ 𝒳_T`, the identification of the fiber over `T` of the collage. -/
def fiberFunctorSource : B ⥤ Fiber (proj H) 0 := Fiber.inducedFunctor inclSource_comp_proj

instance : (fiberFunctorTarget H).IsIso where
  faithful := ⟨fun {_ _} {u v} h ↦ congrArg Subtype.val h⟩
  full := ⟨fun {a a'} φ ↦ ⟨(φ.val : Hom (Sum.inr a) (Sum.inr a')), rfl⟩⟩
  bijective_obj := by
    constructor
    · intro a a' h
      have := congrArg Subtype.val h
      exact Sum.inr_injective this
    · rintro ⟨x, hx⟩
      rcases x with b | a
      · exact absurd hx (show (0 : Fin 2) ≠ 1 by decide)
      · exact ⟨a, rfl⟩

instance : (fiberFunctorSource H).IsIso where
  faithful := ⟨fun {_ _} {u v} h ↦ congrArg Subtype.val h⟩
  full := ⟨fun {b b'} φ ↦ ⟨(φ.val : Hom (Sum.inl b) (Sum.inl b')), rfl⟩⟩
  bijective_obj := by
    constructor
    · intro b b' h
      have := congrArg Subtype.val h
      exact Sum.inl_injective this
    · rintro ⟨x, hx⟩
      rcases x with b | a
      · exact ⟨b, rfl⟩
      · exact absurd hx (show (1 : Fin 2) ≠ 0 by decide)

variable (H) in
/-- VI.11 f): the fiber of the collage over `S` is (isomorphic to) `A`. -/
noncomputable def fiberIsoTarget : IsoCat A (Fiber (proj H) 1) :=
  (fiberFunctorTarget H).asIsomorphism

variable (H) in
/-- VI.11 f): the fiber of the collage over `T` is (isomorphic to) `B`. -/
noncomputable def fiberIsoSource : IsoCat B (Fiber (proj H) 0) :=
  (fiberFunctorSource H).asIsomorphism

/-- VI.11 f): the arrows of the collage over `f : T ⟶ S` from `b` to `a` are the elements of
`H(b, a)`. -/
def homOverEquiv (b : B) (a : A) :
    HomOver (proj H) walkingArrow (Sum.inl b : Collage H) (Sum.inr a) ≃ (H.obj (op b)).obj a where
  toFun φ := φ.val
  invFun h := ⟨(h : Hom (Sum.inl b) (Sum.inr a)), fin2_isHomLift (proj H) walkingArrow _ rfl rfl⟩
  left_inv _ := rfl
  right_inv _ := rfl

end Collage

/-! ### Every category over the walking arrow is a collage -/

section Reconstruction

variable {C : Type u} [Category.{v} C] (p : C ⥤ Fin 2)

/-- VI.11 f): the bifunctor `H(η, ξ) = Hom_f(η, ξ)` of a category over the walking arrow. -/
@[simps]
def homOverBifunctor : (Fiber p 0)ᵒᵖ ⥤ Fiber p 1 ⥤ Type v where
  obj η :=
    { obj := fun ξ ↦ HomOver p walkingArrow η.unop.val ξ.val
      map := fun {ξ ξ'} w ↦ TypeCat.ofHom fun φ ↦ ⟨φ.val ≫ w.val,
        fin2_isHomLift p walkingArrow _ η.unop.property ξ'.property⟩
      map_id := fun ξ ↦ by ext φ; exact Category.comp_id (obj := C) _
      map_comp := fun _ _ ↦ by ext φ; exact (Category.assoc (obj := C) _ _ _).symm }
  map {η η'} u :=
    { app := fun ξ ↦ TypeCat.ofHom fun φ ↦ ⟨u.unop.val ≫ φ.val,
        fin2_isHomLift p walkingArrow _ η'.unop.property ξ.property⟩
      naturality := fun _ _ _ ↦ by ext φ; exact (Category.assoc (obj := C) _ _ _).symm }
  map_id _ := by ext; exact Category.id_comp (obj := C) _
  map_comp _ _ := by ext; exact Category.assoc (obj := C) _ _ _

/-- VI.11 f): the canonical functor from the collage of `(𝒳_S, 𝒳_T, Hom_f)` to `𝒳`. -/
def collageToSelf : Collage (homOverBifunctor p) ⥤ C where
  obj x := match x with
    | Sum.inl η => η.val
    | Sum.inr ξ => ξ.val
  map {x y} φ := match x, y, φ with
    | Sum.inl _, Sum.inl _, u => (u : _ ⟶ _).val
    | Sum.inr _, Sum.inr _, w => (w : _ ⟶ _).val
    | Sum.inl _, Sum.inr _, φ => (φ : HomOver _ _ _ _).val
    | Sum.inr _, Sum.inl _, e => PEmpty.elim e
  map_id x := by rcases x with η | ξ <;> rfl
  map_comp {x y z} φ ψ := by
    rcases x with η | ξ <;> rcases y with η' | ξ' <;> rcases z with η'' | ξ''
    all_goals first
      | exact PEmpty.elim φ
      | exact PEmpty.elim ψ
      | rfl

theorem collageToSelf_obj_proj (x : Collage (homOverBifunctor p)) :
    p.obj ((collageToSelf p).obj x) = (Collage.proj _).obj x := by
  rcases x with η | ξ
  · exact η.property
  · exact ξ.property

/-- VI.11 f): the canonical functor from the collage of the data of `𝒳` to `𝒳` lies over the
walking arrow. -/
theorem collageToSelf_comp : collageToSelf p ⋙ p = Collage.proj (homOverBifunctor p) :=
  functor_comp_eq_of_isHomLift _ _ _ (collageToSelf_obj_proj p) fun {x y} _ ↦
    fin2_isHomLift p _ _ (collageToSelf_obj_proj p x) (collageToSelf_obj_proj p y)

instance : (collageToSelf p).IsIso where
  faithful := ⟨fun {x y} {φ ψ} h ↦ by
    rcases x with η | ξ <;> rcases y with η' | ξ'
    · exact Subtype.ext h
    · exact Subtype.ext h
    · exact PEmpty.elim φ
    · exact Subtype.ext h⟩
  full := ⟨fun {x y} m ↦ by
    rcases x with η | ξ <;> rcases y with η' | ξ'
    · exact ⟨(⟨m, fin2_isHomLift p (𝟙 0) m η.property η'.property⟩ : η ⟶ η'), rfl⟩
    · exact ⟨(⟨m, fin2_isHomLift p walkingArrow m η.property ξ'.property⟩ :
        HomOver p walkingArrow η.val ξ'.val), rfl⟩
    · have h := leOfHom (p.map m)
      change p.obj ξ.val ≤ p.obj η'.val at h
      rw [ξ.property, η'.property] at h
      exact absurd h (by decide)
    · exact ⟨(⟨m, fin2_isHomLift p (𝟙 1) m ξ.property ξ'.property⟩ : ξ ⟶ ξ'), rfl⟩⟩
  bijective_obj := by
    constructor
    · intro x y h
      rcases x with η | ξ <;> rcases y with η' | ξ'
      · exact congrArg Sum.inl (Subtype.ext h)
      · have h' := congrArg p.obj h
        change p.obj η.val = p.obj ξ'.val at h'
        rw [η.property, ξ'.property] at h'
        exact absurd h' (by decide)
      · have h' := congrArg p.obj h
        change p.obj ξ.val = p.obj η'.val at h'
        rw [ξ.property, η'.property] at h'
        exact absurd h' (by decide)
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro c
      rcases (by decide : ∀ i : Fin 2, i = 0 ∨ i = 1) (p.obj c) with h | h
      · exact ⟨Sum.inl ⟨c, h⟩, rfl⟩
      · exact ⟨Sum.inr ⟨c, h⟩, rfl⟩

/-- VI.11 f): a category `𝒳` over the walking arrow is isomorphic (over `E`, by
`collageToSelf_comp`) to the category defined by its fibers `𝒳_S`, `𝒳_T` and the bifunctor
`Hom_f(η, ξ)`. -/
noncomputable def collageIso : IsoCat (Collage (homOverBifunctor p)) C :=
  (collageToSelf p).asIsomorphism

end Reconstruction

end SGA.SGA1.ExposeVI
