/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.Products
import SGA.SGA1.ExposeVI.Cleavage
import Mathlib.CategoryTheory.Pi.Basic

/-!
# SGA 1, Exposé VI, VI.3 and VI.6.3–6.5 for arbitrary families

SGA remarks that VI.6.3–6.5 "extend to the case of the fibered product of an arbitrary family of
categories over `E`". The fibered product `∏_E 𝒳_i` of a family `(𝒳_i)_{i ∈ I}` of categories over
`E` (the projective limit in `Cat_{/E}`) has as objects an object `S` of `E` with objects `x_i`
of the `𝒳_i` over `S`, and as arrows over `f` families of arrows over `f` (for `I` empty it is
`E`). We prove:

* VI.3: `Hom_E(𝒵, ∏_E 𝒳_i) ≅ ∏ Hom_E(𝒵, 𝒳_i)`, an isomorphism of categories;
* VI.6.3: an arrow of `∏_E 𝒳_i` is cartesian iff all its components are;
* VI.6.4: an `E`-functor into `∏_E 𝒳_i` is cartesian iff all its components are, whence
  `Cart_E(𝒵, ∏_E 𝒳_i) ≅ ∏ Cart_E(𝒵, 𝒳_i)`;
* VI.6.5: a product of prefibered (resp. fibered) categories is prefibered (resp. fibered);
* VI.7.1: cleavages of the `𝒳_i` give a cleavage of the product.
-/

universe w v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

/-- If every `F.map φ` lies over `q.map φ`, then `F ⋙ p = q`. -/
theorem functor_comp_eq_of_isHomLift {E : Type u} [Category.{v} E] {A : Type u₁}
    [Category.{v₁} A] {C : Type u₂} [Category.{v₂} C] (F : A ⥤ C) (p : C ⥤ E) (q : A ⥤ E)
    (hobj : ∀ a, p.obj (F.obj a) = q.obj a)
    (hmap : ∀ {a b : A} (φ : a ⟶ b), IsHomLift p (q.map φ) (F.map φ)) : F ⋙ p = q :=
  Functor.ext hobj fun _ _ φ ↦ by
    have := hmap φ
    exact IsHomLift.fac' p (q.map φ) (F.map φ)

/-- A vertical arrow also lies over any identification `R₁ = R₂` of the images of its ends. -/
theorem isHomLift_eqToHom_of_isHomLift_id {E : Type u} [Category.{v} E] {C : Type u₂}
    [Category.{v₂} C] {p : C ⥤ E} {R R₁ R₂ : E} {a b : C} (φ : a ⟶ b) [IsHomLift p (𝟙 R) φ]
    (h : R₁ = R₂) (ha : p.obj a = R₁) (hb : p.obj b = R₂) : IsHomLift p (eqToHom h) φ :=
  IsHomLift.of_fac' p _ φ ha hb (by rw [IsHomLift.fac' p (𝟙 R) φ]; simp)

variable {E : Type u} [Category.{v} E] {I : Type w}

/-- VI.3, VI.6.5: an object of the fibered product `∏_E 𝒳_i` of a family of categories over `E`:
an object `S` of `E` together with objects `x_i` of the `𝒳_i` over `S`. -/
structure FiberPi (X : I → BasedCategory.{v₁, u₁} E) where
  /-- The common image `S` in `E`. -/
  base : E
  /-- The components `x_i`. -/
  obj (i : I) : (X i).obj
  obj_proj (i : I) : (X i).p.obj (obj i) = base

namespace FiberPi

variable {X : I → BasedCategory.{v₁, u₁} E}

/-- Arrows of `∏_E 𝒳_i`: an arrow `f` of `E` and arrows of the `𝒳_i` over `f`. -/
structure Hom (x y : FiberPi X) where
  /-- The common image in `E`. -/
  base : x.base ⟶ y.base
  /-- The components. -/
  map (i : I) : x.obj i ⟶ y.obj i
  isHomLift (i : I) : IsHomLift (X i).p base (map i) := by infer_instance

attribute [instance] Hom.isHomLift

instance : CategoryStruct (FiberPi X) where
  Hom := Hom
  id x := ⟨𝟙 x.base, fun i ↦ 𝟙 (x.obj i), fun i ↦ IsHomLift.id (x.obj_proj i)⟩
  comp f g := ⟨f.base ≫ g.base, fun i ↦ f.map i ≫ g.map i, fun _ ↦ inferInstance⟩

@[simp] theorem id_base (x : FiberPi X) : Hom.base (𝟙 x) = 𝟙 x.base := rfl
@[simp] theorem id_map (x : FiberPi X) (i : I) : Hom.map (𝟙 x) i = 𝟙 (x.obj i) := rfl
@[simp] theorem comp_base {x y z : FiberPi X} (f : x ⟶ y) (g : y ⟶ z) :
    Hom.base (f ≫ g) = f.base ≫ g.base := rfl
@[simp] theorem comp_map {x y z : FiberPi X} (f : x ⟶ y) (g : y ⟶ z) (i : I) :
    Hom.map (f ≫ g) i = f.map i ≫ g.map i := rfl

@[ext]
theorem hom_ext {x y : FiberPi X} {f g : x ⟶ y} (h₁ : f.base = g.base)
    (h₂ : ∀ i, f.map i = g.map i) : f = g := by
  obtain ⟨fb, fm, _⟩ := f
  obtain ⟨gb, gm, _⟩ := g
  obtain rfl : fb = gb := h₁
  obtain rfl : fm = gm := funext h₂
  rfl

instance : Category (FiberPi X) where
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp

/-- An arrow of `∏_E 𝒳_i` with given components over `f`. -/
def homMk {x y : FiberPi X} (f : x.base ⟶ y.base) (φ : ∀ i, x.obj i ⟶ y.obj i)
    [∀ i, IsHomLift (X i).p f (φ i)] : x ⟶ y :=
  { base := f, map := φ }

@[simp] theorem homMk_base {x y : FiberPi X} (f : x.base ⟶ y.base) (φ : ∀ i, x.obj i ⟶ y.obj i)
    [∀ i, IsHomLift (X i).p f (φ i)] : (homMk f φ).base = f := rfl

@[simp] theorem homMk_map {x y : FiberPi X} (f : x.base ⟶ y.base) (φ : ∀ i, x.obj i ⟶ y.obj i)
    [∀ i, IsHomLift (X i).p f (φ i)] (i : I) : (homMk f φ).map i = φ i := rfl

theorem ext' {x y : FiberPi X} (hb : x.base = y.base) (ho : ∀ i, x.obj i = y.obj i) : x = y := by
  obtain ⟨xb, xo, _⟩ := x
  obtain ⟨yb, yo, _⟩ := y
  obtain rfl : xb = yb := hb
  obtain rfl : xo = yo := funext ho
  rfl

@[simp] theorem eqToHom_base {x y : FiberPi X} (h : x = y) :
    Hom.base (eqToHom h) = eqToHom (congrArg FiberPi.base h) := by
  subst h
  rfl

@[simp] theorem eqToHom_map {x y : FiberPi X} (h : x = y) (i : I) :
    Hom.map (eqToHom h) i = eqToHom (congrArg (fun x ↦ x.obj i) h) := by
  subst h
  rfl

/-! ### Replacing one component -/

section Update

variable [DecidableEq I]

/-- Replace the `i`-th component of `x` by an object `a` over the same base. -/
def update (x : FiberPi X) (i : I) (a : (X i).obj) (ha : (X i).p.obj a = x.base) :
    FiberPi X where
  base := x.base
  obj := Function.update x.obj i a
  obj_proj j := by
    rcases eq_or_ne j i with rfl | h
    · rw [Function.update_self]
      exact ha
    · rw [Function.update_of_ne h]
      exact x.obj_proj j

variable (x : FiberPi X) (i : I) (a : (X i).obj) (ha : (X i).p.obj a = x.base)

theorem update_obj_self : (x.update i a ha).obj i = a :=
  show Function.update x.obj i a i = a from Function.update_self i a x.obj

theorem update_obj_of_ne {j : I} (h : j ≠ i) : (x.update i a ha).obj j = x.obj j :=
  show Function.update x.obj i a j = x.obj j from Function.update_of_ne h a x.obj

variable {y : FiberPi X} (g : x.base ⟶ y.base) (φ : a ⟶ y.obj i) (ψ : ∀ j, x.obj j ⟶ y.obj j)

/-- The components of `updateHom`. -/
def updateMap (j : I) : (x.update i a ha).obj j ⟶ y.obj j :=
  if h : j = i then
    @Eq.rec I i (fun k _ ↦ (x.update i a ha).obj k ⟶ y.obj k)
      (eqToHom (x.update_obj_self i a ha) ≫ φ) j h.symm
  else eqToHom (x.update_obj_of_ne i a ha h) ≫ ψ j

theorem updateMap_self :
    updateMap x i a ha φ ψ i = eqToHom (x.update_obj_self i a ha) ≫ φ := by
  rw [updateMap, dite_eq_left rfl]

theorem updateMap_of_ne {j : I} (h : j ≠ i) :
    updateMap x i a ha φ ψ j = eqToHom (x.update_obj_of_ne i a ha h) ≫ ψ j := by
  rw [updateMap, dite_eq_right h]

theorem isHomLift_updateMap [IsHomLift (X i).p g φ] [∀ j, IsHomLift (X j).p g (ψ j)] (j : I) :
    IsHomLift (X j).p g (updateMap x i a ha φ ψ j) := by
  rcases eq_or_ne j i with rfl | h
  · rw [updateMap_self]
    infer_instance
  · rw [updateMap_of_ne _ _ _ _ _ _ h]
    infer_instance

/-- An arrow out of `x.update i a`: `φ` on the `i`-th component and `ψ_j` on the others. -/
def updateHom [IsHomLift (X i).p g φ] [∀ j, IsHomLift (X j).p g (ψ j)] :
    x.update i a ha ⟶ y where
  base := g
  map := updateMap x i a ha φ ψ
  isHomLift := isHomLift_updateMap x i a ha g φ ψ

end Update

end FiberPi

variable (X : I → BasedCategory.{v₁, u₁} E)

/-- VI.3, VI.6.5: the fibered product `∏_E 𝒳_i`, a category over `E`. -/
abbrev fiberPi : BasedCategory.{max v v₁ w, max u u₁ w} E where
  obj := FiberPi X
  p :=
    { obj := FiberPi.base
      map := FiberPi.Hom.base }

namespace fiberPi

variable {X}

@[simp] theorem p_obj (x : FiberPi X) : (fiberPi X).p.obj x = x.base := rfl

@[simp] theorem p_map {x y : FiberPi X} (f : x ⟶ y) : (fiberPi X).p.map f = f.base := rfl

theorem isHomLift_base {x y : FiberPi X} (f : x ⟶ y) : IsHomLift (fiberPi X).p f.base f :=
  IsHomLift.map (fiberPi X).p f

/-- Two arrows over the same arrow of `E` have the same base. -/
theorem base_eq_of_isHomLift {R S : E} (f : R ⟶ S) {x y : FiberPi X} (α β : x ⟶ y)
    [IsHomLift (fiberPi X).p f α] [IsHomLift (fiberPi X).p f β] : α.base = β.base :=
  (IsHomLift.fac' (fiberPi X).p f α).trans (IsHomLift.fac' (fiberPi X).p f β).symm

@[simp] theorem eqToHom_base {x y : (fiberPi X).obj} (h : x = y) :
    FiberPi.Hom.base (eqToHom h) = eqToHom (congrArg FiberPi.base h) := by
  subst h
  rfl

@[simp] theorem eqToHom_map {x y : (fiberPi X).obj} (h : x = y) (i : I) :
    FiberPi.Hom.map (eqToHom h) i = eqToHom (congrArg (fun x ↦ FiberPi.obj x i) h) := by
  subst h
  rfl

/-- The components of an arrow over `f` lie over `f`. -/
instance isHomLift_map {R S : E} (f : R ⟶ S) {x y : FiberPi X} (α : x ⟶ y)
    [h : IsHomLift (fiberPi X).p f α] (i : I) : IsHomLift (X i).p f (α.map i) := by
  subst_hom_lift (fiberPi X).p f α
  exact α.isHomLift i

/-- The base of an arrow over `f : x.base ⟶ y.base` is `f`. -/
theorem base_eq {x y : FiberPi X} (f : x.base ⟶ y.base) (α : x ⟶ y)
    [h : IsHomLift (fiberPi X).p f α] : α.base = f :=
  (@IsHomLift.eq_of_isHomLift _ _ _ _ (fiberPi X).p x y f α h).symm

variable (X) in
/-- VI.3: the projection `pr_i : ∏_E 𝒳_i ⥤ 𝒳_i`, an `E`-functor. -/
def proj (i : I) : BasedFunctor (fiberPi X) (X i) where
  toFunctor :=
    { obj := fun x ↦ x.obj i
      map := fun f ↦ f.map i }
  w := functor_comp_eq_of_isHomLift _ _ _ (fun x ↦ x.obj_proj i) fun f ↦ f.isHomLift i

@[simp] theorem proj_obj (i : I) (x : FiberPi X) : (proj X i).obj x = x.obj i := rfl

@[simp] theorem proj_map (i : I) {x y : FiberPi X} (f : x ⟶ y) : (proj X i).map f = f.map i :=
  rfl

/-! ### VI.3: the universal property -/

variable {Z : BasedCategory.{v₂, u₂} E}

/-- VI.3: the `E`-functor into `∏_E 𝒳_i` with prescribed components. -/
def lift (F : ∀ i, BasedFunctor Z (X i)) : BasedFunctor Z (fiberPi X) where
  toFunctor :=
    { obj := fun z ↦ ⟨Z.p.obj z, fun i ↦ (F i).obj z, fun i ↦ (F i).w_obj z⟩
      map := fun {z z'} φ ↦ FiberPi.homMk (Z.p.map φ) (fun i ↦ (F i).map φ) }
  w := rfl

@[simp] theorem lift_proj (F : ∀ i, BasedFunctor Z (X i)) (i : I) :
    BasedFunctor.comp (lift F) (proj X i) = F i := rfl

variable (X Z) in
/-- VI.3: the functor `h ↦ (pr_i ∘ h)_i` on categories of `E`-functors. -/
def pairing : BasedFunctor Z (fiberPi X) ⥤ ∀ i, BasedFunctor Z (X i) :=
  Functor.pi' fun i ↦ basedPostcomp (proj X i)

/-- VI.3: a family of `E`-homomorphisms between the components gives an `E`-homomorphism of
functors into the product. -/
def liftNatTrans {H K : BasedFunctor Z (fiberPi X)}
    (α : ∀ i, BasedFunctor.comp H (proj X i) ⟶ BasedFunctor.comp K (proj X i)) : H ⟶ K where
  app z :=
    { base := eqToHom ((H.w_obj z).trans (K.w_obj z).symm)
      map := fun i ↦ (α i).app z
      isHomLift := fun i ↦ by
        have := (α i).isHomLift' z
        exact isHomLift_eqToHom_of_isHomLift_id (p := (X i).p) (R := Z.p.obj z) ((α i).app z)
          ((H.w_obj z).trans (K.w_obj z).symm) ((H.obj z).obj_proj i) ((K.obj z).obj_proj i) }
  naturality {z z'} φ := by
    have h₁ : IsHomLift (fiberPi X).p (Z.p.map φ) (H.map φ) := H.preserves_isHomLift _ φ
    have h₂ : IsHomLift (fiberPi X).p (Z.p.map φ) (K.map φ) := K.preserves_isHomLift _ φ
    refine FiberPi.hom_ext ?_ fun i ↦ (α i).naturality φ
    have e₁ := IsHomLift.fac' (fiberPi X).p (Z.p.map φ) (H.map φ)
    have e₂ := IsHomLift.fac' (fiberPi X).p (Z.p.map φ) (K.map φ)
    rw [p_map] at e₁ e₂
    simp [e₁, e₂]
  isHomLift' z := IsHomLift.of_fac' _ _ _ (H.w_obj z) (K.w_obj z) (by rw [p_map]; simp)

@[simp] theorem pairing_obj_apply (H : BasedFunctor Z (fiberPi X)) (i : I) :
    (pairing X Z).obj H i = BasedFunctor.comp H (proj X i) := rfl

theorem lift_pairing (H : BasedFunctor Z (fiberPi X)) :
    lift (fun i ↦ BasedFunctor.comp H (proj X i)) = H := by
  apply basedFunctor_ext
  refine Functor.ext (fun z ↦ FiberPi.ext' (H.w_obj z).symm fun i ↦ rfl) fun z z' φ ↦ ?_
  have : IsHomLift (fiberPi X).p (Z.p.map φ) (H.map φ) := H.preserves_isHomLift _ φ
  have : IsHomLift (fiberPi X).p (Z.p.map φ)
      ((lift fun i ↦ BasedFunctor.comp H (proj X i)).map φ) :=
    (lift fun i ↦ BasedFunctor.comp H (proj X i)).preserves_isHomLift _ φ
  refine FiberPi.hom_ext (base_eq_of_isHomLift (Z.p.map φ) _ _) fun i ↦ ?_
  rw [FiberPi.comp_map, FiberPi.comp_map, eqToHom_map, eqToHom_map]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

instance : (pairing X Z).Faithful where
  map_injective {H K} {α β} h := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext z
    refine FiberPi.hom_ext ?_ fun i ↦ congrArg (fun γ ↦ (γ i).app z) h
    have hα : IsHomLift (fiberPi X).p (𝟙 (Z.p.obj z)) (α.app z) := α.isHomLift' z
    have hβ : IsHomLift (fiberPi X).p (𝟙 (Z.p.obj z)) (β.app z) := β.isHomLift' z
    have e₁ := IsHomLift.fac' (fiberPi X).p (𝟙 (Z.p.obj z)) (α.app z)
    have e₂ := IsHomLift.fac' (fiberPi X).p (𝟙 (Z.p.obj z)) (β.app z)
    rw [p_map] at e₁ e₂
    rw [e₁, e₂]

instance : (pairing X Z).Full where
  map_surjective {H K} γ := ⟨liftNatTrans γ, by funext i; rfl⟩

instance : (pairing X Z).IsIso where
  bijective_obj := by
    constructor
    · intro H K h
      rw [← lift_pairing H, ← lift_pairing K]
      exact congrArg lift h
    · intro F
      exact ⟨lift F, rfl⟩

variable (X Z) in
/-- VI.3 (for a family): `Hom_E(𝒵, ∏_E 𝒳_i) ≅ ∏ Hom_E(𝒵, 𝒳_i)`, an isomorphism of categories of
`E`-functors. -/
noncomputable def pairingIso : IsoCat (BasedFunctor Z (fiberPi X)) (∀ i, BasedFunctor Z (X i)) :=
  (pairing X Z).asIsomorphism

/-! ### VI.6.3: cartesian arrows of a product -/

/-- VI.6.3 (for a family), sufficiency: an arrow whose components are cartesian is cartesian. -/
theorem isCartesian_of_forall {R S : E} (f : R ⟶ S) {x y : FiberPi X} (α : x ⟶ y)
    [IsHomLift (fiberPi X).p f α] (h : ∀ i, IsCartesian (X i).p f (α.map i)) :
    IsCartesian (fiberPi X).p f α := by
  subst_hom_lift (fiberPi X).p f α
  refine ⟨fun {z} ψ hψ ↦ ?_⟩
  have hz : z.base = x.base := IsHomLift.domain_eq (fiberPi X).p ((fiberPi X).p.map α) ψ
  have hψb : ψ.base = eqToHom hz ≫ α.base :=
    (IsHomLift.fac' (fiberPi X).p ((fiberPi X).p.map α) ψ).trans
      (by simp only [eqToHom_refl, Category.comp_id])
  have : ∀ i, IsHomLift (X i).p α.base (ψ.map i) := fun i ↦
    isHomLift_map ((fiberPi X).p.map α) ψ i (h := hψ)
  let χ : z ⟶ x :=
    { base := eqToHom hz
      map := fun i ↦ IsCartesian.map (X i).p α.base (α.map i) (ψ.map i)
      isHomLift := fun i ↦ isHomLift_eqToHom_of_isHomLift_id (R := x.base) _ hz
        (z.obj_proj i) (x.obj_proj i) }
  have hχ : IsHomLift (fiberPi X).p (𝟙 x.base) χ :=
    IsHomLift.of_fac' _ _ _ hz rfl (by rw [p_map]; simp [χ])
  refine ⟨χ, ⟨hχ, FiberPi.hom_ext (by simp [χ, hψb]) fun i ↦
    IsCartesian.fac (X i).p α.base (α.map i) (ψ.map i)⟩, ?_⟩
  rintro χ' ⟨hχ', rfl⟩
  have e := IsHomLift.fac' (fiberPi X).p (𝟙 x.base) χ'
  rw [p_map] at e
  refine FiberPi.hom_ext (by simp [χ, e]) fun i ↦ ?_
  exact IsCartesian.map_uniq (X i).p α.base (α.map i) _ _ rfl

/-- VI.6.3 (for a family), necessity: the components of a cartesian arrow are cartesian. -/
theorem isCartesian_map_of_isCartesian {R S : E} (f : R ⟶ S) {x y : FiberPi X}
    (α : x ⟶ y) [IsCartesian (fiberPi X).p f α] (i : I) : IsCartesian (X i).p f (α.map i) := by
  classical
  subst_hom_lift (fiberPi X).p f α
  change IsCartesian (X i).p α.base (α.map i)
  refine ⟨fun {a} φ hφ ↦ ?_⟩
  have ha : (X i).p.obj a = x.base := IsHomLift.domain_eq (X i).p α.base φ
  let ψ := FiberPi.updateHom x i a ha α.base φ α.map
  have : IsHomLift (fiberPi X).p ((fiberPi X).p.map α) ψ := IsHomLift.map (fiberPi X).p ψ
  let χ := IsCartesian.map (fiberPi X).p ((fiberPi X).p.map α) α ψ
  have hχ : χ ≫ α = ψ := IsCartesian.fac _ _ _ _
  refine ⟨eqToHom (x.update_obj_self i a ha).symm ≫ χ.map i, ⟨inferInstance, ?_⟩, ?_⟩
  · have := congrArg (fun γ ↦ FiberPi.Hom.map γ i) hχ
    simp only [FiberPi.comp_map] at this
    simp [this, ψ, FiberPi.updateHom, FiberPi.updateMap_self]
  · rintro χ' ⟨hχ', hfac⟩
    have : ∀ j, IsHomLift (X j).p (𝟙 x.base) (𝟙 (x.obj j)) := fun j ↦ IsHomLift.id (x.obj_proj j)
    let ω := FiberPi.updateHom x i a ha (𝟙 x.base) χ' (fun j ↦ 𝟙 (x.obj j))
    have hω : IsHomLift (fiberPi X).p (𝟙 x.base) ω := isHomLift_base ω
    have : ω = χ := IsCartesian.map_uniq _ _ α ψ ω (by
      refine FiberPi.hom_ext (Category.id_comp _) fun j ↦ ?_
      rcases eq_or_ne j i with rfl | h
      · simp [ω, ψ, FiberPi.updateHom, FiberPi.updateMap_self, hfac]
      · simp [ω, ψ, FiberPi.updateHom, FiberPi.updateMap_of_ne _ _ _ _ _ _ h])
    have hi := congrArg (fun γ ↦ FiberPi.Hom.map γ i) this
    simp only [ω, FiberPi.updateHom, FiberPi.updateMap_self] at hi
    rw [← hi]
    simp

/-- VI.6.3 (for a family): an arrow of `∏_E 𝒳_i` is cartesian iff all its components are. -/
theorem isCartesian_iff {R S : E} (f : R ⟶ S) {x y : FiberPi X} (α : x ⟶ y)
    [IsHomLift (fiberPi X).p f α] :
    IsCartesian (fiberPi X).p f α ↔ ∀ i, IsCartesian (X i).p f (α.map i) :=
  ⟨fun _ i ↦ isCartesian_map_of_isCartesian f α i, isCartesian_of_forall f α⟩

/-- A variant of VI.6.3 (for a family): an arrow whose components are strongly cartesian is
strongly cartesian. -/
theorem isStronglyCartesian_of_forall {R S : E} (f : R ⟶ S) {x y : FiberPi X} (α : x ⟶ y)
    [IsHomLift (fiberPi X).p f α] (h : ∀ i, IsStronglyCartesian (X i).p f (α.map i)) :
    IsStronglyCartesian (fiberPi X).p f α := by
  subst_hom_lift (fiberPi X).p f α
  refine ⟨fun {z} g ψ hψ ↦ ?_⟩
  have hψb : ψ.base = g ≫ α.base :=
    (@IsHomLift.eq_of_isHomLift _ _ _ _ (fiberPi X).p z y _ ψ hψ).symm
  have : ∀ i, IsHomLift (X i).p (g ≫ α.base) (ψ.map i) := fun i ↦
    isHomLift_map (g ≫ (fiberPi X).p.map α) ψ i (h := hψ)
  let χ : z ⟶ x :=
    { base := g
      map := fun i ↦ IsStronglyCartesian.map (X i).p α.base (α.map i) (g := g) rfl (ψ.map i) }
  refine ⟨χ, ⟨isHomLift_base χ, FiberPi.hom_ext hψb.symm fun i ↦
    IsStronglyCartesian.fac (X i).p α.base (α.map i) rfl (ψ.map i)⟩, ?_⟩
  rintro χ' ⟨hχ', rfl⟩
  have hb : χ'.base = g := (@IsHomLift.eq_of_isHomLift _ _ _ _ (fiberPi X).p z x g χ' hχ').symm
  refine FiberPi.hom_ext hb fun i ↦ ?_
  have : IsHomLift (X i).p g (χ'.map i) := isHomLift_map g χ' i (h := hχ')
  exact IsStronglyCartesian.map_uniq (X i).p α.base (α.map i) rfl _ _ rfl

/-! ### VI.6.4: cartesian functors into a product -/

/-- VI.6.4 (for a family): an `E`-functor into `∏_E 𝒳_i` is cartesian iff all its components
are. -/
theorem isCartesianFunctor_iff (F : BasedFunctor Z (fiberPi X)) :
    IsCartesianFunctor F ↔ ∀ i, IsCartesianFunctor (BasedFunctor.comp F (proj X i)) := by
  constructor
  · intro hF i
    refine ⟨fun f φ _ ↦ ?_⟩
    have := hF.map_isCartesian f φ
    exact isCartesian_map_of_isCartesian f (F.map φ) i
  · intro h
    refine ⟨fun f φ hφ ↦ ?_⟩
    have : IsHomLift Z.p f φ := hφ.toIsHomLift
    have : IsHomLift (fiberPi X).p f (F.map φ) := F.preserves_isHomLift f φ
    exact isCartesian_of_forall f (F.map φ) fun i ↦ (h i).map_isCartesian f φ

variable (X Z) in
/-- VI.6.4 (for a family): the pairing functor restricted to cartesian functors. -/
def cartesianPairing : CartesianFunctors Z (fiberPi X) ⥤ ∀ i, CartesianFunctors Z (X i) :=
  Functor.pi' fun i ↦ cartesianFunctorProperty.lift
    (cartesianFunctorProperty.ι ⋙ basedPostcomp (proj X i))
    (fun F ↦ (isCartesianFunctor_iff F.obj).mp F.property i)

instance : (cartesianPairing X Z).Faithful where
  map_injective {H K} {α β} h := by
    apply ObjectProperty.hom_ext
    apply (pairing X Z).map_injective
    funext i
    exact congrArg (fun γ ↦ (γ i).hom) h

instance : (cartesianPairing X Z).Full where
  map_surjective γ := ⟨ObjectProperty.homMk (liftNatTrans fun i ↦ (γ i).hom), rfl⟩

instance : (cartesianPairing X Z).IsIso where
  bijective_obj := by
    constructor
    · intro H K h
      have h' : (pairing X Z).obj H.obj = (pairing X Z).obj K.obj := by
        funext i
        exact congrArg (fun γ ↦ (γ i).obj) h
      exact ObjectProperty.FullSubcategory.ext
        (((pairing X Z).bijective_obj).1 h')
    · intro F
      exact ⟨⟨lift fun i ↦ (F i).obj, (isCartesianFunctor_iff _).mpr fun i ↦ (F i).property⟩, rfl⟩

variable (X Z) in
/-- VI.6.4 (for a family): `Cart_E(𝒵, ∏_E 𝒳_i) ≅ ∏ Cart_E(𝒵, 𝒳_i)`, an isomorphism of
categories. -/
noncomputable def cartesianPairingIso :
    IsoCat (CartesianFunctors Z (fiberPi X)) (∀ i, CartesianFunctors Z (X i)) :=
  (cartesianPairing X Z).asIsomorphism

variable (X) in
/-- VI.6.4 (for a family) with `𝒵 = E`: `lim(∏_E 𝒳_i / E) ≅ ∏ lim(𝒳_i / E)`. -/
noncomputable def cartesianLimitIso :
    IsoCat (cartesianLimit (fiberPi X)) (∀ i, cartesianLimit (X i)) :=
  cartesianPairingIso X (BasedCategory.ofFunctor (𝟭 E))

/-! ### VI.6.5: products of (pre)fibered categories -/

/-- VI.6.5 (for a family): a product of prefibered categories is prefibered. -/
instance isPreFibered [∀ i, IsPreFibered (X i).p] : IsPreFibered (fiberPi X).p where
  exists_isCartesian' {x R} f := by
    choose b φ hφ using fun i ↦ IsPreFibered.exists_isCartesian (X i).p (x.obj_proj i) f
    have : ∀ i, IsHomLift (X i).p f (φ i) := fun i ↦ (hφ i).toIsHomLift
    let y : FiberPi X := ⟨R, b, fun i ↦ IsHomLift.domain_eq (X i).p f (φ i)⟩
    let α : y ⟶ x := FiberPi.homMk f φ
    have : IsHomLift (fiberPi X).p f α := isHomLift_base α
    exact ⟨y, α, isCartesian_of_forall f α hφ⟩

/-- VI.6.5 (for a family): a product of fibered categories is fibered. -/
instance isFibered [∀ i, IsFibered (X i).p] : IsFibered (fiberPi X).p :=
  IsFibered.of_exists_isStronglyCartesian fun x R f ↦ by
    choose b φ hφ using fun i ↦ IsPreFibered.exists_isCartesian (X i).p (x.obj_proj i) f
    have : ∀ i, IsHomLift (X i).p f (φ i) := fun i ↦ (hφ i).toIsHomLift
    let y : FiberPi X := ⟨R, b, fun i ↦ IsHomLift.domain_eq (X i).p f (φ i)⟩
    let α : y ⟶ x := FiberPi.homMk f φ
    have : IsHomLift (fiberPi X).p f α := isHomLift_base α
    exact ⟨y, α, isStronglyCartesian_of_forall f α fun i ↦ by
      have := hφ i
      exact inferInstanceAs (IsStronglyCartesian (X i).p f (φ i))⟩

end fiberPi

/-! ### VI.7.1: cleavage of a product -/

namespace Cleavage

variable {X}

/-- The `i`-th component of an object of a fiber of `∏_E 𝒳_i`. -/
abbrev fiberComponent {S : E} (ξ : Fiber (fiberPi X).p S) (i : I) : Fiber (X i).p S :=
  ⟨ξ.val.obj i, (ξ.val.obj_proj i).trans ξ.property⟩

/-- VI.7.1: cleavages `K_i` of the `𝒳_i` give a cleavage of `∏_E 𝒳_i`, with
`f^*(x_i) = (f^* x_i)` and transports `(α_f(x_i))`. -/
noncomputable def pi (K : ∀ i, Cleavage (X i).p) : Cleavage (fiberPi X).p :=
  ofLifts
    (fun {R _} f ξ ↦ ⟨⟨R, fun i ↦ ((K i).pullback f |>.obj (fiberComponent ξ i)).val,
      fun i ↦ ((K i).pullback f |>.obj (fiberComponent ξ i)).property⟩, rfl⟩)
    (fun f ξ ↦ FiberPi.homMk (f ≫ eqToHom ξ.property.symm)
      fun i ↦ (K i).transport f (fiberComponent ξ i))
    (fun {R S} f ξ ↦ by
      let α : (⟨R, fun i ↦ ((K i).pullback f |>.obj (fiberComponent ξ i)).val,
          fun i ↦ ((K i).pullback f |>.obj (fiberComponent ξ i)).property⟩ : FiberPi X) ⟶ ξ.val :=
        FiberPi.homMk (f ≫ eqToHom ξ.property.symm) fun i ↦ (K i).transport f (fiberComponent ξ i)
      have : IsHomLift (fiberPi X).p f α :=
        IsHomLift.of_fac' _ _ _ rfl ξ.property (by simp [α])
      exact fiberPi.isCartesian_of_forall f α fun i ↦
        (K i).transport_isCartesian f (fiberComponent ξ i))

@[simp] theorem pi_transport_map (K : ∀ i, Cleavage (X i).p) {R S : E} (f : R ⟶ S)
    (ξ : Fiber (fiberPi X).p S) (i : I) :
    ((pi K).transport f ξ).map i = (K i).transport f (fiberComponent ξ i) := rfl

@[simp] theorem pi_transport_base (K : ∀ i, Cleavage (X i).p) {R S : E} (f : R ⟶ S)
    (ξ : Fiber (fiberPi X).p S) :
    ((pi K).transport f ξ).base = f ≫ eqToHom ξ.property.symm := rfl

end Cleavage

end SGA.SGA1.ExposeVI
