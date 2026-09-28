/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.OverCategories
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Category.Cat.Limit
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.IsoCat

/-!
# SGA 1, Exposé VI, §3: change of base

`BaseChange p L` is the strict fiber product: objects have equal images in
the base and morphisms have equal images after transporting their endpoints.
This is the fiber product used in SGA, not an iso-comma category.

We construct its projections, universal lifting functor, and change of
base on based functors and transformations. The ordinary slice-category
adjunction and preservation of limits are supplied using `Over.pullback`.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} {C : Type u₁} {D : Type u₂}
  [Category.{v} E] [Category.{v₁} C] [Category.{v₂} D]

/-- VI.3: the objects of the strict fiber product `C ×_E D`. -/
def BaseChange (p : C ⥤ E) (L : D ⥤ E) := {x : C × D // p.obj x.1 = L.obj x.2}

namespace BaseChange

variable {p : C ⥤ E} {L : D ⥤ E}

/-- VI.3: morphisms are pairs with the same image in the base. -/
@[ext] structure Hom (x y : BaseChange p L) where
  left : x.val.1 ⟶ y.val.1
  right : x.val.2 ⟶ y.val.2
  over : IsHomLift p (L.map right) left

instance : Category (BaseChange p L) where
  Hom := Hom
  id x := ⟨𝟙 x.val.1, 𝟙 x.val.2, by
    rw [L.map_id]
    exact IsHomLift.id x.property⟩
  comp f g := ⟨f.left ≫ g.left, f.right ≫ g.right, by
    have := f.over
    have := g.over
    rw [L.map_comp]
    infer_instance⟩
  id_comp f := by ext <;> simp
  comp_id f := by ext <;> simp
  assoc f g h := by ext <;> simp [Category.assoc]

/-- VI.3: the first projection of the strict fiber product. -/
def fst (p : C ⥤ E) (L : D ⥤ E) : BaseChange p L ⥤ C where
  obj x := x.val.1
  map f := f.left

/-- VI.3: the second projection, used as the new structure functor. -/
def snd (p : C ⥤ E) (L : D ⥤ E) : BaseChange p L ⥤ D where
  obj x := x.val.2
  map f := f.right

/-- The two projections commute with the structure functors. -/
def projectionIso (p : C ⥤ E) (L : D ⥤ E) : fst p L ⋙ p ≅ snd p L ⋙ L :=
  NatIso.ofComponents (fun x ↦ eqToIso x.property) (fun {x y} f ↦ by
    have := f.over
    exact (IsHomLift.commSq p (L.map f.right) f.left).w)

/-- VI.3: commutation here is equality of functors, not just an isomorphism. -/
theorem condition (p : C ⥤ E) (L : D ⥤ E) : fst p L ⋙ p = snd p L ⋙ L :=
  Functor.ext_of_iso (projectionIso p L) (fun x ↦ x.property)

variable {A : Type u₃} [Category.{v₃} A]

/-- VI.3: the functor to the fiber product induced by a commuting pair. -/
def lift (F : A ⥤ C) (G : A ⥤ D) (h : F ⋙ p = G ⋙ L) : A ⥤ BaseChange p L where
  obj a := ⟨(F.obj a, G.obj a), Functor.congr_obj h a⟩
  map {a b} f := ⟨F.map f, G.map f,
    IsHomLift.of_commsq p _ _ (Functor.congr_obj h a) (Functor.congr_obj h b)
      (by simpa using (eqToIso h).hom.naturality f)⟩

@[simp] theorem lift_fst (F : A ⥤ C) (G : A ⥤ D) (h : F ⋙ p = G ⋙ L) :
    lift F G h ⋙ fst p L = F := rfl

@[simp] theorem lift_snd (F : A ⥤ C) (G : A ⥤ D) (h : F ⋙ p = G ⋙ L) :
    lift F G h ⋙ snd p L = G := rfl

/-- VI.3: a functor to the fiber product is recovered from its projections. -/
theorem lift_projections (H : A ⥤ BaseChange p L) :
    lift (H ⋙ fst p L) (H ⋙ snd p L)
      (by rw [Functor.assoc, condition, ← Functor.assoc]) = H := rfl

/-- VI.3: the universal bijection on functors into a fiber product. -/
def functorEquiv (p : C ⥤ E) (L : D ⥤ E) :
    (A ⥤ BaseChange p L) ≃ {FG : (A ⥤ C) × (A ⥤ D) // FG.1 ⋙ p = FG.2 ⋙ L} where
  toFun H := ⟨(H ⋙ fst p L, H ⋙ snd p L), by
    rw [Functor.assoc, condition, ← Functor.assoc]⟩
  invFun FG := lift FG.val.1 FG.val.2 FG.property
  left_inv := lift_projections
  right_inv FG := by cases FG; rfl

/-- VI.3: natural transformations to the fiber product are precisely compatible
pairs of natural transformations. This is the morphism part of the universal property. -/
def natTransEquiv (H K : A ⥤ BaseChange p L) :
    (H ⟶ K) ≃ {αβ : (H ⋙ fst p L ⟶ K ⋙ fst p L) × (H ⋙ snd p L ⟶ K ⋙ snd p L) //
      ∀ a, IsHomLift p (L.map (αβ.2.app a)) (αβ.1.app a)} where
  toFun τ := ⟨(whiskerRight τ (fst p L), whiskerRight τ (snd p L)),
    fun a ↦ (τ.app a).over⟩
  invFun αβ :=
    { app := fun a ↦ ⟨αβ.val.1.app a, αβ.val.2.app a, αβ.property a⟩
      naturality := fun {_ _} f ↦ Hom.ext (αβ.val.1.naturality f) (αβ.val.2.naturality f) }
  left_inv τ := by
    apply NatTrans.ext
    funext a
    rfl
  right_inv αβ := by rcases αβ with ⟨⟨α, β⟩, h⟩; rfl

end BaseChange

/-- VI.3: a based category after change of base along `L`: `𝒳 ×_E D` over `D` via `pr₂`. -/
abbrev changeOfBase (X : BasedCategory.{v₁, u₁} E) (L : D ⥤ E) :
    BasedCategory.{max v₁ v₂, max u₁ u₂} D where
  obj := BaseChange X.p L
  p := BaseChange.snd X.p L

/-- VI.3: restriction of the base along `L`: a category over `D` regarded over `E`. -/
abbrev restrictBase (Z : BasedCategory.{v₃, u₃} D) (L : D ⥤ E) : BasedCategory.{v₃, u₃} E where
  obj := Z.obj
  p := Z.p ⋙ L

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₃, u₃} E}

/-- VI.3: change of base of an `E`-functor. -/
def changeOfBaseMap (F : BasedFunctor X Y) (L : D ⥤ E) :
    BasedFunctor (changeOfBase X L) (changeOfBase Y L) where
  obj x := ⟨(F.obj x.val.1, x.val.2), (F.w_obj x.val.1).trans x.property⟩
  map f := ⟨F.map f.left, f.right, by
    have := f.over
    exact BasedFunctor.preserves_isHomLift F _ _⟩
  map_id x := by
    apply BaseChange.Hom.ext
    · exact F.map_id x.val.1
    · rfl
  map_comp f g := by
    apply BaseChange.Hom.ext
    · exact F.map_comp f.left g.left
    · rfl

/-- VI.3: base change sends a component `α(x)` to `(α(x), id)`. -/
def changeOfBaseNatTrans {F G : BasedFunctor X Y} (α : F ⟶ G) (L : D ⥤ E) :
    changeOfBaseMap F L ⟶ changeOfBaseMap G L where
  app x := ⟨α.app x.val.1, 𝟙 x.val.2, by
    change IsHomLift Y.p (L.map (𝟙 x.val.2)) (α.app x.val.1)
    rw [L.map_id]
    exact α.isHomLift x.property⟩
  naturality {x y} f := by
    apply BaseChange.Hom.ext
    · exact α.naturality f.left
    · change f.right ≫ 𝟙 _ = 𝟙 _ ≫ f.right
      simp
  isHomLift' x := by
    change IsHomLift (BaseChange.snd Y.p L) (𝟙 x.val.2) _
    apply IsHomLift.of_fac' _ _ _ rfl rfl
    change 𝟙 x.val.2 = 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _
    simp

/-- VI.3: change of base is a functor between categories of based functors. -/
def changeOfBaseHom (L : D ⥤ E) :
    BasedFunctor X Y ⥤ BasedFunctor (changeOfBase X L) (changeOfBase Y L) where
  obj F := changeOfBaseMap F L
  map α := changeOfBaseNatTrans α L
  map_id F := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    rfl
  map_comp α β := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext x
    apply BaseChange.Hom.ext
    · rfl
    · change 𝟙 x.val.2 = 𝟙 x.val.2 ≫ 𝟙 x.val.2
      simp

section Compatibility

variable {W : BasedCategory.{v₂, u₂} E} (L : D ⥤ E)

/-- VI.3: `(gf)' = g'f'`: change of base is compatible with composition of `E`-functors. -/
theorem changeOfBaseMap_comp (F : BasedFunctor X Y) (G : BasedFunctor Y W) :
    changeOfBaseMap (BasedFunctor.comp F G) L =
      BasedFunctor.comp (changeOfBaseMap F L) (changeOfBaseMap G L) := rfl

/-- VI.3: `(v * u)' = v' * u'`: change of base is compatible with horizontal composition of
`E`-homomorphisms. -/
theorem changeOfBaseNatTrans_horizontalComp {F F' : BasedFunctor X Y} {G G' : BasedFunctor Y W}
    (α : F ⟶ F') (β : G ⟶ G') :
    changeOfBaseNatTrans (horizontalComp α β) L =
      horizontalComp (changeOfBaseNatTrans α L) (changeOfBaseNatTrans β L) := by
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext x
  apply BaseChange.Hom.ext
  · rfl
  · change 𝟙 x.val.2 = 𝟙 x.val.2 ≫ 𝟙 x.val.2
    simp

end Compatibility

namespace BaseChange

variable {p : C ⥤ E} {L : D ⥤ E}

/-- An arrow of `C ×_E D` over `g` in `D` has first component over `L g`. -/
theorem isHomLift_left {R S : D} (g : R ⟶ S) {x y : BaseChange p L} (α : x ⟶ y)
    [IsHomLift (snd p L) g α] : IsHomLift p (L.map g) α.left := by
  subst_hom_lift (snd p L) g α
  exact α.over

/-- Two arrows of `C ×_E D` over the same arrow of `D` have the same second component. -/
theorem right_eq_of_isHomLift {R S : D} (g : R ⟶ S) {x y : BaseChange p L} (α β : x ⟶ y)
    [IsHomLift (snd p L) g α] [IsHomLift (snd p L) g β] : α.right = β.right := by
  have hα := IsHomLift.fac' (snd p L) g α
  have hβ := IsHomLift.fac' (snd p L) g β
  exact hα.trans hβ.symm

/-- Arrows of `C ×_E D` over the same arrow of `D` are equal iff their first components are. -/
theorem hom_ext_of_isHomLift {R S : D} (g : R ⟶ S) {x y : BaseChange p L} {α β : x ⟶ y}
    [IsHomLift (snd p L) g α] [IsHomLift (snd p L) g β] (h : α.left = β.left) : α = β :=
  Hom.ext h (right_eq_of_isHomLift g α β)

end BaseChange

section Adjunction

variable {Z : BasedCategory.{v₃, u₃} D} {Y : BasedCategory.{v₁, u₁} E} {L : D ⥤ E}

/-- VI.3: composition with `pr₁ : 𝒴 ×_E D ⥤ 𝒴`, from `D`-functors `𝒵 ⥤ 𝒴 ×_E D` to
`E`-functors `𝒵 ⥤ 𝒴` (with `𝒵` regarded over `E` through `L`). -/
def changeOfBaseTranspose (Z : BasedCategory.{v₃, u₃} D) (Y : BasedCategory.{v₁, u₁} E)
    (L : D ⥤ E) : BasedFunctor Z (changeOfBase Y L) ⥤ BasedFunctor (restrictBase Z L) Y where
  obj F :=
    { toFunctor := F.toFunctor ⋙ BaseChange.fst Y.p L
      w := by
        change F.toFunctor ⋙ (BaseChange.fst Y.p L ⋙ Y.p) = Z.p ⋙ L
        rw [BaseChange.condition, ← Functor.assoc]
        exact congrArg (· ⋙ L) F.w }
  map {F G} α :=
    { toNatTrans := Functor.whiskerRight α.toNatTrans (BaseChange.fst Y.p L)
      isHomLift' := fun z ↦ by
        have := α.isHomLift' z
        have h := BaseChange.isHomLift_left (𝟙 (Z.p.obj z)) (α.app z)
        rw [L.map_id] at h
        exact h }

/-- The second component of a `D`-functor into `𝒴 ×_E D` is the structure functor. -/
private theorem snd_obj_eq (F : BasedFunctor Z (changeOfBase Y L)) (z : Z.obj) :
    (F.obj z).val.2 = Z.p.obj z :=
  F.w_obj z

/-- The morphism of `𝒴 ×_E D` with prescribed first component over an identity. -/
private def verticalHomMk {F G : BasedFunctor Z (changeOfBase Y L)} (z : Z.obj)
    (φ : (F.obj z).val.1 ⟶ (G.obj z).val.1) [hφ : IsHomLift Y.p (𝟙 (L.obj (Z.p.obj z))) φ] :
    F.obj z ⟶ G.obj z where
  left := φ
  right := eqToHom ((snd_obj_eq F z).trans (snd_obj_eq G z).symm)
  over := by
    rw [eqToHom_map]
    have h : IsHomLift Y.p (eqToHom (congrArg L.obj (snd_obj_eq F z)) ≫
        𝟙 (L.obj (Z.p.obj z)) ≫ eqToHom (congrArg L.obj (snd_obj_eq G z)).symm) φ :=
      inferInstance
    simpa using h

private theorem verticalHomMk_isHomLift {F G : BasedFunctor Z (changeOfBase Y L)} (z : Z.obj)
    (φ : (F.obj z).val.1 ⟶ (G.obj z).val.1) [hφ : IsHomLift Y.p (𝟙 (L.obj (Z.p.obj z))) φ] :
    IsHomLift (BaseChange.snd Y.p L) (𝟙 (Z.p.obj z)) (verticalHomMk z φ) := by
  apply IsHomLift.of_fac' (BaseChange.snd Y.p L) (𝟙 (Z.p.obj z)) (verticalHomMk z φ)
    (snd_obj_eq F z) (snd_obj_eq G z)
  change eqToHom ((snd_obj_eq F z).trans (snd_obj_eq G z).symm) = _
  rw [Category.id_comp]
  exact (eqToHom_trans _ _).symm

instance : (changeOfBaseTranspose Z Y L).Faithful where
  map_injective {F G} {α β} h := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext z
    have := α.isHomLift' z
    have := β.isHomLift' z
    exact BaseChange.hom_ext_of_isHomLift (𝟙 (Z.p.obj z))
      (congrArg (fun γ ↦ γ.toNatTrans.app z) h)

/-- The inverse of `changeOfBaseTranspose` on morphisms. -/
private def transposeInvHom {F G : BasedFunctor Z (changeOfBase Y L)}
    (β : (changeOfBaseTranspose Z Y L).obj F ⟶ (changeOfBaseTranspose Z Y L).obj G) :
    F ⟶ G where
  app z := verticalHomMk z (β.app z) (hφ := β.isHomLift' z)
  naturality {z z'} f := by
    have : IsHomLift (BaseChange.snd Y.p L) (Z.p.map f) (F.map f) :=
      F.preserves_isHomLift (Z.p.map f) f
    have : IsHomLift (BaseChange.snd Y.p L) (Z.p.map f) (G.map f) :=
      G.preserves_isHomLift (Z.p.map f) f
    have := verticalHomMk_isHomLift z (β.app z) (hφ := β.isHomLift' z)
    have := verticalHomMk_isHomLift z' (β.app z') (hφ := β.isHomLift' z')
    exact BaseChange.hom_ext_of_isHomLift (Z.p.map f) (β.naturality f)
  isHomLift' z := verticalHomMk_isHomLift z (β.app z) (hφ := β.isHomLift' z)

instance : (changeOfBaseTranspose Z Y L).Full where
  map_surjective β := ⟨transposeInvHom β, by ext; rfl⟩

theorem changeOfBaseTranspose_obj_bijective :
    Function.Bijective (changeOfBaseTranspose Z Y L).obj := by
  constructor
  · intro F G h
    cases F with | mk F hF =>
    cases G with | mk G hG =>
    have h₁ : F ⋙ BaseChange.fst Y.p L = G ⋙ BaseChange.fst Y.p L :=
      congrArg (fun H ↦ H.toFunctor) h
    have h₂ : F ⋙ BaseChange.snd Y.p L = G ⋙ BaseChange.snd Y.p L := hF.trans hG.symm
    have : F = G :=
      (BaseChange.functorEquiv Y.p L).injective (Subtype.ext (Prod.ext h₁ h₂))
    subst this
    rfl
  · intro H
    exact ⟨{ toFunctor := BaseChange.lift H.toFunctor Z.p H.w, w := rfl }, rfl⟩

instance : (changeOfBaseTranspose Z Y L).IsIso where
  bijective_obj := changeOfBaseTranspose_obj_bijective

/-- VI.3 (i): `Hom_{D}(𝒵, 𝒴 ×_E D) ≅ Hom_E(𝒵, 𝒴)` as an isomorphism of categories of
functors over the bases (change of base is right adjoint to restriction of the base).
With `𝒵 = 𝒳 ×_E D` this is SGA's isomorphism
`Hom_{D}(𝒳 ×_E D, 𝒴 ×_E D) ≅ Hom_E(𝒳 ×_E D, 𝒴)`. -/
noncomputable def changeOfBaseTransposeIso (Z : BasedCategory.{v₃, u₃} D)
    (Y : BasedCategory.{v₁, u₁} E) (L : D ⥤ E) :
    IsoCat (BasedFunctor Z (changeOfBase Y L)) (BasedFunctor (restrictBase Z L) Y) :=
  (changeOfBaseTranspose Z Y L).asIsomorphism

end Adjunction

section SmallCategories

open CategoryTheory.Limits

/-- VI.3: the change-of-base functor on the ordinary slice of small categories. -/
noncomputable def baseChangeOnOver {B B' : Cat.{u, u}} (L : B' ⥤ B) : Over B ⥤ Over B' :=
  Over.pullback L.toCatHom

/-- VI.3: restriction of the base is left adjoint to change of base. -/
noncomputable def baseChangeAdjunction {B B' : Cat.{u, u}} (L : B' ⥤ B) :
    Over.map L.toCatHom ⊣ baseChangeOnOver L := Over.mapPullbackAdj L.toCatHom

/-- VI.3: change of base commutes with small projective limits. -/
theorem baseChange_preservesLimits {B B' : Cat.{u, u}} (L : B' ⥤ B) :
    PreservesLimitsOfSize.{u, u} (baseChangeOnOver L) :=
  (baseChangeAdjunction L).rightAdjoint_preservesLimits

/-- VI.3: change of base along the identity is naturally isomorphic to the identity. -/
noncomputable def baseChangeIdentity (B : Cat.{u, u}) :
    baseChangeOnOver (𝟭 B) ≅ 𝟭 (Over B) := Over.pullbackId

/-- VI.3: transitivity of change of base on the slice of small categories. -/
noncomputable def baseChangeComposition {B B' B'' : Cat.{u, u}}
    (L : B' ⥤ B) (K : B'' ⥤ B') :
    baseChangeOnOver (K ⋙ L) ≅ baseChangeOnOver L ⋙ baseChangeOnOver K :=
  Over.pullbackComp K.toCatHom L.toCatHom

end SmallCategories

end SGA.SGA1.ExposeVI
