/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.FamilyProducts

/-!
# SGA 1, Exposé VI, remark at the end of VI.3: `Hom_E(𝒳, 𝒴)` as an internal Hom

For categories `𝒳, 𝒴` over `E` and a category `ℋ`, regard `𝒳 × ℋ` as a category over `E` through
the first projection. SGA's formula

`Hom(ℋ, Hom_E(𝒳, 𝒴)) ≅ Hom_E(𝒳 × ℋ, 𝒴)`

is `basedCurryEquiv`: a functor `Φ : ℋ ⥤ Hom_E(𝒳, 𝒴)` corresponds to the `E`-functor
`(x, h) ↦ Φ(h)(x)`. We also prove its naturality in `ℋ`, `𝒳` and `𝒴`
(`basedUncurry_precomp`, `basedUncurry_comp_left`, `basedUncurry_comp_right`).
-/

universe w v v₁ v₂ v₃ u u₁ u₂ u₃ u₄

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]

/-- VI.3, remark: `𝒳 × ℋ` as a category over `E` through the first projection. -/
abbrev prodRight (X : BasedCategory.{v₁, u₁} E) (H : Type u₃) [Category.{v₃} H] :
    BasedCategory.{max v₁ v₃, max u₁ u₃} E where
  obj := X.obj × H
  p := CategoryTheory.Prod.fst X.obj H ⋙ X.p

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}
  {H : Type u₃} [Category.{v₃} H]

/-- The arrow `(φ, ψ) : (x, h) ⟶ (x', h')` of `𝒳 × ℋ`. -/
abbrev prodHom {x x' : X.obj} {h h' : H} (φ : x ⟶ x') (ψ : h ⟶ h') :
    ((x, h) : X.obj × H) ⟶ (x', h') :=
  (φ, ψ)

/-- The components of the identity of a based functor along an equality. -/
theorem basedNatTrans_eqToHom_app {F G : BasedFunctor X Y} (h : F = G) (x : X.obj) :
    (eqToHom h).toNatTrans.app x = eqToHom (by rw [h]) := by
  subst h
  rfl

@[simp] theorem basedNatTrans_id_app (F : BasedFunctor X Y) (x : X.obj) :
    (𝟙 F : F ⟶ F).toNatTrans.app x = 𝟙 (F.obj x) := rfl

@[simp] theorem basedNatTrans_comp_app {F G K : BasedFunctor X Y} (α : F ⟶ G) (β : G ⟶ K)
    (x : X.obj) : (α ≫ β).toNatTrans.app x = α.toNatTrans.app x ≫ β.toNatTrans.app x := rfl

/-- VI.3, remark: the `E`-functor `(x, h) ↦ Φ(h)(x)` attached to `Φ : ℋ ⥤ Hom_E(𝒳, 𝒴)`. -/
def basedUncurry (Φ : H ⥤ BasedFunctor X Y) : BasedFunctor (prodRight X H) Y where
  toFunctor :=
    { obj := fun xh ↦ (Φ.obj xh.2).obj xh.1
      map := fun {xh xh'} φ ↦ (Φ.obj xh.2).map φ.1 ≫ (Φ.map φ.2).toNatTrans.app xh'.1
      map_id := fun xh ↦ by simp
      map_comp := fun {xh xh' xh''} φ ψ ↦ by
        simp only [prod_comp, Functor.map_comp, basedNatTrans_comp_app, Category.assoc]
        congr 1
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        exact (Φ.map φ.2).naturality ψ.1 }
  w := functor_comp_eq_of_isHomLift _ _ _ (fun xh ↦ (Φ.obj xh.2).w_obj xh.1) fun {xh xh'} φ ↦ by
    have : IsHomLift Y.p (X.p.map φ.1) ((Φ.obj xh.2).map φ.1) :=
      (Φ.obj xh.2).preserves_isHomLift _ φ.1
    have : IsHomLift Y.p (𝟙 (X.p.obj xh'.1)) ((Φ.map φ.2).toNatTrans.app xh'.1) :=
      (Φ.map φ.2).isHomLift' xh'.1
    change IsHomLift Y.p (X.p.map φ.1) ((Φ.obj xh.2).map φ.1 ≫ (Φ.map φ.2).toNatTrans.app xh'.1)
    infer_instance

@[simp] theorem basedUncurry_obj (Φ : H ⥤ BasedFunctor X Y) (x : X.obj) (h : H) :
    (basedUncurry Φ).obj (x, h) = (Φ.obj h).obj x := rfl

@[simp] theorem basedUncurry_map (Φ : H ⥤ BasedFunctor X Y) {xh xh' : X.obj × H}
    (φ : xh ⟶ xh') :
    (basedUncurry Φ).map φ = (Φ.obj xh.2).map φ.1 ≫ (Φ.map φ.2).toNatTrans.app xh'.1 := rfl

/-- The `E`-functor `x ↦ Ψ(x, h)`. -/
def basedCurryObj (Ψ : BasedFunctor (prodRight X H) Y) (h : H) : BasedFunctor X Y where
  toFunctor :=
    { obj := fun x ↦ Ψ.obj (x, h)
      map := fun φ ↦ Ψ.map (prodHom φ (𝟙 h))
      map_id := fun x ↦ Ψ.map_id (x, h)
      map_comp := fun φ ψ ↦ by
        rw [← Ψ.map_comp, prod_comp, Category.comp_id] }
  w := functor_comp_eq_of_isHomLift _ _ _ (fun x ↦ Ψ.w_obj (x, h)) fun {x x'} φ ↦ by
    have : IsHomLift (prodRight X H).p (X.p.map φ) (prodHom φ (𝟙 h)) :=
      IsHomLift.map (prodRight X H).p (prodHom φ (𝟙 h))
    exact Ψ.preserves_isHomLift _ _

/-- VI.3, remark: the functor `h ↦ (x ↦ Ψ(x, h))` attached to an `E`-functor `Ψ : 𝒳 × ℋ ⥤ 𝒴`. -/
def basedCurry (Ψ : BasedFunctor (prodRight X H) Y) : H ⥤ BasedFunctor X Y where
  obj := basedCurryObj Ψ
  map {h h'} ψ :=
    { app := fun x ↦ Ψ.map (prodHom (𝟙 x) ψ)
      naturality := fun {x x'} φ ↦ by
        change Ψ.map (prodHom φ (𝟙 h)) ≫ Ψ.map (prodHom (𝟙 x') ψ) =
          Ψ.map (prodHom (𝟙 x) ψ) ≫ Ψ.map (prodHom φ (𝟙 h'))
        rw [← Ψ.map_comp, ← Ψ.map_comp, prod_comp, prod_comp]
        simp
      isHomLift' := fun x ↦ by
        have : IsHomLift (prodRight X H).p (𝟙 (X.p.obj x)) (prodHom (𝟙 x) ψ) := by
          have := IsHomLift.map (prodRight X H).p (prodHom (𝟙 x) ψ)
          simpa using this
        exact Ψ.preserves_isHomLift _ _ }
  map_id h := by
    ext x
    exact Ψ.map_id (x, h)
  map_comp {h h' h''} ψ ψ' := by
    ext x
    change Ψ.map (prodHom (𝟙 x) (ψ ≫ ψ')) = Ψ.map (prodHom (𝟙 x) ψ) ≫ Ψ.map (prodHom (𝟙 x) ψ')
    rw [← Ψ.map_comp, prod_comp, Category.comp_id]

@[simp] theorem basedCurry_obj_obj (Ψ : BasedFunctor (prodRight X H) Y) (h : H) (x : X.obj) :
    ((basedCurry Ψ).obj h).obj x = Ψ.obj (x, h) := rfl

theorem basedUncurry_basedCurry (Ψ : BasedFunctor (prodRight X H) Y) :
    basedUncurry (basedCurry Ψ) = Ψ := by
  apply basedFunctor_ext
  refine Functor.ext (fun _ ↦ rfl) fun xh xh' φ ↦ ?_
  change Ψ.map (prodHom φ.1 (𝟙 xh.2)) ≫ Ψ.map (prodHom (𝟙 xh'.1) φ.2) = _
  rw [← Ψ.map_comp, prod_comp, Category.comp_id, Category.id_comp]
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

theorem basedCurry_basedUncurry (Φ : H ⥤ BasedFunctor X Y) :
    basedCurry (basedUncurry Φ) = Φ := by
  have hobj : ∀ h, (basedCurry (basedUncurry Φ)).obj h = Φ.obj h := fun h ↦ by
    apply basedFunctor_ext
    refine Functor.ext (fun _ ↦ rfl) fun x x' φ ↦ ?_
    change (Φ.obj h).map φ ≫ (Φ.map (𝟙 h)).toNatTrans.app x' = _
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    simp
  refine Functor.ext hobj fun h h' ψ ↦ ?_
  ext x
  rw [basedNatTrans_comp_app, basedNatTrans_comp_app, basedNatTrans_eqToHom_app,
    basedNatTrans_eqToHom_app]
  change (Φ.obj h).map (𝟙 x) ≫ (Φ.map ψ).toNatTrans.app x = _
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  simp

/-- VI.3, remark: `Hom(ℋ, Hom_E(𝒳, 𝒴)) ≃ Hom_E(𝒳 × ℋ, 𝒴)`, where `𝒳 × ℋ` lies over `E` through
the first projection. -/
def basedCurryEquiv : (H ⥤ BasedFunctor X Y) ≃ BasedFunctor (prodRight X H) Y where
  toFun := basedUncurry
  invFun := basedCurry
  left_inv := basedCurry_basedUncurry
  right_inv := basedUncurry_basedCurry

/-! ### Naturality in `ℋ`, `𝒳` and `𝒴` -/

section Naturality

variable {H' : Type u₄} [Category.{v} H']

/-- The `E`-functor `𝒳 × ℋ' ⥤ 𝒳 × ℋ` induced by `G : ℋ' ⥤ ℋ`. -/
def prodRightMap (X : BasedCategory.{v₁, u₁} E) (G : H' ⥤ H) :
    BasedFunctor (prodRight X H') (prodRight X H) where
  toFunctor := (𝟭 X.obj).prod G

/-- VI.3, remark: naturality in `ℋ`. -/
theorem basedUncurry_precomp (G : H' ⥤ H) (Φ : H ⥤ BasedFunctor X Y) :
    basedUncurry (G ⋙ Φ) = BasedFunctor.comp (prodRightMap X G) (basedUncurry Φ) := rfl

/-- VI.3, remark: naturality in `𝒴`. -/
theorem basedUncurry_comp_right {Z : BasedCategory.{v₃, u₃} E} (Φ : H ⥤ BasedFunctor X Y)
    (G : BasedFunctor Y Z) :
    basedUncurry (Φ ⋙ basedPostcomp G) = BasedFunctor.comp (basedUncurry Φ) G := by
  apply basedFunctor_ext
  refine Functor.ext (fun _ ↦ rfl) fun xh xh' φ ↦ ?_
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (G.map_comp _ _).symm

/-- The `E`-functor `𝒳' × ℋ ⥤ 𝒳 × ℋ` induced by an `E`-functor `F : 𝒳' ⥤ 𝒳`. -/
def prodRightMapLeft {X' : BasedCategory.{v₃, u₃} E} (F : BasedFunctor X' X) (H : Type u₄)
    [Category.{v} H] : BasedFunctor (prodRight X' H) (prodRight X H) where
  toFunctor := F.toFunctor.prod (𝟭 H)
  w := by
    change (F.toFunctor.prod (𝟭 H) ⋙ CategoryTheory.Prod.fst X.obj H) ⋙ X.p =
      CategoryTheory.Prod.fst X'.obj H ⋙ X'.p
    rw [← F.w]
    rfl

/-- VI.3, remark: naturality in `𝒳`. -/
theorem basedUncurry_comp_left {X' : BasedCategory.{v₃, u₃} E} {H : Type u₄} [Category.{v} H]
    (F : BasedFunctor X' X) (Φ : H ⥤ BasedFunctor X Y) :
    basedUncurry (Φ ⋙ basedPrecomp F) = BasedFunctor.comp (prodRightMapLeft F H) (basedUncurry Φ) :=
  rfl

end Naturality

end SGA.SGA1.ExposeVI
