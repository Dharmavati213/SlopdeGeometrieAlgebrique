/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.BaseChange
import SGA.SGA1.ExposeVI.Equivalences

/-!
# SGA 1, Exposé VI, §4: fibers and full faithfulness

The fiber category is mathlib's `Functor.Fiber`. We construct the induced
functor on fibers, its action on based natural transformations, and the
full-faithfulness result VI.4.1 for arbitrary strict change of base.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- VI.4: restriction of an `E`-functor to the fiber at `S`. -/
def fiberMap (F : BasedFunctor X Y) (S : E) : Fiber X.p S ⥤ Fiber Y.p S where
  obj x := ⟨F.obj x.val, (F.w_obj x.val).trans x.property⟩
  map f := ⟨F.map f.val, by
    have := f.property
    exact BasedFunctor.preserves_isHomLift F _ _⟩
  map_id x := Subtype.ext (F.map_id x.val)
  map_comp f g := Subtype.ext (F.map_comp f.val g.val)

/-- VI.4: restriction of a based natural transformation to a fiber. -/
def fiberNatTrans {F G : BasedFunctor X Y} (α : F ⟶ G) (S : E) :
    fiberMap F S ⟶ fiberMap G S where
  app x := ⟨α.app x.val, α.isHomLift x.property⟩
  naturality {_ _} f := Subtype.ext (α.naturality f.val)

/-- VI.4: passage to the fiber is functorial on based functors. -/
def fiberHom (S : E) : BasedFunctor X Y ⥤ (Fiber X.p S ⥤ Fiber Y.p S) where
  obj F := fiberMap F S
  map α := fiberNatTrans α S

/-- A full based functor reflects the base arrow of its chosen preimage. -/
theorem preimage_isHomLift (F : BasedFunctor X Y) [F.toFunctor.Full]
    {R S : E} (f : R ⟶ S) {a b : X.obj} (φ : F.obj a ⟶ F.obj b)
    [IsHomLift Y.p f φ] : IsHomLift X.p f (F.toFunctor.preimage φ) := by
  apply (BasedFunctor.isHomLift_iff F f (F.toFunctor.preimage φ)).mp
  simpa using (inferInstance : IsHomLift Y.p f φ)

/-- VI.4.1 in particular: restriction to a fiber preserves faithfulness. -/
instance fiberMap_faithful (F : BasedFunctor X Y) [F.toFunctor.Faithful] (S : E) :
    (fiberMap F S).Faithful where
  map_injective h := Subtype.ext (F.toFunctor.map_injective (congrArg Subtype.val h))

set_option backward.isDefEq.respectTransparency false in
/-- VI.4.1 in particular: restriction to a fiber preserves fullness. -/
instance fiberMap_full (F : BasedFunctor X Y) [F.toFunctor.Full] (S : E) :
    (fiberMap F S).Full where
  map_surjective {a b} f := by
    have := f.property
    exact ⟨⟨F.toFunctor.preimage f.val, preimage_isHomLift F (𝟙 S) f.val⟩,
      Subtype.ext (F.toFunctor.map_preimage f.val)⟩

/-- VI.4.1: arbitrary change of base preserves faithfulness. -/
instance changeOfBaseMap_faithful {D : Type u₃} [Category.{v₃} D]
    (F : BasedFunctor X Y) [F.toFunctor.Faithful] (L : D ⥤ E) :
    (changeOfBaseMap F L).toFunctor.Faithful where
  map_injective h := by
    apply BaseChange.Hom.ext
    · exact F.toFunctor.map_injective (congrArg BaseChange.Hom.left h)
    · have hr := congrArg BaseChange.Hom.right h
      exact hr

set_option backward.isDefEq.respectTransparency false in
/-- VI.4.1: arbitrary change of base preserves fullness, hence full faithfulness. -/
instance changeOfBaseMap_full {D : Type u₃} [Category.{v₃} D]
    (F : BasedFunctor X Y) [F.toFunctor.Full] (L : D ⥤ E) :
    (changeOfBaseMap F L).toFunctor.Full where
  map_surjective {a b} f := by
    have := f.over
    refine ⟨⟨F.toFunctor.preimage f.left, f.right,
      preimage_isHomLift F (L.map f.right) f.left⟩, ?_⟩
    apply BaseChange.Hom.ext
    · exact F.toFunctor.map_preimage f.left
    · rfl

/-- VI.4: a vertical isomorphism in the total category gives an isomorphism in a fiber. -/
def fiberIso {C : Type u₁} [Category.{v₁} C] {p : C ⥤ E} {S : E}
    {a b : Fiber p S} (e : a.val ≅ b.val) [IsHomLift p (𝟙 S) e.hom] : a ≅ b where
  hom := ⟨e.hom, inferInstance⟩
  inv := ⟨e.inv, inferInstance⟩
  hom_inv_id := Subtype.ext e.hom_inv_id
  inv_hom_id := Subtype.ext e.inv_hom_id

set_option backward.isDefEq.respectTransparency false in
/-- VI.4: the inclusion of a fiber reflects isomorphisms. -/
instance fiberInclusion_reflectsIsomorphisms {C : Type u₁} [Category.{v₁} C]
    (p : C ⥤ E) (S : E) :
    (Fiber.fiberInclusion : Fiber p S ⥤ C).ReflectsIsomorphisms where
  reflects {a b} f hf := by
    have : IsIso f.val := hf
    have : IsHomLift p (𝟙 S) f.val := f.property
    have : IsHomLift p (𝟙 S) (asIso f.val).hom := f.property
    exact (fiberIso (p := p) (S := S) (a := a) (b := b) (asIso f.val)).isIso_hom

section IdentityBaseChange

variable {C : Type u₁} [Category.{v₁} C] (p : C ⥤ E)

/-- The first projection after identity base change is faithful. -/
instance identityBaseChange_faithful : (BaseChange.fst p (𝟭 E)).Faithful where
  map_injective {a b} {f g} h := by
    change f.left = g.left at h
    apply BaseChange.Hom.ext h
    have : IsHomLift p f.right f.left := f.over
    have : IsHomLift p g.right g.left := g.over
    calc
      f.right = eqToHom a.property.symm ≫ p.map f.left ≫ eqToHom b.property :=
        IsHomLift.fac p f.right f.left
      _ = eqToHom a.property.symm ≫ p.map g.left ≫ eqToHom b.property :=
        congrArg (fun k ↦ eqToHom a.property.symm ≫ p.map k ≫ eqToHom b.property) h
      _ = g.right := (IsHomLift.fac p g.right g.left).symm

/-- The first projection after identity base change is full. -/
instance identityBaseChange_full : (BaseChange.fst p (𝟭 E)).Full where
  map_surjective {a b} f :=
    ⟨⟨f, eqToHom a.property.symm ≫ p.map f ≫ eqToHom b.property,
      IsHomLift.of_fac p _ f a.property b.property rfl⟩, rfl⟩

/-- Every object lifts to the fiber product with the identity base functor. -/
instance identityBaseChange_essSurj : (BaseChange.fst p (𝟭 E)).EssSurj where
  mem_essImage x := ⟨⟨(x, p.obj x), rfl⟩, ⟨Iso.refl x⟩⟩

/-- VI.3–4: the projection from identity base change is an equivalence. -/
instance identityBaseChange_isEquivalence : (BaseChange.fst p (𝟭 E)).IsEquivalence where

end IdentityBaseChange

end SGA.SGA1.ExposeVI
