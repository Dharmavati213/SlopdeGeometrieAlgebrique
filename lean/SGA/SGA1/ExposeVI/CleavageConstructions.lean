/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Splittings
import SGA.SGA1.ExposeVI.BaseChangeCartesian

/-!
# SGA 1, Exposé VI, VI.7.1 and §9: cleavages of products and of changes of base

Cleavages `K₁` of `𝒳` and `K₂` of `𝒴` over `E` give a cleavage `K₁.prod K₂` of `𝒳 ×_E 𝒴`
(inverse images and transports computed componentwise), and a cleavage `K` of `𝒴` over `E`
gives, for `L : D ⥤ E`, a cleavage `K.baseChange L` of `𝒴 ×_E D` over `D`, with
`f^* = (L f)^*`. Both constructions preserve normalized cleavages and splittings.
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {D : Type u₂} [Category.{v₂} D]

namespace BaseChange

variable {C : Type u₁} [Category.{v₁} C] {p : C ⥤ E} {L : D ⥤ E}

/-- A morphism of `C ×_E D` whose components are identifications is an identification. -/
theorem eq_eqToHom {x y : BaseChange p L} (h : x = y) (α : x ⟶ y)
    (h₁ : α.left = eqToHom (congrArg (fun z : BaseChange p L ↦ z.val.1) h))
    (h₂ : α.right = eqToHom (congrArg (fun z : BaseChange p L ↦ z.val.2) h)) :
    α = eqToHom h := by
  subst h
  exact Hom.ext h₁ h₂

/-- Componentwise criterion for `α = eqToHom h ≫ β` in `C ×_E D`. -/
theorem eq_eqToHom_comp {x y z : BaseChange p L} (h : x = y) (α : x ⟶ z) (β : y ⟶ z)
    (h₁ : α.left = eqToHom (congrArg (fun z : BaseChange p L ↦ z.val.1) h) ≫ β.left)
    (h₂ : α.right = eqToHom (congrArg (fun z : BaseChange p L ↦ z.val.2) h) ≫ β.right) :
    α = eqToHom h ≫ β := by
  subst h
  exact Hom.ext (by simpa using h₁) (by simpa using h₂)

end BaseChange

namespace Cleavage

section Product

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- The first component of an object of a fiber of `𝒳 ×_E 𝒴`. -/
abbrev fiberFst {S : E} (ξ : Fiber (fiberProduct X Y).p S) : Fiber X.p S :=
  ⟨ξ.val.val.1, ξ.property⟩

/-- The second component of an object of a fiber of `𝒳 ×_E 𝒴`. -/
abbrev fiberSnd {S : E} (ξ : Fiber (fiberProduct X Y).p S) : Fiber Y.p S :=
  ⟨ξ.val.val.2, ξ.val.property.symm.trans ξ.property⟩

/-- VI.7.1: the product of cleavages of `𝒳` and `𝒴` is a cleavage of `𝒳 ×_E 𝒴`, with
`f^*(ξ, η) = (f^*ξ, f^*η)` and transports `(α_f(ξ), α_f(η))`. -/
noncomputable def prod (K₁ : Cleavage X.p) (K₂ : Cleavage Y.p) :
    Cleavage (fiberProduct X Y).p :=
  ofLifts
    (fun f ξ ↦ ⟨⟨(((K₁.pullback f).obj (fiberFst ξ)).val, ((K₂.pullback f).obj (fiberSnd ξ)).val),
      ((K₁.pullback f).obj (fiberFst ξ)).property.trans
        ((K₂.pullback f).obj (fiberSnd ξ)).property.symm⟩,
      ((K₁.pullback f).obj (fiberFst ξ)).property⟩)
    (fun f ξ ↦ fiberProduct.homMk f (K₁.transport f (fiberFst ξ)) (K₂.transport f (fiberSnd ξ)))
    (fun f _ ↦ fiberProduct.isCartesian_homMk f _ _)

variable (K₁ : Cleavage X.p) (K₂ : Cleavage Y.p)

@[simp] theorem prod_transport_left {R S : E} (f : R ⟶ S) (ξ : Fiber (fiberProduct X Y).p S) :
    ((K₁.prod K₂).transport f ξ).left = K₁.transport f (fiberFst ξ) := rfl

@[simp] theorem prod_transport_right {R S : E} (f : R ⟶ S) (ξ : Fiber (fiberProduct X Y).p S) :
    ((K₁.prod K₂).transport f ξ).right = K₂.transport f (fiberSnd ξ) := rfl

theorem fiberFst_prod_pullback {R S : E} (f : R ⟶ S) (ξ : Fiber (fiberProduct X Y).p S) :
    fiberFst ((K₁.prod K₂).pullback f |>.obj ξ) = (K₁.pullback f).obj (fiberFst ξ) := rfl

theorem fiberSnd_prod_pullback {R S : E} (f : R ⟶ S) (ξ : Fiber (fiberProduct X Y).p S) :
    fiberSnd ((K₁.prod K₂).pullback f |>.obj ξ) = (K₂.pullback f).obj (fiberSnd ξ) := rfl

variable {K₁ K₂}

/-- VI.7.1: the product of normalized cleavages is normalized. -/
theorem IsNormalized.prod (h₁ : K₁.IsNormalized) (h₂ : K₂.IsNormalized) :
    (K₁.prod K₂).IsNormalized := by
  intro S ξ
  obtain ⟨e₁, t₁⟩ := h₁ S (fiberFst ξ)
  obtain ⟨e₂, t₂⟩ := h₂ S (fiberSnd ξ)
  exact ⟨Subtype.ext (Prod.ext e₁ e₂), BaseChange.eq_eqToHom _ _ t₁ t₂⟩

/-- VI.9: the product of splittings is a splitting. -/
theorem IsSplitting.prod (h₁ : K₁.IsSplitting) (h₂ : K₂.IsSplitting) :
    (K₁.prod K₂).IsSplitting := by
  refine ⟨h₁.1.prod h₂.1, fun {U T S} f g ξ ↦ ?_⟩
  obtain ⟨e₁, t₁⟩ := h₁.2 f g (fiberFst ξ)
  obtain ⟨e₂, t₂⟩ := h₂.2 f g (fiberSnd ξ)
  exact ⟨Subtype.ext (Prod.ext e₁ e₂), BaseChange.eq_eqToHom_comp _ _ _ t₁ t₂⟩

end Product

section ChangeOfBase

variable {Y : BasedCategory.{v₁, u₁} E} {L : D ⥤ E}

/-- An object of a fiber of `𝒴 ×_E D` over `S`, seen in the fiber of `𝒴` over `L S`. -/
abbrev fiberBase {S : D} (ξ : Fiber (changeOfBase Y L).p S) : Fiber Y.p (L.obj S) :=
  ⟨ξ.val.val.1, ξ.val.property.trans (congrArg L.obj ξ.property)⟩

theorem isHomLift_id_comp_eqToHom {R S S' : D} (f : R ⟶ S) (h : S = S') :
    IsHomLift (𝟭 D) f (f ≫ eqToHom h) := by
  subst h
  simpa using (IsHomLift.map (𝟭 D) f : IsHomLift (𝟭 D) ((𝟭 D).map f) f)

/-- VI.7.1: a cleavage of `𝒴` over `E` induces a cleavage of `𝒴 ×_E D` over `D`, with
`f^* = (L f)^*` and transports `α_{L f}`. -/
noncomputable def baseChange (K : Cleavage Y.p) (L : D ⥤ E) :
    Cleavage (changeOfBase Y L).p :=
  ofLifts
    (fun {R _} f ξ ↦ ⟨⟨(((K.pullback (L.map f)).obj (fiberBase ξ)).val, R),
      ((K.pullback (L.map f)).obj (fiberBase ξ)).property⟩, rfl⟩)
    (fun {R _} f ξ ↦ BaseChange.homOver f (K.transport (L.map f) (fiberBase ξ))
      (f ≫ eqToHom ξ.property.symm) (h₂ := isHomLift_id_comp_eqToHom f _))
    (fun {R _} f ξ ↦ by
      have h₂ := isHomLift_id_comp_eqToHom f ξ.property.symm
      refine BaseChange.isCartesian_of_isCartesian_left f _ (hαf := ?_)
        (K.transport_isCartesian _ _)
      exact (BaseChange.isHomLift_snd_iff f _).mpr h₂)

variable (K : Cleavage Y.p) (L)

@[simp] theorem baseChange_transport_left {R S : D} (f : R ⟶ S)
    (ξ : Fiber (changeOfBase Y L).p S) :
    ((K.baseChange L).transport f ξ).left = K.transport (L.map f) (fiberBase ξ) := rfl

@[simp] theorem baseChange_transport_right {R S : D} (f : R ⟶ S)
    (ξ : Fiber (changeOfBase Y L).p S) :
    ((K.baseChange L).transport f ξ).right = f ≫ eqToHom ξ.property.symm := rfl

theorem fiberBase_baseChange_pullback {R S : D} (f : R ⟶ S) (ξ : Fiber (changeOfBase Y L).p S) :
    (fiberBase ((K.baseChange L).pullback f |>.obj ξ)).val =
      ((K.pullback (L.map f)).obj (fiberBase ξ)).val := rfl

variable {K L}

/-- VI.7.1: the inverse image of a normalized cleavage by a change of base is normalized. -/
theorem IsNormalized.baseChange (hK : K.IsNormalized) : (K.baseChange L).IsNormalized := by
  intro S ξ
  obtain ⟨e, t⟩ := hK (L.obj S) (fiberBase ξ)
  have e' := congrArg (fun k ↦ ((K.pullback k).obj (fiberBase ξ)).val) (L.map_id S)
  refine ⟨Subtype.ext (Prod.ext (e'.trans e) ξ.property.symm), BaseChange.eq_eqToHom _ _ ?_ ?_⟩
  · change K.transport (L.map (𝟙 S)) (fiberBase ξ) = _
    rw [K.transport_congr (L.map_id S), t, eqToHom_trans]
    rfl
  · change 𝟙 S ≫ eqToHom _ = _
    simp
    rfl

/-- VI.9: the inverse image of a splitting by a change of base is a splitting. -/
theorem IsSplitting.baseChange (hK : K.IsSplitting) : (K.baseChange L).IsSplitting := by
  refine ⟨hK.1.baseChange, fun {U T S} f g ξ ↦ ?_⟩
  obtain ⟨e, t⟩ := hK.2 (L.map f) (L.map g) (fiberBase ξ)
  have e' := congrArg (fun k ↦ ((K.pullback k).obj (fiberBase ξ)).val) (L.map_comp g f).symm
  refine ⟨Subtype.ext (Prod.ext (e.trans e') rfl), BaseChange.eq_eqToHom_comp _ _ _ ?_ ?_⟩
  · change K.transport (L.map g) ((K.pullback (L.map f)).obj (fiberBase ξ)) ≫
      K.transport (L.map f) (fiberBase ξ) = _ ≫ K.transport (L.map (g ≫ f)) (fiberBase ξ)
    rw [t, K.transport_congr (L.map_comp g f).symm, eqToHom_trans_assoc]
    rfl
  · change (g ≫ eqToHom rfl) ≫ f ≫ eqToHom _ = _ ≫ (g ≫ f) ≫ eqToHom _
    simp only [eqToHom_refl, Category.comp_id, Category.assoc]
    exact (Category.id_comp _).symm

end ChangeOfBase

end Cleavage

end SGA.SGA1.ExposeVI
