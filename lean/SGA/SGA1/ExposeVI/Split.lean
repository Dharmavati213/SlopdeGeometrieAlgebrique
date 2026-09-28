/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.IsoCat
import SGA.SGA1.ExposeVI.Cleavage

/-!
# SGA 1, Exposé VI, VI.8–VI.9: Grothendieck construction and split categories

VI.8 reconstructs a cloven category from a pseudofunctor `Eᵒᵖ → Cat`. Mathlib's `∫ᶜ F`
(`Pseudofunctor.CoGrothendieck`) is that construction when the comparisons `mapComp` are
isomorphisms (SGA also allows non-invertible `c_{f,g}`, i.e. normalized lax functors, whose
cloven categories are prefibered; that case is `LaxCoGrothendieck.lean`). We prove SGA's points
3)–6) for `∫ᶜ F`: `h_f(η̄, ξ̄) ≃ Hom_f(η̄, ξ̄)`, `i_S : F(S) ≅ (∫ᶜ F)_S` is an isomorphism of
categories, the transports `(f, 𝟙)` form a cleavage whose inverse images agree with the `f^*`
of `F` on objects, and whose comparisons are the given `c_{f,g} = (mapComp f g)⁻¹`. The converse
(a cleavage gives a pseudofunctor, and the two constructions are inverse) is in
`PseudofunctorOfCleavage.lean`, `LaxCoGrothendieckCleavage.lean` and `ClovenCategories.lean`.

VI.9 specialises to a 1-functor `φ : Eᵒᵖ ⥤ Cat`, equivalently a
pseudofunctor with `c_{f,g} = id` (implemented as `eqToIso` of `map_comp`).
The associated split fibered category is `SplitFibered φ`.
-/

universe v₁ v₂ u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite
open CategoryTheory.Pseudofunctor Bicategory

variable {E : Type u₁} [Category.{v₁} E]

/-! ### VI.8: cloven fibered category from a pseudofunctor -/

variable (Fψ : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂})

/-- VI.8: the CoGrothendieck construction of a pseudofunctor
`LocallyDiscrete Eᵒᵖ ⥤ᵖ Cat` is fibered over `E`. -/
theorem cogrothendieck_isFibered : IsFibered (CoGrothendieck.forget Fψ) :=
  inferInstance

/-- VI.8: it is in particular prefibered. -/
theorem cogrothendieck_isPreFibered : IsPreFibered (CoGrothendieck.forget Fψ) :=
  inferInstance

/-- VI.8(5): the chosen lift of `f` at `ξ` is the transport morphism `(f, 𝟙)`,
and it is strongly cartesian. -/
theorem cogrothendieck_isStronglyCartesian_cartesianLift {S : E}
    (a : Fψ.obj ⟨op S⟩) {R : E} (f : R ⟶ S) :
    IsStronglyCartesian (CoGrothendieck.forget Fψ) f
      (CoGrothendieck.cartesianLift a f) :=
  CoGrothendieck.isStronglyCartesian_homCartesianLift a f

/-- VI.8(4): the fiber over `S` is equivalent to `F(S)`. -/
noncomputable def cogrothendieck_fiberEquiv (S : E) :
    Fψ.obj ⟨op S⟩ ≌ Fiber (CoGrothendieck.forget Fψ) S :=
  (HasFibers.inducedFunctor (CoGrothendieck.forget Fψ) S).asEquivalence


/-! ### VI.8: the cleavage of `∫ᶜ F` -/

section Cleavage

variable {Fψ : Pseudofunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}}

/-- VI.8 3): for `f : T ⟶ S`, `h_f(η̄, ξ̄) = Hom_{F(T)}(η, f^* ξ)` is in bijection with the
`f`-morphisms `η̄ ⟶ ξ̄` of `∫ᶜ F`. -/
def cogrothendieckHomOverEquiv {T S : E} (f : T ⟶ S) (b : Fψ.obj ⟨op T⟩) (a : Fψ.obj ⟨op S⟩) :
    (b ⟶ (Fψ.map f.op.toLoc).toFunctor.obj a) ≃
      HomOver (CoGrothendieck.forget Fψ) f (⟨T, b⟩ : CoGrothendieck Fψ) ⟨S, a⟩ where
  toFun u := ⟨⟨f, u⟩, CategoryTheory.IsHomLift.map (CoGrothendieck.forget Fψ)
    (⟨f, u⟩ : (⟨T, b⟩ : CoGrothendieck Fψ) ⟶ ⟨S, a⟩)⟩
  invFun φ := φ.val.fiber ≫ eqToHom (by
    have h : φ.val.base = f := (@IsHomLift.eq_of_isHomLift _ _ _ _ (CoGrothendieck.forget Fψ)
      ⟨T, b⟩ ⟨S, a⟩ f φ.val φ.property).symm
    rw [h])
  left_inv u := by simp
  right_inv φ := by
    have h : φ.val.base = f := (@IsHomLift.eq_of_isHomLift _ _ _ _ (CoGrothendieck.forget Fψ)
      ⟨T, b⟩ ⟨S, a⟩ f φ.val φ.property).symm
    apply Subtype.ext
    exact (CoGrothendieck.Hom.ext _ _ h (by simp)).symm

/-- VI.8 4): `i_S : F(S) ⥤ (∫ᶜ F)_S` is an isomorphism of categories. -/
instance cogrothendieck_inducedFunctor_isIso (S : E) :
    (Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).IsIso where
  bijective_obj := by
    constructor
    · intro a b h
      have := congrArg (fun x : Fiber (CoGrothendieck.forget Fψ) S ↦ x.val) h
      exact eq_of_heq ((CoGrothendieck.ext_iff.mp this).2)
    · rintro ⟨⟨B, x⟩, h⟩
      change B = S at h
      subst h
      exact ⟨x, rfl⟩

/-- VI.8 4): `F(S) ≅ (∫ᶜ F)_S`. -/
noncomputable def cogrothendieckFiberIso (S : E) :
    IsoCat (Fψ.obj ⟨op S⟩) (Fiber (CoGrothendieck.forget Fψ) S) :=
  (Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).asIsomorphism

/-- Transport of an object of `F(B)` along `B = S`. -/
def fiberCast {B S : E} (h : B = S) (x : Fψ.obj ⟨op B⟩) : Fψ.obj ⟨op S⟩ := h ▸ x

theorem cogrothendieck_mk_fiberCast {B S : E} (h : B = S) (x : Fψ.obj ⟨op B⟩) :
    (⟨S, fiberCast h x⟩ : CoGrothendieck Fψ) = ⟨B, x⟩ := by
  subst h
  rfl

/-- VI.8 5): the transports `α_f(ξ) = (f, 𝟙) : (T, f^* ξ) ⟶ (S, ξ)` form a cleavage of
`∫ᶜ F`. -/
noncomputable def cogrothendieckCleavage : Cleavage (CoGrothendieck.forget Fψ) :=
  Cleavage.ofLifts (fun {R S} f ξ ↦ ⟨⟨R, (Fψ.map f.op.toLoc).toFunctor.obj
      (fiberCast ξ.property ξ.val.fiber)⟩, rfl⟩)
    (fun {R S} f ξ ↦ CoGrothendieck.cartesianLift (fiberCast ξ.property ξ.val.fiber) f ≫
      eqToHom (cogrothendieck_mk_fiberCast ξ.property ξ.val.fiber))
    (fun {R S} f ξ ↦ by
      have := CoGrothendieck.isStronglyCartesian_homCartesianLift
        (fiberCast ξ.property ξ.val.fiber) f
      have : IsHomLift (CoGrothendieck.forget Fψ) (𝟙 S)
          (eqToIso (cogrothendieck_mk_fiberCast ξ.property ξ.val.fiber)).hom :=
        IsHomLift.eqToHom_domain_lift_id (cogrothendieck_mk_fiberCast ξ.property ξ.val.fiber) rfl
      exact IsCartesian.of_comp_iso _ f _
        (eqToIso (cogrothendieck_mk_fiberCast ξ.property ξ.val.fiber)))

/-- VI.8 5): the inverse image functors of this cleavage commute with the `i_S` on objects:
`f^*_𝒳 ∘ i_S = i_T ∘ f^*`. -/
theorem cogrothendieckCleavage_pullback_obj {T S : E} (f : T ⟶ S) (a : Fψ.obj ⟨op S⟩) :
    (cogrothendieckCleavage.pullback f).obj
        ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a) =
      (Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ T)).obj
        ((Fψ.map f.op.toLoc).toFunctor.obj a) := rfl

/-- VI.8 5): on objects `i_S(a)` the transport of the cleavage is `(f, 𝟙)`. -/
theorem cogrothendieckCleavage_transport {T S : E} (f : T ⟶ S) (a : Fψ.obj ⟨op S⟩) :
    cogrothendieckCleavage.transport f
        ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a) =
      CoGrothendieck.cartesianLift a f := by
  change CoGrothendieck.cartesianLift a f ≫ eqToHom rfl = _
  simp

/-- An arrow `(h, x)` of `∫ᶜ F` is its vertical part `i(x)` followed by the transport `(h, 𝟙)`. -/
theorem cogrothendieck_ι_map_comp_cartesianLift {U S : E} (h : U ⟶ S) (a : Fψ.obj ⟨op S⟩)
    (b : Fψ.obj ⟨op U⟩) (x : b ⟶ (Fψ.map h.op.toLoc).toFunctor.obj a) :
    (CoGrothendieck.ι Fψ U).map x ≫ CoGrothendieck.cartesianLift a h =
      (⟨h, x⟩ : (⟨U, b⟩ : CoGrothendieck Fψ) ⟶ ⟨S, a⟩) := by
  fapply CoGrothendieck.Hom.ext
  · change 𝟙 U ≫ h = h
    simp
  · change (x ≫ (Fψ.mapId ⟨op U⟩).inv.toNatTrans.app _) ≫
      (Fψ.map (𝟙 U).op.toLoc).toFunctor.map (𝟙 _) ≫
        (Fψ.mapComp h.op.toLoc (𝟙 U).op.toLoc).inv.toNatTrans.app a = _
    simp [Fψ.mapComp_id_right_inv_app, Strict.rightUnitor_eqToIso, PrelaxFunctor.map₂_eqToHom]
    rfl

/-- The composite of two transports `(g, 𝟙) ≫ (f, 𝟙)` is `(g ≫ f, c_{f,g})`, with
`c_{f,g} = (mapComp f g)⁻¹`. -/
theorem cogrothendieck_cartesianLift_comp {U T S : E} (f : T ⟶ S) (g : U ⟶ T)
    (a : Fψ.obj ⟨op S⟩) :
    CoGrothendieck.cartesianLift ((Fψ.map f.op.toLoc).toFunctor.obj a) g ≫
        CoGrothendieck.cartesianLift a f =
      (⟨g ≫ f, (Fψ.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app a⟩ :
        (⟨U, (Fψ.map g.op.toLoc).toFunctor.obj ((Fψ.map f.op.toLoc).toFunctor.obj a)⟩ :
          CoGrothendieck Fψ) ⟶ ⟨S, a⟩) := by
  fapply CoGrothendieck.Hom.ext
  · rfl
  · change 𝟙 _ ≫ (Fψ.map g.op.toLoc).toFunctor.map (𝟙 _) ≫
      (Fψ.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app a = _
    simp

/-- VI.8 6): the comparison `c_{f,g}` of the cleavage of `∫ᶜ F` at `i_S(a)` is the image by
`i_U` of the given `c_{f,g}(a) = (mapComp f g)⁻¹(a) : g^* f^* a ⟶ (fg)^* a`. -/
theorem cogrothendieckCleavage_comparison {U T S : E} (f : T ⟶ S) (g : U ⟶ T)
    (a : Fψ.obj ⟨op S⟩) :
    (cogrothendieckCleavage.comparison f g
        ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a)).val =
      (CoGrothendieck.ι Fψ U).map ((Fψ.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app a) := by
  have : IsHomLift (CoGrothendieck.forget Fψ)
      (a := ((cogrothendieckCleavage.pullback g).obj ((cogrothendieckCleavage.pullback f).obj
        ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a))).val)
      (b := ((cogrothendieckCleavage.pullback (g ≫ f)).obj
        ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a)).val) (𝟙 U)
      ((CoGrothendieck.ι Fψ U).map ((Fψ.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app a)) :=
    CategoryTheory.IsHomLift.map (CoGrothendieck.forget Fψ)
      ((CoGrothendieck.ι Fψ U).map ((Fψ.mapComp f.op.toLoc g.op.toLoc).inv.toNatTrans.app a))
  refine @Functor.IsCartesian.ext _ _ _ _ (CoGrothendieck.forget Fψ) _ _ _ _ (g ≫ f)
    (cogrothendieckCleavage.transport (g ≫ f)
      ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a)) _ _ _ _ _ this ?_
  have e₁ : cogrothendieckCleavage.transport g ((cogrothendieckCleavage.pullback f).obj
      ((Fiber.inducedFunctor (CoGrothendieck.comp_const Fψ S)).obj a)) =
        CoGrothendieck.cartesianLift ((Fψ.map f.op.toLoc).toFunctor.obj a) g :=
    cogrothendieckCleavage_transport g ((Fψ.map f.op.toLoc).toFunctor.obj a)
  rw [Cleavage.comparison_fac, e₁, cogrothendieckCleavage_transport,
    cogrothendieckCleavage_transport]
  exact (cogrothendieck_cartesianLift_comp f g a).trans
    (cogrothendieck_ι_map_comp_cartesianLift (g ≫ f) a _ _).symm

end Cleavage

variable {Fψ}

/-! ### VI.9: split fibered category from a functor `Eᵒᵖ ⥤ Cat` -/

/-- VI.9: the split fibered category associated to a functor `φ : Eᵒᵖ ⥤ Cat`. -/
abbrev SplitFibered (F : Eᵒᵖ ⥤ Cat.{v₂, u₂}) :=
  CoGrothendieck F.toPseudofunctor'

namespace SplitFibered

variable (F : Eᵒᵖ ⥤ Cat.{v₂, u₂})

/-- VI.9: the projection of the split category to the base. -/
abbrev forget : SplitFibered F ⥤ E :=
  CoGrothendieck.forget F.toPseudofunctor'

/-- VI.9: a split category is fibered. -/
theorem forget_isFibered : IsFibered (forget F) :=
  cogrothendieck_isFibered F.toPseudofunctor'

/-- VI.9: a split category is prefibered. -/
theorem forget_isPreFibered : IsPreFibered (forget F) :=
  cogrothendieck_isPreFibered F.toPseudofunctor'

instance : IsFibered (forget F) :=
  forget_isFibered F

/-- The fiber category `φ(S)` as it appears in the Grothendieck construction. -/
abbrev fiberCat (S : E) := F.toPseudofunctor'.obj ⟨op S⟩

/-- VI.8(4): the Grothendieck fiber is the value of the original functor. -/
theorem fiberCat_eq (S : E) : fiberCat F S = F.obj (op S) :=
  Functor.toPseudofunctor'_obj F ⟨op S⟩

/-- Inverse image functor `f^* : φ(S) ⥤ φ(T)`. -/
abbrev pullback {S T : E} (f : T ⟶ S) : fiberCat F S ⥤ fiberCat F T :=
  (F.toPseudofunctor'.map f.op.toLoc).toFunctor

/-- VI.9 / VI.8(4): the fiber over `S` is equivalent to `φ(S)`. -/
noncomputable def fiberEquiv (S : E) :
    fiberCat F S ≌ Fiber (forget F) S :=
  cogrothendieck_fiberEquiv F.toPseudofunctor' S

end SplitFibered

end SGA.SGA1.ExposeVI
