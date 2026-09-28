/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.BasedFunctorSystems
import SGA.SGA1.ExposeVI.SplitEquivalence

/-!
# SGA 1, Exposé VI, VI.8–VI.9: categories of cloven categories and of pseudofunctors

SGA (VI.8): "one should consider the pseudofunctors `Eᵒᵖ → Cat` as the objects of a new category,
and show that our constructions furnish equivalences, quasi-inverse to one another, between the
latter and the category of cloven categories over `E`"; (VI.9) "the category of split
categories over `E` is thus equivalent to `Hom(Eᵒᵖ, Cat)`".

A morphism of cloven categories is an `E`-functor sending transport morphisms to transport
morphisms (`IsClovenFunctor`, VI.7; bundled as `ClovenHom`). We first show that such a functor is
determined by its fiber functors (`IsClovenFunctor.ext`), which commute strictly with the inverse
images (`IsClovenFunctor.pullback_comp_fiberMap`) and with the comparisons
(`IsClovenFunctor.map_comparison`); conversely a family of fiber functors with these properties
comes from a morphism of cloven categories (`Cleavage.ofFiberFamily`, using VI.12). Then:

* `NormalizedPseudofunctor E`: the category of normalized pseudofunctors `Eᵒᵖ → Cat` (SGA's
  pseudofunctors: strictly unitary lax functors, the `c_{f,g}` need not be invertible), with the
  strict morphisms `StrictTrans` (functors `θ_S` with `f^* ∘ θ_S = θ_T ∘ f^*`, compatible with the
  `c_{f,g}`); a strict morphism with invertible components is invertible;
* `ClovenCat E`: normalized cloven categories over `E`, with the morphisms of cloven categories;
* `ClovenCat.toPseudofunctor`, `𝒳 ↦ (S ↦ 𝒳_S, f ↦ f^*)`, is fully faithful, and essentially
  surjective (via `P ↦ ∫ P` and the isomorphisms `i_S : P(S) ≅ (∫ P)_S`); `clovenCatEquivalence`
  is the resulting equivalence (VI.8), with quasi-inverse `P ↦ ∫ P` on objects, counit given by
  the `i_S`, and unit inverse to `(S, ξ) ↦ ξ` (`clovenCatEquivalence_unitIso_inv_app`);
* `SplitCat E`: split categories over `E` with morphisms of cloven categories;
  `splitEquivalence : SplitCat E ≌ (Eᵒᵖ ⥤ Cat)` (VI.9), with quasi-inverse `ψ ↦ ∫ ψ`.

The equivalences are stated with the universes of `∫ P` (`max` of those of `E` and of the
fibers), as in SGA where everything lives in one universe.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor Opposite

/-- A natural transformation whose components are identifications `eqToHom` is an equality of
functors. -/
theorem functor_eq_of_forall_eqToHom {A : Type*} {B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} (α : F ⟶ G) (h : ∀ X, F.obj X = G.obj X) (hα : ∀ X, α.app X = eqToHom (h X)) :
    F = G :=
  CategoryTheory.Functor.ext h fun X Y f ↦ by
    have := α.naturality f
    rw [hα, hα, comp_eqToHom_iff] at this
    rw [this, Category.assoc]

/-- The identification `θ₃ (a₂ (a₁ x)) = b₂ (b₁ (θ₁ x))` deduced from two strict commutations
`a₁ ⋙ θ₂ = θ₁ ⋙ b₁` and `a₂ ⋙ θ₃ = θ₂ ⋙ b₂`. -/
theorem obj_eq_of_comp_eq {A₁ A₂ A₃ B₁ B₂ B₃ : Type*} [Category A₁] [Category A₂] [Category A₃]
    [Category B₁] [Category B₂] [Category B₃] {a₁ : A₁ ⥤ A₂} {a₂ : A₂ ⥤ A₃} {b₁ : B₁ ⥤ B₂}
    {b₂ : B₂ ⥤ B₃} {θ₁ : A₁ ⥤ B₁} {θ₂ : A₂ ⥤ B₂} {θ₃ : A₃ ⥤ B₃} (h₁ : a₁ ⋙ θ₂ = θ₁ ⋙ b₁)
    (h₂ : a₂ ⋙ θ₃ = θ₂ ⋙ b₂) (x : A₁) : θ₃.obj (a₂.obj (a₁.obj x)) = b₂.obj (b₁.obj (θ₁.obj x)) :=
  (Functor.congr_obj h₂ _).trans (congrArg b₂.obj (Functor.congr_obj h₁ x))

variable {E : Type u₁} [Category.{v₁} E]

section ClovenFunctors

variable {X : BasedCategory.{v₂, u₂} E} {Y : BasedCategory.{v₃, u₃} E}
  {K : Cleavage X.p} {K' : Cleavage Y.p} {F : BasedFunctor X Y}

/-- For a morphism of cloven categories, the constraints `φ_f` of VI.12 are identifications. -/
theorem IsClovenFunctor.basedConstraintApp_eq (hF : IsClovenFunctor K K' F) {T S : E}
    (f : T ⟶ S) (ξ : Fiber X.p S) : ∃ h, basedConstraintApp K K' F f ξ = eqToHom h := by
  obtain ⟨h, hh⟩ := hF f ξ
  refine ⟨h, ?_⟩
  have : IsHomLift Y.p (𝟙 T) (eqToHom h) :=
    IsHomLift.eqToHom_domain_lift_id h ((F.w_obj _).trans ((K.pullback f).obj ξ).property)
  exact (IsCartesian.map_uniq Y.p f _ _ _ hh.symm).symm

/-- VI.8: a morphism of cloven categories commutes strictly with the inverse image functors:
`f^* ∘ F_S = F_T ∘ f^*`. -/
theorem IsClovenFunctor.pullback_comp_fiberMap (hF : IsClovenFunctor K K' F) {T S : E}
    (f : T ⟶ S) : K.pullback f ⋙ fiberMap F T = fiberMap F S ⋙ K'.pullback f := by
  have hobj : ∀ ξ, (K.pullback f ⋙ fiberMap F T).obj ξ = (fiberMap F S ⋙ K'.pullback f).obj ξ :=
    fun ξ ↦ Subtype.ext (hF f ξ).choose
  refine functor_eq_of_forall_eqToHom (basedConstraint K K' F f) hobj fun ξ ↦ ?_
  apply Subtype.ext
  obtain ⟨h, hh⟩ := hF.basedConstraintApp_eq f ξ
  rw [fiber_eqToHom_val]
  exact hh

/-- For a morphism of cloven categories, `φ_f` is the identification `f^* ∘ F_S = F_T ∘ f^*`. -/
theorem IsClovenFunctor.basedConstraint_eq_eqToHom (hF : IsClovenFunctor K K' F) {T S : E}
    (f : T ⟶ S) : basedConstraint K K' F f = eqToHom (hF.pullback_comp_fiberMap f) := by
  ext ξ
  obtain ⟨h, hh⟩ := hF.basedConstraintApp_eq f ξ
  rw [eqToHom_app, eqToHom_map]
  exact hh

/-- VI.12 b′) at the level of the fibers. -/
theorem basedConstraint_comp_fiber (F : BasedFunctor X Y) {U T S : E} (f : T ⟶ S) (g : U ⟶ T)
    (ξ : Fiber X.p S) :
    (fiberMap F U).map (K.comparison f g ξ) ≫ (basedConstraint K K' F (g ≫ f)).app ξ =
      (basedConstraint K K' F g).app ((K.pullback f).obj ξ) ≫
        (K'.pullback g).map ((basedConstraint K K' F f).app ξ) ≫
          K'.comparison f g ((fiberMap F S).obj ξ) :=
  Fiber.hom_ext (basedConstraint_comp K K' F f g ξ)

variable (K K') in
/-- VI.8: a morphism of cloven categories: an `E`-functor sending transports to transports. -/
@[ext]
structure ClovenHom where
  /-- The underlying `E`-functor. -/
  functor : BasedFunctor X Y
  /-- It sends transports to transports. -/
  cloven : IsClovenFunctor K K' functor

/-- VI.8: a morphism of cloven categories transforms the comparisons `c_{f,g}` into the
comparisons `c′_{f,g}` (up to the identifications `f^* ∘ F_S = F_T ∘ f^*`). -/
theorem IsClovenFunctor.map_comparison (hF : IsClovenFunctor K K' F) {U T S : E} (f : T ⟶ S)
    (g : U ⟶ T) (ξ : Fiber X.p S) :
    (fiberMap F U).map (K.comparison f g ξ) =
      eqToHom (obj_eq_of_comp_eq (hF.pullback_comp_fiberMap f) (hF.pullback_comp_fiberMap g) ξ) ≫
        K'.comparison f g ((fiberMap F S).obj ξ) ≫
          eqToHom (Functor.congr_obj (hF.pullback_comp_fiberMap (g ≫ f)) ξ).symm := by
  have h := basedConstraint_comp_fiber (K := K) (K' := K') F f g ξ
  rw [hF.basedConstraint_eq_eqToHom, hF.basedConstraint_eq_eqToHom,
    hF.basedConstraint_eq_eqToHom, eqToHom_app, eqToHom_app, eqToHom_app, eqToHom_map,
    comp_eqToHom_iff] at h
  rw [h]
  erw [eqToHom_trans_assoc]
  exact Category.assoc _ _ _

variable (K) in
/-- VI.8: the identity functor is a morphism of cloven categories. -/
theorem isClovenFunctor_id : IsClovenFunctor K K (BasedFunctor.id X) :=
  fun _ _ ↦ ⟨rfl, (Category.id_comp _).symm⟩

/-- VI.8: morphisms of cloven categories are stable under composition. -/
theorem IsClovenFunctor.comp {Z : BasedCategory.{v₂, u₂} E} {K'' : Cleavage Z.p}
    {G : BasedFunctor Y Z} (hF : IsClovenFunctor K K' F) (hG : IsClovenFunctor K' K'' G) :
    IsClovenFunctor K K'' (BasedFunctor.comp F G) := by
  intro T S f ξ
  obtain ⟨h, hh⟩ := hF f ξ
  obtain ⟨h', hh'⟩ := hG f ((fiberMap F S).obj ξ)
  refine ⟨(congrArg G.obj h).trans h', ?_⟩
  change G.map (F.map (K.transport f ξ)) = _
  rw [hh, Functor.map_comp, eqToHom_map, hh', eqToHom_trans_assoc]
  rfl

/-- VI.8: a morphism of cloven categories is determined by its fiber functors. -/
theorem IsClovenFunctor.ext {G : BasedFunctor X Y} (hF : IsClovenFunctor K K' F)
    (hG : IsClovenFunctor K K' G) (h : ∀ S, fiberMap F S = fiberMap G S) : F = G := by
  rw [← BasedFunctorSystem.toBasedFunctor_ofBasedFunctor (K := K) (K' := K') F,
    ← BasedFunctorSystem.toBasedFunctor_ofBasedFunctor (K := K) (K' := K') G]
  congr 1
  refine BasedFunctorSystem.ext' h fun {T S} f ξ ↦ ?_
  change ((basedConstraint K K' F f).app ξ).val =
    eqToHom _ ≫ ((basedConstraint K K' G f).app ξ).val ≫ eqToHom _
  rw [hF.basedConstraint_eq_eqToHom, hG.basedConstraint_eq_eqToHom, eqToHom_app, eqToHom_app,
    fiber_eqToHom_val, fiber_eqToHom_val]
  erw [eqToHom_trans, eqToHom_trans]

end ClovenFunctors

namespace Cleavage

/-- VI.9: for a splitting, the comparisons are the identifications `g^* f^* = (fg)^*`. -/
theorem IsSplitting.comparison_eq {C : Type u₂} [Category.{v₂} C] {p : C ⥤ E}
    {K : Cleavage p} (hK : K.IsSplitting) {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber p S) :
    K.comparison f g ξ = eqToHom (Functor.congr_obj (hK.pullback_comp f g) ξ) := by
  obtain ⟨h, hc⟩ := ((K.isSplitting_iff).mp hK).2 f g ξ
  apply Subtype.ext
  rw [hc, fiber_eqToHom_val]

/-- VI.9: for split categories, any family of fiber functors commuting strictly with the inverse
images also commutes with the comparisons (which are identifications). -/
theorem IsSplitting.map_comparison_eq {X : BasedCategory.{v₂, u₂} E}
    {Y : BasedCategory.{v₃, u₃} E} {K : Cleavage X.p} {K' : Cleavage Y.p} (hK : K.IsSplitting)
    (hK' : K'.IsSplitting) (θ : ∀ S, Fiber X.p S ⥤ Fiber Y.p S)
    (hnat : ∀ {T S : E} (f : T ⟶ S), K.pullback f ⋙ θ T = θ S ⋙ K'.pullback f)
    {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber X.p S) :
    (θ U).map (K.comparison f g ξ) = eqToHom (obj_eq_of_comp_eq (hnat f) (hnat g) ξ) ≫
      K'.comparison f g ((θ S).obj ξ) ≫ eqToHom (Functor.congr_obj (hnat (g ≫ f)) ξ).symm := by
  rw [hK.comparison_eq, hK'.comparison_eq, eqToHom_map]
  simp only [eqToHom_trans]

theorem IsNormalized.transportId_eq {C : Type u₂} [Category.{v₂} C] {p : C ⥤ E}
    {K : Cleavage p} (hK : K.IsNormalized) (S : E) (ξ : Fiber p S) :
    K.transportId S ξ = eqToHom (hK.pullback_obj ξ) :=
  Subtype.ext (by obtain ⟨h, ht⟩ := hK S ξ; simpa [transportId] using ht)

/-! ### From a family of fiber functors to a morphism of cloven categories -/

section OfFiberFamily

variable {X : BasedCategory.{v₂, u₂} E} {Y : BasedCategory.{v₃, u₃} E}
  {K : Cleavage X.p} {K' : Cleavage Y.p} (hK : K.IsNormalized) (hK' : K'.IsNormalized)
  (θ : ∀ S, Fiber X.p S ⥤ Fiber Y.p S)
  (hnat : ∀ {T S : E} (f : T ⟶ S), K.pullback f ⋙ θ T = θ S ⋙ K'.pullback f)
  (hcomp : ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber X.p S),
    (θ U).map (K.comparison f g ξ) = eqToHom (obj_eq_of_comp_eq (hnat f) (hnat g) ξ) ≫
      K'.comparison f g ((θ S).obj ξ) ≫ eqToHom (Functor.congr_obj (hnat (g ≫ f)) ξ).symm)

include hK hK' hcomp in
/-- VI.8, VI.12: a family of fiber functors commuting strictly with the inverse images and the
comparisons, as a system satisfying a′) and b′) (with identifications as constraints). -/
noncomputable def fiberFamilySystem : BasedFunctorSystem K K' where
  obj := θ
  φ f := eqToHom (hnat f)
  φ_id S ξ := by
    rw [hK.transportId_eq, hK'.transportId_eq, eqToHom_map, eqToHom_app, eqToHom_trans]
  φ_comp {U T S} f g ξ := by
    rw [hcomp, eqToHom_app, eqToHom_app, eqToHom_app, eqToHom_map]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, eqToHom_trans_assoc]

include hK hK' hcomp in
/-- VI.8: the morphism of cloven categories defined by a family of fiber functors commuting
strictly with the inverse images and the comparisons. -/
noncomputable def ofFiberFamily : BasedFunctor X Y :=
  (fiberFamilySystem hK hK' θ hnat hcomp).toBasedFunctor

theorem fiberMap_ofFiberFamily (S : E) : fiberMap (ofFiberFamily hK hK' θ hnat hcomp) S = θ S :=
  BasedFunctorSystem.fiberMap_toBasedFunctor _ S

theorem isClovenFunctor_ofFiberFamily :
    IsClovenFunctor K K' (ofFiberFamily hK hK' θ hnat hcomp) := by
  intro T S f ξ
  have hζ : (fiberMap (ofFiberFamily hK hK' θ hnat hcomp) S).obj ξ = (θ S).obj ξ :=
    Functor.congr_obj (fiberMap_ofFiberFamily hK hK' θ hnat hcomp S) ξ
  have hφ : (((fiberFamilySystem hK hK' θ hnat hcomp).φ f).app ξ).val =
      eqToHom (congrArg Fiber.fiberInclusion.obj (Functor.congr_obj (hnat f) ξ)) := by
    change Fiber.fiberInclusion.map ((eqToHom (hnat f)).app ξ) = _
    rw [eqToHom_app, eqToHom_map]
  erw [BasedFunctorSystem.toBasedFunctor_map_transport, hφ,
    BasedFunctorSystem.transport_eq_eqToHom K' f hζ]
  refine ⟨(congrArg Subtype.val (Functor.congr_obj (fiberMap_ofFiberFamily hK hK' θ hnat hcomp T)
    ((K.pullback f).obj ξ))).trans ((congrArg Subtype.val (Functor.congr_obj (hnat f) ξ)).trans
      (by rw [hζ]; rfl)), ?_⟩
  exact (eqToHom_trans_assoc (C := Y.obj) _ _ _).trans (eqToHom_trans_assoc (C := Y.obj) _ _ _).symm

end OfFiberFamily

end Cleavage

/-- A component of a family of morphisms, conjugated along an identification of the indices. -/
theorem app_eq_eqToHom_comp {β : Type*} {C : Type*} [Category C] {f g : β → C}
    (z : ∀ b, f b ⟶ g b) {j j' : β} (w : j = j') :
    z j = eqToHom (congrArg f w) ≫ z j' ≫ eqToHom (congrArg g w).symm := by
  subst w
  simp

theorem self_eq_eqToHom_comp_comp_eqToHom {C : Type*} [Category C] {a b : C} (f : a ⟶ b)
    (h₁ : a = a) (h₂ : b = b) : f = eqToHom h₁ ≫ f ≫ eqToHom h₂ := by
  simp

/-! ### The category of normalized pseudofunctors `Eᵒᵖ → Cat` -/

section Pseudofunctors

/-- VI.8: a (strict) morphism `θ : P ⟶ Q` of normalized pseudofunctors `Eᵒᵖ → Cat`: functors
`θ_S : P(S) ⥤ Q(S)` commuting strictly with the inverse images, `f^* ∘ θ_S = θ_T ∘ f^*`, and
transforming the comparisons `c_{f,g}` of `P` into those of `Q`. -/
@[ext]
structure StrictTrans (P Q : StrictlyUnitaryLaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}) where
  /-- The functors `θ_S : P(S) ⥤ Q(S)`. -/
  app (S : E) : P.obj ⟨op S⟩ ⥤ Q.obj ⟨op S⟩
  /-- `f^* ∘ θ_S = θ_T ∘ f^*`. -/
  naturality {T S : E} (f : T ⟶ S) :
    laxPullback P.toLaxFunctor f ⋙ app T = app S ⋙ laxPullback Q.toLaxFunctor f
  /-- `θ_U(c_{f,g}(x)) = c_{f,g}(θ_S x)` (up to the identifications given by `naturality`). -/
  comparison {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (x : P.obj ⟨op S⟩) :
    (app U).map ((laxComparison P.toLaxFunctor f g).app x) =
      eqToHom (obj_eq_of_comp_eq (naturality f) (naturality g) x) ≫
        (laxComparison Q.toLaxFunctor f g).app ((app S).obj x) ≫
          eqToHom (Functor.congr_obj (naturality (g ≫ f)) x).symm

namespace StrictTrans

variable {P Q R : StrictlyUnitaryLaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}}

variable (P) in
/-- The identity strict morphism. -/
def id : StrictTrans P P where
  app _ := 𝟭 _
  naturality _ := rfl
  comparison _ _ _ := by simp

/-- The composition of strict morphisms. -/
def comp (θ : StrictTrans P Q) (θ' : StrictTrans Q R) : StrictTrans P R where
  app S := θ.app S ⋙ θ'.app S
  naturality {T S} f := by
    rw [← Functor.assoc, θ.naturality, Functor.assoc, θ'.naturality, Functor.assoc]
  comparison {U T S} f g x := by
    change (θ'.app U).map ((θ.app U).map _) = _
    rw [θ.comparison, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map,
      θ'.comparison]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc]
    rfl

/-- The inverse of a strict morphism whose components are isomorphisms of categories, with
given strict inverses `ι_S`. -/
def inverse (θ : StrictTrans P Q) (ι : ∀ S, Q.obj ⟨op S⟩ ⥤ P.obj ⟨op S⟩)
    (h₁ : ∀ S, θ.app S ⋙ ι S = 𝟭 _) (h₂ : ∀ S, ι S ⋙ θ.app S = 𝟭 _) : StrictTrans Q P where
  app := ι
  naturality {T S} f := by
    calc laxPullback Q.toLaxFunctor f ⋙ ι T
        = (ι S ⋙ θ.app S) ⋙ laxPullback Q.toLaxFunctor f ⋙ ι T := by
          rw [h₂, Functor.id_comp]
      _ = ι S ⋙ (laxPullback P.toLaxFunctor f ⋙ θ.app T) ⋙ ι T := by
          rw [θ.naturality]; rfl
      _ = ι S ⋙ laxPullback P.toLaxFunctor f := by
          rw [Functor.assoc, h₁, Functor.comp_id]
  comparison {U T S} f g y := by
    have : (θ.app U).Faithful := Functor.Faithful.of_comp_eq (h₁ U)
    apply (θ.app U).map_injective
    have hy : (θ.app S).obj ((ι S).obj y) = y := Functor.congr_obj (h₂ S) y
    have e : (laxComparison Q.toLaxFunctor f g).app ((θ.app S).obj ((ι S).obj y)) =
        eqToHom _ ≫ (laxComparison Q.toLaxFunctor f g).app y ≫ eqToHom _ :=
      app_eq_eqToHom_comp (fun z ↦ (laxComparison Q.toLaxFunctor f g).app z) hy
    have h := Functor.congr_hom (h₂ U) ((laxComparison Q.toLaxFunctor f g).app y)
    rw [Functor.comp_map] at h
    rw [h, Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map, θ.comparison, e]
    simp only [Category.assoc, eqToHom_trans, eqToHom_trans_assoc, Functor.id_map]

end StrictTrans

end Pseudofunctors

/-! ### Equivalences from fully faithful functors with explicit preimages -/

/-- An equivalence of categories from a fully faithful functor `F` together with explicit objects
`G₀ Y` and isomorphisms `F (G₀ Y) ≅ Y`; the quasi-inverse is `G₀` on objects. -/
@[simps! functor inverse_obj counitIso_hom_app counitIso_inv_app]
noncomputable def equivalenceOfFullyFaithful {C D : Type*} [Category C] [Category D] {F : C ⥤ D}
    (hF : F.FullyFaithful) (G₀ : D → C) (e : ∀ Y, F.obj (G₀ Y) ≅ Y) : C ≌ D where
  functor := F
  inverse :=
    { obj := G₀
      map {X Y} f := hF.preimage ((e X).hom ≫ f ≫ (e Y).inv)
      map_id X := hF.map_injective (by simp)
      map_comp f g := hF.map_injective (by simp) }
  unitIso := NatIso.ofComponents (fun X ↦ (hF.preimageIso (e (F.obj X))).symm)
    fun f ↦ hF.map_injective (by simp)
  counitIso := NatIso.ofComponents e (by simp)

/-! ### The category of normalized pseudofunctors -/

variable (E) in
/-- VI.8: the category of normalized pseudofunctors `Eᵒᵖ → Cat` (strictly unitary lax functors,
whose comparisons `c_{f,g}` need not be invertible), with the strict morphisms `StrictTrans`. -/
structure NormalizedPseudofunctor where
  /-- The underlying strictly unitary lax functor. -/
  F : StrictlyUnitaryLaxFunctor (LocallyDiscrete Eᵒᵖ) Cat.{v₂, u₂}

namespace NormalizedPseudofunctor

instance : Category (NormalizedPseudofunctor.{v₁, v₂, u₁, u₂} E) where
  Hom P Q := StrictTrans P.F Q.F
  id P := StrictTrans.id P.F
  comp θ θ' := θ.comp θ'
  id_comp _ := StrictTrans.ext rfl
  comp_id _ := StrictTrans.ext rfl
  assoc _ _ _ := StrictTrans.ext rfl

variable {P Q : NormalizedPseudofunctor.{v₁, v₂, u₁, u₂} E}

@[ext] theorem hom_ext {θ θ' : P ⟶ Q} (h : ∀ S, θ.app S = θ'.app S) : θ = θ' :=
  StrictTrans.ext (funext h)

@[simp] theorem id_app (S : E) : (𝟙 P : P ⟶ P).app S = 𝟭 _ := rfl

@[simp] theorem comp_app {R : NormalizedPseudofunctor.{v₁, v₂, u₁, u₂} E} (θ : P ⟶ Q)
    (θ' : Q ⟶ R) (S : E) : (θ ≫ θ').app S = θ.app S ⋙ θ'.app S := rfl

/-- A strict morphism whose components are isomorphisms of categories is an isomorphism. -/
instance isIso_of_isIso_app (θ : P ⟶ Q) [∀ S, (θ.app S).IsIso] : IsIso θ :=
  ⟨⟨StrictTrans.inverse θ (fun S ↦ (θ.app S).strictInv)
      (fun S ↦ (θ.app S).asIsomorphism.unit_eq.symm) (fun S ↦ (θ.app S).asIsomorphism.counit_eq),
    StrictTrans.ext (funext fun S ↦ (θ.app S).asIsomorphism.unit_eq.symm),
    StrictTrans.ext (funext fun S ↦ (θ.app S).asIsomorphism.counit_eq)⟩⟩

end NormalizedPseudofunctor

/-! ### The category of normalized cloven categories -/

variable (E) in
/-- VI.8: the category of normalized cloven categories over `E`; the morphisms are the
`E`-functors sending transports to transports (`IsClovenFunctor`, VI.7). -/
structure ClovenCat where
  /-- The category over `E`. -/
  X : BasedCategory.{v₂, u₂} E
  /-- The cleavage. -/
  K : Cleavage X.p
  /-- The cleavage is normalized. -/
  hK : K.IsNormalized

namespace ClovenCat

instance : Category (ClovenCat.{v₁, v₂, u₁, u₂} E) where
  Hom A B := ClovenHom A.K B.K
  id A := ⟨BasedFunctor.id A.X, isClovenFunctor_id A.K⟩
  comp F G := ⟨BasedFunctor.comp F.functor G.functor, IsClovenFunctor.comp F.cloven G.cloven⟩

/-- VI.8: the functor sending a normalized cloven category to its normalized pseudofunctor
`S ↦ 𝒳_S`, `f ↦ f^*`, and a morphism of cloven categories to its fiber functors. -/
noncomputable def toPseudofunctor :
    ClovenCat.{v₁, v₂, u₁, u₂} E ⥤ NormalizedPseudofunctor.{v₁, v₂, u₁, u₂} E where
  obj A := ⟨A.hK.strictlyUnitaryLaxFunctor⟩
  map F :=
    { app S := fiberMap F.functor S
      naturality f := IsClovenFunctor.pullback_comp_fiberMap F.cloven f
      comparison f g x := IsClovenFunctor.map_comparison F.cloven f g x }
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem toPseudofunctor_map_app {A B : ClovenCat.{v₁, v₂, u₁, u₂} E} (F : A ⟶ B) (S : E) :
    (toPseudofunctor.map F).app S = fiberMap F.functor S := rfl

instance : (toPseudofunctor (E := E)).Faithful where
  map_injective {_ _} {F G} h :=
    ClovenHom.ext (IsClovenFunctor.ext F.cloven G.cloven fun S ↦
      congrArg (fun θ ↦ StrictTrans.app θ S) h)

instance : (toPseudofunctor (E := E)).Full where
  map_surjective {A B} θ :=
    ⟨⟨Cleavage.ofFiberFamily A.hK B.hK θ.app θ.naturality θ.comparison,
      Cleavage.isClovenFunctor_ofFiberFamily A.hK B.hK θ.app θ.naturality θ.comparison⟩,
      NormalizedPseudofunctor.hom_ext fun S ↦
        Cleavage.fiberMap_ofFiberFamily A.hK B.hK θ.app θ.naturality θ.comparison S⟩

end ClovenCat

namespace NormalizedPseudofunctor

variable (P : NormalizedPseudofunctor.{v₁, max v₁ v₂, u₁, max u₁ u₂} E)

/-- VI.8: the normalized cloven category `∫ P` over `E` defined by a normalized pseudofunctor,
with its cleavage by the transports `(f, 𝟙)`. -/
noncomputable def toClovenCat : ClovenCat.{v₁, max v₁ v₂, u₁, max u₁ u₂} E where
  X := BasedCategory.ofFunctor (LaxCoGrothendieck.forget P.F.toLaxFunctor)
  K := LaxCoGrothendieck.cleavage P.F
  hK := LaxCoGrothendieck.cleavage_isNormalized

/-- VI.8 4)–6): the isomorphisms `i_S : P(S) ≅ (∫ P)_S` form a strict morphism from `P` to the
pseudofunctor of `∫ P`. -/
noncomputable def fiberFunctorTrans : P ⟶ ClovenCat.toPseudofunctor.obj P.toClovenCat where
  app S := LaxCoGrothendieck.fiberFunctor P.F S
  naturality f := (LaxCoGrothendieck.fiberFunctor_comp_pullback f).symm
  comparison f g x := by
    exact (LaxCoGrothendieck.cleavage_comparison f g x).symm.trans
      (self_eq_eqToHom_comp_comp_eqToHom _ _ _)

instance : IsIso P.fiberFunctorTrans :=
  have : ∀ S, (P.fiberFunctorTrans.app S).IsIso := fun S ↦
    inferInstanceAs (LaxCoGrothendieck.fiberFunctor P.F S).IsIso
  inferInstance

/-- VI.8: `P` is isomorphic to the pseudofunctor of `∫ P`. -/
noncomputable def toClovenCatIso : ClovenCat.toPseudofunctor.obj P.toClovenCat ≅ P :=
  (asIso P.fiberFunctorTrans).symm

end NormalizedPseudofunctor

/-- VI.8: every normalized pseudofunctor is (isomorphic to) the pseudofunctor of a normalized
cloven category. -/
instance : (ClovenCat.toPseudofunctor.{v₁, max v₁ v₂, u₁, max u₁ u₂} (E := E)).EssSurj where
  mem_essImage P := ⟨P.toClovenCat, ⟨P.toClovenCatIso⟩⟩

/-- VI.8: the equivalence between the category of normalized cloven categories over `E` and the
category of normalized pseudofunctors `Eᵒᵖ → Cat`, `𝒳 ↦ (S ↦ 𝒳_S, f ↦ f^*)`, whose quasi-inverse
is `P ↦ ∫ P` (with its cleavage by the `(f, 𝟙)`); the counit is given by the isomorphisms
`i_S : P(S) ≅ (∫ P)_S`. -/
noncomputable def clovenCatEquivalence :
    ClovenCat.{v₁, max v₁ v₂, u₁, max u₁ u₂} E ≌
      NormalizedPseudofunctor.{v₁, max v₁ v₂, u₁, max u₁ u₂} E :=
  equivalenceOfFullyFaithful (Functor.FullyFaithful.ofFullyFaithful _)
    NormalizedPseudofunctor.toClovenCat NormalizedPseudofunctor.toClovenCatIso

/-- VI.8: `ClovenCat.toPseudofunctor` is an equivalence of categories. -/
instance : (ClovenCat.toPseudofunctor.{v₁, max v₁ v₂, u₁, max u₁ u₂} (E := E)).IsEquivalence :=
  clovenCatEquivalence.isEquivalence_functor

/-- VI.8: the unit `𝒳 ⟶ ∫ F_𝒳` of `clovenCatEquivalence` has the fiber functors
`i_S : 𝒳_S ⥤ (∫ F_𝒳)_S`. -/
theorem clovenCatEquivalence_unitIso_hom_app_fiberMap
    (A : ClovenCat.{v₁, max v₁ v₂, u₁, max u₁ u₂} E) (S : E) :
    fiberMap (clovenCatEquivalence.unitIso.hom.app A).functor S =
      LaxCoGrothendieck.fiberFunctor A.hK.strictlyUnitaryLaxFunctor S := by
  have h : ClovenCat.toPseudofunctor.map (clovenCatEquivalence.unitIso.hom.app A) =
      (ClovenCat.toPseudofunctor.obj A).fiberFunctorTrans := by
    change ClovenCat.toPseudofunctor.map
      ((Functor.FullyFaithful.ofFullyFaithful ClovenCat.toPseudofunctor).preimage
        (ClovenCat.toPseudofunctor.obj A).fiberFunctorTrans) = _
    exact Functor.FullyFaithful.map_preimage _ _
  exact congrArg (fun θ ↦ StrictTrans.app θ S) h

theorem Cleavage.IsNormalized.comp_eqToHom_comp_transportId {X : BasedCategory.{v₂, u₂} E}
    {K : Cleavage X.p} (hK : K.IsNormalized) {S : E} {ξ ξ' : Fiber X.p S} (u : ξ ⟶ ξ')
    (h : ξ' = (K.pullback (𝟙 S)).obj ξ') : (u ≫ eqToHom h).val ≫ K.transport (𝟙 S) ξ' = u.val := by
  obtain ⟨h', ht⟩ := hK S ξ'
  rw [ht, fiber_comp_val, fiber_eqToHom_val, Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.comp_id]

/-- VI.8: for a normalized cleavage, `𝒳_S ⥤ (∫ F_𝒳)_S ⥤ 𝒳_S` (by `i_S` and `(S, ξ) ↦ ξ`) is the
identity. -/
theorem Cleavage.IsNormalized.fiberFunctor_comp_fiberMap_fromLaxCoGrothendieckBased
    {X : BasedCategory.{v₂, u₂} E} {K : Cleavage X.p} (hK : K.IsNormalized) (S : E) :
    LaxCoGrothendieck.fiberFunctor hK.strictlyUnitaryLaxFunctor S ⋙
      fiberMap K.fromLaxCoGrothendieckBased S = 𝟭 _ := by
  refine CategoryTheory.Functor.ext (fun _ ↦ rfl) fun ξ ξ' u ↦
    (?_ : _ = (𝟭 (Fiber X.p S)).map u).trans (self_eq_eqToHom_comp_comp_eqToHom _ _ _)
  apply Subtype.ext
  change (u ≫ eqToHom _).val ≫ K.transport (𝟙 S) ξ' = u.val
  exact hK.comp_eqToHom_comp_transportId u _

/-- VI.8: the inverse of the unit of `clovenCatEquivalence` is the isomorphism
`∫ F_𝒳 ≅ 𝒳`, `(S, ξ) ↦ ξ` of `Cleavage.laxCoGrothendieckIso`. -/
theorem clovenCatEquivalence_unitIso_inv_app (A : ClovenCat.{v₁, max v₁ v₂, u₁, max u₁ u₂} E) :
    (clovenCatEquivalence.unitIso.inv.app A).functor = A.K.fromLaxCoGrothendieckBased := by
  let G : clovenCatEquivalence.inverse.obj (clovenCatEquivalence.functor.obj A) ⟶ A :=
    ⟨A.K.fromLaxCoGrothendieckBased, A.hK.isClovenFunctor_fromLaxCoGrothendieckBased⟩
  have hG : clovenCatEquivalence.unitIso.hom.app A ≫ G = 𝟙 A := by
    refine ClovenHom.ext (IsClovenFunctor.ext (IsClovenFunctor.comp
      (clovenCatEquivalence.unitIso.hom.app A).cloven G.cloven) (isClovenFunctor_id A.K)
      fun S ↦ ?_)
    change fiberMap (clovenCatEquivalence.unitIso.hom.app A).functor S ⋙
      fiberMap A.K.fromLaxCoGrothendieckBased S = 𝟭 _
    rw [clovenCatEquivalence_unitIso_hom_app_fiberMap]
    exact A.hK.fiberFunctor_comp_fiberMap_fromLaxCoGrothendieckBased S
  have h := (Iso.hom_comp_eq_id (clovenCatEquivalence.unitIso.app A)).mp hG
  rw [Iso.app_inv] at h
  exact (congrArg ClovenHom.functor h).symm

/-! ### Split categories and functors `Eᵒᵖ ⥤ Cat` (VI.9) -/

variable (E) in
/-- VI.9: the category of split categories over `E`; the morphisms are the morphisms of cloven
categories (`E`-functors sending transports to transports). -/
structure SplitCat where
  /-- The category over `E`. -/
  X : BasedCategory.{v₂, u₂} E
  /-- The splitting. -/
  K : Cleavage X.p
  /-- The cleavage is a splitting. -/
  hK : K.IsSplitting

namespace SplitCat

instance : Category (SplitCat.{v₁, v₂, u₁, u₂} E) where
  Hom A B := ClovenHom A.K B.K
  id A := ⟨BasedFunctor.id A.X, isClovenFunctor_id A.K⟩
  comp F G := ⟨BasedFunctor.comp F.functor G.functor, IsClovenFunctor.comp F.cloven G.cloven⟩

/-- VI.9: the functor sending a split category to the functor `S ↦ 𝒳_S`, `f ↦ f^*`, and a morphism
of split categories to its fiber functors. -/
def toFunctor : SplitCat.{v₁, v₂, u₁, u₂} E ⥤ (Eᵒᵖ ⥤ Cat.{v₂, u₂}) where
  obj A := A.hK.toFunctor
  map F :=
    { app S := (fiberMap F.functor S.unop).toCatHom
      naturality _ _ f :=
        Cat.Hom.ext (IsClovenFunctor.pullback_comp_fiberMap F.cloven f.unop) }
  map_id _ := rfl
  map_comp _ _ := rfl

instance : (toFunctor (E := E)).Faithful where
  map_injective {_ _} {F G} h :=
    ClovenHom.ext (IsClovenFunctor.ext F.cloven G.cloven fun S ↦
      congrArg Cat.Hom.toFunctor (NatTrans.congr_app h (op S)))

instance : (toFunctor (E := E)).Full where
  map_surjective {A B} τ := by
    have hnat : ∀ {T S : E} (f : T ⟶ S), A.K.pullback f ⋙ (τ.app (op T)).toFunctor =
        (τ.app (op S)).toFunctor ⋙ B.K.pullback f :=
      fun f ↦ congrArg Cat.Hom.toFunctor (τ.naturality f.op)
    have hcomp : ∀ {U T S : E} (f : T ⟶ S) (g : U ⟶ T) (ξ : Fiber A.X.p S), _ :=
      fun f g ξ ↦ Cleavage.IsSplitting.map_comparison_eq A.hK B.hK
        (fun S ↦ (τ.app (op S)).toFunctor) hnat f g ξ
    exact ⟨⟨Cleavage.ofFiberFamily A.hK.1 B.hK.1 (fun S ↦ (τ.app (op S)).toFunctor) hnat hcomp,
      Cleavage.isClovenFunctor_ofFiberFamily A.hK.1 B.hK.1 _ hnat hcomp⟩,
      NatTrans.ext (funext fun S ↦ Cat.Hom.ext
        (Cleavage.fiberMap_ofFiberFamily A.hK.1 B.hK.1 _ hnat hcomp S.unop))⟩

/-- VI.9: the split category `∫ ψ` over `E` defined by a functor `ψ : Eᵒᵖ ⥤ Cat`, with its
canonical splitting by the transports `(f, 𝟙)`. -/
noncomputable def ofFunctor (ψ : Eᵒᵖ ⥤ Cat.{max v₁ v₂, max u₁ u₂}) :
    SplitCat.{v₁, max v₁ v₂, u₁, max u₁ u₂} E where
  X := BasedCategory.ofFunctor (LaxCoGrothendieck.forget (laxOfFunctor ψ).toLaxFunctor)
  K := LaxCoGrothendieck.cleavage (laxOfFunctor ψ)
  hK := isSplitting_cleavage_laxOfFunctor ψ

/-- VI.9: the functor of `∫ ψ` is isomorphic to `ψ`, by the isomorphisms `i_S : ψ(S) ≅ (∫ ψ)_S`. -/
noncomputable def ofFunctorIso (ψ : Eᵒᵖ ⥤ Cat.{max v₁ v₂, max u₁ u₂}) :
    toFunctor.obj (ofFunctor ψ) ≅ ψ :=
  (splittingFunctorIso ψ).symm

instance : (toFunctor.{v₁, max v₁ v₂, u₁, max u₁ u₂} (E := E)).EssSurj where
  mem_essImage ψ := ⟨ofFunctor ψ, ⟨ofFunctorIso ψ⟩⟩

end SplitCat

/-- VI.9: the category of split categories over `E` is equivalent to the category of functors
`Eᵒᵖ ⥤ Cat`, by `𝒳 ↦ (S ↦ 𝒳_S, f ↦ f^*)`, with quasi-inverse `ψ ↦ ∫ ψ` (with its canonical
splitting); the counit is given by the isomorphisms `i_S : ψ(S) ≅ (∫ ψ)_S`. -/
noncomputable def splitEquivalence :
    SplitCat.{v₁, max v₁ v₂, u₁, max u₁ u₂} E ≌ (Eᵒᵖ ⥤ Cat.{max v₁ v₂, max u₁ u₂}) :=
  equivalenceOfFullyFaithful (Functor.FullyFaithful.ofFullyFaithful _) SplitCat.ofFunctor
    SplitCat.ofFunctorIso

/-- VI.9: `SplitCat.toFunctor` is an equivalence of categories. -/
instance : (SplitCat.toFunctor.{v₁, max v₁ v₂, u₁, max u₁ u₂} (E := E)).IsEquivalence :=
  splitEquivalence.isEquivalence_functor

end SGA.SGA1.ExposeVI
