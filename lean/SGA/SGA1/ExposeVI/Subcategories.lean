/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.BaseChangeCartesian
import Mathlib.CategoryTheory.Widesubcategory
import Mathlib.CategoryTheory.Groupoid

/-!
# SGA 1, Exposé VI, remarks after VI.6.1 and VI.6.8: fibered subcategories

* A full subcategory `𝒢` of a fibered category `𝒳` is a fibered subcategory iff every inverse
  image `f^*ξ` of an object `ξ ∈ 𝒢_S` is isomorphic over `T` to an object of `𝒢_T`.
* The subcategory `𝒳̃` of cartesian arrows of a fibered category `𝒳` is a fibered subcategory,
  all of whose arrows are cartesian and whose fibers are groupoids; cartesian sections of `𝒳`
  correspond bijectively to sections of `𝒳̃` (and the comparison functor is faithful).
* VI.6.8, second part: for `𝒳` fibered, the objects of `lim(𝒳 ×_E D / D)` are in bijection with
  the functors `D ⥤ 𝒳̃` over `L`.
-/

universe v v₁ v₂ u u₁ u₂

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {C : Type u₁} [Category.{v₁} C]

/-- An arrow cartesian over its own image is cartesian over any arrow it lies over. -/
theorem isCartesian_of_isCartesian_map (p : C ⥤ E) {R S : E} (f : R ⟶ S) {a b : C}
    (φ : a ⟶ b) [IsHomLift p f φ] (h : IsCartesian p (p.map φ) φ) : IsCartesian p f φ := by
  subst_hom_lift p f φ
  exact h

/-! ### Full subcategories -/

section Full

variable (p : C ⥤ E) (P : ObjectProperty C)

/-- A morphism of a full subcategory which is cartesian in `𝒳` is cartesian in the
subcategory. -/
theorem fullSubcategory_isCartesian_of_isCartesian {R S : E} (f : R ⟶ S)
    {a b : P.FullSubcategory} (φ : a ⟶ b) (h : IsCartesian p f φ.hom) :
    IsCartesian (P.ι ⋙ p) f φ := by
  have : IsHomLift (P.ι ⋙ p) f φ := (isHomLift_comp_iff P.ι p f φ).mpr h.toIsHomLift
  refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
  have : IsHomLift p f φ'.hom := (isHomLift_comp_iff P.ι p f φ').mp hφ'
  refine ⟨ObjectProperty.homMk (IsCartesian.map p f φ.hom φ'.hom),
    ⟨(isHomLift_comp_iff P.ι p _ _).mpr (IsCartesian.map_isHomLift p f φ.hom φ'.hom),
      ObjectProperty.hom_ext _ (IsCartesian.fac p f φ.hom φ'.hom)⟩, ?_⟩
  rintro χ ⟨hχ, hfac⟩
  have : IsHomLift p (𝟙 R) χ.hom := (isHomLift_comp_iff P.ι p _ χ).mp hχ
  exact ObjectProperty.hom_ext _
    (IsCartesian.map_uniq p f φ.hom φ'.hom χ.hom (P.ι.congr_map hfac))

/-- VI.6.1, remark: a full subcategory `𝒢` of a fibered category is a fibered subcategory
(fibered, with cartesian inclusion) iff, for every cartesian `φ : a ⟶ b` with `b ∈ 𝒢`, the
source `a` is vertically isomorphic to an object of `𝒢`. -/
theorem fullSubcategory_isFiberedSubcategory_iff [IsFibered p] :
    (IsFibered (P.ι ⋙ p) ∧ ∀ {R S : E} (f : R ⟶ S) {a b : P.FullSubcategory} (φ : a ⟶ b),
      IsCartesian (P.ι ⋙ p) f φ → IsCartesian p f φ.hom) ↔
    ∀ {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b), IsCartesian p f φ → P b →
      ∃ a' : C, P a' ∧ ∃ e : a' ≅ a, IsHomLift p (𝟙 R) e.hom := by
  constructor
  · rintro ⟨hfib, hincl⟩ R S f a b φ hφ hb
    have hpb : (P.ι ⋙ p).obj ⟨b, hb⟩ = S := IsHomLift.codomain_eq p f φ
    obtain ⟨a', ψ, hψ⟩ := IsPreFibered.exists_isCartesian (P.ι ⋙ p) hpb f
    have := hincl f ψ hψ
    exact ⟨a'.obj, a'.property, IsCartesian.domainUniqueUpToIso p f φ ψ.hom, inferInstance⟩
  · intro h
    -- every morphism over `f` into an object of `𝒢` has a cartesian lift in `𝒢`
    have hlift : ∀ {R : E} (b : P.FullSubcategory) (f : R ⟶ p.obj b.obj),
        ∃ (a : P.FullSubcategory) (φ : a ⟶ b), IsCartesian p f φ.hom := by
      intro R b f
      obtain ⟨a, φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p) (a := b.obj) f
      obtain ⟨a', ha', e, he⟩ := h f φ hφ b.property
      exact ⟨⟨a', ha'⟩, ObjectProperty.homMk (e.hom ≫ φ), IsCartesian.of_iso_comp p f φ e⟩
    -- cartesian arrows of `𝒢` are cartesian in `𝒳`
    have hincl : ∀ {R S : E} (f : R ⟶ S) {a b : P.FullSubcategory} (φ : a ⟶ b),
        IsCartesian (P.ι ⋙ p) f φ → IsCartesian p f φ.hom := by
      intro R S f a b φ hφ
      have hb : p.obj b.obj = S := IsHomLift.codomain_eq (P.ι ⋙ p) f φ
      subst hb
      obtain ⟨a', ψ, hψ⟩ := hlift b f
      have := fullSubcategory_isCartesian_of_isCartesian p P f ψ hψ
      let e := IsCartesian.domainUniqueUpToIso (P.ι ⋙ p) f ψ φ
      have he : e.hom ≫ ψ = φ := IsCartesian.fac (P.ι ⋙ p) f ψ φ
      have : IsHomLift p (𝟙 R) (P.ι.mapIso e).hom :=
        (isHomLift_comp_iff P.ι p (𝟙 R) e.hom).mp inferInstance
      rw [← he]
      exact IsCartesian.of_iso_comp p f ψ.hom (P.ι.mapIso e)
    refine ⟨?_, hincl⟩
    have : IsPreFibered (P.ι ⋙ p) := ⟨fun {b R} f ↦ by
      obtain ⟨a, φ, hφ⟩ := hlift b f
      exact ⟨a, φ, fullSubcategory_isCartesian_of_isCartesian p P f φ hφ⟩⟩
    refine (isFibered_iff_comp (P.ι ⋙ p)).mpr fun {R S T} f g {a b c} φ ψ hφ hψ ↦ ?_
    have := hincl f φ hφ
    have := hincl g ψ hψ
    exact fullSubcategory_isCartesian_of_isCartesian p P (f ≫ g) (φ ≫ ψ)
      (inferInstance : IsCartesian p (f ≫ g) (φ.hom ≫ ψ.hom))

end Full

/-! ### The subcategory of cartesian arrows -/

section CartesianArrows

variable (p : C ⥤ E)

/-- VI.6.1, remark: the class of cartesian arrows of `𝒳`. -/
def cartesianArrows : MorphismProperty C := fun _ _ φ ↦ IsCartesian p (p.map φ) φ

theorem cartesianArrows_iff {R S : E} (f : R ⟶ S) {a b : C} (φ : a ⟶ b) [IsHomLift p f φ] :
    cartesianArrows p φ ↔ IsCartesian p f φ := by
  subst_hom_lift p f φ
  rfl

instance [IsFibered p] : (cartesianArrows p).IsMultiplicative where
  id_mem a := (inferInstance : IsCartesian p (p.map (𝟙 a)) (𝟙 a))
  comp_mem {a b c} φ ψ hφ hψ := by
    have : IsCartesian p (p.map φ) φ := hφ
    have : IsCartesian p (p.map ψ) ψ := hψ
    change IsCartesian p (p.map (φ ≫ ψ)) (φ ≫ ψ)
    rw [p.map_comp]
    infer_instance

variable [IsFibered p]

/-- VI.6.1, remark: the subcategory `𝒳̃` of `𝒳` with the same objects and the cartesian arrows
as morphisms. -/
abbrev CartesianSubcategory := WideSubcategory (cartesianArrows p)

/-- The projection `𝒳̃ ⥤ E`. -/
abbrev cartesianSubcategoryProj : CartesianSubcategory p ⥤ E :=
  wideSubcategoryInclusion (cartesianArrows p) ⋙ p

/-- VI.6.1, remark: every arrow of `𝒳̃` is cartesian (over its image) in `𝒳̃`. -/
theorem cartesianSubcategory_isCartesian {x y : CartesianSubcategory p} (φ : x ⟶ y) :
    IsCartesian (cartesianSubcategoryProj p) (p.map φ.1) φ := by
  have hφ : IsCartesian p (p.map φ.1) φ.1 := φ.2
  have : IsHomLift (cartesianSubcategoryProj p) (p.map φ.1) φ :=
    IsHomLift.map (cartesianSubcategoryProj p) φ
  refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
  have : IsHomLift p (p.map φ.1) φ'.1 := (isHomLift_comp_iff _ p _ φ').mp hφ'
  have hφ'c : IsCartesian p (p.map φ.1) φ'.1 :=
    (cartesianArrows_iff p (p.map φ.1) φ'.1).mp φ'.2
  let χ₀ := IsCartesian.map p (p.map φ.1) φ.1 φ'.1
  have hχ₀ : χ₀ ≫ φ.1 = φ'.1 := IsCartesian.fac p _ _ _
  have hcart : IsCartesian p (𝟙 (p.obj x.obj)) χ₀ := by
    have : IsCartesian p (𝟙 (p.obj x.obj) ≫ p.map φ.1) (χ₀ ≫ φ.1) := by
      rw [hχ₀, Category.id_comp]
      exact hφ'c
    exact (isCartesian_comp_iff p _ _ χ₀ φ.1).mp this
  refine ⟨⟨χ₀, (cartesianArrows_iff p (𝟙 _) χ₀).mpr hcart⟩,
    ⟨(isHomLift_comp_iff _ p _ _).mpr (IsCartesian.map_isHomLift p (p.map φ.1) φ.1 φ'.1),
      WideSubcategory.hom_ext _ hχ₀⟩, ?_⟩
  rintro χ ⟨hχ, hfac⟩
  have : IsHomLift p (𝟙 (p.obj x.obj)) χ.1 := (isHomLift_comp_iff _ p _ χ).mp hχ
  exact WideSubcategory.hom_ext _
    (IsCartesian.map_uniq p (p.map φ.1) φ.1 φ'.1 χ.1 (congrArg (fun k ↦ k.1) hfac))

/-- VI.6.1, remark: `𝒳̃` is fibered over `E`, all its arrows being cartesian. -/
instance cartesianSubcategory_isFibered : IsFibered (cartesianSubcategoryProj p) := by
  have hall : ∀ {R S : E} (f : R ⟶ S) {a b : CartesianSubcategory p} (φ : a ⟶ b),
      IsHomLift (cartesianSubcategoryProj p) f φ → IsCartesian (cartesianSubcategoryProj p) f φ :=
    fun {_ _} f {_ _} φ h ↦ by
      have := h
      exact isCartesian_of_isCartesian_map _ f φ (cartesianSubcategory_isCartesian p φ)
  have : IsPreFibered (cartesianSubcategoryProj p) := ⟨fun {b R} f ↦ by
    obtain ⟨a, φ, hφ⟩ := IsPreFibered.exists_isCartesian' (p := p) (a := b.obj) f
    have : IsHomLift p f φ := hφ.toIsHomLift
    refine ⟨⟨a⟩, ⟨φ, (cartesianArrows_iff p f φ).mpr hφ⟩, hall f _ ?_⟩
    exact (isHomLift_comp_iff _ p f _).mpr hφ.toIsHomLift⟩
  exact (isFibered_iff_comp _).mpr fun {_ _ _} f g {_ _ _} φ ψ _ _ ↦
    hall (f ≫ g) (φ ≫ ψ) inferInstance

/-- VI.6.1, remark: the inclusion `𝒳̃ ⥤ 𝒳` is cartesian, so `𝒳̃` is a fibered subcategory. -/
theorem cartesianSubcategory_inclusion_isCartesian {R S : E} (f : R ⟶ S)
    {a b : CartesianSubcategory p} (φ : a ⟶ b) (_ : IsCartesian (cartesianSubcategoryProj p) f φ) :
    IsCartesian p f φ.1 := by
  have : IsHomLift p f φ.1 :=
    (isHomLift_comp_iff (wideSubcategoryInclusion (cartesianArrows p)) p f φ).mp inferInstance
  exact (cartesianArrows_iff p f φ.1).mp φ.2

/-- VI.6.1, remark: the fibers of `𝒳̃` are groupoids. -/
instance (S : E) : IsGroupoid (Fiber (cartesianSubcategoryProj p) S) where
  all_isIso {a b} u := by
    have hu : IsHomLift p (𝟙 S) u.val.1 := (isHomLift_comp_iff _ p _ u.val).mp u.property
    have := (cartesianArrows_iff p (𝟙 S) u.val.1).mp u.val.2
    have : IsIso u.val.1 := isIso_of_vertical_isCartesian p (S := S) u.val.1
    have hinv : IsHomLift p (𝟙 S) (inv u.val.1) := IsHomLift.lift_id_inv_isIso p S u.val.1
    let v : b ⟶ a := ⟨⟨inv u.val.1, (cartesianArrows_iff p (𝟙 S) _).mpr inferInstance⟩,
      (isHomLift_comp_iff _ p _ _).mpr hinv⟩
    exact ⟨v, Subtype.ext (WideSubcategory.hom_ext _ (IsIso.hom_inv_id u.val.1)),
      Subtype.ext (WideSubcategory.hom_ext _ (IsIso.inv_hom_id u.val.1))⟩

/-- VI.6.1, remark: cartesian sections of `𝒳` correspond bijectively to sections of `𝒳̃`. -/
def cartesianSectionEquiv (X : BasedCategory.{v₁, u₁} E) [IsFibered X.p] :
    cartesianLimit X ≃
      {H : E ⥤ CartesianSubcategory X.p // H ⋙ cartesianSubcategoryProj X.p = 𝟭 E} where
  toFun s :=
    ⟨{ obj := fun e ↦ ⟨s.obj.obj e⟩
       map := fun {e e'} φ ↦ ⟨s.obj.map φ, by
         have : IsCartesian (BasedCategory.ofFunctor (𝟭 E)).p φ φ := isCartesian_id_functor φ
         have := s.property.map_isCartesian φ φ
         exact (cartesianArrows_iff X.p φ _).mpr this⟩
       map_id := fun e ↦ WideSubcategory.hom_ext _ (s.obj.map_id e)
       map_comp := fun φ ψ ↦ WideSubcategory.hom_ext _ (s.obj.map_comp φ ψ) }, s.obj.w⟩
  invFun H :=
    ⟨{ toFunctor := H.val ⋙ wideSubcategoryInclusion _
       w := H.property },
     ⟨fun {R S a b} f φ hφ ↦ by
      have h₁ : IsHomLift (H.val ⋙ cartesianSubcategoryProj X.p) f φ := by
        rw [H.property]
        exact hφ.toIsHomLift
      have h₂ : IsHomLift (cartesianSubcategoryProj X.p) f (H.val.map φ) :=
        (isHomLift_comp_iff _ _ f φ).mp h₁
      have : IsHomLift X.p f (H.val.map φ).1 :=
        (isHomLift_comp_iff (wideSubcategoryInclusion _) X.p f _).mp h₂
      change IsCartesian X.p f (H.val.map φ).1
      exact (cartesianArrows_iff X.p f _).mp (H.val.map φ).2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- VI.6.1, remark: sections of `𝒳̃` give cartesian sections of `𝒳`; this functor
`Hom_E(E, 𝒳̃) ⥤ lim(𝒳/E)` is faithful (but not full in general). -/
def cartesianSubcategorySections (X : BasedCategory.{v₁, u₁} E) [IsFibered X.p] :
    BasedFunctor (BasedCategory.ofFunctor (𝟭 E))
      (BasedCategory.ofFunctor (cartesianSubcategoryProj X.p)) ⥤ cartesianLimit X :=
  cartesianFunctorProperty.lift
    (basedPostcomp (X := BasedCategory.ofFunctor (𝟭 E))
      ⟨wideSubcategoryInclusion (cartesianArrows X.p), rfl⟩)
    (fun H ↦ ⟨fun {R S a b} f φ hφ ↦ by
      have hφ' : IsCartesian (cartesianSubcategoryProj X.p) f (H.map φ) := by
        have : IsHomLift (cartesianSubcategoryProj X.p) f (H.map φ) :=
          BasedFunctor.preserves_isHomLift H f φ
        exact isCartesian_of_isCartesian_map _ f _ (cartesianSubcategory_isCartesian X.p _)
      exact cartesianSubcategory_inclusion_isCartesian X.p f (H.map φ) hφ'⟩)

instance (X : BasedCategory.{v₁, u₁} E) [IsFibered X.p] :
    (cartesianSubcategorySections X).Faithful where
  map_injective {F G} {α β} h := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext e
    exact WideSubcategory.hom_ext _
      (congrArg (fun γ ↦ γ.hom.toNatTrans.app e) h)

end CartesianArrows

/-! ### VI.6.8, second part -/

section Sections

variable {D : Type u₂} [Category.{v₂} D] (X : BasedCategory.{v₁, u₁} E) [IsFibered X.p]
  (L : D ⥤ E)

/-- VI.6.8: `E`-functors `D ⥤ 𝒳` over `L` sending all arrows to cartesian arrows are the
same as functors `D ⥤ 𝒳̃` over `L`. -/
def transformsToCartesianEquiv :
    (TransformsToCartesian X L).FullSubcategory ≃
      {H : D ⥤ CartesianSubcategory X.p // H ⋙ cartesianSubcategoryProj X.p = L} where
  toFun H :=
    ⟨{ obj := fun d ↦ ⟨H.obj.obj d⟩
       map := fun φ ↦ ⟨H.obj.map φ, by
         have : IsHomLift X.p (L.map φ) (H.obj.map φ) := H.property φ |>.toIsHomLift
         exact (cartesianArrows_iff X.p (L.map φ) _).mpr (H.property φ)⟩
       map_id := fun d ↦ WideSubcategory.hom_ext _ (H.obj.map_id d)
       map_comp := fun φ ψ ↦ WideSubcategory.hom_ext _ (H.obj.map_comp φ ψ) }, H.obj.w⟩
  invFun H :=
    ⟨{ toFunctor := H.val ⋙ wideSubcategoryInclusion _
       w := H.property },
     fun {a b} φ ↦ by
      have : IsHomLift X.p (L.map φ) (H.val.map φ).1 :=
        IsHomLift.of_fac' X.p (L.map φ) _ (Functor.congr_obj H.property a)
          (Functor.congr_obj H.property b) (Functor.congr_hom H.property φ)
      change IsCartesian X.p (L.map φ) (H.val.map φ).1
      exact (cartesianArrows_iff X.p (L.map φ) _).mp (H.val.map φ).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- VI.6.8: if `𝒳` is fibered, the objects of `lim(𝒳 ×_E D / D)` correspond bijectively to
the functors `D ⥤ 𝒳̃` over `L`. -/
noncomputable def cartesianLimitChangeOfBaseObjEquiv :
    cartesianLimit (changeOfBase X L) ≃
      {H : D ⥤ CartesianSubcategory X.p // H ⋙ cartesianSubcategoryProj X.p = L} :=
  (cartesianLimitChangeOfBaseIso X L).objEquiv.trans (transformsToCartesianEquiv X L)

end Sections

end SGA.SGA1.ExposeVI
