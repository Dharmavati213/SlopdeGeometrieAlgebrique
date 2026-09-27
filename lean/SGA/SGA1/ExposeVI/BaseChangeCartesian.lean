/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.Products

/-!
# SGA 1, Exposé VI, VI.6.6–6.9: change of base and cartesian morphisms

For `L : D ⥤ E` and `𝒳` over `E`, the category `𝒳' = 𝒳 ×_E D` over `D` is
`changeOfBase 𝒳 L`. We prove:

* VI.6.6: an arrow of `𝒳'` is cartesian iff its image in `𝒳` is cartesian;
* VI.6.7: change of base preserves cartesian functors, and cartesian `D`-functors
  `𝒳' ⥤ 𝒴'` correspond to the `E`-functors `𝒳 ×_E D ⥤ 𝒴` sending arrows with cartesian
  first projection to cartesian arrows;
* VI.6.8: cartesian sections of `𝒳'` over `D` form a category isomorphic to the category of
  `E`-functors `D ⥤ 𝒳` (over `L`) sending every arrow to a cartesian arrow;
* VI.6.9: change of base preserves prefibered and fibered categories.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- Every arrow of a category is cartesian for the identity functor. -/
instance isCartesian_id_functor {a b : D} (φ : a ⟶ b) : IsCartesian (𝟭 D) φ φ where
  toIsHomLift := IsHomLift.map (𝟭 D) φ
  universal_property {a'} φ' hφ' := by
    have ha' : a' = a := IsHomLift.domain_eq (𝟭 D) φ φ'
    subst ha'
    have hφ' : φ' = φ := by simpa using IsHomLift.fac' (𝟭 D) φ φ'
    subst hφ'
    refine ⟨𝟙 a', ⟨IsHomLift.map (𝟭 D) (𝟙 a'), Category.id_comp _⟩, ?_⟩
    rintro χ ⟨hχ, -⟩
    simpa using IsHomLift.fac' (𝟭 D) (𝟙 a') χ

namespace BaseChange

variable {p : C ⥤ E} {L : D ⥤ E}

theorem isHomLift_snd_iff {R S : D} (f : R ⟶ S) {x y : BaseChange p L} (α : x ⟶ y) :
    IsHomLift (snd p L) f α ↔ IsHomLift (𝟭 D) f α.right :=
  isHomLift_comp_iff (snd p L) (𝟭 D) f α

/-- A morphism of `C ×_E D` from components over `L f` and `f`. -/
def homOver {R S : D} (f : R ⟶ S) {x y : BaseChange p L} (α₁ : x.val.1 ⟶ y.val.1)
    (α₂ : x.val.2 ⟶ y.val.2) [h₁ : IsHomLift p (L.map f) α₁] [h₂ : IsHomLift (𝟭 D) f α₂] :
    x ⟶ y where
  left := α₁
  right := α₂
  over := by
    subst_hom_lift (𝟭 D) f α₂
    exact h₁

theorem isHomLift_homOver {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2) [h₁ : IsHomLift p (L.map f) α₁]
    [h₂ : IsHomLift (𝟭 D) f α₂] : IsHomLift (snd p L) f (homOver f α₁ α₂) :=
  (isHomLift_snd_iff f _).mpr h₂

/-- VI.6.6, one direction: the image in `𝒳` of a cartesian arrow of `𝒳 ×_E D` is
cartesian. -/
theorem isCartesian_left_of_isCartesian {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [hα : IsCartesian (snd p L) f α] : IsCartesian p (L.map f) α.left := by
  have := isHomLift_left f α
  have hα₂ : IsHomLift (𝟭 D) f α.right := (isHomLift_snd_iff f α).mp inferInstance
  refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
  have hx : x.val.2 = R := IsHomLift.domain_eq (𝟭 D) f α.right
  have hR : p.obj a' = L.obj R := IsHomLift.domain_eq p (L.map f) φ'
  let z : BaseChange p L := ⟨(a', x.val.2), hR.trans (congrArg L.obj hx.symm)⟩
  let ψ : z ⟶ y := homOver f (x := z) φ' α.right
  have : IsHomLift (snd p L) f ψ := isHomLift_homOver f (x := z) φ' α.right
  let χ := IsCartesian.map (snd p L) f α ψ
  have hχ : IsHomLift p (L.map (𝟙 R)) χ.left := isHomLift_left (𝟙 R) χ
  rw [L.map_id] at hχ
  refine ⟨χ.left, ⟨hχ, congrArg Hom.left (IsCartesian.fac (snd p L) f α ψ)⟩, ?_⟩
  rintro χ' ⟨hχ', hfac⟩
  have : IsHomLift p (L.map (𝟙 R)) χ' := by rwa [L.map_id]
  have : IsHomLift (𝟭 D) (𝟙 R) (𝟙 x.val.2) := IsHomLift.id hx
  have : IsHomLift (snd p L) (𝟙 R) (homOver (𝟙 R) (x := z) χ' (𝟙 x.val.2)) :=
    isHomLift_homOver (𝟙 R) (x := z) χ' (𝟙 x.val.2)
  exact congrArg Hom.left (IsCartesian.map_uniq (snd p L) f α ψ
    (homOver (𝟙 R) (x := z) χ' (𝟙 x.val.2)) (Hom.ext hfac (Category.id_comp _)))

/-- VI.6.6, other direction: an arrow of `𝒳 ×_E D` whose image in `𝒳` is cartesian is
cartesian. -/
theorem isCartesian_of_isCartesian_left {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [hαf : IsHomLift (snd p L) f α] (h : IsCartesian p (L.map f) α.left) :
    IsCartesian (snd p L) f α := by
  have hα₂ : IsHomLift (𝟭 D) f α.right := (isHomLift_snd_iff f α).mp hαf
  have hx : x.val.2 = R := IsHomLift.domain_eq (𝟭 D) f α.right
  refine ⟨fun {z} ψ hψ ↦ ?_⟩
  have : IsHomLift p (L.map f) ψ.left := isHomLift_left f ψ
  have hψ₂ : IsHomLift (𝟭 D) f ψ.right := (isHomLift_snd_iff f ψ).mp hψ
  have hz : z.val.2 = R := IsHomLift.domain_eq (𝟭 D) f ψ.right
  let χ₁ := IsCartesian.map p (L.map f) α.left ψ.left
  have : IsHomLift p (L.map (eqToHom (hz.trans hx.symm))) χ₁ := by
    rw [eqToHom_map]
    have : IsHomLift p (eqToHom (congrArg L.obj hz) ≫ 𝟙 (L.obj R) ≫
      eqToHom (congrArg L.obj hx.symm)) χ₁ := inferInstance
    simpa using this
  have : IsHomLift (𝟭 D) (𝟙 R) (eqToHom (hz.trans hx.symm)) :=
    IsHomLift.of_fac' (𝟭 D) _ _ hz hx (by simp)
  have : IsHomLift p (L.map (𝟙 R)) χ₁ := by
    rw [L.map_id]
    exact IsCartesian.map_isHomLift p (L.map f) α.left ψ.left
  let χ : z ⟶ x := homOver (𝟙 R) χ₁ (eqToHom (hz.trans hx.symm))
  have : IsHomLift (snd p L) (𝟙 R) χ := isHomLift_homOver (𝟙 R) χ₁ _
  refine ⟨χ, ⟨inferInstance, ?_⟩, ?_⟩
  · apply Hom.ext
    · exact IsCartesian.fac p (L.map f) α.left ψ.left
    · have : IsHomLift (snd p L) f (χ ≫ α) := inferInstance
      exact right_eq_of_isHomLift f (χ ≫ α) ψ
  · rintro χ' ⟨hχ', hfac⟩
    have h₁ := isHomLift_left (𝟙 R) χ'
    rw [L.map_id] at h₁
    apply Hom.ext
    · exact IsCartesian.map_uniq p (L.map f) α.left ψ.left χ'.left
        (congrArg Hom.left hfac)
    · exact right_eq_of_isHomLift (𝟙 R) χ' χ

/-- VI.6.6: an arrow `α'` of `𝒳 ×_E D` is cartesian iff its image `α` in `𝒳` is. -/
theorem isCartesian_iff {R S : D} (f : R ⟶ S) {x y : BaseChange p L} (α : x ⟶ y)
    [IsHomLift (snd p L) f α] : IsCartesian (snd p L) f α ↔ IsCartesian p (L.map f) α.left :=
  ⟨fun _ ↦ isCartesian_left_of_isCartesian f α, isCartesian_of_isCartesian_left f α⟩

/-- VI.6.6, with the base arrow read off from the arrow itself. -/
theorem isCartesian_iff' {x y : BaseChange p L} (α : x ⟶ y) :
    IsCartesian (snd p L) α.right α ↔ IsCartesian p (L.map α.right) α.left :=
  have : IsHomLift (snd p L) α.right α := IsHomLift.map (snd p L) α
  isCartesian_iff α.right α

/-- VI.6.9: change of base preserves prefibered categories. -/
instance isPreFibered_snd [IsPreFibered p] : IsPreFibered (snd p L) where
  exists_isCartesian' {x R} f := by
    obtain ⟨b, φ, hφ⟩ := IsPreFibered.exists_isCartesian p x.property (L.map f)
    have : IsHomLift p (L.map f) φ := hφ.toIsHomLift
    let y : BaseChange p L := ⟨(b, R), IsHomLift.domain_eq p (L.map f) φ⟩
    have h₂ : IsHomLift (𝟭 D) f f := IsHomLift.map (𝟭 D) f
    have : IsHomLift (snd p L) f (homOver f (x := y) (y := x) φ f (h₂ := h₂)) :=
      isHomLift_homOver f (x := y) (y := x) φ f (h₂ := h₂)
    exact ⟨y, homOver f (x := y) (y := x) φ f (h₂ := h₂), isCartesian_of_isCartesian_left f _ hφ⟩

/-- VI.6.9: change of base preserves fibered categories. -/
instance isFibered_snd [IsFibered p] : IsFibered (snd p L) where
  comp {R S T} f g {x y z} α β hα hβ := by
    have := isCartesian_left_of_isCartesian f α
    have := isCartesian_left_of_isCartesian g β
    have h : IsCartesian p (L.map (f ≫ g)) (α.left ≫ β.left) := by
      rw [L.map_comp]
      infer_instance
    exact isCartesian_of_isCartesian_left (f ≫ g) (α ≫ β) h

end BaseChange

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₃, u₃} E} {L : D ⥤ E}

/-- VI.6.6: an arrow of `𝒳' = 𝒳 ×_E D` over `f` is cartesian iff its image in `𝒳`
(an arrow over `L f`) is cartesian. -/
theorem changeOfBase_isCartesian_iff {R S : D} (f : R ⟶ S) {x y : BaseChange X.p L}
    (α : x ⟶ y) [IsHomLift (changeOfBase X L).p f α] :
    IsCartesian (changeOfBase X L).p f α ↔ IsCartesian X.p (L.map f) α.left :=
  BaseChange.isCartesian_iff f α

/-- VI.6.9: `𝒳 ×_E D` is prefibered over `D` if `𝒳` is prefibered over `E`. -/
instance changeOfBase_isPreFibered [IsPreFibered X.p] : IsPreFibered (changeOfBase X L).p :=
  BaseChange.isPreFibered_snd

/-- VI.6.9: `𝒳 ×_E D` is fibered over `D` if `𝒳` is fibered over `E`. -/
instance changeOfBase_isFibered [IsFibered X.p] : IsFibered (changeOfBase X L).p :=
  BaseChange.isFibered_snd

/-- VI.6.7: change of base of a cartesian functor is cartesian. -/
theorem isCartesianFunctor_changeOfBaseMap (F : BasedFunctor X Y) [hF : IsCartesianFunctor F]
    (L : D ⥤ E) : IsCartesianFunctor (changeOfBaseMap F L) where
  map_isCartesian {R S a b} f φ hφ := by
    have := BaseChange.isCartesian_left_of_isCartesian f φ
    have h : IsCartesian Y.p (L.map f) (F.map φ.left) := hF.map_isCartesian (L.map f) φ.left
    have : IsHomLift (BaseChange.snd Y.p L) f ((changeOfBaseMap F L).map φ) :=
      BasedFunctor.preserves_isHomLift (changeOfBaseMap F L) f φ
    exact BaseChange.isCartesian_of_isCartesian_left f _ h

/-- VI.6.7: change of base as a functor `Cart_E(𝒳, 𝒴) ⥤ Cart_D(𝒳', 𝒴')`. -/
def changeOfBaseCartesian (L : D ⥤ E) :
    CartesianFunctors X Y ⥤ CartesianFunctors (changeOfBase X L) (changeOfBase Y L) :=
  cartesianFunctorProperty.lift (cartesianFunctorProperty.ι ⋙ changeOfBaseHom L)
    (fun F ↦ isCartesianFunctor_changeOfBaseMap F.obj L (hF := F.property))

/-- VI.6.7: under the isomorphism `Hom_D(𝒳', 𝒴') ≅ Hom_E(𝒳 ×_E D, 𝒴)` of VI.3, the
cartesian `D`-functors are those whose transpose sends every arrow with cartesian first
projection to a cartesian arrow. -/
theorem isCartesianFunctor_iff_transpose (H : BasedFunctor (changeOfBase X L) (changeOfBase Y L)) :
    IsCartesianFunctor H ↔ ∀ {x y : BaseChange X.p L} (α : x ⟶ y),
      IsCartesian X.p (L.map α.right) α.left →
        IsCartesian Y.p (L.map α.right) (((changeOfBaseTranspose _ Y L).obj H).map α) := by
  constructor
  · intro hH x y α hα
    have := (BaseChange.isCartesian_iff' α).mpr hα
    have := hH.map_isCartesian α.right α
    exact BaseChange.isCartesian_left_of_isCartesian α.right (H.map α)
  · intro h
    refine ⟨fun {R S a b} f φ hφ ↦ ?_⟩
    subst_hom_lift (BaseChange.snd X.p L) f φ
    have : IsCartesian (BaseChange.snd X.p L) φ.right φ := hφ
    have hφ' := BaseChange.isCartesian_left_of_isCartesian (L := L) φ.right φ
    have : IsHomLift (BaseChange.snd Y.p L) φ.right (H.map φ) :=
      (H.isHomLift_iff φ.right φ).mpr (IsHomLift.map (BaseChange.snd X.p L) φ)
    exact BaseChange.isCartesian_of_isCartesian_left φ.right (H.map φ) (h φ hφ')

section Sections

variable (Y L)

/-- VI.6.8: an `E`-functor `D ⥤ 𝒴` over `L` sends every arrow to a cartesian arrow. -/
def TransformsToCartesian : ObjectProperty
    (BasedFunctor (restrictBase (BasedCategory.ofFunctor (𝟭 D)) L) Y) :=
  fun H ↦ ∀ {a b : D} (φ : a ⟶ b), IsCartesian Y.p (L.map φ) (H.map φ)

theorem isCartesianFunctor_iff_transformsToCartesian
    (s : BasedFunctor (BasedCategory.ofFunctor (𝟭 D)) (changeOfBase Y L)) :
    IsCartesianFunctor s ↔ TransformsToCartesian Y L
      ((changeOfBaseTranspose (BasedCategory.ofFunctor (𝟭 D)) Y L).obj s) := by
  constructor
  · intro hs a b φ
    have : IsCartesian (BasedCategory.ofFunctor (𝟭 D)).p φ φ := isCartesian_id_functor φ
    have := hs.map_isCartesian φ φ
    exact BaseChange.isCartesian_left_of_isCartesian φ (s.map φ)
  · intro h
    refine ⟨fun {R S a b} f φ hφ ↦ ?_⟩
    have : IsHomLift (𝟭 D) f φ := hφ.toIsHomLift
    subst_hom_lift (𝟭 D) f φ
    have hs : IsHomLift (BaseChange.snd Y.p L) φ (s.map φ) :=
      (s.isHomLift_iff φ φ).mpr (IsHomLift.map (𝟭 D) φ)
    exact BaseChange.isCartesian_of_isCartesian_left φ (s.map φ) (hαf := hs) (h φ)

/-- VI.6.8: `lim(𝒴'/D)`, the category of cartesian sections of `𝒴' = 𝒴 ×_E D` over `D`,
is isomorphic to the full subcategory of `E`-functors `D ⥤ 𝒴` (over `L`) that send every
arrow to a cartesian arrow. -/
noncomputable def cartesianLimitChangeOfBaseIso :
    IsoCat (cartesianLimit (changeOfBase Y L)) (TransformsToCartesian Y L).FullSubcategory :=
  haveI := ObjectProperty.isIso_lift_of_isIso (changeOfBaseTranspose _ Y L)
    (cartesianFunctorProperty (X := BasedCategory.ofFunctor (𝟭 D)) (Y := changeOfBase Y L))
    (TransformsToCartesian Y L) (isCartesianFunctor_iff_transformsToCartesian Y L)
  ((TransformsToCartesian Y L).lift
    ((cartesianFunctorProperty (X := BasedCategory.ofFunctor (𝟭 D))
      (Y := changeOfBase Y L)).ι ⋙ changeOfBaseTranspose _ Y L)
    (fun s ↦ (isCartesianFunctor_iff_transformsToCartesian Y L s.obj).mp s.property)
    ).asIsomorphism

end Sections

end SGA.SGA1.ExposeVI
