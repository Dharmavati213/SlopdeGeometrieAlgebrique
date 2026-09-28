/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import Mathlib.CategoryTheory.IsoCat

/-!
# SGA 1, Exposé VI, §3 and VI.6.3–6.5: fibered products over `E`

The fibered product `𝒳 ×_E 𝒴` of two categories over `E` is the strict fiber
product `BaseChange 𝒳.p 𝒴.p`, regarded over `E`. We prove its universal property
as an isomorphism of categories of `E`-functors (VI.3), and VI.6.3–6.5: a morphism
of the product is cartesian iff both components are, a functor into the product is
cartesian iff both components are (with the resulting isomorphisms of categories of
cartesian functors and of cartesian sections), and products of (pre)fibered categories
are (pre)fibered.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

section HomLift

variable {E : Type u} [Category.{v} E] {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

/-- An arrow lifts `f` along `G ⋙ p` iff its image under `G` lifts `f` along `p`. -/
theorem isHomLift_comp_iff (G : C ⥤ D) (p : D ⥤ E) {R S : E} (f : R ⟶ S)
    {a b : C} (φ : a ⟶ b) : IsHomLift (G ⋙ p) f φ ↔ IsHomLift p f (G.map φ) := by
  constructor
  · intro h
    subst_hom_lift (G ⋙ p) f φ
    exact IsHomLift.map p (G.map φ)
  · intro h
    subst_hom_lift p f (G.map φ)
    exact IsHomLift.map (G ⋙ p) φ

/-- If `φ` lifts `f` along `p` and `ψ` lifts `f` along `q`, then `φ` lifts `q ψ`. -/
theorem isHomLift_map_of_isHomLift (p : C ⥤ E) (q : D ⥤ E) {R S : E} (f : R ⟶ S)
    {a b : C} (φ : a ⟶ b) {c d : D} (ψ : c ⟶ d) [IsHomLift p f φ] [IsHomLift q f ψ] :
    IsHomLift p (q.map ψ) φ := by
  subst_hom_lift q f ψ
  infer_instance

/-- If `φ` lifts both `f` and `q ψ` along `p`, then `ψ` lifts `f` along `q`. -/
theorem isHomLift_of_isHomLift_map (p : C ⥤ E) (q : D ⥤ E) {R S : E} (f : R ⟶ S)
    {a b : C} (φ : a ⟶ b) {c d : D} (ψ : c ⟶ d) [IsHomLift p f φ]
    [h : IsHomLift p (q.map ψ) φ] : IsHomLift q f ψ := by
  subst_hom_lift p f φ
  have h₂ := IsHomLift.fac' p (q.map ψ) φ
  refine IsHomLift.of_fac' q (p.map φ) ψ (IsHomLift.domain_eq p (q.map ψ) φ).symm
    (IsHomLift.codomain_eq p (q.map ψ) φ).symm ?_
  rw [h₂]
  simp

end HomLift

variable {E : Type u} [Category.{v} E]

/-- VI.3: the fibered product `𝒳 ×_E 𝒴` of two categories over `E`, a category over `E`. -/
abbrev fiberProduct (X : BasedCategory.{v₁, u₁} E) (Y : BasedCategory.{v₂, u₂} E) :
    BasedCategory.{max v₁ v₂, max u₁ u₂} E where
  obj := BaseChange X.p Y.p
  p := BaseChange.fst X.p Y.p ⋙ X.p

namespace fiberProduct

variable {X : BasedCategory.{v₁, u₁} E} {Y : BasedCategory.{v₂, u₂} E}

/-- VI.3: the first projection `pr₁ : 𝒳 ×_E 𝒴 ⥤ 𝒳`, an `E`-functor. -/
def fst (X : BasedCategory.{v₁, u₁} E) (Y : BasedCategory.{v₂, u₂} E) :
    BasedFunctor (fiberProduct X Y) X where
  toFunctor := BaseChange.fst X.p Y.p
  w := rfl

/-- VI.3: the second projection `pr₂ : 𝒳 ×_E 𝒴 ⥤ 𝒴`, an `E`-functor. -/
def snd (X : BasedCategory.{v₁, u₁} E) (Y : BasedCategory.{v₂, u₂} E) :
    BasedFunctor (fiberProduct X Y) Y where
  toFunctor := BaseChange.snd X.p Y.p
  w := (BaseChange.condition X.p Y.p).symm

theorem isHomLift_iff {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p} (α : x ⟶ y) :
    IsHomLift (fiberProduct X Y).p f α ↔ IsHomLift X.p f α.left ∧ IsHomLift Y.p f α.right := by
  change IsHomLift (BaseChange.fst X.p Y.p ⋙ X.p) f α ↔ _
  rw [isHomLift_comp_iff]
  constructor
  · intro h
    have h' : IsHomLift X.p f α.left := h
    have := α.over
    exact ⟨h', isHomLift_of_isHomLift_map X.p Y.p f α.left α.right⟩
  · exact fun h ↦ h.1

theorem isHomLift_left {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p} (α : x ⟶ y)
    [h : IsHomLift (fiberProduct X Y).p f α] : IsHomLift X.p f α.left :=
  ((isHomLift_iff f α).mp h).1

theorem isHomLift_right {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p} (α : x ⟶ y)
    [h : IsHomLift (fiberProduct X Y).p f α] : IsHomLift Y.p f α.right :=
  ((isHomLift_iff f α).mp h).2

/-- A morphism of `𝒳 ×_E 𝒴` from two components lying over the same arrow of `E`. -/
def homMk {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    [h₁ : IsHomLift X.p f α₁] [h₂ : IsHomLift Y.p f α₂] : x ⟶ y where
  left := α₁
  right := α₂
  over := isHomLift_map_of_isHomLift X.p Y.p f α₁ α₂

@[simp] theorem homMk_left {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    [IsHomLift X.p f α₁] [IsHomLift Y.p f α₂] : (homMk f α₁ α₂).left = α₁ := rfl

@[simp] theorem homMk_right {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    [IsHomLift X.p f α₁] [IsHomLift Y.p f α₂] : (homMk f α₁ α₂).right = α₂ := rfl

instance isHomLift_homMk {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    [h₁ : IsHomLift X.p f α₁] [h₂ : IsHomLift Y.p f α₂] :
    IsHomLift (fiberProduct X Y).p f (homMk f α₁ α₂) :=
  (isHomLift_iff f _).mpr ⟨h₁, h₂⟩

/-! ### VI.3: the universal property -/

variable {Z : BasedCategory.{v₃, u₃} E}

/-- VI.3: the `E`-functor into `𝒳 ×_E 𝒴` with prescribed components. -/
def lift (F : BasedFunctor Z X) (G : BasedFunctor Z Y) : BasedFunctor Z (fiberProduct X Y) where
  toFunctor := BaseChange.lift F.toFunctor G.toFunctor (by rw [F.w, G.w])
  w := F.w

@[simp] theorem lift_fst (F : BasedFunctor Z X) (G : BasedFunctor Z Y) :
    BasedFunctor.comp (lift F G) (fst X Y) = F := rfl

@[simp] theorem lift_snd (F : BasedFunctor Z X) (G : BasedFunctor Z Y) :
    BasedFunctor.comp (lift F G) (snd X Y) = G := rfl

/-- VI.3: the functor `h ↦ (pr₁ ∘ h, pr₂ ∘ h)` on categories of `E`-functors. -/
def pairing (Z : BasedCategory.{v₃, u₃} E) :
    BasedFunctor Z (fiberProduct X Y) ⥤ BasedFunctor Z X × BasedFunctor Z Y :=
  (basedPostcomp (fst X Y)).prod' (basedPostcomp (snd X Y))

/-- VI.3: a pair of `E`-homomorphisms between the components gives an
`E`-homomorphism of functors into the product. -/
def liftNatTrans {H K : BasedFunctor Z (fiberProduct X Y)}
    (α : BasedFunctor.comp H (fst X Y) ⟶ BasedFunctor.comp K (fst X Y))
    (β : BasedFunctor.comp H (snd X Y) ⟶ BasedFunctor.comp K (snd X Y)) : H ⟶ K where
  app z := homMk (𝟙 (Z.p.obj z)) (α.app z) (β.app z) (h₁ := α.isHomLift' z)
    (h₂ := β.isHomLift' z)
  naturality {_ _} f := BaseChange.Hom.ext (α.naturality f) (β.naturality f)
  isHomLift' z := isHomLift_homMk (𝟙 (Z.p.obj z)) (α.app z) (β.app z) (h₁ := α.isHomLift' z)
    (h₂ := β.isHomLift' z)

instance : (pairing (X := X) (Y := Y) Z).Faithful where
  map_injective {H K} {α β} h := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext z
    have h₁ := congrArg (fun γ ↦ γ.1.app z) h
    have h₂ := congrArg (fun γ ↦ γ.2.app z) h
    exact BaseChange.Hom.ext h₁ h₂

instance : (pairing (X := X) (Y := Y) Z).Full where
  map_surjective {H K} γ := ⟨liftNatTrans γ.1 γ.2, Prod.ext (by ext; rfl) (by ext; rfl)⟩

/-- VI.3: `h ↦ (pr₁ ∘ h, pr₂ ∘ h)` is bijective on `E`-functors. -/
theorem pairing_obj_bijective :
    Function.Bijective (pairing (X := X) (Y := Y) Z).obj := by
  constructor
  · intro H K h
    apply basedFunctor_ext
    have h₁ := congrArg (fun γ ↦ γ.1.toFunctor) h
    have h₂ := congrArg (fun γ ↦ γ.2.toFunctor) h
    exact (BaseChange.functorEquiv X.p Y.p).injective (Subtype.ext (Prod.ext h₁ h₂))
  · intro FG
    exact ⟨lift FG.1 FG.2, rfl⟩

instance : (pairing (X := X) (Y := Y) Z).IsIso where
  bijective_obj := pairing_obj_bijective

/-- VI.3: `Hom_E(𝒵, 𝒳 ×_E 𝒴) ≅ Hom_E(𝒵, 𝒳) × Hom_E(𝒵, 𝒴)` as an isomorphism of
categories of `E`-functors. -/
noncomputable def pairingIso (Z : BasedCategory.{v₃, u₃} E) :=
  (pairing (X := X) (Y := Y) Z).asIsomorphism

/-! ### VI.6.3: cartesian morphisms of a fibered product -/

/-- VI.6.3, one direction: the first component of a cartesian morphism is cartesian. -/
theorem isCartesian_left {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p} (α : x ⟶ y)
    [hα : IsCartesian (fiberProduct X Y).p f α] : IsCartesian X.p f α.left := by
  have := isHomLift_left f α
  have := isHomLift_right f α
  refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
  have hR₂ : Y.p.obj x.val.2 = R := IsHomLift.domain_eq Y.p f α.right
  have hR₁ : X.p.obj a' = R := IsHomLift.domain_eq X.p f φ'
  -- `(a', η₂)` is an object of the product over `R`, and `(φ', α₂)` a morphism over `f`.
  let z : BaseChange X.p Y.p := ⟨(a', x.val.2), hR₁.trans hR₂.symm⟩
  let ψ : z ⟶ y := homMk f (x := z) φ' α.right
  let χ := IsCartesian.map (fiberProduct X Y).p f α ψ
  refine ⟨χ.left, ⟨isHomLift_left (𝟙 R) χ, ?_⟩, ?_⟩
  · exact congrArg BaseChange.Hom.left (IsCartesian.fac (fiberProduct X Y).p f α ψ)
  · rintro χ' ⟨hχ', hfac⟩
    have : IsHomLift Y.p (𝟙 R) (𝟙 x.val.2) := IsHomLift.id hR₂
    have := IsCartesian.map_uniq (fiberProduct X Y).p f α ψ (homMk (𝟙 R) (x := z) χ' (𝟙 _))
      (BaseChange.Hom.ext hfac (Category.id_comp _))
    exact congrArg BaseChange.Hom.left this

/-- VI.6.3, one direction: the second component of a cartesian morphism is cartesian. -/
theorem isCartesian_right {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p} (α : x ⟶ y)
    [hα : IsCartesian (fiberProduct X Y).p f α] : IsCartesian Y.p f α.right := by
  have := isHomLift_left f α
  have := isHomLift_right f α
  refine ⟨fun {a'} φ' hφ' ↦ ?_⟩
  have hR₁ : X.p.obj x.val.1 = R := IsHomLift.domain_eq X.p f α.left
  have hR₂ : Y.p.obj a' = R := IsHomLift.domain_eq Y.p f φ'
  let z : BaseChange X.p Y.p := ⟨(x.val.1, a'), hR₁.trans hR₂.symm⟩
  let ψ : z ⟶ y := homMk f (x := z) α.left φ'
  let χ := IsCartesian.map (fiberProduct X Y).p f α ψ
  refine ⟨χ.right, ⟨isHomLift_right (𝟙 R) χ, ?_⟩, ?_⟩
  · exact congrArg BaseChange.Hom.right (IsCartesian.fac (fiberProduct X Y).p f α ψ)
  · rintro χ' ⟨hχ', hfac⟩
    have : IsHomLift X.p (𝟙 R) (𝟙 x.val.1) := IsHomLift.id hR₁
    have := IsCartesian.map_uniq (fiberProduct X Y).p f α ψ (homMk (𝟙 R) (x := z) (𝟙 _) χ')
      (BaseChange.Hom.ext (Category.id_comp _) hfac)
    exact congrArg BaseChange.Hom.right this

/-- VI.6.3, the other direction: a morphism with cartesian components is cartesian. -/
theorem isCartesian_homMk {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    [h₁ : IsCartesian X.p f α₁] [h₂ : IsCartesian Y.p f α₂] :
    IsCartesian (fiberProduct X Y).p f (homMk f α₁ α₂) := by
  refine ⟨fun {z} ψ hψ ↦ ?_⟩
  have := isHomLift_left f ψ
  have := isHomLift_right f ψ
  refine ⟨homMk (𝟙 R) (IsCartesian.map X.p f α₁ ψ.left) (IsCartesian.map Y.p f α₂ ψ.right),
    ⟨inferInstance, BaseChange.Hom.ext (IsCartesian.fac X.p f α₁ ψ.left)
      (IsCartesian.fac Y.p f α₂ ψ.right)⟩, ?_⟩
  rintro χ ⟨hχ, hfac⟩
  have := isHomLift_left (𝟙 R) χ
  have := isHomLift_right (𝟙 R) χ
  exact BaseChange.Hom.ext
    (IsCartesian.map_uniq X.p f α₁ ψ.left χ.left (congrArg BaseChange.Hom.left hfac))
    (IsCartesian.map_uniq Y.p f α₂ ψ.right χ.right (congrArg BaseChange.Hom.right hfac))

/-- VI.6.3: a morphism `α = (α₁, α₂)` of `𝒳 ×_E 𝒴` is cartesian iff `α₁` and `α₂` are. -/
theorem isCartesian_iff {R S : E} (f : R ⟶ S) {x y : BaseChange X.p Y.p} (α : x ⟶ y) :
    IsCartesian (fiberProduct X Y).p f α ↔
      IsCartesian X.p f α.left ∧ IsCartesian Y.p f α.right := by
  constructor
  · intro h
    exact ⟨isCartesian_left f α, isCartesian_right f α⟩
  · rintro ⟨h₁, h₂⟩
    have : α = homMk f α.left α.right := rfl
    rw [this]
    exact isCartesian_homMk f α.left α.right

/-! ### VI.6.4: cartesian functors into a fibered product -/

/-- VI.6.4: an `E`-functor `F = (F₁, F₂)` into `𝒳 ×_E 𝒴` is cartesian iff `F₁` and `F₂` are. -/
theorem isCartesianFunctor_iff (F : BasedFunctor Z (fiberProduct X Y)) :
    IsCartesianFunctor F ↔ IsCartesianFunctor (BasedFunctor.comp F (fst X Y)) ∧
      IsCartesianFunctor (BasedFunctor.comp F (snd X Y)) := by
  constructor
  · intro h
    exact ⟨⟨fun f φ _ ↦ isCartesian_left f (F.map φ) (hα := h.map_isCartesian f φ)⟩,
      ⟨fun f φ _ ↦ isCartesian_right f (F.map φ) (hα := h.map_isCartesian f φ)⟩⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨fun f φ _ ↦ (isCartesian_iff f (F.map φ)).mpr ⟨?_, ?_⟩⟩
    · exact h₁.map_isCartesian f φ
    · exact h₂.map_isCartesian f φ

/-- VI.6.4: the pairing functor restricted to cartesian functors. -/
def cartesianPairing (Z : BasedCategory.{v₃, u₃} E) :
    CartesianFunctors Z (fiberProduct X Y) ⥤ CartesianFunctors Z X × CartesianFunctors Z Y :=
  (cartesianFunctorProperty.lift (cartesianFunctorProperty.ι ⋙ basedPostcomp (fst X Y))
      (fun F ↦ ((isCartesianFunctor_iff F.obj).mp F.property).1)).prod'
    (cartesianFunctorProperty.lift (cartesianFunctorProperty.ι ⋙ basedPostcomp (snd X Y))
      (fun F ↦ ((isCartesianFunctor_iff F.obj).mp F.property).2))

instance : (cartesianPairing (X := X) (Y := Y) Z).Faithful where
  map_injective {H K} {α β} h := by
    apply ObjectProperty.hom_ext
    apply (pairing (X := X) (Y := Y) Z).map_injective
    exact Prod.ext (congrArg (fun γ ↦ γ.1.hom) h) (congrArg (fun γ ↦ γ.2.hom) h)

instance : (cartesianPairing (X := X) (Y := Y) Z).Full where
  map_surjective γ := ⟨ObjectProperty.homMk (liftNatTrans γ.1.hom γ.2.hom), rfl⟩

instance : (cartesianPairing (X := X) (Y := Y) Z).IsIso where
  bijective_obj := by
    constructor
    · intro H K h
      have h' : (pairing (X := X) (Y := Y) Z).obj H.obj = (pairing Z).obj K.obj :=
        Prod.ext (congrArg (fun γ ↦ γ.1.obj) h) (congrArg (fun γ ↦ γ.2.obj) h)
      exact ObjectProperty.FullSubcategory.ext (pairing_obj_bijective.1 h')
    · intro FG
      refine ⟨⟨lift FG.1.obj FG.2.obj, (isCartesianFunctor_iff _).mpr ⟨FG.1.property,
        FG.2.property⟩⟩, rfl⟩

/-- VI.6.4: `Cart_E(𝒵, 𝒳 ×_E 𝒴) ≅ Cart_E(𝒵, 𝒳) × Cart_E(𝒵, 𝒴)`, an isomorphism of
categories. -/
noncomputable def cartesianPairingIso (Z : BasedCategory.{v₃, u₃} E) :=
  (cartesianPairing (X := X) (Y := Y) Z).asIsomorphism

/-- VI.6.4 with `𝒵 = E`: `lim(𝒳 ×_E 𝒴 / E) ≅ lim(𝒳/E) × lim(𝒴/E)`. -/
noncomputable def cartesianLimitIso (X : BasedCategory.{v₁, u₁} E)
    (Y : BasedCategory.{v₂, u₂} E) :=
  cartesianPairingIso (X := X) (Y := Y) (BasedCategory.ofFunctor (𝟭 E))

/-! ### VI.6.5: products of (pre)fibered categories -/

/-- VI.6.5: the fibered product of prefibered categories is prefibered. -/
instance isPreFibered [IsPreFibered X.p] [IsPreFibered Y.p] :
    IsPreFibered (fiberProduct X Y).p where
  exists_isCartesian' {x R} f := by
    obtain ⟨b₁, φ₁, hφ₁⟩ := IsPreFibered.exists_isCartesian' (p := X.p) f
    obtain ⟨b₂, φ₂, hφ₂⟩ := IsPreFibered.exists_isCartesian Y.p x.property.symm f
    have : IsHomLift X.p f φ₁ := hφ₁.toIsHomLift
    have : IsHomLift Y.p f φ₂ := hφ₂.toIsHomLift
    let b : BaseChange X.p Y.p :=
      ⟨(b₁, b₂), (IsHomLift.domain_eq X.p f φ₁).trans (IsHomLift.domain_eq Y.p f φ₂).symm⟩
    exact ⟨b, homMk f (x := b) φ₁ φ₂ (h₁ := hφ₁.toIsHomLift) (h₂ := hφ₂.toIsHomLift),
      isCartesian_homMk f (x := b) φ₁ φ₂ (h₁ := hφ₁) (h₂ := hφ₂)⟩

/-- VI.6.5: the fibered product of fibered categories is fibered. -/
instance isFibered [IsFibered X.p] [IsFibered Y.p] : IsFibered (fiberProduct X Y).p where
  comp {R S T} f g {x y z} α β hα hβ := by
    have := isCartesian_left f α
    have := isCartesian_right f α
    have := isCartesian_left g β
    have := isCartesian_right g β
    exact (isCartesian_iff (f ≫ g) (α ≫ β)).mpr ⟨(inferInstance :
      IsCartesian X.p (f ≫ g) (α.left ≫ β.left)), (inferInstance :
      IsCartesian Y.p (f ≫ g) (α.right ≫ β.right))⟩

end fiberProduct

end SGA.SGA1.ExposeVI
