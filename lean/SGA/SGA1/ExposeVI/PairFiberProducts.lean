/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.BaseChange
import SGA.SGA1.ExposeVI.Cartesian
import SGA.SGA1.ExposeVI.CartesianFunctors
import SGA.SGA1.ExposeVI.Fibered
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.EqToHom

/-!
# SGA 1, Exposé VI, VI.6.3–6.5: fiber products over a common base

* VI.6.3: a morphism in a strict fiber product is cartesian iff both components are
  (`fiberProduct.isCartesian_iff`), with the `IsHomLift` projection/`iff` lemmas.
* VI.6.4: a based functor into a fiber product is cartesian iff both projections are.
* VI.6.5: the fiber product of (pre)fibered categories is (pre)fibered.

Change-of-base cartesian / (pre)fibered results (VI.6.6–6.9) live in
`ChangeOfBaseFibered.lean`.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E]
  {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]

abbrev fiberProduct (p₁ : C₁ ⥤ E) (p₂ : C₂ ⥤ E) := BaseChange p₁ p₂

def fiberProductProj (p₁ : C₁ ⥤ E) (p₂ : C₂ ⥤ E) : fiberProduct p₁ p₂ ⥤ E :=
  BaseChange.fst p₁ p₂ ⋙ p₁

namespace fiberProduct

variable {p₁ : C₁ ⥤ E} {p₂ : C₂ ⥤ E}

set_option linter.style.haveILetI false

theorem isHomLift_left {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α : x ⟶ y) [IsHomLift (fiberProductProj p₁ p₂) f α] :
    IsHomLift p₁ f α.left := by
  have h := IsHomLift.fac' (fiberProductProj p₁ p₂) f α
  change p₁.map α.left =
      eqToHom (IsHomLift.domain_eq (fiberProductProj p₁ p₂) f α) ≫ f ≫
        eqToHom (IsHomLift.codomain_eq (fiberProductProj p₁ p₂) f α).symm at h
  exact IsHomLift.of_fac' p₁ f α.left
    (IsHomLift.domain_eq (fiberProductProj p₁ p₂) f α)
    (IsHomLift.codomain_eq (fiberProductProj p₁ p₂) f α) h

theorem isHomLift_right {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α : x ⟶ y) [IsHomLift (fiberProductProj p₁ p₂) f α] :
    IsHomLift p₂ f α.right := by
  haveI h₁ : IsHomLift p₁ f α.left := isHomLift_left f α
  haveI : IsHomLift p₁ (p₂.map α.right) α.left := α.over
  refine IsHomLift.of_fac' p₂ f α.right
    (x.property.symm.trans (IsHomLift.domain_eq p₁ f α.left))
    (y.property.symm.trans (IsHomLift.codomain_eq p₁ f α.left)) ?_
  have hleft := IsHomLift.fac' p₁ f α.left
  have hover := IsHomLift.fac p₁ (p₂.map α.right) α.left
  calc
    p₂.map α.right =
        eqToHom (IsHomLift.domain_eq p₁ (p₂.map α.right) α.left).symm ≫
          p₁.map α.left ≫
            eqToHom (IsHomLift.codomain_eq p₁ (p₂.map α.right) α.left) := hover
    _ = eqToHom (IsHomLift.domain_eq p₁ (p₂.map α.right) α.left).symm ≫
          (eqToHom (IsHomLift.domain_eq p₁ f α.left) ≫ f ≫
            eqToHom (IsHomLift.codomain_eq p₁ f α.left).symm) ≫
            eqToHom (IsHomLift.codomain_eq p₁ (p₂.map α.right) α.left) := by
              rw [hleft]
    _ = eqToHom (x.property.symm.trans (IsHomLift.domain_eq p₁ f α.left)) ≫ f ≫
          eqToHom (y.property.symm.trans (IsHomLift.codomain_eq p₁ f α.left)).symm := by
            simp [eqToHom_trans, eqToHom_trans_assoc, Category.assoc]

theorem isHomLift_iff {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂} (α : x ⟶ y) :
    IsHomLift (fiberProductProj p₁ p₂) f α ↔
      IsHomLift p₁ f α.left ∧ IsHomLift p₂ f α.right := by
  constructor
  · intro h
    haveI := h
    exact ⟨isHomLift_left f α, isHomLift_right f α⟩
  · rintro ⟨h₁, _⟩
    have h := @IsHomLift.fac' _ _ _ _ p₁ _ _ _ _ f α.left h₁
    exact IsHomLift.of_fac' (fiberProductProj p₁ p₂) f α
      (@IsHomLift.domain_eq _ _ _ _ p₁ _ _ _ _ f α.left h₁)
      (@IsHomLift.codomain_eq _ _ _ _ p₁ _ _ _ _ f α.left h₁)
      (by change p₁.map α.left = _; exact h)

def homMk {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    (h₁ : IsHomLift p₁ f α₁) (h₂ : IsHomLift p₂ f α₂) : x ⟶ y where
  left := α₁
  right := α₂
  over := by
    haveI := h₁
    haveI := h₂
    refine IsHomLift.of_fac' p₁ (p₂.map α₂) α₁ x.property y.property ?_
    have hleft := IsHomLift.fac' p₁ f α₁
    have hright := IsHomLift.fac' p₂ f α₂
    have hd₁ := IsHomLift.domain_eq p₁ f α₁
    have hc₁ := IsHomLift.codomain_eq p₁ f α₁
    subst hd₁; subst hc₁
    simp [hleft, hright, eqToHom_trans, eqToHom_trans_assoc, Category.assoc]

theorem isCartesian_left {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α : x ⟶ y) [hα : IsCartesian (fiberProductProj p₁ p₂) f α] :
    IsCartesian p₁ f α.left := by
  haveI : IsHomLift (fiberProductProj p₁ p₂) f α := hα.toIsHomLift
  have hα₁ : IsHomLift p₁ f α.left := isHomLift_left f α
  have hα₂ : IsHomLift p₂ f α.right := isHomLift_right f α
  refine ⟨?_⟩
  intro a' φ' hφ'
  have hR₂ : p₂.obj x.val.2 = R := IsHomLift.domain_eq p₂ f α.right
  have hR₁ : p₁.obj a' = R := IsHomLift.domain_eq p₁ f φ'
  let z : fiberProduct p₁ p₂ := ⟨(a', x.val.2), hR₁.trans hR₂.symm⟩
  let ψ : z ⟶ y := homMk f φ' α.right hφ' hα₂
  haveI : IsHomLift (fiberProductProj p₁ p₂) f ψ :=
    (isHomLift_iff f _).mpr ⟨hφ', hα₂⟩
  let χFull := IsCartesian.map (fiberProductProj p₁ p₂) f α ψ
  refine ⟨χFull.left, ⟨isHomLift_left (𝟙 R) χFull, ?_⟩, ?_⟩
  · exact congrArg BaseChange.Hom.left (IsCartesian.fac (fiberProductProj p₁ p₂) f α ψ)
  · intro χ ⟨hχ, hfac⟩
    let χLift : z ⟶ x :=
      homMk (𝟙 R) χ (𝟙 x.val.2) hχ (IsHomLift.id hR₂)
    haveI : IsHomLift (fiberProductProj p₁ p₂) (𝟙 R) χLift :=
      (isHomLift_iff (𝟙 R) _).mpr ⟨hχ, IsHomLift.id hR₂⟩
    have hfacLift : χLift ≫ α = ψ := by
      apply BaseChange.Hom.ext
      · exact hfac
      · change (𝟙 x.val.2) ≫ α.right = α.right
        rw [Category.id_comp]
    exact congrArg BaseChange.Hom.left
      (IsCartesian.map_uniq (fiberProductProj p₁ p₂) f α ψ χLift hfacLift)

theorem isCartesian_right {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α : x ⟶ y) [hα : IsCartesian (fiberProductProj p₁ p₂) f α] :
    IsCartesian p₂ f α.right := by
  haveI : IsHomLift (fiberProductProj p₁ p₂) f α := hα.toIsHomLift
  have hα₁ : IsHomLift p₁ f α.left := isHomLift_left f α
  have hα₂ : IsHomLift p₂ f α.right := isHomLift_right f α
  refine ⟨?_⟩
  intro a' φ' hφ'
  have hR₁ : p₁.obj x.val.1 = R := IsHomLift.domain_eq p₁ f α.left
  have hR₂ : p₂.obj a' = R := IsHomLift.domain_eq p₂ f φ'
  let z : fiberProduct p₁ p₂ := ⟨(x.val.1, a'), hR₁.trans hR₂.symm⟩
  let ψ : z ⟶ y := homMk f α.left φ' hα₁ hφ'
  haveI : IsHomLift (fiberProductProj p₁ p₂) f ψ :=
    (isHomLift_iff f _).mpr ⟨hα₁, hφ'⟩
  let χFull := IsCartesian.map (fiberProductProj p₁ p₂) f α ψ
  refine ⟨χFull.right, ⟨isHomLift_right (𝟙 R) χFull, ?_⟩, ?_⟩
  · exact congrArg BaseChange.Hom.right (IsCartesian.fac (fiberProductProj p₁ p₂) f α ψ)
  · intro χ ⟨hχ, hfac⟩
    let χLift : z ⟶ x :=
      homMk (𝟙 R) (𝟙 x.val.1) χ (IsHomLift.id hR₁) hχ
    haveI : IsHomLift (fiberProductProj p₁ p₂) (𝟙 R) χLift :=
      (isHomLift_iff (𝟙 R) _).mpr ⟨IsHomLift.id hR₁, hχ⟩
    have hfacLift : χLift ≫ α = ψ := by
      apply BaseChange.Hom.ext
      · change (𝟙 x.val.1) ≫ α.left = α.left
        rw [Category.id_comp]
      · exact hfac
    exact congrArg BaseChange.Hom.right
      (IsCartesian.map_uniq (fiberProductProj p₁ p₂) f α ψ χLift hfacLift)

theorem isCartesian_homMk {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α₁ : x.val.1 ⟶ y.val.1) (α₂ : x.val.2 ⟶ y.val.2)
    (h₁ : IsCartesian p₁ f α₁) (h₂ : IsCartesian p₂ f α₂) :
    IsCartesian (fiberProductProj p₁ p₂) f
      (homMk f α₁ α₂ h₁.toIsHomLift h₂.toIsHomLift) := by
  let α := homMk f α₁ α₂ h₁.toIsHomLift h₂.toIsHomLift
  haveI : IsHomLift (fiberProductProj p₁ p₂) f α :=
    (isHomLift_iff f _).mpr ⟨h₁.toIsHomLift, h₂.toIsHomLift⟩
  refine ⟨?_⟩
  intro z ψ hψ
  have hψ₁ := isHomLift_left f ψ
  have hψ₂ := isHomLift_right f ψ
  haveI := hψ₁; haveI := h₁
  haveI := hψ₂; haveI := h₂
  let χ₁ := IsCartesian.map p₁ f α₁ ψ.left
  let χ₂ := IsCartesian.map p₂ f α₂ ψ.right
  have hχ₁ : IsHomLift p₁ (𝟙 R) χ₁ := inferInstance
  have hχ₂ : IsHomLift p₂ (𝟙 R) χ₂ := inferInstance
  let χ := homMk (𝟙 R) χ₁ χ₂ hχ₁ hχ₂
  haveI : IsHomLift (fiberProductProj p₁ p₂) (𝟙 R) χ :=
    (isHomLift_iff (𝟙 R) _).mpr ⟨hχ₁, hχ₂⟩
  refine ⟨χ, ⟨inferInstance, ?_⟩, ?_⟩
  · apply BaseChange.Hom.ext
    · exact IsCartesian.fac p₁ f α₁ ψ.left
    · exact IsCartesian.fac p₂ f α₂ ψ.right
  · intro χ' ⟨hχ', hfac'⟩
    have hχ'₁ := isHomLift_left (𝟙 R) χ'
    have hχ'₂ := isHomLift_right (𝟙 R) χ'
    haveI := hχ'₁; haveI := hχ'₂
    have hl : χ'.left ≫ α₁ = ψ.left := congrArg BaseChange.Hom.left hfac'
    have hr : χ'.right ≫ α₂ = ψ.right := congrArg BaseChange.Hom.right hfac'
    apply BaseChange.Hom.ext
    · exact IsCartesian.map_uniq p₁ f α₁ ψ.left χ'.left hl
    · exact IsCartesian.map_uniq p₂ f α₂ ψ.right χ'.right hr

theorem isCartesian_iff {R S : E} (f : R ⟶ S) {x y : fiberProduct p₁ p₂}
    (α : x ⟶ y) [IsHomLift (fiberProductProj p₁ p₂) f α] :
    IsCartesian (fiberProductProj p₁ p₂) f α ↔
      IsCartesian p₁ f α.left ∧ IsCartesian p₂ f α.right := by
  constructor
  · intro h
    haveI := h
    exact ⟨isCartesian_left f α, isCartesian_right f α⟩
  · rintro ⟨h₁, h₂⟩
    have hα₁ := isHomLift_left f α
    have hα₂ := isHomLift_right f α
    have : α = homMk f α.left α.right hα₁ hα₂ := BaseChange.Hom.ext rfl rfl
    rw [this]
    exact isCartesian_homMk f α.left α.right h₁ h₂

instance instIsPreFibered [IsPreFibered p₁] [IsPreFibered p₂] :
    IsPreFibered (fiberProductProj p₁ p₂) where
  exists_isCartesian' {x R} f := by
    obtain ⟨b₁, φ₁, hφ₁⟩ := IsPreFibered.exists_isCartesian' (p := p₁) f
    obtain ⟨b₂, φ₂, hφ₂⟩ :=
      IsPreFibered.exists_isCartesian p₂ x.property.symm f
    have hb₁ : p₁.obj b₁ = R :=
      @IsHomLift.domain_eq _ _ _ _ p₁ _ _ _ _ f φ₁ hφ₁.toIsHomLift
    have hb₂ : p₂.obj b₂ = R :=
      @IsHomLift.domain_eq _ _ _ _ p₂ _ _ _ _ f φ₂ hφ₂.toIsHomLift
    let b : fiberProduct p₁ p₂ := ⟨(b₁, b₂), hb₁.trans hb₂.symm⟩
    let ψ := homMk (x := b) (y := x) f φ₁ φ₂ hφ₁.toIsHomLift hφ₂.toIsHomLift
    exact ⟨b, ψ, isCartesian_homMk (x := b) (y := x) f φ₁ φ₂ hφ₁ hφ₂⟩

instance instIsFibered [IsFibered p₁] [IsFibered p₂] :
    IsFibered (fiberProductProj p₁ p₂) where
  comp {R S T} f g {x y z} α β hα hβ := by
    haveI := hα; haveI := hβ
    have hα₁ := isCartesian_left f α
    have hα₂ := isCartesian_right f α
    have hβ₁ := isCartesian_left g β
    have hβ₂ := isCartesian_right g β
    haveI := hα₁; haveI := hβ₁
    haveI := hα₂; haveI := hβ₂
    have h₁ : IsCartesian p₁ (f ≫ g) (α.left ≫ β.left) := inferInstance
    have h₂ : IsCartesian p₂ (f ≫ g) (α.right ≫ β.right) := inferInstance
    have : α ≫ β =
        homMk (f ≫ g) (α.left ≫ β.left) (α.right ≫ β.right)
          h₁.toIsHomLift h₂.toIsHomLift := BaseChange.Hom.ext rfl rfl
    rw [this]
    exact isCartesian_homMk (f ≫ g) _ _ h₁ h₂

end fiberProduct

/-! ### VI.6.4: cartesian functors into a fiber product -/

variable {p₁ : C₁ ⥤ E} {p₂ : C₂ ⥤ E}

def basedFunctorFiberProductFst {X : BasedCategory.{v₃, u₃} E}
    (F : BasedFunctor X (BasedCategory.ofFunctor (fiberProductProj p₁ p₂))) :
    BasedFunctor X (BasedCategory.ofFunctor p₁) where
  toFunctor := F.toFunctor ⋙ BaseChange.fst p₁ p₂
  w := F.w

def basedFunctorFiberProductSnd {X : BasedCategory.{v₃, u₃} E}
    (F : BasedFunctor X (BasedCategory.ofFunctor (fiberProductProj p₁ p₂))) :
    BasedFunctor X (BasedCategory.ofFunctor p₂) where
  toFunctor := F.toFunctor ⋙ BaseChange.snd p₁ p₂
  w :=
    (congrArg (F.toFunctor ⋙ ·) (BaseChange.condition p₁ p₂).symm).trans F.w

set_option linter.style.haveILetI false in
theorem isCartesianFunctor_fiberProduct_iff {X : BasedCategory.{v₃, u₃} E}
    (F : BasedFunctor X (BasedCategory.ofFunctor (fiberProductProj p₁ p₂))) :
    IsCartesianFunctor F ↔
      IsCartesianFunctor (basedFunctorFiberProductFst F) ∧
        IsCartesianFunctor (basedFunctorFiberProductSnd F) := by
  constructor
  · intro h
    constructor
    · exact ⟨fun {R S a b} f φ hφ => by
        haveI := hφ
        haveI : IsCartesian (fiberProductProj p₁ p₂) f (F.map φ) :=
          h.map_isCartesian f φ
        exact fiberProduct.isCartesian_left f (F.map φ)⟩
    · exact ⟨fun {R S a b} f φ hφ => by
        haveI := hφ
        haveI : IsCartesian (fiberProductProj p₁ p₂) f (F.map φ) :=
          h.map_isCartesian f φ
        exact fiberProduct.isCartesian_right f (F.map φ)⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun {R S a b} f φ hφ => by
      haveI := hφ
      have hL : IsCartesian p₁ f (F.map φ).left := by
        change IsCartesian p₁ f ((basedFunctorFiberProductFst F).map φ)
        exact h₁.map_isCartesian f φ
      have hR : IsCartesian p₂ f (F.map φ).right := by
        change IsCartesian p₂ f ((basedFunctorFiberProductSnd F).map φ)
        exact h₂.map_isCartesian f φ
      haveI : IsHomLift (fiberProductProj p₁ p₂) f (F.map φ) :=
        BasedFunctor.preserves_isHomLift F f φ
      exact (fiberProduct.isCartesian_iff f (F.map φ)).mpr ⟨hL, hR⟩⟩

end SGA.SGA1.ExposeVI
