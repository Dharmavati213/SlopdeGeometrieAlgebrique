/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeVI.BaseChangeCartesian
import SGA.SGA1.ExposeVI.Cofibered

/-!
# SGA 1, Exposé VI, VI.11 c): change of base of cofibered categories

The duals of VI.6.6 and VI.6.9, used in VI.11 c) ("a category `𝒳'` over `E'` … which is fibered
resp. cofibered when `𝒳` is so over `E`"): an arrow of `𝒳 ×_E D` is cocartesian iff its image in
`𝒳` is, and change of base preserves coprefibered and cofibered categories.
-/

universe v v₁ v₂ v₃ u u₁ u₂ u₃

namespace SGA.SGA1.ExposeVI

open CategoryTheory CategoryTheory.Functor

variable {E : Type u} [Category.{v} E] {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]

namespace BaseChange

variable {p : C ⥤ E} {L : D ⥤ E}

/-- VI.11 c): the image in `𝒳` of a cocartesian arrow of `𝒳 ×_E D` is cocartesian. -/
theorem isCocartesian_left_of_isCocartesian {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [hα : IsCocartesian (snd p L) f α] : IsCocartesian p (L.map f) α.left := by
  have := isHomLift_left f α
  have hα₂ : IsHomLift (𝟭 D) f α.right := (isHomLift_snd_iff f α).mp inferInstance
  refine ⟨fun {b'} φ' hφ' ↦ ?_⟩
  have hy : y.val.2 = S := IsHomLift.codomain_eq (𝟭 D) f α.right
  have hS : p.obj b' = L.obj S := IsHomLift.codomain_eq p (L.map f) φ'
  let z : BaseChange p L := ⟨(b', y.val.2), hS.trans (congrArg L.obj hy.symm)⟩
  let ψ : x ⟶ z := homOver f (y := z) φ' α.right
  have : IsHomLift (snd p L) f ψ := isHomLift_homOver f (y := z) φ' α.right
  let χ := IsCocartesian.map (snd p L) f α ψ
  have hχ : IsHomLift p (L.map (𝟙 S)) χ.left := isHomLift_left (𝟙 S) χ
  rw [L.map_id] at hχ
  refine ⟨χ.left, ⟨hχ, congrArg Hom.left (IsCocartesian.fac (snd p L) f α ψ)⟩, ?_⟩
  rintro χ' ⟨hχ', hfac⟩
  have : IsHomLift p (L.map (𝟙 S)) χ' := by rwa [L.map_id]
  have : IsHomLift (𝟭 D) (𝟙 S) (𝟙 y.val.2) := IsHomLift.id hy
  have : IsHomLift (snd p L) (𝟙 S) (homOver (𝟙 S) (y := z) χ' (𝟙 y.val.2)) :=
    isHomLift_homOver (𝟙 S) (y := z) χ' (𝟙 y.val.2)
  exact congrArg Hom.left (IsCocartesian.map_uniq (snd p L) f α ψ
    (homOver (𝟙 S) (y := z) χ' (𝟙 y.val.2)) (Hom.ext hfac (Category.comp_id _)))

/-- VI.11 c): an arrow of `𝒳 ×_E D` whose image in `𝒳` is cocartesian is cocartesian. -/
theorem isCocartesian_of_isCocartesian_left {R S : D} (f : R ⟶ S) {x y : BaseChange p L}
    (α : x ⟶ y) [hαf : IsHomLift (snd p L) f α] (h : IsCocartesian p (L.map f) α.left) :
    IsCocartesian (snd p L) f α := by
  have hα₂ : IsHomLift (𝟭 D) f α.right := (isHomLift_snd_iff f α).mp hαf
  have hy : y.val.2 = S := IsHomLift.codomain_eq (𝟭 D) f α.right
  refine ⟨fun {z} ψ hψ ↦ ?_⟩
  have : IsHomLift p (L.map f) ψ.left := isHomLift_left f ψ
  have hψ₂ : IsHomLift (𝟭 D) f ψ.right := (isHomLift_snd_iff f ψ).mp hψ
  have hz : z.val.2 = S := IsHomLift.codomain_eq (𝟭 D) f ψ.right
  let χ₁ := IsCocartesian.map p (L.map f) α.left ψ.left
  have : IsHomLift (𝟭 D) (𝟙 S) (eqToHom (hy.trans hz.symm)) :=
    IsHomLift.of_fac' (𝟭 D) _ _ hy hz (by simp)
  have : IsHomLift p (L.map (𝟙 S)) χ₁ := by
    rw [L.map_id]
    exact IsCocartesian.map_isHomLift p (L.map f) α.left ψ.left
  let χ : y ⟶ z := homOver (𝟙 S) χ₁ (eqToHom (hy.trans hz.symm))
  have : IsHomLift (snd p L) (𝟙 S) χ := isHomLift_homOver (𝟙 S) χ₁ _
  refine ⟨χ, ⟨inferInstance, ?_⟩, ?_⟩
  · apply Hom.ext
    · exact IsCocartesian.fac p (L.map f) α.left ψ.left
    · have : IsHomLift (snd p L) f (α ≫ χ) := inferInstance
      exact right_eq_of_isHomLift f (α ≫ χ) ψ
  · rintro χ' ⟨hχ', hfac⟩
    have h₁ := isHomLift_left (𝟙 S) χ'
    rw [L.map_id] at h₁
    apply Hom.ext
    · exact IsCocartesian.map_uniq p (L.map f) α.left ψ.left χ'.left
        (congrArg Hom.left hfac)
    · exact right_eq_of_isHomLift (𝟙 S) χ' χ

/-- VI.11 c): an arrow `α'` of `𝒳 ×_E D` is cocartesian iff its image `α` in `𝒳` is. -/
theorem isCocartesian_iff {R S : D} (f : R ⟶ S) {x y : BaseChange p L} (α : x ⟶ y)
    [IsHomLift (snd p L) f α] :
    IsCocartesian (snd p L) f α ↔ IsCocartesian p (L.map f) α.left :=
  ⟨fun _ ↦ isCocartesian_left_of_isCocartesian f α, isCocartesian_of_isCocartesian_left f α⟩

/-- VI.11 c): change of base preserves coprefibered categories. -/
instance isPreCofibered_snd [IsPreCofibered p] : IsPreCofibered (snd p L) where
  exists_isCocartesian' {x S} f := by
    obtain ⟨b, φ, hφ⟩ := IsPreCofibered.exists_isCocartesian p x.property (L.map f)
    have : IsHomLift p (L.map f) φ := hφ.toIsHomLift
    let y : BaseChange p L := ⟨(b, S), IsHomLift.codomain_eq p (L.map f) φ⟩
    have h₂ : IsHomLift (𝟭 D) f f := IsHomLift.map (𝟭 D) f
    have : IsHomLift (snd p L) f (homOver f (x := x) (y := y) φ f (h₂ := h₂)) :=
      isHomLift_homOver f (x := x) (y := y) φ f (h₂ := h₂)
    exact ⟨y, homOver f (x := x) (y := y) φ f (h₂ := h₂),
      isCocartesian_of_isCocartesian_left f _ hφ⟩

/-- VI.11 c): change of base preserves cofibered categories. -/
instance isCofibered_snd [IsCofibered p] : IsCofibered (snd p L) where
  comp {R S T} f g {x y z} α β hα hβ := by
    have := isCocartesian_left_of_isCocartesian f α
    have := isCocartesian_left_of_isCocartesian g β
    have h : IsCocartesian p (L.map (f ≫ g)) (α.left ≫ β.left) := by
      rw [L.map_comp]
      infer_instance
    exact isCocartesian_of_isCocartesian_left (f ≫ g) (α ≫ β) h

end BaseChange

variable {X : BasedCategory.{v₁, u₁} E} {L : D ⥤ E}

/-- VI.11 c): `𝒳 ×_E D` is coprefibered over `D` if `𝒳` is coprefibered over `E`. -/
instance changeOfBase_isPreCofibered [IsPreCofibered X.p] :
    IsPreCofibered (changeOfBase X L).p :=
  BaseChange.isPreCofibered_snd

/-- VI.11 c): `𝒳 ×_E D` is cofibered over `D` if `𝒳` is cofibered over `E`. -/
instance changeOfBase_isCofibered [IsCofibered X.p] : IsCofibered (changeOfBase X L).p :=
  BaseChange.isCofibered_snd

end SGA.SGA1.ExposeVI
