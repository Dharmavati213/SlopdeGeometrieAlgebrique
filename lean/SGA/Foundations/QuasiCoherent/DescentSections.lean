/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiCoherent.DescentLocalizing

/-!
# Descent condition for sections on `S' ×_S S'`

For a descent datum `D` relative to `g : S' ⟶ S`, the condition `IsDescentSection D W s` (for all
pairs `f₁, f₂` with `f₁ ≫ g = f₂ ≫ g`) follows from the condition for the two projections
`S' ×_S S' ⟶ S'` (`isDescentSection_of_fst_snd`). For the descent datum of an inverse image
`g^* G`, the descent isomorphisms are the canonical ones (`descentHom_toDescentData`), so a
section of `g^* G` whose two inverse images to `S' ×_S S'` agree in `(g ∘ pr₁)^* G` is compatible
with the descent datum (`isDescentSection_toDescentData`). Used for SGA 1 VIII.1.7.
-/

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {S S' : Scheme.{u}} {g : S' ⟶ S} (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))

/-- The descent condition for a section, pulled back along `u`, from the pair `(f₁, f₂)` to the
pair `(u ≫ f₁, u ≫ f₂)`. -/
lemma isDescentSection_comp {Y Y' : Scheme.{u}} (u : Y' ⟶ Y) (f₁ f₂ : Y ⟶ S')
    (h : f₁ ≫ g = f₂ ≫ g) (h' : (u ≫ f₁) ≫ g = (u ≫ f₂) ≫ g) (W : S.Opens)
    (s : Γ(descentObj D, g ⁻¹ᵁ W))
    (hs : (descentHom D f₁ f₂ h).app (f₁ ⁻¹ᵁ g ⁻¹ᵁ W) (pullbackApp f₁ (descentObj D) (g ⁻¹ᵁ W) s) =
      ((Scheme.Modules.pullback f₂).obj (descentObj D)).presheaf.map
        (homOfLE (preimage_le_of_comp_eq h W)).op (pullbackApp f₂ (descentObj D) (g ⁻¹ᵁ W) s)) :
    (descentHom D (u ≫ f₁) (u ≫ f₂) h').app ((u ≫ f₁) ⁻¹ᵁ g ⁻¹ᵁ W)
        (pullbackApp (u ≫ f₁) (descentObj D) (g ⁻¹ᵁ W) s) =
      ((Scheme.Modules.pullback (u ≫ f₂)).obj (descentObj D)).presheaf.map
        (homOfLE (preimage_le_of_comp_eq h' W)).op
        (pullbackApp (u ≫ f₂) (descentObj D) (g ⁻¹ᵁ W) s) := by
  rw [← descentHom_pull D u f₁ f₂ h h', Hom.comp_app_apply, Hom.comp_app_apply,
    pullbackCompIso'_rfl_hom_app]
  have e₁ := pullbackApp_naturality u (descentHom D f₁ f₂ h) (f₁ ⁻¹ᵁ g ⁻¹ᵁ W)
    (pullbackApp f₁ (descentObj D) (g ⁻¹ᵁ W) s)
  refine (congrArg ((pullbackCompIso' u f₂ (u ≫ f₂) rfl (descentObj D)).inv.app _)
    e₁.symm).trans ?_
  rw [hs, pullbackApp_map, Hom.app_map]
  have e₂ := pullbackCompIso'_rfl_inv_app u f₂ (descentObj D) (g ⁻¹ᵁ W) s
  refine (congrArg _ e₂).trans ?_
  exact presheaf_map_subsingleton _ _ _ _

/-- A section is compatible with the descent datum as soon as it is so for the two projections
`S' ×_S S' ⟶ S'`. -/
lemma isDescentSection_of_fst_snd (W : S.Opens) (s : Γ(descentObj D, g ⁻¹ᵁ W))
    (hs : (descentHom D (Limits.pullback.fst g g) (Limits.pullback.snd g g)
        Limits.pullback.condition).app _
        (pullbackApp (Limits.pullback.fst g g) (descentObj D) (g ⁻¹ᵁ W) s) =
      ((Scheme.Modules.pullback (Limits.pullback.snd g g)).obj (descentObj D)).presheaf.map
        (homOfLE (preimage_le_of_comp_eq Limits.pullback.condition W)).op
        (pullbackApp (Limits.pullback.snd g g) (descentObj D) (g ⁻¹ᵁ W) s)) :
    IsDescentSection D W s := by
  intro Y f₁ f₂ h
  obtain ⟨u, rfl, rfl⟩ : ∃ u : Y ⟶ Limits.pullback g g, f₁ = u ≫ Limits.pullback.fst g g ∧
      f₂ = u ≫ Limits.pullback.snd g g :=
    ⟨Limits.pullback.lift f₁ f₂ h, (Limits.pullback.lift_fst _ _ _).symm,
      (Limits.pullback.lift_snd _ _ _).symm⟩
  exact isDescentSection_comp D u _ _ Limits.pullback.condition h W s hs

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum of an inverse image `g^* G` is given by the canonical isomorphisms
`f₁^* g^* G ≅ (f₁ ≫ g)^* G ≅ f₂^* g^* G`. -/
lemma descentHom_toDescentData (G : S.Modules) {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S')
    (h : f₁ ≫ g = f₂ ≫ g) :
    descentHom ((pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj G) f₁ f₂ h =
      (pullbackCompIso' f₁ g (f₁ ≫ g) rfl G).inv ≫
        (pullbackCompIso' f₂ g (f₁ ≫ g) h.symm G).hom := by
  rw [← pseudofunctorCat_mapComp'_inv_app f₁ g (f₁ ≫ g) rfl,
    ← pseudofunctorCat_mapComp'_hom_app f₂ g (f₁ ≫ g) h.symm]
  rfl

/-- A section `s'` of `g^* G` over `g⁻¹ W` whose two inverse images to `S' ×_S S'` agree in the
inverse image of `G` is compatible with the descent datum of `g^* G`. -/
lemma isDescentSection_toDescentData (G : S.Modules) (W : S.Opens)
    (s' : Γ((Scheme.Modules.pullback g).obj G, g ⁻¹ᵁ W))
    (hs' : (pullbackCompIso' (Limits.pullback.fst g g) g (Limits.pullback.fst g g ≫ g) rfl
        G).inv.app _
        (pullbackApp (Limits.pullback.fst g g) _ (g ⁻¹ᵁ W) s') =
      ((Scheme.Modules.pullback (Limits.pullback.fst g g ≫ g)).obj G).presheaf.map
        (homOfLE (preimage_le_of_comp_eq Limits.pullback.condition W)).op
        ((pullbackCompIso' (Limits.pullback.snd g g) g (Limits.pullback.fst g g ≫ g)
          Limits.pullback.condition.symm G).inv.app _
          (pullbackApp (Limits.pullback.snd g g) _ (g ⁻¹ᵁ W) s'))) :
    IsDescentSection ((pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj G) W s' := by
  refine isDescentSection_of_fst_snd ((pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj G)
    W s' ?_
  have e := descentHom_toDescentData G (Limits.pullback.fst g g) (Limits.pullback.snd g g)
    Limits.pullback.condition
  have h₁ : (descentHom ((pseudofunctorCat.toDescentData (fun _ : Unit ↦ g)).obj G)
      (Limits.pullback.fst g g) (Limits.pullback.snd g g) Limits.pullback.condition).app _
        (pullbackApp (Limits.pullback.fst g g) ((Scheme.Modules.pullback g).obj G) (g ⁻¹ᵁ W) s') =
      (pullbackCompIso' (Limits.pullback.snd g g) g (Limits.pullback.fst g g ≫ g)
        Limits.pullback.condition.symm G).hom.app _
        ((pullbackCompIso' (Limits.pullback.fst g g) g (Limits.pullback.fst g g ≫ g) rfl
          G).inv.app _
          (pullbackApp (Limits.pullback.fst g g) _ (g ⁻¹ᵁ W) s')) := by
    rw [e]
    exact Hom.comp_app_apply _ _ _ _
  refine h₁.trans ((congrArg ((pullbackCompIso' (Limits.pullback.snd g g) g
    (Limits.pullback.fst g g ≫ g) Limits.pullback.condition.symm G).hom.app _) hs').trans ?_)
  rw [Hom.app_map, iso_hom_app_inv_app]
  rfl

end AlgebraicGeometry.Scheme.Modules
