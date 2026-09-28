/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.QuasiCoherent.Descent

/-!
# Descent data on quotients

Let `D` be a descent datum on a module `E` relative to `g : S' ⟶ S`, and `q' : E ⟶ Q'` an
epimorphism. A morphism `ψ : pr₁^* Q' ⟶ pr₂^* Q'` on `S' ×_S S'` compatible with `q'` and the
descent isomorphism of `D` (`pr₁^* q' ≫ ψ = D ≫ pr₂^* q'`) extends uniquely to a descent datum
`quotientDescentData D q' ψ hψ` on `Q'`, for which `q'` is a morphism of descent data
(`toQuotientDescentData`): the cocycle conditions are automatic since `q'` stays an epimorphism
after inverse images. This is the formal part of SGA 1 VIII.1.8 ("the inverse image functor is
right exact").
-/

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

@[reassoc]
lemma pullbackCompIso'_hom_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) {M N : Z.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback q).map φ ≫ (pullbackCompIso' f g q h N).hom =
      (pullbackCompIso' f g q h M).hom ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) :=
  (Scheme.Modules.pullbackCongr h.symm ≪≫ (Scheme.Modules.pullbackComp f g).symm).hom.naturality φ

@[reassoc]
lemma pullbackCompIso'_inv_naturality {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : X ⟶ Z)
    (h : f ≫ g = q) {M N : Z.Modules} (φ : M ⟶ N) :
    (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map φ) ≫
        (pullbackCompIso' f g q h N).inv =
      (pullbackCompIso' f g q h M).inv ≫ (Scheme.Modules.pullback q).map φ :=
  (Scheme.Modules.pullbackCongr h.symm ≪≫ (Scheme.Modules.pullbackComp f g).symm).inv.naturality φ

section Quotient

variable {S S' : Scheme.{u}} {g : S' ⟶ S} (D : pseudofunctorCat.DescentData (fun _ : Unit ↦ g))
  {Q' : S'.Modules} (q' : descentObj D ⟶ Q')
  (ψ : (Scheme.Modules.pullback (Limits.pullback.fst g g)).obj Q' ⟶
    (Scheme.Modules.pullback (Limits.pullback.snd g g)).obj Q')

/-- Auxiliary morphism for `quotientHom`: the inverse image of `ψ` along `l : Y ⟶ S' ×_S S'`. -/
noncomputable def quotientHomAux {Y : Scheme.{u}} (l : Y ⟶ Limits.pullback g g) (f₁ f₂ : Y ⟶ S')
    (hl₁ : l ≫ Limits.pullback.fst g g = f₁) (hl₂ : l ≫ Limits.pullback.snd g g = f₂) :
    (Scheme.Modules.pullback f₁).obj Q' ⟶ (Scheme.Modules.pullback f₂).obj Q' :=
  (pullbackCompIso' l _ f₁ hl₁ Q').hom ≫ (Scheme.Modules.pullback l).map ψ ≫
    (pullbackCompIso' l _ f₂ hl₂ Q').inv

variable {D q' ψ}
variable (hψ : (Scheme.Modules.pullback (Limits.pullback.fst g g)).map q' ≫ ψ =
    descentHom D (Limits.pullback.fst g g) (Limits.pullback.snd g g) Limits.pullback.condition ≫
      (Scheme.Modules.pullback (Limits.pullback.snd g g)).map q')

include hψ in
lemma quotientHomAux_spec {Y : Scheme.{u}} (l : Y ⟶ Limits.pullback g g) (f₁ f₂ : Y ⟶ S')
    (hl₁ : l ≫ Limits.pullback.fst g g = f₁) (hl₂ : l ≫ Limits.pullback.snd g g = f₂)
    (h : f₁ ≫ g = f₂ ≫ g) :
    (Scheme.Modules.pullback f₁).map q' ≫ quotientHomAux ψ l f₁ f₂ hl₁ hl₂ =
      descentHom D f₁ f₂ h ≫ (Scheme.Modules.pullback f₂).map q' := by
  subst hl₁ hl₂
  rw [quotientHomAux, pullbackCompIso'_hom_naturality_assoc, ← Functor.map_comp_assoc, hψ,
    Functor.map_comp_assoc, pullbackCompIso'_inv_naturality,
    ← descentHom_pull D l _ _ Limits.pullback.condition h]
  simp only [Category.assoc]

variable (ψ) in
/-- The descent isomorphisms of the quotient: `f₁^* Q' ⟶ f₂^* Q'`, for `f₁ ≫ g = f₂ ≫ g`. -/
noncomputable def quotientHom {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g) :
    (Scheme.Modules.pullback f₁).obj Q' ⟶ (Scheme.Modules.pullback f₂).obj Q' :=
  quotientHomAux ψ (Limits.pullback.lift f₁ f₂ h) f₁ f₂ (Limits.pullback.lift_fst _ _ _)
    (Limits.pullback.lift_snd _ _ _)

include hψ in
@[reassoc]
lemma quotientHom_spec {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g) :
    (Scheme.Modules.pullback f₁).map q' ≫ quotientHom ψ f₁ f₂ h =
      descentHom D f₁ f₂ h ≫ (Scheme.Modules.pullback f₂).map q' :=
  quotientHomAux_spec hψ _ f₁ f₂ _ _ h

variable [Epi q']

include hψ in
lemma quotientHom_self {Y : Scheme.{u}} (f : Y ⟶ S') : quotientHom ψ f f rfl = 𝟙 _ := by
  apply (cancel_epi ((Scheme.Modules.pullback f).map q')).1
  rw [quotientHom_spec hψ, descentHom_self, Category.id_comp, Category.comp_id]

include hψ in
lemma quotientHom_comp {Y : Scheme.{u}} (f₁ f₂ f₃ : Y ⟶ S') (h₁₂ : f₁ ≫ g = f₂ ≫ g)
    (h₂₃ : f₂ ≫ g = f₃ ≫ g) :
    quotientHom ψ f₁ f₂ h₁₂ ≫ quotientHom ψ f₂ f₃ h₂₃ = quotientHom ψ f₁ f₃ (h₁₂.trans h₂₃) := by
  apply (cancel_epi ((Scheme.Modules.pullback f₁).map q')).1
  rw [quotientHom_spec_assoc hψ, quotientHom_spec hψ, ← Category.assoc, descentHom_comp,
    quotientHom_spec hψ]

include hψ in
lemma quotientHom_pull {Y Y' : Scheme.{u}} (u : Y' ⟶ Y) (f₁ f₂ : Y ⟶ S')
    (h : f₁ ≫ g = f₂ ≫ g) (h' : (u ≫ f₁) ≫ g = (u ≫ f₂) ≫ g) :
    (pullbackCompIso' u f₁ (u ≫ f₁) rfl Q').hom ≫
      (Scheme.Modules.pullback u).map (quotientHom ψ f₁ f₂ h) ≫
      (pullbackCompIso' u f₂ (u ≫ f₂) rfl Q').inv = quotientHom ψ (u ≫ f₁) (u ≫ f₂) h' := by
  apply (cancel_epi ((Scheme.Modules.pullback (u ≫ f₁)).map q')).1
  rw [pullbackCompIso'_hom_naturality_assoc, ← Functor.map_comp_assoc, quotientHom_spec hψ,
    Functor.map_comp_assoc, pullbackCompIso'_inv_naturality, quotientHom_spec hψ,
    ← descentHom_pull D u f₁ f₂ h h']
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
variable (D q' ψ) in
/-- The descent datum on a quotient `q' : E ⟶ Q'` of a module with a descent datum `D`, given by a
morphism `ψ : pr₁^* Q' ⟶ pr₂^* Q'` on `S' ×_S S'` compatible with `q'` and `D`. -/
noncomputable def quotientDescentData : pseudofunctorCat.DescentData (fun _ : Unit ↦ g) where
  obj _ := Q'
  hom _ _ _ _ f₁ f₂ hf₁ hf₂ := quotientHom ψ f₁ f₂ (hf₁.trans hf₂.symm)
  pullHom_hom Y' Y u q q'' hq i₁ i₂ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    subst hgf₁ hgf₂
    simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom]
    rw [pseudofunctorCat_mapComp'_hom_app u f₁ (u ≫ f₁) rfl,
      pseudofunctorCat_mapComp'_inv_app u f₂ (u ≫ f₂) rfl]
    exact quotientHom_pull hψ u f₁ f₂ _ _
  hom_self _ _ _ f _ := quotientHom_self hψ f
  hom_comp _ _ _ _ _ f₁ f₂ f₃ _ _ _ := quotientHom_comp hψ f₁ f₂ f₃ _ _

lemma descentObj_quotientDescentData : descentObj (quotientDescentData D q' ψ hψ) = Q' := rfl

lemma descentHom_quotientDescentData {Y : Scheme.{u}} (f₁ f₂ : Y ⟶ S') (h : f₁ ≫ g = f₂ ≫ g) :
    descentHom (quotientDescentData D q' ψ hψ) f₁ f₂ h = quotientHom ψ f₁ f₂ h := rfl

set_option backward.isDefEq.respectTransparency false in
variable (D q' ψ) in
/-- The quotient map `q'`, as a morphism of descent data. -/
noncomputable def toQuotientDescentData : D ⟶ quotientDescentData D q' ψ hψ where
  hom _ := q'
  comm _ q i₁ i₂ f₁ f₂ hf₁ hf₂ := by
    cases i₁; cases i₂
    subst hf₁
    exact (quotientHom_spec hψ f₁ f₂ hf₂.symm).trans
      (congrArg (· ≫ (Scheme.Modules.pullback f₂).map q')
        (hom_eq_descentHom D (f₁ ≫ g) f₁ f₂ rfl hf₂).symm)

lemma toQuotientDescentData_hom (i : Unit) :
    (toQuotientDescentData D q' ψ hψ).hom i = q' := rfl

end Quotient

end AlgebraicGeometry.Scheme.Modules
