/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import SGA.Foundations.Formal.OpenImmersion
import SGA.Foundations.Formal.TowerLimit

/-!
# Étale coverings of formal schemes, as compatible systems

Let `X₀ ⟶ X₁ ⟶ ⋯` be a thickening sequence with colimit the formal scheme `𝔛 = lim→ Xₙ`. An
étale covering of `𝔛` is given by a coherent locally free sheaf of algebras `ℬ` with separable
fibres, equivalently by compatible finite étale coverings `Yₙ ⟶ Xₙ` with
`Yₙ₊₁ ×_{Xₙ₊₁} Xₙ ≅ Yₙ` (SGA 1 I.8.4 and the discussion after it). We use the latter description:
`Scheme.FormalFiniteEtale F` is the limit of the tower of base change functors
`⋯ ⥤ FEt(X₁) ⥤ FEt(X₀)`.

SGA 1 I.8.4: the functor to étale coverings of `X₀` is an equivalence. Its proof is formal given
SGA 1 I.8.3 (base change along a surjective closed immersion is an equivalence on finite étale
coverings), which we take as a hypothesis
(`Scheme.FormalFiniteEtale.isEquivalence_toZero`). For `𝔛 = Spf A` with `A` noetherian the
hypothesis is proved (`Spf.isEquivalence_formalFiniteEtale_toZero` in
`SGA.Foundations.Formal.FiniteEtaleSpec`), and the algebraic form of I.8.4 is in
`SGA.Foundations.Formal.FiniteEtale`.

An étale covering `(Yₙ ⟶ Xₙ)` of `𝔛` defines the thickening sequence `Y₀ ⟶ Y₁ ⟶ ⋯`
(`Scheme.FormalFiniteEtale.diagram`) and the morphism of formal schemes
`𝔜 = lim→ Yₙ ⟶ 𝔛` (`Scheme.FormalFiniteEtale.toFormalColimit`).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Finite étale morphisms are stable under base change (instance search does not find the
instance for the infimum by itself). -/
instance isStableUnderBaseChange_isFinite_inf_etale :
    MorphismProperty.IsStableUnderBaseChange (@IsFinite ⊓ @Etale : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- Finite étale morphisms of schemes, `@IsFinite ⊓ @Etale`. -/
def finiteEtaleHom : MorphismProperty Scheme.{u} := @IsFinite ⊓ @Etale

lemma finiteEtaleHom_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    finiteEtaleHom f ↔ IsFinite f ∧ Etale f := Iff.rfl

instance : finiteEtaleHom.{u}.IsStableUnderBaseChange :=
  MorphismProperty.IsStableUnderBaseChange.inf

/-- The category of finite étale `X`-schemes (étale coverings of `X`). -/
abbrev FiniteEtale (X : Scheme.{u}) : Type _ :=
  finiteEtaleHom.{u}.Over ⊤ X

/-- Base change of étale coverings along `f : X ⟶ Y`. -/
noncomputable abbrev FiniteEtale.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Y.FiniteEtale ⥤ X.FiniteEtale :=
  MorphismProperty.Over.pullback _ ⊤ f

variable (F : ℕ ⥤ Scheme.{u})

/-- The tower `⋯ ⥤ FEt(X₂) ⥤ FEt(X₁) ⥤ FEt(X₀)` of base change functors of a sequence of
schemes. -/
noncomputable abbrev finiteEtaleTower (n : ℕ) :
    (F.obj (n + 1)).FiniteEtale ⥤ (F.obj n).FiniteEtale :=
  FiniteEtale.pullback (F.map (homOfLE n.le_succ))

/-- Étale coverings of the formal scheme `lim→ Xₙ`, described as compatible systems of étale
coverings `Yₙ ⟶ Xₙ` with `Yₙ₊₁ ×_{Xₙ₊₁} Xₙ ≅ Yₙ` (SGA 1 I.8.4). -/
abbrev FormalFiniteEtale : Type _ :=
  TowerLimit (C := fun n ↦ (F.obj n).FiniteEtale) (finiteEtaleTower F)

/-- Restriction of an étale covering of `lim→ Xₙ` to `X₀`. -/
noncomputable abbrev FormalFiniteEtale.toZero : FormalFiniteEtale F ⥤ (F.obj 0).FiniteEtale :=
  TowerLimit.π (C := fun n ↦ (F.obj n).FiniteEtale) (finiteEtaleTower F) 0

/-- SGA 1 I.8.4, for a formal scheme presented as a thickening sequence `X₀ ⟶ X₁ ⟶ ⋯`, assuming
SGA 1 I.8.3 in the form: base change of étale coverings along a surjective closed immersion is an
equivalence. Then étale coverings of `lim→ Xₙ` and of `X₀` correspond. -/
theorem FormalFiniteEtale.isEquivalence_toZero [IsThickeningSequence F]
    (h : ∀ ⦃X Y : Scheme.{u}⦄ (i : X ⟶ Y), IsClosedImmersion i → Surjective i →
      (FiniteEtale.pullback i).IsEquivalence) :
    (FormalFiniteEtale.toZero F).IsEquivalence := by
  have (n : ℕ) : (finiteEtaleTower F n).IsEquivalence :=
    h _ (IsThickeningSequence.isClosedImmersion n) (IsThickeningSequence.surjective n)
  infer_instance

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.FormalFiniteEtale

variable {F : ℕ ⥤ Scheme.{u}} (Y : FormalFiniteEtale F)

/-- The transition maps `Yₙ ≅ Yₙ₊₁ ×_{Xₙ₊₁} Xₙ ⟶ Yₙ₊₁` of an étale covering of `lim→ Xₙ`. -/
noncomputable def transition (n : ℕ) : (Y.obj n).left ⟶ (Y.obj (n + 1)).left :=
  (Y.iso n).inv.left ≫ pullback.fst (Y.obj (n + 1)).hom (F.map (homOfLE n.le_succ))

lemma transition_hom (n : ℕ) :
    Y.transition n ≫ (Y.obj (n + 1)).hom = (Y.obj n).hom ≫ F.map (homOfLE n.le_succ) := by
  have h₁ : (Y.iso n).inv.left ≫ pullback.snd (Y.obj (n + 1)).hom (F.map (homOfLE n.le_succ)) =
      (Y.obj n).hom := by
    simpa using (Y.iso n).inv.w
  rw [transition]
  erw [Category.assoc, pullback.condition, ← Category.assoc, h₁]

/-- The sequence of schemes `Y₀ ⟶ Y₁ ⟶ ⋯` underlying an étale covering of `lim→ Xₙ`. -/
noncomputable def diagram : ℕ ⥤ Scheme.{u} :=
  Functor.ofSequence Y.transition

/-- The structure morphisms `Yₙ ⟶ Xₙ`, as a morphism of sequences. -/
noncomputable def toBase : Y.diagram ⟶ F :=
  NatTrans.ofSequence (fun n ↦ (Y.obj n).hom) fun n ↦ by
    simp only [diagram, Functor.ofSequence_map_homOfLE_succ]
    exact Y.transition_hom n

instance (n : ℕ) : IsIso (Y.iso n).inv.left :=
  ⟨(Y.iso n).hom.left, congrArg (fun f ↦ f.left) (Y.iso n).inv_hom_id,
    congrArg (fun f ↦ f.left) (Y.iso n).hom_inv_id⟩

instance isClosedImmersion_transition [IsThickeningSequence F] (n : ℕ) :
    IsClosedImmersion (Y.transition n) := by
  have := IsThickeningSequence.isClosedImmersion (F := F) n
  have : IsClosedImmersion (pullback.fst (Y.obj (n + 1)).hom (F.map (homOfLE n.le_succ))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion)
      (IsPullback.of_hasPullback _ _).flip this
  have h : IsClosedImmersion (Y.iso n).inv.left := inferInstance
  exact @IsClosedImmersion.comp _ _ _ _ _ h this

instance surjective_transition [IsThickeningSequence F] (n : ℕ) :
    Surjective (Y.transition n) := by
  have := IsThickeningSequence.surjective (F := F) n
  have : Surjective (pullback.fst (Y.obj (n + 1)).hom (F.map (homOfLE n.le_succ))) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback _ _).flip this
  have h : Surjective (Y.iso n).inv.left := inferInstance
  exact ⟨this.surj.comp h.surj⟩

instance [IsThickeningSequence F] : IsThickeningSequence Y.diagram where
  isClosedImmersion n := by
    simp only [diagram, Functor.ofSequence_map_homOfLE_succ]
    exact Y.isClosedImmersion_transition n
  surjective n := by
    simp only [diagram, Functor.ofSequence_map_homOfLE_succ]
    exact Y.surjective_transition n

/-- The formal scheme `𝔜 = lim→ Yₙ` of an étale covering `(Yₙ ⟶ Xₙ)` of `𝔛 = lim→ Xₙ`, with its
structure morphism `𝔜 ⟶ 𝔛` (SGA 1 I.8.4, the covering of `𝔛` defined by the `ℬₙ`). -/
noncomputable def toFormalColimit : formalColimit Y.diagram ⟶ formalColimit F :=
  formalColimit.map Y.toBase

variable {Y} {Y' Y'' : FormalFiniteEtale F}

lemma transition_comp_app_left (φ : Y ⟶ Y') (n : ℕ) :
    Y.transition n ≫ (φ.app (n + 1)).left = (φ.app n).left ≫ Y'.transition n := by
  have h : (Y.iso n).inv ≫ (finiteEtaleTower F n).map (φ.app (n + 1)) =
      φ.app n ≫ (Y'.iso n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← φ.comm, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have h' := congrArg (fun f ↦ f.left) h
  simp only [MorphismProperty.Comma.comp_left] at h'
  have hL : ((finiteEtaleTower F n).map (φ.app (n + 1))).left ≫
      pullback.fst (Y'.obj (n + 1)).hom (F.map (homOfLE n.le_succ)) =
        pullback.fst (Y.obj (n + 1)).hom (F.map (homOfLE n.le_succ)) ≫ (φ.app (n + 1)).left := by
    erw [MorphismProperty.Over.pullback_map_left, pullback.lift_fst]
  calc Y.transition n ≫ (φ.app (n + 1)).left
      = (Y.iso n).inv.left ≫ (pullback.fst (Y.obj (n + 1)).hom (F.map (homOfLE n.le_succ)) ≫
          (φ.app (n + 1)).left) := Category.assoc _ _ _
    _ = (Y.iso n).inv.left ≫ (((finiteEtaleTower F n).map (φ.app (n + 1))).left ≫
          pullback.fst (Y'.obj (n + 1)).hom (F.map (homOfLE n.le_succ))) :=
        congrArg ((Y.iso n).inv.left ≫ ·) hL.symm
    _ = ((Y.iso n).inv.left ≫ ((finiteEtaleTower F n).map (φ.app (n + 1))).left) ≫
          pullback.fst (Y'.obj (n + 1)).hom (F.map (homOfLE n.le_succ)) :=
        (Category.assoc _ _ _).symm
    _ = ((φ.app n).left ≫ (Y'.iso n).inv.left) ≫
          pullback.fst (Y'.obj (n + 1)).hom (F.map (homOfLE n.le_succ)) :=
        congrArg (· ≫ pullback.fst (Y'.obj (n + 1)).hom (F.map (homOfLE n.le_succ))) h'
    _ = (φ.app n).left ≫ Y'.transition n := Category.assoc _ _ _

/-- The morphism of sequences `(Yₙ) ⟶ (Y'ₙ)` induced by a morphism of étale coverings. -/
noncomputable def diagramMap (φ : Y ⟶ Y') : Y.diagram ⟶ Y'.diagram :=
  NatTrans.ofSequence (fun n ↦ (φ.app n).left) fun n ↦ by
    simp only [diagram, Functor.ofSequence_map_homOfLE_succ]
    exact transition_comp_app_left φ n

@[simp]
lemma diagramMap_app (φ : Y ⟶ Y') (n : ℕ) : (diagramMap φ).app n = (φ.app n).left := rfl

@[simp]
lemma diagramMap_id : diagramMap (𝟙 Y) = 𝟙 Y.diagram := by
  ext n : 2
  rfl

@[simp]
lemma diagramMap_comp (φ : Y ⟶ Y') (ψ : Y' ⟶ Y'') :
    diagramMap (φ ≫ ψ) = diagramMap φ ≫ diagramMap ψ := by
  ext n : 2
  rfl

@[reassoc (attr := simp)]
lemma diagramMap_toBase (φ : Y ⟶ Y') : diagramMap φ ≫ Y'.toBase = Y.toBase := by
  ext n : 2
  exact MorphismProperty.Over.w (φ.app n)

/-- Étale coverings of `𝔛 = lim→ Xₙ`, as formal schemes over `𝔛` (SGA 1 I.8.4): the covering
`(Yₙ ⟶ Xₙ)` goes to `𝔜 = lim→ Yₙ ⟶ 𝔛`. -/
@[simps]
noncomputable def toOver : FormalFiniteEtale F ⥤ Over (formalColimit F) where
  obj Y := Over.mk Y.toFormalColimit
  map φ := Over.homMk (formalColimit.map (diagramMap φ)) (by
    simp [toFormalColimit])
  map_id Y := by
    ext : 1
    simp
  map_comp φ ψ := by
    ext : 1
    change formalColimit.map (diagramMap (φ ≫ ψ)) =
      formalColimit.map (diagramMap φ) ≫ formalColimit.map (diagramMap ψ)
    rw [diagramMap_comp, formalColimit.map_comp]

end AlgebraicGeometry.Scheme.FormalFiniteEtale
