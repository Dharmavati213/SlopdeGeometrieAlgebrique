/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIX.FiniteEtaleDescentDiagram
import SGA.SGA1.ExposeIX.ProperEffectiveDescent
import SGA.SGA1.ExposeIX.ExactSequenceCompleteLocal

/-!
# SGA 1, Exposé IX: effective descent of étale coverings in the language of IX.5

In IX.3–IX.4 descent data are actions `X' ×_S S' ⟶ X'` (`DescentDatum`); in IX.5 they are
isomorphisms `φ : p₁^* Y ≅ p₂^* Y` satisfying the cocycle condition, and `g` is an effective descent
morphism for étale coverings when the comparison functor `fetComparison g` is an equivalence. We
compare the two:

* a gluing datum `φ` defines an action `(y, s') ↦ φ(y; a(y), s')` (`descentDatumOfFetDatum`),
  satisfying the axioms of a descent datum by the cocycle condition;
* if `g` is universally submersive, `fetComparison g` is fully faithful (IX.3.3), and it is
  essentially surjective as soon as every descent datum on an étale covering is effective
  (`isEquivalence_fetComparison_of_isEffective`).

Hence IX.4.12 in the form of IX.5: for `g` proper and surjective onto a locally noetherian scheme,
`fetComparison g` is an equivalence (`isEquivalence_fetComparison_of_isProper`), so that IX.5.6
computes `π₁(S)` from `π₁(S')` and `π₁(S'')` for such `g`
(`ker_etaleFundamentalGroup_map_eq_relations_of_isProper`,
`etaleFundamentalGroupQuotientRelationsEquivOfIsProper`). Over locally noetherian bases this also
gives IX.6.9 (`isEquivalence_fetComparison_pullback_snd_of_isProper`) and the first three parts of
IX.6.8 (`properDescent_of_isLocallyNoetherian`); over a complete noetherian local base all of
IX.6.8 holds (`properDescent_of_completeLocal`).
-/

universe u

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

section FetLift

variable {T T' W : Scheme.{u}} (p : T ⟶ T') (Y : MorphismProperty.Over FEt ⊤ T')

/-- The point of the inverse image `p^* Y` given by compatible points of `Y` and of `T`. -/
noncomputable def fetLift (y : W ⟶ Y.left) (t : W ⟶ T) (h : y ≫ Y.hom = t ≫ p) :
    W ⟶ ((pb p).obj Y).left :=
  pullback.lift y t h

@[reassoc (attr := simp)]
lemma fetLift_fetProj (y : W ⟶ Y.left) (t : W ⟶ T) (h : y ≫ Y.hom = t ≫ p) :
    fetLift p Y y t h ≫ fetProj p Y = y :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma fetLift_hom (y : W ⟶ Y.left) (t : W ⟶ T) (h : y ≫ Y.hom = t ≫ p) :
    fetLift p Y y t h ≫ ((pb p).obj Y).hom = t :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma fetProj_hom : fetProj p Y ≫ Y.hom = ((pb p).obj Y).hom ≫ p :=
  pullback.condition

variable {p Y} in
lemma fetPullback_hom_ext {a b : W ⟶ ((pb p).obj Y).left}
    (h₁ : a ≫ fetProj p Y = b ≫ fetProj p Y)
    (h₂ : a ≫ ((pb p).obj Y).hom = b ≫ ((pb p).obj Y).hom) : a = b :=
  pullback.hom_ext h₁ h₂

end FetLift

section Ev

variable {S S' : Scheme.{u}} {g : S' ⟶ S} (Y : MorphismProperty.Over FEt ⊤ S')
  (φ : (pb (pullback.fst g g)).obj Y ≅ (pb (pullback.snd g g)).obj Y)

/-- The image `φ(y; w)` of a point `y` of `Y` lying over the first component of a point `w` of
`S'' = S' ×_S S'`: a point of `Y` over the second component of `w`. -/
noncomputable def gluingEv {T : Scheme.{u}} (y : T ⟶ Y.left) (w : T ⟶ pullback g g)
    (hw : y ≫ Y.hom = w ≫ pullback.fst g g) : T ⟶ Y.left :=
  fetLift _ Y y w hw ≫ φ.hom.left ≫ fetProj (pullback.snd g g) Y

variable {Y φ}

lemma gluingEv_comp_hom {T : Scheme.{u}} (y : T ⟶ Y.left) (w : T ⟶ pullback g g)
    (hw : y ≫ Y.hom = w ≫ pullback.fst g g) :
    gluingEv Y φ y w hw ≫ Y.hom = w ≫ pullback.snd g g := by
  rw [gluingEv, Category.assoc, Category.assoc, fetProj_hom, MorphismProperty.Over.w_assoc,
    fetLift_hom_assoc]

lemma fetLift_comp_hom_left {T : Scheme.{u}} (y : T ⟶ Y.left) (w : T ⟶ pullback g g)
    (hw : y ≫ Y.hom = w ≫ pullback.fst g g) :
    fetLift _ Y y w hw ≫ φ.hom.left =
      fetLift _ Y (gluingEv Y φ y w hw) w (gluingEv_comp_hom y w hw) := by
  apply fetPullback_hom_ext
  · rw [fetLift_fetProj, gluingEv, Category.assoc]
  · rw [fetLift_hom, Category.assoc, MorphismProperty.Over.w, fetLift_hom]

lemma comp_gluingEv {T T' : Scheme.{u}} (u : T' ⟶ T) (y : T ⟶ Y.left) (w : T ⟶ pullback g g)
    (hw : y ≫ Y.hom = w ≫ pullback.fst g g) :
    u ≫ gluingEv Y φ y w hw =
      gluingEv Y φ (u ≫ y) (u ≫ w) (by rw [Category.assoc, hw, Category.assoc]) := by
  have : u ≫ fetLift _ Y y w hw = fetLift _ Y (u ≫ y) (u ≫ w)
      (by rw [Category.assoc, hw, Category.assoc]) := by
    apply fetPullback_hom_ext
    · rw [Category.assoc, fetLift_fetProj, fetLift_fetProj]
    · rw [Category.assoc, fetLift_hom, fetLift_hom]
  rw [gluingEv, gluingEv, reassoc_of% this]

lemma gluingEv_congr {T : Scheme.{u}} {y y' : T ⟶ Y.left} {w w' : T ⟶ pullback g g}
    (hy : y = y') (hw' : w = w') (hw : y ≫ Y.hom = w ≫ pullback.fst g g) :
    gluingEv Y φ y w hw = gluingEv Y φ y' w' (hy ▸ hw' ▸ hw) := by
  subst hy hw'
  rfl

end Ev

section Cocycle

variable {S S' : Scheme.{u}} {g : S' ⟶ S} {Y : MorphismProperty.Over FEt ⊤ S'}
  {φ : (pb (pullback.fst g g)).obj Y ≅ (pb (pullback.snd g g)).obj Y}

lemma tripleLift_proj₃₁ {T : Scheme.{u}} (w₁ w₂ : T ⟶ pullback g g)
    (h₁₂ : w₁ ≫ pullback.snd g g = w₂ ≫ pullback.fst g g) :
    pullback.lift w₁ w₂ h₁₂ ≫ tripleProj₃₁ g =
      pullback.lift (w₁ ≫ pullback.fst g g) (w₂ ≫ pullback.snd g g) (by
        simp only [Category.assoc]
        rw [pullback.condition, reassoc_of% h₁₂, pullback.condition]) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, pullback.lift_snd_assoc]

/-- The cocycle condition in terms of points: `φ(φ(y; s₁, s₂); s₂, s₃) = φ(y; s₁, s₃)`. -/
lemma gluingEv_gluingEv (hφ : (fetDescentDiagram g).IsCocycle φ) {T : Scheme.{u}}
    (y : T ⟶ Y.left) (w₁ w₂ : T ⟶ pullback g g)
    (h₁₂ : w₁ ≫ pullback.snd g g = w₂ ≫ pullback.fst g g)
    (hy : y ≫ Y.hom = w₁ ≫ pullback.fst g g) :
    gluingEv Y φ (gluingEv Y φ y w₁ hy) w₂ ((gluingEv_comp_hom y w₁ hy).trans h₁₂) =
      gluingEv Y φ y (pullback.lift (w₁ ≫ pullback.fst g g) (w₂ ≫ pullback.snd g g) (by
        simp only [Category.assoc]
        rw [pullback.condition, reassoc_of% h₁₂, pullback.condition]))
        (by rw [pullback.lift_fst, hy]) := by
  set t : T ⟶ pullback (pullback.snd g g) (pullback.fst g g) := pullback.lift w₁ w₂ h₁₂
  have ht₂₁ : t ≫ tripleProj₂₁ g = w₁ := pullback.lift_fst _ _ _
  have ht₃₂ : t ≫ tripleProj₃₂ g = w₂ := pullback.lift_snd _ _ _
  have ht₃₁ := tripleLift_proj₃₁ w₁ w₂ h₁₂
  set y₁ := fetLift (pullback.fst g g) Y y w₁ hy
  set z := fetLift (tripleProj₂₁ g) ((pb (pullback.fst g g)).obj Y) y₁ t
    (by rw [fetLift_hom, ht₂₁])
  have key := congrArg (fun f ↦ z ≫ f.left ≫
    fetProj (tripleProj₃₂ g) ((pb (pullback.snd g g)).obj Y) ≫ fetProj (pullback.snd g g) Y) hφ
  simp only [MorphismProperty.Comma.comp_left, Category.assoc] at key
  -- the left hand side
  have he₂ := fetPullbackCompCongr_hom_app_left_fetProj (pullback.snd g g) (tripleProj₂₁ g)
    (pullback.fst g g) (tripleProj₃₂ g) pullback.condition Y
  have hL : z ≫ ((pb (tripleProj₂₁ g)).map φ.hom).left ≫
      ((fetPullbackCompCongr (pullback.snd g g) (tripleProj₂₁ g) (pullback.fst g g)
        (tripleProj₃₂ g) pullback.condition).hom.app Y).left ≫
        fetProj (tripleProj₃₂ g) ((pb (pullback.fst g g)).obj Y) =
      fetLift (pullback.fst g g) Y (gluingEv Y φ y w₁ hy) w₂
        ((gluingEv_comp_hom y w₁ hy).trans h₁₂) := by
    apply fetPullback_hom_ext
    · simp only [Category.assoc]
      rw [fetLift_fetProj, he₂, fetPullback_map_left_fetProj_assoc, fetLift_fetProj_assoc]
      rfl
    · simp only [Category.assoc]
      rw [fetLift_hom, fetProj_hom]
      erw [MorphismProperty.Over.w_assoc, MorphismProperty.Over.w_assoc]
      rw [fetLift_hom_assoc, ht₃₂]
  have he₁ := fetPullbackCompCongr_hom_app_left_fetProj (pullback.fst g g) (tripleProj₂₁ g)
    (pullback.fst g g) (tripleProj₃₁ g) (pullback.lift_fst _ _ _).symm Y
  have hR : z ≫ ((fetPullbackCompCongr (pullback.fst g g) (tripleProj₂₁ g) (pullback.fst g g)
        (tripleProj₃₁ g) (pullback.lift_fst _ _ _).symm).hom.app Y).left ≫
      fetProj (tripleProj₃₁ g) ((pb (pullback.fst g g)).obj Y) =
      fetLift (pullback.fst g g) Y y (t ≫ tripleProj₃₁ g)
        (by rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ht₂₁, hy]) := by
    apply fetPullback_hom_ext
    · simp only [Category.assoc]
      rw [fetLift_fetProj, he₁, fetLift_fetProj_assoc, fetLift_fetProj]
    · simp only [Category.assoc]
      rw [fetLift_hom, fetProj_hom]
      erw [MorphismProperty.Over.w_assoc, fetLift_hom_assoc]
  have he₃ := fetPullbackCompCongr_hom_app_left_fetProj (pullback.snd g g) (tripleProj₃₁ g)
    (pullback.snd g g) (tripleProj₃₂ g) (pullback.lift_snd _ _ _) Y
  have lhs : z ≫ ((pb (tripleProj₂₁ g)).map φ.hom).left ≫
      ((fetPullbackCompCongr (pullback.snd g g) (tripleProj₂₁ g) (pullback.fst g g)
        (tripleProj₃₂ g) pullback.condition).hom.app Y).left ≫
      ((pb (tripleProj₃₂ g)).map φ.hom).left ≫
      fetProj (tripleProj₃₂ g) ((pb (pullback.snd g g)).obj Y) ≫ fetProj (pullback.snd g g) Y =
      gluingEv Y φ (gluingEv Y φ y w₁ hy) w₂ ((gluingEv_comp_hom y w₁ hy).trans h₁₂) := by
    rw [fetPullback_map_left_fetProj_assoc]
    simp only [← Category.assoc] at hL ⊢
    rw [hL]
    rfl
  have rhs : z ≫ ((fetPullbackCompCongr (pullback.fst g g) (tripleProj₂₁ g) (pullback.fst g g)
        (tripleProj₃₁ g) (pullback.lift_fst _ _ _).symm).hom.app Y).left ≫
      ((pb (tripleProj₃₁ g)).map φ.hom).left ≫
      ((fetPullbackCompCongr (pullback.snd g g) (tripleProj₃₁ g) (pullback.snd g g)
        (tripleProj₃₂ g) (pullback.lift_snd _ _ _)).hom.app Y).left ≫
      fetProj (tripleProj₃₂ g) ((pb (pullback.snd g g)).obj Y) ≫ fetProj (pullback.snd g g) Y =
      gluingEv Y φ y (t ≫ tripleProj₃₁ g)
        (by rw [Category.assoc, pullback.lift_fst, ← Category.assoc, ht₂₁, hy]) := by
    rw [he₃, fetPullback_map_left_fetProj_assoc]
    simp only [← Category.assoc] at hR ⊢
    rw [hR]
    rfl
  exact lhs.symm.trans (key.trans (rhs.trans (gluingEv_congr rfl ht₃₁ _)))

/-- On the diagonal, a gluing datum satisfying the cocycle condition is the identity:
`φ(y; a(y), a(y)) = y`. -/
lemma gluingEv_diag (hφ : (fetDescentDiagram g).IsCocycle φ) :
    gluingEv Y φ (𝟙 Y.left) (pullback.lift Y.hom Y.hom rfl)
      (by rw [Category.id_comp, pullback.lift_fst]) = 𝟙 Y.left := by
  set w₀ : Y.left ⟶ pullback g g := pullback.lift Y.hom Y.hom rfl
  have hf : w₀ ≫ pullback.fst g g = Y.hom := pullback.lift_fst _ _ _
  have hs : w₀ ≫ pullback.snd g g = Y.hom := pullback.lift_snd _ _ _
  have hw₀ : 𝟙 Y.left ≫ Y.hom = w₀ ≫ pullback.fst g g := by
    rw [Category.id_comp, hf]
  set ψ := gluingEv Y φ (𝟙 Y.left) w₀ hw₀
  have hψ : ψ ≫ Y.hom = Y.hom := (gluingEv_comp_hom _ _ _).trans hs
  have hψw : ψ ≫ w₀ = w₀ := by
    apply pullback.hom_ext
    · rw [Category.assoc, hf, hψ]
    · rw [Category.assoc, hs, hψ]
  -- `ψ` is idempotent
  have hidem : ψ ≫ ψ = ψ := by
    have h := gluingEv_gluingEv hφ (𝟙 Y.left) w₀ w₀ (by rw [hf, hs]) hw₀
    have h₁ : pullback.lift (w₀ ≫ pullback.fst g g) (w₀ ≫ pullback.snd g g)
        (by simp only [Category.assoc, pullback.condition]) = w₀ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst]
      · rw [pullback.lift_snd]
    rw [comp_gluingEv]
    refine Eq.trans ?_ (h.trans (gluingEv_congr rfl h₁ _))
    exact gluingEv_congr (Category.comp_id ψ) hψw _
  -- `ψ` has a left inverse
  set χ := fetLift (pullback.snd g g) Y (𝟙 Y.left) w₀
      (by rw [Category.id_comp, hs]) ≫ φ.inv.left ≫
    fetProj (pullback.fst g g) Y
  have hψχ : ψ ≫ χ = 𝟙 Y.left := by
    have h₁ : ψ ≫ fetLift (pullback.snd g g) Y (𝟙 Y.left) w₀
        (by rw [Category.id_comp, hs]) =
        fetLift (pullback.fst g g) Y (𝟙 Y.left) w₀ hw₀ ≫ φ.hom.left := by
      rw [fetLift_comp_hom_left]
      apply fetPullback_hom_ext
      · rw [Category.assoc, fetLift_fetProj, fetLift_fetProj, Category.comp_id]
      · rw [Category.assoc, fetLift_hom, fetLift_hom, hψw]
    have h₂ : φ.hom.left ≫ φ.inv.left = 𝟙 _ := congrArg (fun f ↦ f.left) φ.hom_inv_id
    rw [reassoc_of% h₁, reassoc_of% h₂, fetLift_fetProj]
  calc ψ = ψ ≫ ψ ≫ χ := by rw [hψχ, Category.comp_id]
    _ = ψ ≫ χ := by rw [← Category.assoc, hidem]
    _ = 𝟙 Y.left := hψχ

/-- The cocycle condition in terms of points, in a form suited for rewriting. -/
lemma gluingEv_eq_of_isCocycle (hφ : (fetDescentDiagram g).IsCocycle φ) {T : Scheme.{u}}
    {y₀ y₁ : T ⟶ Y.left} {w₁ w₂ w₃ : T ⟶ pullback g g}
    (h₀ : y₀ ≫ Y.hom = w₁ ≫ pullback.fst g g) (hy₁ : y₁ = gluingEv Y φ y₀ w₁ h₀)
    (h₁₂ : w₁ ≫ pullback.snd g g = w₂ ≫ pullback.fst g g)
    (h₃₁ : w₃ ≫ pullback.fst g g = w₁ ≫ pullback.fst g g)
    (h₃₂ : w₃ ≫ pullback.snd g g = w₂ ≫ pullback.snd g g)
    (hw₂ : y₁ ≫ Y.hom = w₂ ≫ pullback.fst g g) (hw₃ : y₀ ≫ Y.hom = w₃ ≫ pullback.fst g g) :
    gluingEv Y φ y₁ w₂ hw₂ = gluingEv Y φ y₀ w₃ hw₃ := by
  subst hy₁
  refine (gluingEv_gluingEv hφ y₀ w₁ w₂ h₁₂ h₀).trans (gluingEv_congr rfl ?_ _)
  apply pullback.hom_ext
  · rw [pullback.lift_fst, h₃₁]
  · rw [pullback.lift_snd, h₃₂]

end Cocycle

section Action

variable {S S' : Scheme.{u}} {g : S' ⟶ S}

variable (g) in
/-- The action `(y, s') ↦ φ(y; a(y), s')` on `Y` defined by a gluing datum `φ`. -/
noncomputable def fetDatumAct (D : (fetDescentDiagram g).Datum) :
    pullback (D.obj.hom ≫ g) g ⟶ D.obj.left :=
  gluingEv D.obj D.φ (pullback.fst _ _)
    (pullback.lift (pullback.fst _ _ ≫ D.obj.hom) (pullback.snd _ _)
      (by rw [Category.assoc]; exact pullback.condition))
    (by rw [pullback.lift_fst])

lemma comp_fetDatumAct (D : (fetDescentDiagram g).Datum) {T : Scheme.{u}}
    (k : T ⟶ pullback (D.obj.hom ≫ g) g) :
    k ≫ fetDatumAct g D = gluingEv D.obj D.φ (k ≫ pullback.fst _ _)
      (pullback.lift (k ≫ pullback.fst _ _ ≫ D.obj.hom) (k ≫ pullback.snd _ _)
        (by simp only [Category.assoc]; rw [pullback.condition]))
      (by rw [pullback.lift_fst, Category.assoc]) := by
  rw [fetDatumAct, comp_gluingEv]
  refine gluingEv_congr rfl ?_ _
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

lemma fetDatumAct_comp_hom (D : (fetDescentDiagram g).Datum) :
    fetDatumAct g D ≫ D.obj.hom = pullback.snd _ _ := by
  rw [fetDatumAct, gluingEv_comp_hom, pullback.lift_snd]

lemma lift_comp_fetDatumAct (D : (fetDescentDiagram g).Datum) {T : Scheme.{u}}
    (y : T ⟶ D.obj.left) (s : T ⟶ S') (h : y ≫ D.obj.hom ≫ g = s ≫ g) :
    pullback.lift y s h ≫ fetDatumAct g D = gluingEv D.obj D.φ y
      (pullback.lift (y ≫ D.obj.hom) s (by rw [Category.assoc, h]))
      (by rw [pullback.lift_fst]) := by
  rw [comp_fetDatumAct]
  refine gluingEv_congr (pullback.lift_fst _ _ _) ?_ _
  apply pullback.hom_ext
  · rw [pullback.lift_fst, pullback.lift_fst, pullback.lift_fst_assoc]
  · rw [pullback.lift_snd, pullback.lift_snd, pullback.lift_snd]

/-- The associativity law `(y·s₁)·s₂ = y·s₂` of the action defined by a gluing datum. -/
lemma fetDatumAct_lift_fetDatumAct (D : (fetDescentDiagram g).Datum) {T : Scheme.{u}}
    (k : T ⟶ pullback (D.obj.hom ≫ g) g) (s₂ : T ⟶ S')
    (hs : k ≫ pullback.snd (D.obj.hom ≫ g) g ≫ g = s₂ ≫ g) :
    pullback.lift (f := D.obj.hom ≫ g) (g := g) (k ≫ fetDatumAct g D) s₂
        (by rw [Category.assoc, reassoc_of% (fetDatumAct_comp_hom D), hs]) ≫
        fetDatumAct g D =
      pullback.lift (f := D.obj.hom ≫ g) (g := g) (k ≫ pullback.fst _ _) s₂
        (by simp only [Category.assoc, pullback.condition, hs]) ≫ fetDatumAct g D := by
  rw [lift_comp_fetDatumAct, lift_comp_fetDatumAct]
  have hk : (k ≫ pullback.fst _ _ ≫ D.obj.hom) ≫ g = (k ≫ pullback.snd _ _) ≫ g := by
    simp only [Category.assoc]; rw [pullback.condition]
  have h₂ : (k ≫ fetDatumAct g D ≫ D.obj.hom) ≫ g = s₂ ≫ g := by
    rw [fetDatumAct_comp_hom, Category.assoc, hs]
  have h₃ : (k ≫ pullback.fst _ _ ≫ D.obj.hom) ≫ g = s₂ ≫ g := by
    rw [hk, Category.assoc, hs]
  refine gluingEv_eq_of_isCocycle D.cocycle (y₀ := k ≫ pullback.fst _ _)
    (y₁ := k ≫ fetDatumAct g D)
    (w₁ := pullback.lift (k ≫ pullback.fst _ _ ≫ D.obj.hom) (k ≫ pullback.snd _ _) hk)
    (w₂ := pullback.lift (k ≫ fetDatumAct g D ≫ D.obj.hom) s₂ h₂)
    (w₃ := pullback.lift (k ≫ pullback.fst _ _ ≫ D.obj.hom) s₂ h₃)
    (by rw [pullback.lift_fst, Category.assoc]) ?_ ?_ ?_ ?_ _ _
  · exact comp_fetDatumAct D k
  · rw [pullback.lift_snd, pullback.lift_fst, fetDatumAct_comp_hom]
  · rw [pullback.lift_fst, pullback.lift_fst]
  · rw [pullback.lift_snd, pullback.lift_snd]

variable (g) in
/-- IX.5 ⟶ IX.4: the descent datum, in the form of an action (`DescentDatum`), defined by a gluing
datum on a finite étale covering. -/
noncomputable def descentDatumOfFetDatum (D : (fetDescentDiagram g).Datum) :
    DescentDatum g D.obj.hom where
  act := fetDatumAct g D
  act_comp := fetDatumAct_comp_hom D
  unit := by
    rw [lift_comp_fetDatumAct]
    refine (gluingEv_congr rfl ?_ _).trans (gluingEv_diag D.cocycle)
    simp only [Category.id_comp]
  assoc := fetDatumAct_lift_fetDatumAct D _ _ pullback.condition

end Action

section Comparison

/-- A morphism of objects with descent data whose underlying morphism is an isomorphism is an
isomorphism. -/
lemma DescentDiagram.isIso_of_isIso_hom {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂]
    [Category C₃] {D : DescentDiagram C₁ C₂ C₃} {X Y : D.Datum} (f : X ⟶ Y)
    [IsIso (DescentDiagram.Datum.Hom.hom f)] : IsIso f := by
  have comm' : D.p₁.map (inv (DescentDiagram.Datum.Hom.hom f)) ≫ X.φ.hom =
      Y.φ.hom ≫ D.p₂.map (inv (DescentDiagram.Datum.Hom.hom f)) := by
    rw [← cancel_epi (D.p₁.map (DescentDiagram.Datum.Hom.hom f)), ← D.p₁.map_comp_assoc,
      IsIso.hom_inv_id, D.p₁.map_id, Category.id_comp, DescentDiagram.Datum.Hom.comm_assoc,
      ← D.p₂.map_comp, IsIso.hom_inv_id, D.p₂.map_id, Category.comp_id]
  exact ⟨⟨⟨inv (DescentDiagram.Datum.Hom.hom f), comm'⟩,
    DescentDiagram.Datum.Hom.ext (by simp), DescentDiagram.Datum.Hom.ext (by simp)⟩⟩

variable {S S' : Scheme.{u}} {g : S' ⟶ S}

lemma fetLift_self {T T' : Scheme.{u}} (p : T ⟶ T') (Y : MorphismProperty.Over FEt ⊤ T') :
    fetLift p Y (fetProj p Y) ((pb p).obj Y).hom (fetProj_hom p Y) = 𝟙 _ := by
  apply fetPullback_hom_ext
  · rw [fetLift_fetProj, Category.id_comp]
  · rw [fetLift_hom, Category.id_comp]

variable (g) in
@[reassoc]
lemma fetCanonicalDatum_hom_app_left_fetProj (X : MorphismProperty.Over FEt ⊤ S) :
    ((fetCanonicalDatum g).hom.app X).left ≫ fetProj (pullback.snd g g) ((pb g).obj X) ≫
      fetProj g X = fetProj (pullback.fst g g) ((pb g).obj X) ≫ fetProj g X :=
  fetPullbackCompCongr_hom_app_left_fetProj _ _ _ _ _ X

/-- If `v : Y ⟶ X` is invariant under the action defined by a gluing datum, it is invariant under
the gluing datum. -/
lemma gluingEv_comp_of_fetDatumAct (D : (fetDescentDiagram g).Datum) {X : Scheme.{u}}
    (v : D.obj.left ⟶ X) (hact : fetDatumAct g D ≫ v = pullback.fst _ _ ≫ v) {T : Scheme.{u}}
    (y : T ⟶ D.obj.left) (w : T ⟶ pullback g g) (hw : y ≫ D.obj.hom = w ≫ pullback.fst g g) :
    gluingEv D.obj D.φ y w hw ≫ v = y ≫ v := by
  have h : y ≫ D.obj.hom ≫ g = (w ≫ pullback.snd g g) ≫ g := by
    rw [reassoc_of% hw, Category.assoc, pullback.condition]
  have h' := lift_comp_fetDatumAct D y (w ≫ pullback.snd g g) h
  have hw' : pullback.lift (y ≫ D.obj.hom) (w ≫ pullback.snd g g)
      (by rw [Category.assoc, h]) = w := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, hw]
    · rw [pullback.lift_snd]
  rw [gluingEv_congr rfl hw'.symm hw, ← h', Category.assoc, hact, pullback.lift_fst_assoc]

variable (g) in
/-- IX.4 ⟶ IX.5: if every descent datum (in the sense of IX.4) on a finite étale covering of `S'`
is effective, the comparison functor of `g` for finite étale coverings is essentially
surjective. -/
theorem essSurj_fetComparison_of_isEffective
    (h : ∀ ⦃X' : Scheme.{u}⦄ (a : X' ⟶ S') (D : DescentDatum g a), FEt a → D.IsEffective FEt) :
    (fetComparison g).EssSurj := by
  refine ⟨fun D ↦ ?_⟩
  obtain ⟨X, b, v, hb, hv, hact⟩ := h _ (descentDatumOfFetDatum g D) D.obj.prop
  let Xo : MorphismProperty.Over FEt ⊤ S := MorphismProperty.Over.mk ⊤ b hb
  let e : (pb g).obj Xo ≅ D.obj :=
    MorphismProperty.Over.isoMk hv.isoPullback.symm hv.isoPullback_inv_snd
  have he : e.hom.left ≫ v = fetProj g Xo := hv.isoPullback_inv_fst
  have hact' : fetDatumAct g D ≫ v = pullback.fst _ _ ≫ v := hact
  -- the action on `D` is the identity on the points of `X`
  have hφv : D.φ.hom.left ≫ fetProj (pullback.snd g g) D.obj ≫ v =
      fetProj (pullback.fst g g) D.obj ≫ v := by
    have := gluingEv_comp_of_fetDatumAct D v hact' (fetProj (pullback.fst g g) D.obj)
      ((pb (pullback.fst g g)).obj D.obj).hom (fetProj_hom _ _)
    rwa [gluingEv, fetLift_self, Category.id_comp, Category.assoc] at this
  have hcomm : (pb (pullback.fst g g)).map e.hom ≫ D.φ.hom =
      (fetCanonicalDatum g).hom.app Xo ≫ (pb (pullback.snd g g)).map e.hom := by
    ext : 1
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    apply fetPullback_hom_ext
    · refine hv.hom_ext ?_ ?_
      · simp only [Category.assoc]
        rw [hφv, fetPullback_map_left_fetProj_assoc, he, fetPullback_map_left_fetProj_assoc, he]
        exact (fetCanonicalDatum_hom_app_left_fetProj g Xo).symm
      · simp only [Category.assoc]
        rw [fetProj_hom, MorphismProperty.Over.w_assoc,
          MorphismProperty.Over.w_assoc, MorphismProperty.Over.w_assoc,
          MorphismProperty.Over.w_assoc]
    · simp only [Category.assoc]
      rw [MorphismProperty.Over.w, MorphismProperty.Over.w, MorphismProperty.Over.w,
        MorphismProperty.Over.w]
  let f : (fetComparison g).obj Xo ⟶ D := ⟨e.hom, hcomm⟩
  have : IsIso (DescentDiagram.Datum.Hom.hom f) := inferInstanceAs (IsIso e.hom)
  have := DescentDiagram.isIso_of_isIso_hom f
  exact ⟨Xo, ⟨asIso f⟩⟩

variable (g) in
/-- IX.3.3 in the form of IX.5: if `g` is a descent morphism for finite étale coverings (e.g.
universally submersive), the comparison functor of `g` is faithful. -/
theorem faithful_fetComparison_of_isDescentMorphism (hg : IsDescentMorphism FEt g) :
    (fetComparison g).Faithful := by
  refine ⟨fun {X Y} u₁ u₂ h ↦ ?_⟩
  have h₁ : ((pb g).map u₁).left ≫ fetProj g Y = ((pb g).map u₂).left ≫ fetProj g Y :=
    congrArg (fun F : (fetComparison g).obj X ⟶ (fetComparison g).obj Y ↦
      (DescentDiagram.Datum.Hom.hom F).left ≫ fetProj g Y) h
  rw [fetPullback_map_left_fetProj, fetPullback_map_left_fetProj] at h₁
  obtain ⟨φ, -, huniq⟩ := hg X.hom Y.hom X.prop Y.prop (pullback.fst X.hom g ≫ u₁.left)
    (by rw [Category.assoc, MorphismProperty.Over.w]) (by rw [pullback.condition_assoc])
  ext : 1
  exact (huniq _ ⟨MorphismProperty.Over.w u₁, rfl⟩).trans
    (huniq _ ⟨MorphismProperty.Over.w u₂, h₁.symm⟩).symm

variable (g) in
/-- IX.3.3 in the form of IX.5: if `g` is a descent morphism for finite étale coverings (e.g.
universally submersive), the comparison functor of `g` is full: morphisms of inverse images
compatible with the canonical descent data descend. -/
theorem full_fetComparison_of_isDescentMorphism (hg : IsDescentMorphism FEt g) :
    (fetComparison g).Full := by
  refine ⟨fun {X Y} F ↦ ?_⟩
  set ψ : (pb g).obj X ⟶ (pb g).obj Y := DescentDiagram.Datum.Hom.hom F
  have hcomm : (pb (pullback.fst g g)).map ψ ≫ (fetCanonicalDatum g).hom.app Y =
      (fetCanonicalDatum g).hom.app X ≫ (pb (pullback.snd g g)).map ψ :=
    DescentDiagram.Datum.Hom.comm F
  have hφ : (ψ.left ≫ fetProj g Y) ≫ Y.hom = pullback.fst X.hom g ≫ X.hom := by
    rw [Category.assoc, fetProj_hom, MorphismProperty.Over.w_assoc]
    exact pullback.condition.symm
  -- the kernel pair of `X ×_S S' ⟶ X`, as points of `p₁^* g^* X`
  set k₁ := pullback.fst (pullback.fst X.hom g) (pullback.fst X.hom g)
  set k₂ := pullback.snd (pullback.fst X.hom g) (pullback.fst X.hom g)
  have hk : (k₁ ≫ pullback.snd X.hom g) ≫ g = (k₂ ≫ pullback.snd X.hom g) ≫ g := by
    simp only [Category.assoc]
    rw [← pullback.condition, pullback.condition_assoc]
  obtain ⟨κ, hκ₁, hκ₂⟩ : ∃ κ : _ ⟶ ((pb (pullback.fst g g)).obj ((pb g).obj X)).left,
      κ ≫ fetProj (pullback.fst g g) ((pb g).obj X) = k₁ ∧
        κ ≫ ((pb (pullback.fst g g)).obj ((pb g).obj X)).hom =
          pullback.lift (k₁ ≫ pullback.snd X.hom g) (k₂ ≫ pullback.snd X.hom g) hk :=
    ⟨fetLift (pullback.fst g g) ((pb g).obj X) k₁
      (pullback.lift (k₁ ≫ pullback.snd X.hom g) (k₂ ≫ pullback.snd X.hom g) hk)
      (pullback.lift_fst _ _ _).symm, fetLift_fetProj _ _ _ _ _, fetLift_hom _ _ _ _ _⟩
  have hκ : κ ≫ ((fetCanonicalDatum g).hom.app X).left ≫
      fetProj (pullback.snd g g) ((pb g).obj X) = k₂ := by
    apply fetPullback_hom_ext
    · rw [Category.assoc, Category.assoc, fetCanonicalDatum_hom_app_left_fetProj,
        reassoc_of% hκ₁]
      exact pullback.condition
    · rw [Category.assoc, Category.assoc, fetProj_hom]
      erw [MorphismProperty.Over.w_assoc]
      exact ((reassoc_of% hκ₂) (pullback.snd g g)).trans (pullback.lift_snd _ _ _)
  have hker : k₁ ≫ ψ.left ≫ fetProj g Y = k₂ ≫ ψ.left ≫ fetProj g Y := by
    have h₁ := congrArg (fun f ↦ κ ≫ f.left ≫ fetProj (pullback.snd g g) ((pb g).obj Y) ≫
      fetProj g Y) hcomm
    simp only [MorphismProperty.Comma.comp_left, Category.assoc] at h₁
    rw [fetCanonicalDatum_hom_app_left_fetProj, fetPullback_map_left_fetProj_assoc,
      fetPullback_map_left_fetProj_assoc, reassoc_of% hκ₁, reassoc_of% hκ] at h₁
    exact h₁
  obtain ⟨φ, ⟨hφ₁, hφ₂⟩, -⟩ := hg X.hom Y.hom X.prop Y.prop (ψ.left ≫ fetProj g Y) hφ hker
  refine ⟨MorphismProperty.Over.homMk φ hφ₁, DescentDiagram.Datum.Hom.ext ?_⟩
  change (pb g).map (MorphismProperty.Over.homMk φ hφ₁) = ψ
  ext : 1
  apply fetPullback_hom_ext
  · rw [fetPullback_map_left_fetProj]
    exact hφ₂
  · rw [MorphismProperty.Over.w, MorphismProperty.Over.w]

variable (g) in
/-- IX.4 ⟶ IX.5: if `g` is a descent morphism for finite étale coverings and every descent datum
on a finite étale covering of `S'` is effective, then `g` is an effective descent morphism for
finite étale coverings in the sense of IX.5: the comparison functor is an equivalence. -/
theorem isEquivalence_fetComparison_of_isEffective (hg : IsDescentMorphism FEt g)
    (h : ∀ ⦃X' : Scheme.{u}⦄ (a : X' ⟶ S') (D : DescentDatum g a), FEt a → D.IsEffective FEt) :
    (fetComparison g).IsEquivalence where
  faithful := faithful_fetComparison_of_isDescentMorphism g hg
  full := full_fetComparison_of_isDescentMorphism g hg
  essSurj := essSurj_fetComparison_of_isEffective g h

variable (g) in
/-- IX.4 ⟶ IX.5: an effective descent morphism for étale coverings in the sense of IX.4 is one in
the sense of IX.5. -/
theorem isEquivalence_fetComparison_of_isEffectiveDescentMorphism
    (hg : IsEffectiveDescentMorphism g etaleCovering) : (fetComparison g).IsEquivalence :=
  isEquivalence_fetComparison_of_isEffective g hg.1 hg.2

end Comparison

section Proper

variable {S S' : Scheme.{u}} (g : S' ⟶ S)

/-- **IX.4.12** in the language of IX.5 (locally noetherian base): a proper surjective morphism to
a locally noetherian scheme is an effective descent morphism for étale coverings, i.e. `g^*`
identifies the étale coverings of `S` with the étale coverings of `S'` endowed with descent
data. -/
theorem isEquivalence_fetComparison_of_isProper [IsLocallyNoetherian S] [IsProper g]
    [Surjective g] : (fetComparison g).IsEquivalence :=
  isEquivalence_fetComparison_of_isEffectiveDescentMorphism g
    (isEffectiveDescentMorphism_of_isProper g)

/-- **IX.6.9** (locally noetherian bases): a proper surjective morphism `f : X ⟶ S` is an effective
descent morphism for étale coverings after any base change `T ⟶ S` with `T` locally noetherian.
(`UniversalProperDescentStatement` asks this for all `T`, which needs IX.4.12 over an arbitrary
base, i.e. the reduction to the noetherian case of EGA IV 8.) -/
theorem isEquivalence_fetComparison_pullback_snd_of_isProper {X T : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [Surjective f] [IsLocallyNoetherian T] (t : T ⟶ S) :
    (fetComparison (pullback.snd f t)).IsEquivalence :=
  isEquivalence_fetComparison_of_isProper (pullback.snd f t)

/-- **IX.6.8**, all but the description of the essential image (locally noetherian base): for
`f : X ⟶ S` proper and surjective with geometrically connected fibres, `f` is an effective
descent morphism for étale coverings and `f^*` is fully faithful on étale coverings (the first
three parts of `ProperDescentStatement`). -/
theorem properDescent_of_isLocallyNoetherian {X : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [IsProper f] [Surjective f] [GeometricallyConnected f] :
    (fetComparison f).IsEquivalence ∧ (pb f).Full ∧ (pb f).Faithful :=
  ⟨isEquivalence_fetComparison_of_isProper f,
    full_pullback_of_isProper_of_geometricallyConnected f, faithful_pullback_of_surjective f⟩

open IsLocalRing in
/-- **IX.6.8 over a complete local base** (all of `ProperDescentStatement` for `S = Spec R`, `R` a
complete noetherian local ring): for `f : X ⟶ Spec R` proper with geometrically connected fibres,
`f` is an effective descent morphism for étale coverings, `f^*` is fully faithful, and its
essential image consists of the étale coverings of `X` which are geometrically trivial on every
fibre (equivalently on the closed fibre, `mem_essImage_iff_isGeometricallyTrivial_closedFibre`). -/
theorem properDescent_of_completeLocal (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsProper f] [GeometricallyConnected f] :
    (fetComparison f).IsEquivalence ∧ (pb f).Full ∧ (pb f).Faithful ∧
      ∀ Y : MorphismProperty.Over FEt ⊤ X, (pb f).essImage Y ↔
        ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y) :=
  ⟨(properDescent_of_isLocallyNoetherian f).1, (properDescent_of_isLocallyNoetherian f).2.1,
    (properDescent_of_isLocallyNoetherian f).2.2,
    mem_essImage_iff_forall_isGeometricallyTrivial_of_completeLocal R f⟩

variable (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s' : Spec (.of Ω) ⟶ S')
  [ConnectedSpace S'] [ConnectedSpace ↥(pullback g g)]
  [ConnectedSpace ↥(pullback (pullback.snd g g) (pullback.fst g g))]

open SGA.SGA1.ExposeV

/-- **IX.5.6** for proper coverings, the kernel: for `g : S' ⟶ S` proper and surjective onto a
locally noetherian scheme, with `S'`, `S''`, `S'''` connected, the kernel of
`π₁(S', s') → π₁(S, g(s'))` is the closed normal subgroup generated by the `p₁*(h) p₂*(h)⁻¹`,
`h ∈ π₁(S'', Δ s')`. -/
theorem ker_etaleFundamentalGroup_map_eq_relations_of_isProper [IsLocallyNoetherian S]
    [IsProper g] [Surjective g] :
    (etaleFundamentalGroup.map Ω g s').ker = (fetDiagonalPoint g Ω s').relations :=
  have := isEquivalence_fetComparison_of_isProper g
  ker_etaleFundamentalGroup_map_eq_relations g Ω s'

/-- **IX.5.6** for proper coverings: for `g : S' ⟶ S` proper and surjective onto a locally
noetherian scheme, with `S'`, `S''`, `S'''` connected, `π₁(S, g(s'))` is the quotient of
`π₁(S', s')` by the closed normal subgroup generated by the `p₁*(h) p₂*(h)⁻¹`,
`h ∈ π₁(S'', Δ s')`. -/
noncomputable def etaleFundamentalGroupQuotientRelationsEquivOfIsProper [IsLocallyNoetherian S]
    [IsProper g] [Surjective g] :
    etaleFundamentalGroup Ω s' ⧸ (fetDiagonalPoint g Ω s').relations ≃ₜ*
      etaleFundamentalGroup Ω (s' ≫ g) :=
  have := isEquivalence_fetComparison_of_isProper g
  have : ConnectedSpace S := Surjective.surj.connectedSpace g.continuous
  etaleFundamentalGroupQuotientRelationsEquiv g Ω s'

end Proper

end SGA.SGA1.ExposeIX
