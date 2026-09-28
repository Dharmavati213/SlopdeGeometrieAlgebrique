/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.ProperDescentRigidity
import SGA.Foundations.SpecStalkLimit

/-!
# SGA 1, Exposé IX, 6.7 and 6.8 over a locally noetherian base

Let `f : X ⟶ S` be proper with geometrically connected fibres, `S` locally noetherian, and `Y` an
étale covering of `X` inducing a geometrically trivial covering on every fibre `X_s`. We show that
`Y` comes from an étale covering of `S` (IX.6.7), following the reduction of SGA to a complete
local base (IX.6.6):

* over `Spec 𝒪̂_{S,s}`, `Y` comes from the base (IX.1.10, full faithfulness, and henselian lifting:
  `mem_essImage_iff_isGeometricallyTrivial_closedFibre`), hence carries an action (a descent datum
  in the form of IX.4) satisfying the unit law;
* this action descends to `Spec 𝒪_{S,s}` along the faithfully flat `Spec 𝒪̂_{S,s} ⟶ Spec 𝒪_{S,s}`
  (VIII.5.2; the compatibility on `𝒪̂ ⊗ 𝒪̂` holds since actions satisfying the unit law are unique,
  `IsActAt.eq`), and spreads out to a neighbourhood of `s` (EGA IV 8.8.2);
* the local actions glue (`mem_essImage_of_forall_exists_localAct`), and IX.4.12 concludes.

This gives IX.6.7 (`mem_essImage_of_forall_isGeometricallyTrivial`) and IX.6.8
(`properDescentStatement_of_isLocallyNoetherian`) over a locally noetherian base; IX.6.11 is
deduced in `SGA.SGA1.ExposeIX.ProperDescentGeometricFibres`. SGA states IX.6.7 and IX.6.8 over an
arbitrary base for `f` of finite presentation (`ProperDescentStatement`); the reduction to a
noetherian base (EGA IV 8) is not done here.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty

namespace SGA.SGA1.ExposeIX

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

section ActAt

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)

/-- The structure morphism `Y ×_S X ⟶ S`. -/
noncomputable abbrev actBase : pullback (Y.hom ≫ f) f ⟶ S :=
  pullback.fst (Y.hom ≫ f) f ≫ Y.hom ≫ f

variable {T : Scheme.{u}} (t : T ⟶ S)

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal section `(y, τ) ↦ ((y, π(y)), τ)` of `(Y ×_S X) ×_S T ⟶ Y ×_S T`. -/
noncomputable abbrev actDiagAt : pullback (Y.hom ≫ f) t ⟶ pullback (actBase f Y) t :=
  pullback.map (Y.hom ≫ f) t (actBase f Y) t (actDiag f Y) (𝟙 T) (𝟙 S)
    (by simp only [actBase, pullback.lift_fst_assoc, Category.comp_id]
        exact (Category.id_comp _).symm) (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The projection `(Y ×_S X) ×_S T ⟶ Y ×_S T`. -/
noncomputable abbrev actProjAt : pullback (actBase f Y) t ⟶ pullback (Y.hom ≫ f) t :=
  pullback.map (actBase f Y) t (Y.hom ≫ f) t (pullback.fst (Y.hom ≫ f) f) (𝟙 T) (𝟙 S)
    (by simp) (by simp)

/-- An action over `t : T ⟶ S`: a morphism `(Y ×_S X) ×_S T ⟶ Y` over `X` satisfying the unit
law along `(y, τ) ↦ ((y, π(y)), τ)`. -/
def IsActAt (e : pullback (actBase f Y) t ⟶ Y.left) : Prop :=
  e ≫ Y.hom = pullback.fst (actBase f Y) t ≫ pullback.snd (Y.hom ≫ f) f ∧
    actDiagAt f Y t ≫ e = pullback.fst (Y.hom ≫ f) t

set_option backward.isDefEq.respectTransparency false in
lemma actDiagAt_actProjAt : actDiagAt f Y t ≫ actProjAt f Y t = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [actDiagAt, actProjAt, pullback.map]

set_option backward.isDefEq.respectTransparency false in
lemma isPullback_actProjAt :
    IsPullback (pullback.fst (actBase f Y) t) (actProjAt f Y t) (pullback.fst (Y.hom ≫ f) f)
      (pullback.fst (Y.hom ≫ f) t) := by
  refine IsPullback.of_bot ?_ (by simp [actProjAt, pullback.map])
    (IsPullback.of_hasPullback (Y.hom ≫ f) t)
  have : actProjAt f Y t ≫ pullback.snd (Y.hom ≫ f) t = pullback.snd (actBase f Y) t := by
    simp [actProjAt, pullback.map]
  rw [this]
  exact IsPullback.of_hasPullback (actBase f Y) t

variable [GeometricallyConnected f]

/-- Uniqueness of actions satisfying the unit law, over any base `T ⟶ S` (rigidity along the
connected fibres of `(Y ×_S X) ×_S T ⟶ Y ×_S T`). -/
theorem IsActAt.eq {e e' : pullback (actBase f Y) t ⟶ Y.left} (he : IsActAt f Y t e)
    (he' : IsActAt f Y t e') : e = e' := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  have : GeometricallyConnected (actProjAt f Y t) :=
    MorphismProperty.of_isPullback (isPullback_actProjAt f Y t)
      (inferInstance : GeometricallyConnected (pullback.fst (Y.hom ≫ f) f))
  exact eq_of_isSection_of_geometricallyConnected Y.hom (he.1.trans he'.1.symm)
    (actProjAt f Y t) (actDiagAt f Y t) (actDiagAt_actProjAt f Y t) (he.2.trans he'.2.symm)

set_option backward.isDefEq.respectTransparency false in
omit [GeometricallyConnected f] in
/-- Base change of an action along `m : T' ⟶ T`. -/
lemma IsActAt.comp {e : pullback (actBase f Y) t ⟶ Y.left} (he : IsActAt f Y t e)
    {T' : Scheme.{u}} (m : T' ⟶ T) (t' : T' ⟶ S) (hm : m ≫ t = t') :
    IsActAt f Y t' (pullback.map (actBase f Y) t' (actBase f Y) t (𝟙 _) m (𝟙 S)
      (by simp) (by rw [Category.comp_id, hm]) ≫ e) := by
  constructor
  · rw [Category.assoc, he.1, pullback.lift_fst_assoc, Category.comp_id]
  · have : actDiagAt f Y t' ≫ pullback.map (actBase f Y) t' (actBase f Y) t (𝟙 _) m (𝟙 S)
        (by simp) (by rw [Category.comp_id, hm]) =
        pullback.map (Y.hom ≫ f) t' (Y.hom ≫ f) t (𝟙 _) m (𝟙 S) (by simp)
          (by rw [Category.comp_id, hm]) ≫ actDiagAt f Y t := by
      apply pullback.hom_ext <;> simp [actDiagAt, pullback.map]
    rw [reassoc_of% this, he.2, pullback.lift_fst, Category.comp_id]

end ActAt

section Spreading

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)
  [IsLocallyNoetherian S] [IsProper f]

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 for actions: an action over `Spec 𝒪_{S,s}` satisfying the unit law spreads out to
an action over an open neighbourhood of `s`. -/
theorem exists_isLocalAct_of_isActAt_stalk (s : S)
    {e : pullback (actBase f Y) (S.fromSpecStalk s) ⟶ Y.left}
    (he : IsActAt f Y (S.fromSpecStalk s) e) :
    ∃ (V : S.Opens) (b : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶
      Y.left), s ∈ V ∧ IsLocalAct f Y V b := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  -- the limit over the affine neighbourhoods of `s`, for `Y ×_S X` and for `Y`
  have hX := IsPullback.of_hasPullback (actBase f Y) (S.fromSpecStalk s)
  have hc := Scheme.isLimitPreimageConeOfIsPullback hX
  have hXY := IsPullback.of_hasPullback (Y.hom ≫ f) (S.fromSpecStalk s)
  have hcY := Scheme.isLimitPreimageConeOfIsPullback hXY
  let D := S.preimageDiagram s (actBase f Y)
  let c := Scheme.preimageConeOfIsPullback s (actBase f Y) hX
  let DY := S.preimageDiagram s (Y.hom ≫ f)
  let cY := Scheme.preimageConeOfIsPullback s (Y.hom ≫ f) hXY
  have hcond : pullback.snd (Y.hom ≫ f) f ≫ f = actBase f Y := pullback.condition.symm
  -- spreading out `e`
  obtain ⟨V₁, b₁, hb₁, hb₁f⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D
    (S.preimageDiagramTo s (actBase f Y) (actBase f Y)) (Y.hom ≫ f) c hc e (by
      ext U
      simp only [NatTrans.comp_app, Scheme.preimageDiagramTo_app, Functor.const_obj_obj,
        Functor.const_map_app]
      rw [Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX, reassoc_of% he.1, hcond])
  -- spreading out the compatibility with the projection to `X`
  obtain ⟨V₂, g₂₁, hV₂⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D
    (S.preimageDiagramTo s (actBase f Y) (actBase f Y)) f c hc (b₁ ≫ Y.hom)
    ((actBase f Y ⁻¹ᵁ V₁.1).ι ≫ pullback.snd (Y.hom ≫ f) f)
    (by rw [Category.assoc, hb₁f]) (by rw [Category.assoc, hcond]; rfl) (by
      rw [reassoc_of% hb₁, he.1, Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX])
  -- spreading out the unit law
  have hσ (V : S.AffineNhds s) : cY.π.app V ≫ actDiagRes f Y V.1 =
      actDiagAt f Y (S.fromSpecStalk s) ≫ c.π.app V := by
    have e₁ : c.π.app V ≫ Scheme.Opens.ι
        (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ (Y.hom ≫ f) ⁻¹ᵁ V.1) =
        pullback.fst (actBase f Y) (S.fromSpecStalk s) :=
      Scheme.preimageConeOfIsPullback_π_app_ι hX V
    rw [← cancel_mono (Scheme.Opens.ι _), Category.assoc, Scheme.Hom.resLE_comp_ι,
      Scheme.preimageConeOfIsPullback_π_app_ι_assoc hXY, Category.assoc, e₁]
    simp [actDiagAt, pullback.map]
  obtain ⟨V₃, g₃₂, hV₃⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType DY
    (S.preimageDiagramTo s (Y.hom ≫ f) (Y.hom ≫ f)) (Y.hom ≫ f) cY hcY
    (actDiagRes f Y V₂.1 ≫ D.map g₂₁ ≫ b₁) ((Y.hom ≫ f) ⁻¹ᵁ V₂.1).ι (by
      have k₁ : D.map g₂₁ ≫ b₁ ≫ Y.hom ≫ f = (actBase f Y ⁻¹ᵁ V₂.1).ι ≫ actBase f Y := by
        rw [hb₁f]
        simp [D]
      have k₂ : actDiagRes f Y V₂.1 ≫ (actBase f Y ⁻¹ᵁ V₂.1).ι =
          ((Y.hom ≫ f) ⁻¹ᵁ V₂.1).ι ≫ actDiag f Y := Scheme.Hom.resLE_comp_ι _ _
      simp only [Scheme.preimageDiagramTo_app, Category.assoc]
      rw [k₁, reassoc_of% k₂, pullback.lift_fst_assoc, Category.id_comp]) rfl (by
      have hw : c.π.app V₂ ≫ D.map g₂₁ = c.π.app V₁ := c.w g₂₁
      rw [reassoc_of% hσ V₂, Scheme.preimageConeOfIsPullback_π_app_ι hXY, reassoc_of% hw,
        hb₁, he.2])
  refine ⟨V₃.1, D.map (g₃₂ ≫ g₂₁) ≫ b₁, V₃.2.2, ?_, ?_⟩
  · rw [Functor.map_comp, Category.assoc, Category.assoc, hV₂]
    simp only [D, Scheme.homOfLE_ι_assoc]
    rfl
  · have k (V : S.AffineNhds s) : actDiagRes f Y V.1 ≫ (actBase f Y ⁻¹ᵁ V.1).ι =
        ((Y.hom ≫ f) ⁻¹ᵁ V.1).ι ≫ actDiag f Y := Scheme.Hom.resLE_comp_ι _ _
    have hres : actDiagRes f Y V₃.1 ≫ D.map g₃₂ = DY.map g₃₂ ≫ actDiagRes f Y V₂.1 := by
      rw [← cancel_mono (Scheme.Opens.ι _)]
      simp only [D, DY, Category.assoc, Scheme.homOfLE_ι]
      rw [k, k, Scheme.homOfLE_ι_assoc]
    rw [Functor.map_comp, Category.assoc, reassoc_of% hres, hV₃]
    simp only [DY, Scheme.homOfLE_ι]

end Spreading

section Completion

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)

/-- Geometric triviality on the fibre `X_s` passes to any `F ⟶ X` lying over `Spec κ(s)`. -/
lemma mem_essImage_of_isGeometricallyTrivial (s : S)
    (hY : IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y))
    {F T' : Scheme.{u}} (ι' : F ⟶ X) (g' : F ⟶ T') (m : T' ⟶ Spec (S.residueField s))
    (h : ι' ≫ f = g' ≫ m ≫ S.fromSpecResidueField s) :
    (pb g').essImage ((pb ι').obj Y) := by
  obtain ⟨L, ⟨eL⟩⟩ := hY
  let u : F ⟶ f.fiber s := pullback.lift ι' (g' ≫ m) (by rw [h, Category.assoc])
  have hu₁ : u ≫ f.fiberι s = ι' := pullback.lift_fst _ _ _
  have hu₂ : u ≫ f.fiberToSpecResidueField s = g' ≫ m := pullback.lift_snd _ _ _
  exact ⟨(pb m).obj L, ⟨((fetPullbackCompCongr (f.fiberToSpecResidueField s) u m g' hu₂).app
    L).symm ≪≫ (pb u).mapIso eL ≪≫
      ((MorphismProperty.Over.pullbackComp u (f.fiberι s)).app Y).symm ≪≫
        (MorphismProperty.Over.pullbackCongr hu₁).app Y⟩⟩

lemma fromSpecResidueField_congr_inv {Z : Scheme.{u}} {x y : Z} (e : x = y) :
    Spec.map (Z.residueFieldCongr e).inv ≫ Z.fromSpecResidueField y = Z.fromSpecResidueField x := by
  subst e
  simp

lemma fromSpecCompletedStalk_closedPoint [IsLocallyNoetherian S] (s : S) :
    fromSpecCompletedStalk S s (IsLocalRing.closedPoint (AdicCompletion
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s))) = s := by
  obtain ⟨pt, hpt⟩ : ∃ pt : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal
      (S.presheaf.stalk s)) (S.presheaf.stalk s))), pt = IsLocalRing.closedPoint _ := ⟨_, rfl⟩
  have : IsLocalHom (CommRingCat.ofHom (algebraMap (S.presheaf.stalk s) (AdicCompletion
      (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)))).hom := by
    rw [CommRingCat.hom_ofHom]
    infer_instance
  rw [← hpt, fromSpecCompletedStalk, Scheme.Hom.comp_apply, hpt, Spec_closedPoint,
    Scheme.fromSpecStalk_closedPoint]

end Completion

section CompletedAct

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)
  [IsLocallyNoetherian S] [IsProper f]

set_option backward.isDefEq.respectTransparency false in
/-- IX.6.6 over `Spec 𝒪̂_{S,s}`: if `Y` is geometrically trivial on the fibre `X_s`, then over the
completed local ring `𝒪̂_{S,s}` it comes from the base (IX.1.10 and henselian lifting), hence
carries an action satisfying the unit law. -/
theorem exists_isActAt_fromSpecCompletedStalk (s : S)
    (hY : IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y)) :
    ∃ e, IsActAt f Y (fromSpecCompletedStalk S s) e := by
  have hpt := fromSpecCompletedStalk_closedPoint (S := S) s
  let c := fromSpecCompletedStalk S s
  let fO := pullback.snd f c
  let mh : Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
    (S.presheaf.stalk s))) := IsLocalRing.closedPoint _
  -- the closed fibre of `X ×_S 𝒪̂` is geometrically trivial
  have hfib : fO.fiberι mh ≫ fO = fO.fiberToSpecResidueField mh ≫
      (Spec (.of (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s))
        (S.presheaf.stalk s)))).fromSpecResidueField mh := pullback.condition
  have hGT : IsGeometricallyTrivial (fO.fiberToSpecResidueField mh)
      ((pb (fO.fiberι mh)).obj ((pb (pullback.fst f c)).obj Y)) := by
    have e₁ : (Spec.map (c.residueFieldMap mh) ≫ Spec.map (S.residueFieldCongr hpt).inv) ≫
        S.fromSpecResidueField s = (Spec _).fromSpecResidueField mh ≫ c := by
      rw [Category.assoc, fromSpecResidueField_congr_inv,
        Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
    have h₀ := mem_essImage_of_isGeometricallyTrivial f Y s hY (fO.fiberι mh ≫ pullback.fst f c)
      (fO.fiberToSpecResidueField mh)
      (Spec.map (c.residueFieldMap mh) ≫ Spec.map (S.residueFieldCongr hpt).inv) (by
        rw [e₁, Category.assoc, pullback.condition, ← Category.assoc, hfib, Category.assoc])
    exact Functor.essImage.ofIso ((MorphismProperty.Over.pullbackComp _ _).app Y) h₀
  obtain ⟨W, ⟨φ⟩⟩ := (mem_essImage_iff_isGeometricallyTrivial_closedFibre
    (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) fO
      _).mpr hGT
  -- the action
  let k := pullback.fst (actBase f Y) c
  let oh := pullback.snd (actBase f Y) c
  have hkc : k ≫ actBase f Y = oh ≫ c := pullback.condition
  have hcond : pullback.snd (Y.hom ≫ f) f ≫ f = actBase f Y := pullback.condition.symm
  obtain ⟨yt, hyt₁, hyt₂⟩ : ∃ yt : pullback (actBase f Y) c ⟶ ((pb (pullback.fst f c)).obj Y).left,
      yt ≫ fetProj (pullback.fst f c) Y = k ≫ pullback.fst (Y.hom ≫ f) f ∧
        yt ≫ ((pb (pullback.fst f c)).obj Y).hom =
          pullback.lift (k ≫ pullback.fst (Y.hom ≫ f) f ≫ Y.hom) oh
            (by rw [Category.assoc, Category.assoc, ← hkc]) :=
    ⟨fetLift (pullback.fst f c) Y (k ≫ pullback.fst (Y.hom ≫ f) f)
      (pullback.lift (k ≫ pullback.fst (Y.hom ≫ f) f ≫ Y.hom) oh
        (by rw [Category.assoc, Category.assoc, ← hkc]))
      (by rw [pullback.lift_fst, Category.assoc]), fetLift_fetProj _ _ _ _ _,
      fetLift_hom _ _ _ _ _⟩
  obtain ⟨xt, hxt₁, hxt₂⟩ : ∃ xt : pullback (actBase f Y) c ⟶ pullback f c,
      xt ≫ pullback.fst f c = k ≫ pullback.snd (Y.hom ≫ f) f ∧ xt ≫ fO = oh :=
    ⟨pullback.lift (k ≫ pullback.snd (Y.hom ≫ f) f) oh (by rw [Category.assoc, hcond, hkc]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hw : (yt ≫ φ.inv.left ≫ fetProj fO W) ≫ W.hom = xt ≫ fO := by
    rw [Category.assoc, Category.assoc, fetProj_hom, MorphismProperty.Over.w_assoc,
      reassoc_of% hyt₂, hxt₂]
    exact pullback.lift_snd _ _ _
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z : pullback (actBase f Y) c ⟶ ((pb fO).obj W).left,
      z ≫ fetProj fO W = yt ≫ φ.inv.left ≫ fetProj fO W ∧ z ≫ ((pb fO).obj W).hom = xt :=
    ⟨fetLift fO W _ xt hw, fetLift_fetProj _ _ _ _ _, fetLift_hom _ _ _ _ _⟩
  refine ⟨z ≫ φ.hom.left ≫ fetProj (pullback.fst f c) Y, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, fetProj_hom, MorphismProperty.Over.w_assoc,
      reassoc_of% hz₂, hxt₁]
  · -- along the diagonal, `z` is `φ⁻¹(yt)`
    let d := actDiagAt f Y c
    have hdk : d ≫ k = pullback.fst (Y.hom ≫ f) c ≫ actDiag f Y := pullback.lift_fst _ _ _
    have hdoh : d ≫ oh = pullback.snd (Y.hom ≫ f) c := by
      simp [d, oh, actDiagAt, pullback.map]
    have hdz : d ≫ z = d ≫ yt ≫ φ.inv.left := by
      apply fetPullback_hom_ext
      · rw [Category.assoc, hz₁, Category.assoc, Category.assoc]
      · rw [Category.assoc, hz₂, Category.assoc, Category.assoc,
          MorphismProperty.Over.w, hyt₂]
        apply pullback.hom_ext
        · rw [Category.assoc, hxt₁, Category.assoc, pullback.lift_fst, reassoc_of% hdk,
            reassoc_of% hdk]
          simp only [actDiag, pullback.lift_snd, pullback.lift_fst_assoc]
          exact congrArg (pullback.fst (Y.hom ≫ f) c ≫ ·) (Category.id_comp Y.hom).symm
        · rw [Category.assoc, hxt₂, hdoh, Category.assoc, pullback.lift_snd, hdoh]
    have hinv : φ.inv.left ≫ φ.hom.left = 𝟙 _ := congrArg (fun g ↦ g.left) φ.inv_hom_id
    change d ≫ z ≫ φ.hom.left ≫ fetProj (pullback.fst f c) Y = _
    rw [reassoc_of% hdz, reassoc_of% hinv, hyt₁, reassoc_of% hdk]
    simp [actDiag]
    rfl

end CompletedAct

section StalkAct

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)
  [GeometricallyConnected f]

set_option backward.isDefEq.respectTransparency false in
/-- An action over `ρ ≫ ι` satisfying the unit law descends along a faithfully flat
quasi-compact `ρ` (VIII.5.2): its two pullbacks to `T' ×_T T'` agree since actions satisfying the
unit law are unique (`IsActAt.eq`). -/
theorem exists_isActAt_of_fpqc {T T' : Scheme.{u}} (ι : T ⟶ S) (ρ : T' ⟶ T) [Flat ρ]
    [Surjective ρ] [QuasiCompact ρ] {e : pullback (actBase f Y) (ρ ≫ ι) ⟶ Y.left}
    (he : IsActAt f Y (ρ ≫ ι) e) : ∃ e', IsActAt f Y ι e' := by
  let π' := pullback.fst (pullback.snd (actBase f Y) ι) ρ
  let j := pullbackLeftPullbackSndIso (actBase f Y) ι ρ
  have hj₁ : j.hom ≫ pullback.fst (actBase f Y) (ρ ≫ ι) = π' ≫ pullback.fst (actBase f Y) ι :=
    pullbackLeftPullbackSndIso_hom_fst _ _ _
  have hj₂ : j.hom ≫ pullback.snd (actBase f Y) (ρ ≫ ι) =
      pullback.snd (pullback.snd (actBase f Y) ι) ρ :=
    pullbackLeftPullbackSndIso_hom_snd _ _ _
  let u : pullback (pullback.snd (actBase f Y) ι) ρ ⟶ Y.left := j.hom ≫ e
  have H : ∀ {Z : Scheme.{u}} (a b : Z ⟶ pullback (pullback.snd (actBase f Y) ι) ρ),
      a ≫ π' = b ≫ π' → a ≫ u = b ≫ u := by
    intro Z a b hab
    let ah := a ≫ j.hom ≫ pullback.snd (actBase f Y) (ρ ≫ ι)
    let bh := b ≫ j.hom ≫ pullback.snd (actBase f Y) (ρ ≫ ι)
    have hα : (a ≫ j.hom) ≫ pullback.fst (actBase f Y) (ρ ≫ ι) =
        (b ≫ j.hom) ≫ pullback.fst (actBase f Y) (ρ ≫ ι) := by
      rw [Category.assoc, Category.assoc, hj₁, reassoc_of% hab]
    have hab' : bh ≫ ρ ≫ ι = ah ≫ ρ ≫ ι := by
      simp only [ah, bh, Category.assoc, reassoc_of% hj₂]
      rw [← pullback.condition_assoc]
      have := hab =≫ (pullback.snd (actBase f Y) ι ≫ ι)
      simp only [π', Category.assoc] at this
      exact this.symm
    have ea := he.comp f Y (ρ ≫ ι) ah (ah ≫ ρ ≫ ι) rfl
    have eb := he.comp f Y (ρ ≫ ι) bh (ah ≫ ρ ≫ ι) hab'
    have heq := ea.eq f Y _ eb
    let α := (a ≫ j.hom) ≫ pullback.fst (actBase f Y) (ρ ≫ ι)
    have hαA : α ≫ actBase f Y = 𝟙 Z ≫ ah ≫ ρ ≫ ι := by
      simp only [α, ah, Category.assoc, Category.id_comp]
      rw [pullback.condition]
    let ζ : Z ⟶ pullback (actBase f Y) (ah ≫ ρ ≫ ι) := pullback.lift α (𝟙 Z) hαA
    have hζa : ζ ≫ pullback.map (actBase f Y) (ah ≫ ρ ≫ ι) (actBase f Y) (ρ ≫ ι) (𝟙 _) ah
        (𝟙 S) (by simp) (by rw [Category.comp_id]) = a ≫ j.hom := by
      apply pullback.hom_ext
      · simp only [ζ, Category.assoc, pullback.lift_fst, Category.comp_id]
        rfl
      · simp only [ζ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.id_comp]
        rfl
    have hζb : ζ ≫ pullback.map (actBase f Y) (ah ≫ ρ ≫ ι) (actBase f Y) (ρ ≫ ι) (𝟙 _) bh
        (𝟙 S) (by simp) (by rw [Category.comp_id, hab']) = b ≫ j.hom := by
      apply pullback.hom_ext
      · simp only [ζ, Category.assoc, pullback.lift_fst, Category.comp_id]
        exact hα
      · simp only [ζ, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
          Category.id_comp]
        rfl
    change (a ≫ j.hom) ≫ e = (b ≫ j.hom) ≫ e
    rw [← hζa, ← hζb]
    exact (Category.assoc _ _ _).trans ((congrArg (ζ ≫ ·) heq).trans (Category.assoc _ _ _).symm)
  have hfac : π' ≫ EffectiveEpi.desc π' u H = u := EffectiveEpi.fac π' u H
  refine ⟨EffectiveEpi.desc π' u H, ?_, ?_⟩
  · rw [← cancel_epi π', reassoc_of% hfac, Category.assoc, he.1, ← Category.assoc, hj₁,
      Category.assoc]
  · -- the diagonal, over `T'`
    let πY := pullback.fst (pullback.snd (Y.hom ≫ f) ι) ρ
    let jY := pullbackLeftPullbackSndIso (Y.hom ≫ f) ι ρ
    have hjY₁ : jY.hom ≫ pullback.fst (Y.hom ≫ f) (ρ ≫ ι) = πY ≫ pullback.fst (Y.hom ≫ f) ι :=
      pullbackLeftPullbackSndIso_hom_fst _ _ _
    have hjY₂ : jY.hom ≫ pullback.snd (Y.hom ≫ f) (ρ ≫ ι) =
        pullback.snd (pullback.snd (Y.hom ≫ f) ι) ρ :=
      pullbackLeftPullbackSndIso_hom_snd _ _ _
    have hσ : πY ≫ actDiagAt f Y ι = (jY.hom ≫ actDiagAt f Y (ρ ≫ ι) ≫ j.inv) ≫ π' := by
      apply pullback.hom_ext
      · have h₁ : j.inv ≫ π' ≫ pullback.fst (actBase f Y) ι =
            pullback.fst (actBase f Y) (ρ ≫ ι) := by
          rw [← hj₁, Iso.inv_hom_id_assoc]
        rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, h₁]
        simp only [actDiagAt, pullback.map, pullback.lift_fst, reassoc_of% hjY₁]
      · have h₂ : j.inv ≫ π' ≫ pullback.snd (actBase f Y) ι =
            pullback.snd (actBase f Y) (ρ ≫ ι) ≫ ρ := by
          rw [pullback.condition, ← reassoc_of% hj₂, Iso.inv_hom_id_assoc]
        rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, h₂]
        simp only [actDiagAt, pullback.map, pullback.lift_snd, Category.comp_id,
          pullback.lift_snd_assoc, reassoc_of% hjY₂]
        exact pullback.condition
    rw [← cancel_epi πY, reassoc_of% hσ, hfac]
    simp only [u, Iso.inv_hom_id_assoc, he.2, hjY₁]

set_option backward.isDefEq.respectTransparency false in
/-- An action over `Spec 𝒪̂_{S,s}` satisfying the unit law descends to `Spec 𝒪_{S,s}`. -/
theorem exists_isActAt_fromSpecStalk [IsLocallyNoetherian S] (s : S)
    {e : pullback (actBase f Y) (fromSpecCompletedStalk S s) ⟶ Y.left}
    (he : IsActAt f Y (fromSpecCompletedStalk S s) e) :
    ∃ e', IsActAt f Y (S.fromSpecStalk s) e' := by
  obtain ⟨hflat, hsurj⟩ := flat_and_surjective_specMap_completion (S := S) s
  exact exists_isActAt_of_fpqc f Y (S.fromSpecStalk s) _ he

end StalkAct

section Assembly

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [IsProper f]
  [GeometricallyConnected f]

/-- **IX.6.7** (locally noetherian base): let `f : X ⟶ S` be proper with geometrically connected
fibres. An étale covering `Y` of `X` which is geometrically trivial on every fibre `X_s` comes
from an étale covering of `S`. The action of IX.4 exists over each `Spec 𝒪̂_{S,s}` (IX.6.6),
descends to `Spec 𝒪_{S,s}`, spreads out to a neighbourhood of `s`, and the local actions glue by
uniqueness. -/
theorem mem_essImage_of_forall_isGeometricallyTrivial (Y : MorphismProperty.Over FEt ⊤ X)
    (hY : ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y)) :
    (pb f).essImage Y := by
  refine mem_essImage_of_forall_exists_localAct f Y fun s ↦ ?_
  obtain ⟨e, he⟩ := exists_isActAt_fromSpecCompletedStalk f Y s (hY s)
  obtain ⟨e', he'⟩ := exists_isActAt_fromSpecStalk f Y s he
  exact exists_isLocalAct_of_isActAt_stalk f Y s he'

/-- **IX.6.8**, the essential image (locally noetherian base): for `f : X ⟶ S` proper with
geometrically connected fibres, an étale covering of `X` comes from `S` iff it is geometrically
trivial on every fibre `X_s`. -/
theorem mem_essImage_iff_forall_isGeometricallyTrivial (Y : MorphismProperty.Over FEt ⊤ X) :
    (pb f).essImage Y ↔
      ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y) :=
  ⟨fun h s ↦ isGeometricallyTrivial_of_mem_essImage f s h,
    mem_essImage_of_forall_isGeometricallyTrivial f Y⟩

/-- **IX.6.8 over a locally noetherian base** (the conclusion of `ProperDescentStatement`; no
finite presentation hypothesis is needed, `f` being proper over a locally noetherian base): for
`f : X ⟶ S` proper and surjective with geometrically connected fibres, `f` is an effective descent
morphism for étale coverings, `f^*` is fully faithful, and its essential image consists of the
étale coverings of `X` which are geometrically trivial on every fibre. -/
theorem properDescentStatement_of_isLocallyNoetherian [Surjective f] :
    (fetComparison f).IsEquivalence ∧ (pb f).Full ∧ (pb f).Faithful ∧
      ∀ Y : MorphismProperty.Over FEt ⊤ X, (pb f).essImage Y ↔
        ∀ s, IsGeometricallyTrivial (f.fiberToSpecResidueField s) ((pb (f.fiberι s)).obj Y) :=
  ⟨(properDescent_of_isLocallyNoetherian f).1, (properDescent_of_isLocallyNoetherian f).2.1,
    (properDescent_of_isLocallyNoetherian f).2.2, mem_essImage_iff_forall_isGeometricallyTrivial f⟩

end Assembly

end SGA.SGA1.ExposeIX
