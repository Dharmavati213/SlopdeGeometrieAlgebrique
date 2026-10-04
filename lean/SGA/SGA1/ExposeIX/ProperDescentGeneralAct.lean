/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.EffectiveDescentGeneral
import SGA.SGA1.ExposeIX.ProperDescentLocal

/-!
# SGA 1, Exposé IX, 6.7: actions over an arbitrary base

Let `f : X ⟶ S` be proper with geometrically connected fibres and `Y` an étale covering of `X`.
This file extends the tools of `SGA.SGA1.ExposeIX.ProperDescentRigidity` and
`SGA.SGA1.ExposeIX.ProperDescentLocal` (actions of the groupoid `X ×_S X ⇉ X` on `Y`, IX.6.7) from
a locally noetherian base to `f` of finite presentation over an arbitrary base, using IX.4.12 over
an arbitrary base (`isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation`).

* `exists_isActAt_of_mem_essImage`, `exists_isActAt_of_isPullback`: if `Y` comes from the base
  after base change along `t : T ⟶ S`, it carries an action over `t` (the argument at the end of
  `exists_isActAt_fromSpecCompletedStalk`, for any `t`).
* `exists_act_of_isActAt_id`: an action over `𝟙 S` is an action.
* `mem_essImage_of_act_of_locallyOfFinitePresentation`: IX.4.12 in the form used for IX.6.7, over
  an arbitrary base.
* `mem_essImage_of_isPullback_of_fpqc`: **the essential image of `f^*` is fpqc local on `S`**:
  `Y` comes from `S` if it does after a flat, surjective, quasi-compact base change `T ⟶ S`
  (VIII.5.2 for the action, `exists_isActAt_of_fpqc`).
* `exists_isLocalAct_of_isActAt_stalk_of_locallyOfFinitePresentation`,
  `mem_essImage_of_forall_exists_localAct_of_locallyOfFinitePresentation`: spreading out an
  action from `Spec 𝒪_{S,s}` to a neighbourhood of `s` and gluing local actions, for `f` of
  finite presentation (the proofs of `exists_isLocalAct_of_isActAt_stalk` and
  `mem_essImage_of_forall_exists_localAct` with `[LocallyOfFinitePresentation f]` in place of
  `[IsLocallyNoetherian S]`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty

namespace SGA.SGA1.ExposeIX

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

section ActOfEssImage

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)

set_option backward.isDefEq.respectTransparency false in
/-- If `Y` comes from the base after base change along `t : T ⟶ S` (`Y ×_S T ≅ X ×_S W` for an
étale covering `W` of `T`), then `Y` carries an action over `t` satisfying the unit law. -/
theorem exists_isActAt_of_mem_essImage {T : Scheme.{u}} (t : T ⟶ S)
    (hY : (pb (pullback.snd f t)).essImage ((pb (pullback.fst f t)).obj Y)) :
    ∃ e, IsActAt f Y t e := by
  obtain ⟨W, ⟨φ⟩⟩ := hY
  let c := t
  let fO := pullback.snd f c
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

set_option backward.isDefEq.respectTransparency false in
/-- `exists_isActAt_of_mem_essImage` for any cartesian square `P = X ×_S T`. -/
theorem exists_isActAt_of_isPullback {T P : Scheme.{u}} (t : T ⟶ S) {p : P ⟶ X} {q : P ⟶ T}
    (h : IsPullback p q f t) (hY : (pb q).essImage ((pb p).obj Y)) : ∃ e, IsActAt f Y t e := by
  refine exists_isActAt_of_mem_essImage f Y t ?_
  obtain ⟨W, ⟨φ⟩⟩ := hY
  let ψ := h.isoPullback
  have h₁ : ψ.inv ≫ p = pullback.fst f t := h.isoPullback_inv_fst
  have h₂ : ψ.inv ≫ q = pullback.snd f t := h.isoPullback_inv_snd
  exact ⟨W, ⟨((MorphismProperty.Over.pullbackCongr h₂).app W).symm ≪≫
    (MorphismProperty.Over.pullbackComp ψ.inv q).app W ≪≫ (pb ψ.inv).mapIso φ ≪≫
      ((MorphismProperty.Over.pullbackComp ψ.inv p).app Y).symm ≪≫
        (MorphismProperty.Over.pullbackCongr h₁).app Y⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- An action over the identity `𝟙 S` is an action `Y ×_S X ⟶ Y` satisfying the unit law. -/
theorem exists_act_of_isActAt_id {e : pullback (actBase f Y) (𝟙 S) ⟶ Y.left}
    (he : IsActAt f Y (𝟙 S) e) :
    ∃ act : pullback (Y.hom ≫ f) f ⟶ Y.left,
      act ≫ Y.hom = pullback.snd _ _ ∧ actDiag f Y ≫ act = 𝟙 _ := by
  let l : pullback (Y.hom ≫ f) f ⟶ pullback (actBase f Y) (𝟙 S) :=
    pullback.lift (𝟙 _) (actBase f Y) (by simp)
  refine ⟨l ≫ e, ?_, ?_⟩
  · rw [Category.assoc, he.1, pullback.lift_fst_assoc, Category.id_comp]
  · have hd : actDiag f Y ≫ l = pullback.lift (f := Y.hom ≫ f) (g := 𝟙 S) (𝟙 _) (Y.hom ≫ f)
        (by simp) ≫ actDiagAt f Y (𝟙 S) := by
      apply pullback.hom_ext
      · simp only [l, actDiagAt, pullback.map, Category.assoc, pullback.lift_fst,
          Category.comp_id, pullback.lift_fst_assoc, Functor.id_obj, Category.id_comp]
      · simp only [l, actDiagAt, pullback.map, Category.assoc, pullback.lift_snd,
          Category.comp_id, actBase, pullback.lift_fst_assoc]
        exact Category.id_comp _
    rw [reassoc_of% hd, he.2, pullback.lift_fst]

end ActOfEssImage

section General

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)
  [IsProper f] [Surjective f] [LocallyOfFinitePresentation f] [GeometricallyConnected f]

/-- IX.4.12 in the form used for IX.6.7, over an arbitrary base: an étale covering of `X` with an
action satisfying the unit law comes from an étale covering of `S` (`f` proper, surjective, of
finite presentation, with geometrically connected fibres). -/
theorem mem_essImage_of_act_of_locallyOfFinitePresentation
    (act : pullback (Y.hom ≫ f) f ⟶ Y.left)
    (h : act ≫ Y.hom = pullback.snd _ _) (hu : actDiag f Y ≫ act = 𝟙 _) :
    (pb f).essImage Y := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  obtain ⟨Xw, b, v, hb, hv, -⟩ :=
    (isEffectiveDescentMorphism_of_isProper_of_locallyOfFinitePresentation f).2 Y.hom
      (descentDatumOfAct f Y act h hu) ⟨inferInstance, inferInstance⟩
  have hb' : FEt b := hb
  exact ⟨MorphismProperty.Over.mk ⊤ b hb',
    ⟨(MorphismProperty.Over.isoMk hv.isoPullback hv.isoPullback_hom_snd).symm⟩⟩

/-- **The essential image of `f^*` is fpqc local on the base** (VIII.5.2 and IX.6.7): let `f` be
proper, surjective, of finite presentation, with geometrically connected fibres, and
`ρ : T ⟶ S` flat, surjective and quasi-compact. An étale covering `Y` of `X` comes from `S` as soon
as its inverse image on `P = X ×_S T` comes from `T`. -/
theorem mem_essImage_of_isPullback_of_fpqc {T P : Scheme.{u}} (ρ : T ⟶ S) [Flat ρ] [Surjective ρ]
    [QuasiCompact ρ] {p : P ⟶ X} {q : P ⟶ T} (h : IsPullback p q f ρ)
    (hY : (pb q).essImage ((pb p).obj Y)) : (pb f).essImage Y := by
  obtain ⟨e, he⟩ : ∃ e, IsActAt f Y (ρ ≫ 𝟙 S) e := by
    rw [Category.comp_id]
    exact exists_isActAt_of_isPullback f Y ρ h hY
  obtain ⟨e', he'⟩ := exists_isActAt_of_fpqc f Y (𝟙 S) ρ he
  obtain ⟨act, h₁, h₂⟩ := exists_act_of_isActAt_id f Y he'
  exact mem_essImage_of_act_of_locallyOfFinitePresentation f Y act h₁ h₂

/-- **IX.6.7, gluing and effective descent** over an arbitrary base: if every point of `S` has a
neighbourhood over which the étale covering `Y` of `X` carries an action satisfying the unit law,
`Y` comes from an étale covering of `S` (`f` proper, surjective, of finite presentation, with
geometrically connected fibres). -/
theorem mem_essImage_of_forall_exists_localAct_of_locallyOfFinitePresentation
    (hloc : ∀ s : S, ∃ (V : S.Opens) (b : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ
      ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶ Y.left), s ∈ V ∧ IsLocalAct f Y V b) :
    (pb f).essImage Y := by
  obtain ⟨act, h, hu⟩ := exists_act_of_forall_exists_localAct f Y hloc
  exact mem_essImage_of_act_of_locallyOfFinitePresentation f Y act h hu

end General

section Spreading

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)
  [LocallyOfFinitePresentation f] [IsProper f]

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 for actions, `f` of finite presentation over an arbitrary base: an action over
`Spec 𝒪_{S,s}` satisfying the unit law spreads out to an action over an open neighbourhood of
`s`. (The proof of `exists_isLocalAct_of_isActAt_stalk`, which assumes `S` locally noetherian
only to know that `Y ⟶ S` is locally of finite presentation.) -/
theorem exists_isLocalAct_of_isActAt_stalk_of_locallyOfFinitePresentation (s : S)
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

end SGA.SGA1.ExposeIX
