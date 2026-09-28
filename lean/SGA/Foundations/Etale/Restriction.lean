/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.BaseChange

/-!
# Restriction of étale sheaves along étale morphisms

For an étale morphism `g : Y' ⟶ Y`, composition with `g` is a continuous functor
`Scheme.Etale.map g : Y'.Etale ⥤ Y.Etale`, left adjoint to base change along `g`. Hence the inverse
image `g^*` of étale sheaves is the restriction `F ↦ (W' ↦ F(W'))`
(`Scheme.etalePullbackIsoRestrict`), and the base change morphism of a cartesian square along an
étale `g` is an isomorphism (`Scheme.isIso_etaleBaseChangeMap_of_etale`): this is the (trivial)
étale case of the base change theorems.

## References

* [SGA 4, Exposé VII, 1.4 and Exposé VIII, 5.1][sga4]
* [Stacks Project, Tag 03PT](https://stacks.math.columbia.edu/tag/03PT)

We also show that `Scheme.Etale.map g` is cocontinuous (`mem_smallEtaleTopology_iff` describes
the covering sieves of the small étale site pointwise).
-/

universe w u

open CategoryTheory Limits Opposite

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {Y' Y : Scheme.{u}} (g : Y' ⟶ Y) [Etale g]

/-- Composition with an étale morphism `g : Y' ⟶ Y`: an étale `Y'`-scheme is an étale
`Y`-scheme. -/
noncomputable def Etale.map : Y'.Etale ⥤ Y.Etale :=
  MorphismProperty.Over.map ⊤ (P := @Etale) (f := g) inferInstance

namespace Etale

/-- The adjunction between composition with `g` and base change along `g`. -/
noncomputable def mapPullbackAdj : Etale.map g ⊣ Etale.pullback g :=
  MorphismProperty.Over.mapPullbackAdj @Etale ⊤ g inferInstance trivial

lemma map_comp_forget :
    Etale.map g ⋙ MorphismProperty.Over.forget @Etale ⊤ Y =
      MorphismProperty.Over.forget @Etale ⊤ Y' ⋙ Over.map g :=
  rfl

lemma map_obj_hom (W : Y'.Etale) : ((Etale.map g).obj W).hom = W.hom ≫ g :=
  rfl

lemma map_obj_left (W : Y'.Etale) : ((Etale.map g).obj W).left = W.left :=
  rfl

lemma coverPreserving_map :
    CoverPreserving Y'.smallEtaleTopology Y.smallEtaleTopology (Etale.map g) := by
  constructor
  intro W R hR
  have h₁ := (MorphismProperty.Over.forget @Etale ⊤ Y').coverPreserving_restrictedTopology
    (Y'.overGrothendieckTopology @Etale)
  have h₂ := GrothendieckTopology.over_map_coverPreserving Scheme.etaleTopology g
  have hR' : Sieve.functorPushforward
      (Etale.map g ⋙ MorphismProperty.Over.forget @Etale ⊤ Y) R ∈
      (Scheme.overGrothendieckTopology (@Etale) Y) ((Etale.map g ⋙
        MorphismProperty.Over.forget @Etale ⊤ Y).obj W) :=
    (CoverPreserving.comp _ _ h₁ h₂).cover_preserve hR
  change _ ∈ Y.smallGrothendieckTopology (P := @Etale) _
  rw [Functor.mem_restrictedTopology_iff]
  rwa [Sieve.functorPushforward_comp] at hR'

@[simp]
lemma map_map_left {W₁ W₂ : Y'.Etale} (φ : W₁ ⟶ W₂) : ((Etale.map g).map φ).left = φ.left :=
  rfl

lemma compatiblePreserving_map :
    CompatiblePreserving.{w} Y.smallEtaleTopology (Etale.map g) where
  compatible F {Z T x} hx {Y₁ Y₂ W} f₁ f₂ {g₁ g₂} hg₁ hg₂ h := by
    have h' : f₁.left ≫ g₁.left = f₂.left ≫ g₂.left := by
      have := congr_arg (fun φ ↦ φ.left) h
      rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left] at this
      exact this
    have w₁ : g₁.left ≫ Z.hom = Y₁.hom := MorphismProperty.Over.w g₁
    have w₂ : g₂.left ≫ Z.hom = Y₂.hom := MorphismProperty.Over.w g₂
    let W' : Y'.Etale := Scheme.Etale.mk (f₁.left ≫ Y₁.hom)
    let g₁' : W' ⟶ Y₁ := MorphismProperty.Over.homMk f₁.left rfl
    let g₂' : W' ⟶ Y₂ := MorphismProperty.Over.homMk f₂.left (by
      change f₂.left ≫ Y₂.hom = f₁.left ≫ Y₁.hom
      rw [← w₁, ← w₂, reassoc_of% h'])
    have hcomm : g₁' ≫ g₁ = g₂' ≫ g₂ := MorphismProperty.Over.Hom.ext h'
    have hW : W.hom = f₁.left ≫ Y₁.hom ≫ g := (MorphismProperty.Over.w f₁).symm
    let e : (Etale.map g).obj W' ≅ W := MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ W.hom = (f₁.left ≫ Y₁.hom) ≫ g
      rw [hW, Category.id_comp, Category.assoc])
    have e₁ : f₁ = e.inv ≫ (Etale.map g).map g₁' := MorphismProperty.Over.Hom.ext (by
      rw [MorphismProperty.Comma.comp_left]
      exact (Category.id_comp _).symm)
    have e₂ : f₂ = e.inv ≫ (Etale.map g).map g₂' := MorphismProperty.Over.Hom.ext (by
      rw [MorphismProperty.Comma.comp_left]
      exact (Category.id_comp _).symm)
    have H : F.obj.map ((Etale.map g).map g₁').op (x g₁ hg₁) =
        F.obj.map ((Etale.map g).map g₂').op (x g₂ hg₂) := hx g₁' g₂' hg₁ hg₂ hcomm
    rw [e₁, e₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, H]

instance : (Etale.map g).IsContinuous Y'.smallEtaleTopology Y.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreserving_map g)
    (coverPreserving_map g)

@[reassoc (attr := simp)]
lemma mapPullbackAdj_unit_app_left_fst (A : Y'.Etale) :
    ((mapPullbackAdj g).unit.app A).left ≫
      Limits.pullback.fst ((Etale.map g).obj A).hom g = 𝟙 A.left :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma mapPullbackAdj_unit_app_left_snd (A : Y'.Etale) :
    ((mapPullbackAdj g).unit.app A).left ≫
      Limits.pullback.snd ((Etale.map g).obj A).hom g = A.hom :=
  Limits.pullback.lift_snd _ _ _

lemma mapPullbackAdj_counit_app_left (B : Y.Etale) :
    ((mapPullbackAdj g).counit.app B).left = Limits.pullback.fst B.hom g :=
  rfl

end Etale

/-- The restriction of étale sheaves along an étale morphism `g : Y' ⟶ Y`:
`(g^! F)(W') = F(W')` for `W'` étale over `Y'`. -/
noncomputable def etaleRestrict :
    Sheaf Y.smallEtaleTopology (Type u) ⥤ Sheaf Y'.smallEtaleTopology (Type u) :=
  (Etale.map g).sheafPushforwardContinuous (Type u) _ _

/-- Restriction along an étale morphism is left adjoint to the direct image. -/
noncomputable def etaleRestrictAdjunction : etaleRestrict g ⊣ etalePushforward g :=
  (Etale.mapPullbackAdj g).sheafPushforwardContinuous (E := Type u) _ _

/-- For `g` étale, the inverse image `g^*` is the restriction. -/
noncomputable def etalePullbackIsoRestrict : etalePullback g ≅ etaleRestrict g :=
  (etaleAdjunction g).leftAdjointUniq (etaleRestrictAdjunction g)

lemma conjugateEquiv_etalePullbackIsoRestrict_hom :
    conjugateEquiv (etaleRestrictAdjunction g) (etaleAdjunction g)
      (etalePullbackIsoRestrict g).hom = 𝟙 _ := by
  simp [etalePullbackIsoRestrict, Adjunction.leftAdjointUniq]

lemma conjugateEquiv_etalePullbackIsoRestrict_inv :
    conjugateEquiv (etaleAdjunction g) (etaleRestrictAdjunction g)
      (etalePullbackIsoRestrict g).inv = 𝟙 _ := by
  simp [etalePullbackIsoRestrict, Adjunction.leftAdjointUniq]

section BaseChangeEtale

variable {X X' : Scheme.{u}} {f : X ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'} [Etale h]

/-- The base change morphism for an étale `g`, computed with restrictions instead of inverse
images. -/
noncomputable def etaleBaseChangeMapRestrict (w : h ≫ f = f' ≫ g) :
    TwoSquare (etalePushforward f) (etaleRestrict h) (etaleRestrict g) (etalePushforward f') :=
  (mateEquiv (etaleRestrictAdjunction h) (etaleRestrictAdjunction g)).symm
    (etalePushforwardComparison w)

lemma etaleBaseChangeMap_eq_restrict (w : h ≫ f = f' ≫ g) :
    etaleBaseChangeMap w = ((etaleBaseChangeMapRestrict g w).whiskerLeft
      (etalePullbackIsoRestrict h).inv).whiskerRight (etalePullbackIsoRestrict g).hom := by
  apply (mateEquiv (etaleAdjunction h) (etaleAdjunction g)).injective
  rw [mateEquiv_etaleBaseChangeMap,
    mateEquiv_conjugateEquiv_vcomp _ (etaleRestrictAdjunction g),
    conjugateEquiv_mateEquiv_vcomp _ (etaleRestrictAdjunction h), etaleBaseChangeMapRestrict,
    Equiv.apply_symm_apply, conjugateEquiv_etalePullbackIsoRestrict_hom,
    conjugateEquiv_etalePullbackIsoRestrict_inv]
  ext F
  simp

namespace Etale

/-- The scheme-level comparison `X' ×_{Y'} W ⟶ X ×_Y W` for `W` over `Y'`. -/
noncomputable def restrictComparisonHom (w : h ≫ f = f' ≫ g) {W : Scheme.{u}}
    (p : W ⟶ Y') : Limits.pullback p f' ⟶ Limits.pullback (p ≫ g) f :=
  Limits.pullback.lift (Limits.pullback.fst _ _) (Limits.pullback.snd _ _ ≫ h) (by
    rw [← Category.assoc, Limits.pullback.condition, Category.assoc, Category.assoc, w])

omit [Etale g] [Etale h] in
@[reassoc]
lemma restrictComparisonHom_fst (w : h ≫ f = f' ≫ g) {W : Scheme.{u}} (p : W ⟶ Y') :
    restrictComparisonHom g w p ≫ Limits.pullback.fst _ _ = Limits.pullback.fst _ _ :=
  Limits.pullback.lift_fst _ _ _

omit [Etale g] [Etale h] in
@[reassoc]
lemma restrictComparisonHom_snd (w : h ≫ f = f' ≫ g) {W : Scheme.{u}} (p : W ⟶ Y') :
    restrictComparisonHom g w p ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ ≫ h :=
  Limits.pullback.lift_snd _ _ _

omit [Etale h] in
@[reassoc (attr := simp)]
lemma restrictComparisonHom_fst' (w : h ≫ f = f' ≫ g) (W : Y'.Etale) :
    restrictComparisonHom g w W.hom ≫ Limits.pullback.fst ((Etale.map g).obj W).hom f =
      Limits.pullback.fst W.hom f' :=
  Limits.pullback.lift_fst _ _ _

omit [Etale h] in
@[reassoc (attr := simp)]
lemma restrictComparisonHom_snd' (w : h ≫ f = f' ≫ g) (W : Y'.Etale) :
    restrictComparisonHom g w W.hom ≫ Limits.pullback.snd ((Etale.map g).obj W).hom f =
      Limits.pullback.snd W.hom f' ≫ h :=
  Limits.pullback.lift_snd _ _ _

/-- The natural transformation `X' ×_{Y'} W' ⟶ X ×_Y W'` of functors `Y'.Etale ⥤ X.Etale`. -/
noncomputable def restrictComparison (w : h ≫ f = f' ≫ g) :
    Etale.pullback f' ⋙ Etale.map h ⟶ Etale.map g ⋙ Etale.pullback f where
  app W := MorphismProperty.Over.homMk (restrictComparisonHom g w W.hom)
    (restrictComparisonHom_snd g w W.hom)
  naturality W₁ W₂ φ := by
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    apply Limits.pullback.hom_ext <;> simp

@[simp]
lemma restrictComparison_app_left (w : h ≫ f = f' ≫ g) (W : Y'.Etale) :
    ((restrictComparison g w).app W).left = restrictComparisonHom g w W.hom :=
  rfl

instance : (Etale.pullback f' ⋙ Etale.map h).IsContinuous Y'.smallEtaleTopology
    X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ X'.smallEtaleTopology _

instance : (Etale.map g ⋙ Etale.pullback f).IsContinuous Y'.smallEtaleTopology
    X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

lemma baseChangeComparison_app_eq_restrict (w : h ≫ f = f' ≫ g) (W : Y.Etale) :
    (baseChangeComparison w).app W =
      (mapPullbackAdj h).unit.app ((Etale.pullback f').obj ((Etale.pullback g).obj W)) ≫
        (Etale.pullback h).map ((restrictComparison g w).app ((Etale.pullback g).obj W)) ≫
        (Etale.pullback h).map ((Etale.pullback f).map ((mapPullbackAdj g).counit.app W)) := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext
    · simp [mapPullbackAdj_counit_app_left]
    · simp
  · simp
    rfl

omit [Etale g] [Etale h] in
/-- If the square is cartesian, `X' ×_{Y'} W ⟶ X ×_Y W` is an isomorphism. -/
lemma isIso_restrictComparisonHom (hX : IsPullback h f' f g) {W : Scheme.{u}}
    (p : W ⟶ Y') : IsIso (restrictComparisonHom g hX.w p) := by
  have hP := (IsPullback.of_hasPullback p f').paste_vert hX.flip
  have : restrictComparisonHom g hX.w p = hP.isoPullback.hom := by
    apply Limits.pullback.hom_ext
    · rw [restrictComparisonHom_fst, IsPullback.isoPullback_hom_fst]
    · rw [restrictComparisonHom_snd, IsPullback.isoPullback_hom_snd]
  rw [this]
  infer_instance

lemma isIso_restrictComparison (hX : IsPullback h f' f g) :
    IsIso (restrictComparison g hX.w) := by
  have (W : Y'.Etale) : IsIso ((restrictComparison g hX.w).app W) := by
    have : IsIso ((Over.forget X).map
        ((Scheme.Etale.forget X).map ((restrictComparison g hX.w).app W))) :=
      isIso_restrictComparisonHom g hX W.hom
    have : IsIso ((Scheme.Etale.forget X).map ((restrictComparison g hX.w).app W)) :=
      isIso_of_reflects_iso _ (Over.forget X)
    exact isIso_of_reflects_iso _ (Scheme.Etale.forget X)
  exact NatIso.isIso_of_isIso_app _

end Etale

lemma mateEquiv_restrictComparison (w : h ≫ f = f' ≫ g) :
    mateEquiv (etaleRestrictAdjunction h) (etaleRestrictAdjunction g)
      (TwoSquare.mk (etalePushforward f) (etaleRestrict h) (etaleRestrict g) (etalePushforward f')
        (Functor.sheafPushforwardContinuousNatTrans (Etale.restrictComparison g w) (Type u)
          Y'.smallEtaleTopology X.smallEtaleTopology)) = etalePushforwardComparison w := by
  apply TwoSquare.ext
  intro F
  apply Sheaf.hom_ext
  ext W s
  simp [etaleRestrictAdjunction, etalePushforwardComparison, etaleRestrict, etalePushforward,
    Etale.baseChangeComparison_app_eq_restrict g w]
  rfl

lemma etaleBaseChangeMapRestrict_eq (w : h ≫ f = f' ≫ g) :
    etaleBaseChangeMapRestrict g w =
      TwoSquare.mk (etalePushforward f) (etaleRestrict h) (etaleRestrict g) (etalePushforward f')
        (Functor.sheafPushforwardContinuousNatTrans (Etale.restrictComparison g w) (Type u)
          Y'.smallEtaleTopology X.smallEtaleTopology) := by
  rw [etaleBaseChangeMapRestrict, Equiv.symm_apply_eq, mateEquiv_restrictComparison]

end BaseChangeEtale

lemma etaleBaseChangeMap_app_eq_restrict {X X' : Scheme.{u}} {f : X ⟶ Y} {h : X' ⟶ X}
    {f' : X' ⟶ Y'} [Etale h] (w : h ≫ f = f' ≫ g) (F : Sheaf X.smallEtaleTopology (Type u)) :
    (etaleBaseChangeMap w).app F = (etalePullbackIsoRestrict g).hom.app _ ≫
      (Functor.sheafPushforwardContinuousNatTrans (Etale.restrictComparison g w) (Type u)
        Y'.smallEtaleTopology X.smallEtaleTopology).app F ≫
      (etalePushforward f').map ((etalePullbackIsoRestrict h).inv.app F) := by
  rw [etaleBaseChangeMap_eq_restrict g w, etaleBaseChangeMapRestrict_eq]
  rfl

/-- Étale base change: for a cartesian square `X' = X ×_Y Y'` with `g : Y' ⟶ Y` étale, the base
change morphism `g^* f_* F ⟶ f'_* h^* F` is an isomorphism for every sheaf of sets `F` on `X`. -/
theorem isIso_etaleBaseChangeMap_of_etale {X X' : Scheme.{u}} {f : X ⟶ Y} {h : X' ⟶ X}
    {f' : X' ⟶ Y'} (hX : IsPullback h f' f g) (F : Sheaf X.smallEtaleTopology (Type u)) :
    IsIso ((etaleBaseChangeMap hX.w).app F) := by
  have : Etale h := MorphismProperty.of_isPullback hX.flip ‹Etale g›
  have := Etale.isIso_restrictComparison g hX
  have hσ : IsIso (Functor.sheafPushforwardContinuousNatTrans (Etale.restrictComparison g hX.w)
      (Type u) Y'.smallEtaleTopology X.smallEtaleTopology) :=
    (Functor.sheafPushforwardContinuousIso (asIso (Etale.restrictComparison g hX.w)) (Type u)
      Y'.smallEtaleTopology X.smallEtaleTopology).isIso_inv
  rw [etaleBaseChangeMap_app_eq_restrict g hX.w]
  infer_instance

section Cocontinuous

/-- A sieve on `W` is a covering sieve of the small étale site if and only if every point of `W`
lies in the image of one of its arrows. -/
lemma mem_smallEtaleTopology_iff {X : Scheme.{u}} (W : X.Etale) (R : Sieve W) :
    R ∈ X.smallEtaleTopology W ↔
      ∀ x : W.left, ∃ (V : X.Etale) (f : V ⟶ W) (y : V.left), R f ∧ f.left y = x := by
  let ι := Σ V : X.Etale, {f : V ⟶ W // R f}
  have hR : R = Sieve.ofArrows (fun p : ι ↦ p.1) (fun p ↦ p.2.1) := by
    apply le_antisymm
    · intro V f hf
      exact ⟨V, 𝟙 V, f, Presieve.ofArrows.mk (⟨V, f, hf⟩ : ι), Category.id_comp f⟩
    · rintro V f ⟨_, g, _, ⟨p⟩, rfl⟩
      exact R.downward_closed p.2.2 g
  conv_lhs => rw [hR]
  rw [ofArrows_mem_smallEtaleTopology_iff]
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · have : x ∈ ⋃ p : ι, Set.range p.2.1.left := h ▸ Set.mem_univ x
    obtain ⟨p, y, hy⟩ := Set.mem_iUnion.1 this
    exact ⟨p.1, p.2.1, y, p.2.2, hy⟩
  · refine Set.eq_univ_of_forall fun x ↦ ?_
    obtain ⟨V, f, y, hf, hy⟩ := h x
    exact Set.mem_iUnion.2 ⟨⟨V, f, hf⟩, y, hy⟩

/-- Composition with an étale morphism is cocontinuous. -/
instance : (Etale.map g).IsCocontinuous Y'.smallEtaleTopology Y.smallEtaleTopology where
  cover_lift {W} S hS := by
    rw [mem_smallEtaleTopology_iff] at hS ⊢
    intro x
    obtain ⟨V, f, y, hf, hy⟩ := hS x
    have : Etale f.left := MorphismProperty.of_postcomp (W := @Etale) f.left
      ((Etale.map g).obj W).hom ((Etale.map g).obj W).prop
      (by rw [MorphismProperty.Over.w f]; exact V.prop)
    let V' : Y'.Etale := Scheme.Etale.mk (f.left ≫ W.hom)
    let f' : V' ⟶ W := MorphismProperty.Over.homMk f.left rfl
    let e : (Etale.map g).obj V' ≅ V := MorphismProperty.Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ V.hom = (f.left ≫ W.hom) ≫ g
      rw [Category.id_comp, Category.assoc, ← MorphismProperty.Over.w f]
      rfl)
    have hf' : (Etale.map g).map f' = e.hom ≫ f := MorphismProperty.Over.Hom.ext (by
      rw [MorphismProperty.Comma.comp_left]
      exact (Category.id_comp _).symm)
    refine ⟨V', f', y, ?_, hy⟩
    change S ((Etale.map g).map f')
    rw [hf']
    exact S.downward_closed hf _

end Cocontinuous

end AlgebraicGeometry.Scheme
