/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.Functoriality

/-!
# The base change morphism for étale sheaves

For a commutative square of schemes
```
X' --h--> X
|f'       |f
Y' --g--> Y
```
the base change morphism `g^* f_* F ⟶ f'_* h^* F` of étale sheaves of sets is the mate
(`Scheme.etaleBaseChangeMap`) of the canonical 2-cell `h_* ⋙ f_* ⟶ f'_* ⋙ g_*`, which on
sections over `W` étale over `Y` is the restriction `F(X' ×_X (X ×_Y W)) ⟶ F(X' ×_{Y'} (Y' ×_Y W))`.

We prove the pasting formulas for two squares on top of each other
(`Scheme.etaleBaseChangeMap_comp_app`) and side by side
(`Scheme.etaleBaseChangeMap_comp_horiz_app`).

## References

* [SGA 4, Exposé XII, §4][sga4]
* [Stacks Project, Tag 0E44](https://stacks.math.columbia.edu/tag/0E44)
-/

universe u

open CategoryTheory Limits

-- See the comment in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace CategoryTheory

section Mates

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {G G' : C ⥤ E} {H H' : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

set_option backward.isDefEq.respectTransparency true in
/-- Naturality of the mates correspondence in the two vertical functors. -/
lemma mateEquiv_whisker (φ : G' ⟶ G) (ψ : H ⟶ H') (α : TwoSquare G L₁ L₂ H) :
    mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _
      (Functor.whiskerRight φ L₂ ≫ α.natTrans ≫ Functor.whiskerLeft L₁ ψ)) =
      TwoSquare.mk _ _ _ _ (Functor.whiskerLeft R₁ φ ≫ (mateEquiv adj₁ adj₂ α).natTrans ≫
        Functor.whiskerRight ψ R₂) := by
  ext X
  simp only [mateEquiv_apply, TwoSquare.natTrans]
  simp only [Functor.comp_obj, Functor.whiskerRight_comp, Functor.whiskerRight_twice,
    Category.assoc, Functor.whiskerLeft_comp, NatTrans.comp_app, Functor.id_obj,
    Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.leftUnitor_hom_app, Category.comp_id, Category.id_comp,
    Adjunction.unit_naturality_assoc]
  erw [NatTrans.comp_app, Functor.whiskerRight_app]
  simp only [Functor.whiskerLeft_app, ← Functor.map_comp, Category.assoc, ψ.naturality]

end Mates

end CategoryTheory

namespace AlgebraicGeometry.Scheme

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

namespace Etale

/-- The scheme-level comparison map `X' ×_{Y'} (Y' ×_Y W) ⟶ X' ×_X (X ×_Y W)` for a
commutative square `h ≫ f = f' ≫ g` and a scheme `W` over `Y`. -/
noncomputable def baseChangeComparisonHom (w : h ≫ f = f' ≫ g) {W : Scheme.{u}} (p : W ⟶ Y) :
    Limits.pullback (Limits.pullback.snd p g) f' ⟶ Limits.pullback (Limits.pullback.snd p f) h :=
  Limits.pullback.lift
    (Limits.pullback.lift (Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _)
      (Limits.pullback.snd _ _ ≫ h)
      (by rw [Category.assoc, Limits.pullback.condition, ← Category.assoc,
        Limits.pullback.condition, Category.assoc, Category.assoc, w]))
    (Limits.pullback.snd _ _) (by simp)

@[reassoc]
lemma baseChangeComparisonHom_snd (w : h ≫ f = f' ≫ g) {W : Scheme.{u}} (p : W ⟶ Y) :
    baseChangeComparisonHom w p ≫ Limits.pullback.snd _ _ = Limits.pullback.snd _ _ := by
  simp [baseChangeComparisonHom]

@[reassoc]
lemma baseChangeComparisonHom_fst_fst (w : h ≫ f = f' ≫ g) {W : Scheme.{u}} (p : W ⟶ Y) :
    baseChangeComparisonHom w p ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ =
      Limits.pullback.fst _ _ ≫ Limits.pullback.fst _ _ := by
  simp [baseChangeComparisonHom]

@[reassoc]
lemma baseChangeComparisonHom_fst_snd (w : h ≫ f = f' ≫ g) {W : Scheme.{u}} (p : W ⟶ Y) :
    baseChangeComparisonHom w p ≫ Limits.pullback.fst _ _ ≫ Limits.pullback.snd _ _ =
      Limits.pullback.snd _ _ ≫ h := by
  simp [baseChangeComparisonHom]

@[reassoc (attr := simp)]
lemma baseChangeComparisonHom_snd' (w : h ≫ f = f' ≫ g) (W : Y.Etale) :
    baseChangeComparisonHom w W.hom ≫ Limits.pullback.snd ((Etale.pullback f).obj W).hom h =
      Limits.pullback.snd ((Etale.pullback g).obj W).hom f' :=
  baseChangeComparisonHom_snd w W.hom

@[reassoc (attr := simp)]
lemma baseChangeComparisonHom_fst_fst' (w : h ≫ f = f' ≫ g) (W : Y.Etale) :
    baseChangeComparisonHom w W.hom ≫ Limits.pullback.fst ((Etale.pullback f).obj W).hom h ≫
      Limits.pullback.fst W.hom f = Limits.pullback.fst ((Etale.pullback g).obj W).hom f' ≫
        Limits.pullback.fst W.hom g :=
  baseChangeComparisonHom_fst_fst w W.hom

@[reassoc (attr := simp)]
lemma baseChangeComparisonHom_fst_snd' (w : h ≫ f = f' ≫ g) (W : Y.Etale) :
    baseChangeComparisonHom w W.hom ≫ Limits.pullback.fst ((Etale.pullback f).obj W).hom h ≫
      Limits.pullback.snd W.hom f = Limits.pullback.snd ((Etale.pullback g).obj W).hom f' ≫ h :=
  baseChangeComparisonHom_fst_snd w W.hom

/-- For a commutative square `h ≫ f = f' ≫ g`, the canonical morphism of étale
`X'`-schemes `X' ×_{Y'} (Y' ×_Y W) ⟶ X' ×_X (X ×_Y W)`, natural in `W` étale over `Y`. -/
noncomputable def baseChangeComparison (w : h ≫ f = f' ≫ g) :
    Etale.pullback g ⋙ Etale.pullback f' ⟶ Etale.pullback f ⋙ Etale.pullback h where
  app W := MorphismProperty.Over.homMk (baseChangeComparisonHom w W.hom)
    (baseChangeComparisonHom_snd w W.hom)
  naturality W₁ W₂ φ := by
    apply MorphismProperty.Over.Hom.ext
    rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left]
    apply Limits.pullback.hom_ext
    · apply Limits.pullback.hom_ext <;> simp
    · simp

@[simp]
lemma baseChangeComparison_app_left (w : h ≫ f = f' ≫ g) (W : Y.Etale) :
    ((baseChangeComparison w).app W).left = baseChangeComparisonHom w W.hom :=
  rfl

end Etale

/-- The 2-cell `h_* ⋙ f_* ⟶ f'_* ⋙ g_*` of direct images attached to a commutative square
`h ≫ f = f' ≫ g`: on sections over `W` étale over `Y`, it is the restriction
`F(X' ×_X (X ×_Y W)) ⟶ F(X' ×_{Y'} (Y' ×_Y W))`. -/
noncomputable def etalePushforwardComparison (w : h ≫ f = f' ≫ g) :
    TwoSquare (etalePushforward h) (etalePushforward f') (etalePushforward f)
      (etalePushforward g) :=
  Functor.sheafPushforwardContinuousNatTrans (Etale.baseChangeComparison w) (Type u)
    Y.smallEtaleTopology X'.smallEtaleTopology

/-- The base change morphism `g^* f_* F ⟶ f'_* h^* F` attached to a commutative square
`h ≫ f = f' ≫ g`, defined as the mate of `etalePushforwardComparison` for the adjunctions
`h^* ⊣ h_*` and `g^* ⊣ g_*`. -/
noncomputable def etaleBaseChangeMap (w : h ≫ f = f' ≫ g) :
    TwoSquare (etalePushforward f) (etalePullback h) (etalePullback g) (etalePushforward f') :=
  (mateEquiv (etaleAdjunction h) (etaleAdjunction g)).symm (etalePushforwardComparison w)

lemma mateEquiv_etaleBaseChangeMap (w : h ≫ f = f' ≫ g) :
    mateEquiv (etaleAdjunction h) (etaleAdjunction g) (etaleBaseChangeMap w) =
      etalePushforwardComparison w :=
  Equiv.apply_symm_apply _ _

end BaseChange

section Paste

variable {X Y Z X' Y' Z' : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X' ⟶ X} {k : Y' ⟶ Y}
  {m : Z' ⟶ Z} {f' : X' ⟶ Y'} {g' : Y' ⟶ Z'}

lemma Etale.baseChangeComparison_comp (w₁ : h ≫ f = f' ≫ k) (w₂ : k ≫ g = g' ≫ m)
    (w : h ≫ f ≫ g = (f' ≫ g') ≫ m) (W : Z.Etale) :
    (Etale.baseChangeComparison w).app W =
      (Etale.pullbackComp f' g').hom.app ((Etale.pullback m).obj W) ≫
        (Etale.pullback f').map ((Etale.baseChangeComparison w₂).app W) ≫
        (Etale.baseChangeComparison w₁).app ((Etale.pullback g).obj W) ≫
        (Etale.pullback h).map ((Etale.pullbackComp f g).inv.app W) := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
    MorphismProperty.Comma.comp_left]
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext <;> simp
  · simp

lemma etalePushforwardComparison_comp (w₁ : h ≫ f = f' ≫ k) (w₂ : k ≫ g = g' ≫ m)
    (w : h ≫ f ≫ g = (f' ≫ g') ≫ m) :
    etalePushforwardComparison w = TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft (etalePushforward h) (etalePushforwardComp f g).hom ≫
        ((etalePushforwardComparison w₁).vComp (etalePushforwardComparison w₂)).natTrans ≫
        Functor.whiskerRight (etalePushforwardComp f' g').inv (etalePushforward m)) := by
  apply TwoSquare.ext
  intro F
  apply Sheaf.hom_ext
  ext W s
  simp only [etalePushforwardComparison, etalePushforwardComp, etalePushforward]
  simp [Etale.baseChangeComparison_comp w₁ w₂ w]
  rfl

/-- Pasting of base change morphisms for two squares on top of each other: the base change
morphism of the composite square is `m^* (g_* f_*) ⟶ g'_* k^* f_* ⟶ g'_* f'_* h^*`. -/
lemma etaleBaseChangeMap_comp (w₁ : h ≫ f = f' ≫ k) (w₂ : k ≫ g = g' ≫ m)
    (w : h ≫ f ≫ g = (f' ≫ g') ≫ m) :
    etaleBaseChangeMap w = TwoSquare.mk _ _ _ _
      (Functor.whiskerRight (etalePushforwardComp f g).hom (etalePullback m) ≫
        ((etaleBaseChangeMap w₁).hComp (etaleBaseChangeMap w₂)).natTrans ≫
        Functor.whiskerLeft (etalePullback h) (etalePushforwardComp f' g').inv) := by
  apply (mateEquiv (etaleAdjunction h) (etaleAdjunction m)).injective
  rw [mateEquiv_whisker, mateEquiv_vcomp _ (etaleAdjunction k), mateEquiv_etaleBaseChangeMap,
    mateEquiv_etaleBaseChangeMap, mateEquiv_etaleBaseChangeMap,
    etalePushforwardComparison_comp w₁ w₂ w]

/-- Componentwise form of `etaleBaseChangeMap_comp`: the base change morphism of the composite
square at `F` is `m^*` of the comparison `(f ≫ g)_* F ≅ g_* f_* F`, followed by the base change
morphism of the lower square at `f_* F`, by `g'_*` of the base change morphism of the upper square
at `F`, and by the comparison `g'_* f'_* ≅ (f' ≫ g')_*`. -/
lemma etaleBaseChangeMap_comp_app (w₁ : h ≫ f = f' ≫ k) (w₂ : k ≫ g = g' ≫ m)
    (w : h ≫ f ≫ g = (f' ≫ g') ≫ m) (F : Sheaf X.smallEtaleTopology (Type u)) :
    (etaleBaseChangeMap w).app F =
      (etalePullback m).map ((etalePushforwardComp f g).hom.app F) ≫
        (etaleBaseChangeMap w₂).app ((etalePushforward f).obj F) ≫
        (etalePushforward g').map ((etaleBaseChangeMap w₁).app F) ≫
        (etalePushforwardComp f' g').inv.app ((etalePullback h).obj F) := by
  rw [etaleBaseChangeMap_comp w₁ w₂ w]
  simp [TwoSquare.hComp]

end Paste

section PasteHoriz

variable {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}
  {g₂ : Y'' ⟶ Y'} {h₂ : X'' ⟶ X'} {f'' : X'' ⟶ Y''}

lemma Etale.baseChangeComparison_comp_horiz (w₁ : h ≫ f = f' ≫ g) (w₂ : h₂ ≫ f' = f'' ≫ g₂)
    (w : (h₂ ≫ h) ≫ f = f'' ≫ g₂ ≫ g) (W : Y.Etale) :
    (Etale.baseChangeComparison w).app W =
      (Etale.pullback f'').map ((Etale.pullbackComp g₂ g).hom.app W) ≫
        (Etale.baseChangeComparison w₂).app ((Etale.pullback g).obj W) ≫
        (Etale.pullback h₂).map ((Etale.baseChangeComparison w₁).app W) ≫
        (Etale.pullbackComp h₂ h).inv.app ((Etale.pullback f).obj W) := by
  apply MorphismProperty.Over.Hom.ext
  rw [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.comp_left,
    MorphismProperty.Comma.comp_left]
  apply Limits.pullback.hom_ext
  · apply Limits.pullback.hom_ext <;> simp
  · simp

lemma etalePushforwardComparison_comp_horiz (w₁ : h ≫ f = f' ≫ g)
    (w₂ : h₂ ≫ f' = f'' ≫ g₂) (w : (h₂ ≫ h) ≫ f = f'' ≫ g₂ ≫ g) :
    etalePushforwardComparison w =
      (((etalePushforwardComparison w₂).hComp (etalePushforwardComparison w₁)).whiskerTop
        (etalePushforwardComp h₂ h).hom).whiskerBottom (etalePushforwardComp g₂ g).inv := by
  apply TwoSquare.ext
  intro F
  apply Sheaf.hom_ext
  ext W s
  simp only [etalePushforwardComparison, etalePushforwardComp, etalePushforward]
  simp [Etale.baseChangeComparison_comp_horiz w₁ w₂ w]
  rfl

/-- Pasting of base change morphisms for two squares side by side. -/
lemma etaleBaseChangeMap_comp_horiz (w₁ : h ≫ f = f' ≫ g) (w₂ : h₂ ≫ f' = f'' ≫ g₂)
    (w : (h₂ ≫ h) ≫ f = f'' ≫ g₂ ≫ g) :
    etaleBaseChangeMap w = (((etaleBaseChangeMap w₁).vComp (etaleBaseChangeMap w₂)).whiskerLeft
      (etalePullbackComp h₂ h).hom).whiskerRight (etalePullbackComp g₂ g).inv := by
  apply (mateEquiv (etaleAdjunction (h₂ ≫ h)) (etaleAdjunction (g₂ ≫ g))).injective
  rw [mateEquiv_conjugateEquiv_vcomp _ ((etaleAdjunction g).comp (etaleAdjunction g₂)),
    conjugateEquiv_mateEquiv_vcomp _ ((etaleAdjunction h).comp (etaleAdjunction h₂)),
    mateEquiv_hcomp, mateEquiv_etaleBaseChangeMap, mateEquiv_etaleBaseChangeMap,
    mateEquiv_etaleBaseChangeMap, conjugateEquiv_etalePullbackComp_hom,
    conjugateEquiv_etalePullbackComp_inv, etalePushforwardComparison_comp_horiz w₁ w₂ w]

/-- Componentwise form of `etaleBaseChangeMap_comp_horiz`. -/
lemma etaleBaseChangeMap_comp_horiz_app (w₁ : h ≫ f = f' ≫ g) (w₂ : h₂ ≫ f' = f'' ≫ g₂)
    (w : (h₂ ≫ h) ≫ f = f'' ≫ g₂ ≫ g) (F : Sheaf X.smallEtaleTopology (Type u)) :
    (etaleBaseChangeMap w).app F =
      (etalePullbackComp g₂ g).inv.app ((etalePushforward f).obj F) ≫
        (etalePullback g₂).map ((etaleBaseChangeMap w₁).app F) ≫
        (etaleBaseChangeMap w₂).app ((etalePullback h).obj F) ≫
        (etalePushforward f'').map ((etalePullbackComp h₂ h).hom.app F) := by
  rw [etaleBaseChangeMap_comp_horiz w₁ w₂ w]
  simp [TwoSquare.vComp]

end PasteHoriz

end AlgebraicGeometry.Scheme
