/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Direct and inverse images of sheaves on small étale sites

Let `f : X ⟶ Y` be a morphism of schemes. Base change `W ↦ X ×_Y W` is a functor
`Scheme.Etale.pullback f : Y.Etale ⥤ X.Etale` between the small étale sites; it preserves finite
limits and is continuous. We define:

* `Scheme.etalePushforward f`, the direct image `f_*` of étale sheaves of sets,
  `(f_* F)(W) = F(X ×_Y W)`;
* `Scheme.etalePullback f`, the inverse image `f^*`, its left adjoint
  (`Scheme.etaleAdjunction f`), which exists by a left Kan extension along the dense subsite of
  affine étale schemes;
* the isomorphisms `(f ≫ g)_* ≅ f_* ⋙ g_*` and `f^* ∘ g^* ≅ (f ≫ g)^*`.

## References

* [SGA 4, Exposé VIII, §1][sga4]
* [Stacks Project, Tag 03PQ](https://stacks.math.columbia.edu/tag/03PQ)
-/

universe u

open CategoryTheory Limits

-- Mathlib's `Scheme.Etale` is `MorphismProperty.Over @Etale ⊤ X`; with the default setting,
-- instance arguments and `simp` lemmas about the pullbacks in it do not unify.
set_option backward.isDefEq.respectTransparency false

namespace AlgebraicGeometry.Scheme

variable {X Y Z : Scheme.{u}}

/-- Base change of étale schemes along `f : X ⟶ Y`: the functor `W ↦ X ×_Y W` from the small
étale site of `Y` to that of `X`. -/
noncomputable def Etale.pullback (f : X ⟶ Y) : Y.Etale ⥤ X.Etale :=
  MorphismProperty.Over.pullback @Etale ⊤ f

namespace Etale

section Functor

variable (f : X ⟶ Y)

@[reassoc (attr := simp)]
lemma pullback_map_left_fst {W₁ W₂ : Y.Etale} (φ : W₁ ⟶ W₂) :
    ((Etale.pullback f).map φ).left ≫ Limits.pullback.fst W₂.hom f =
      Limits.pullback.fst W₁.hom f ≫ φ.left :=
  Limits.pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullback_map_left_snd {W₁ W₂ : Y.Etale} (φ : W₁ ⟶ W₂) :
    ((Etale.pullback f).map φ).left ≫ Limits.pullback.snd W₂.hom f =
      Limits.pullback.snd W₁.hom f :=
  Limits.pullback.lift_snd _ _ _

lemma pullback_comp_forget :
    Etale.pullback f ⋙ Scheme.Etale.forget X = Scheme.Etale.forget Y ⋙ Over.pullback f :=
  rfl

instance : PreservesFiniteLimits (Etale.pullback f) := by
  have : PreservesFiniteLimits (Etale.pullback f ⋙ Scheme.Etale.forget X) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget Y ⋙ Over.pullback f))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (Scheme.Etale.forget X)

instance : RepresentablyFlat (Etale.pullback f) := flat_of_preservesFiniteLimits _

lemma coverPreserving_pullback :
    CoverPreserving Y.smallEtaleTopology X.smallEtaleTopology (Etale.pullback f) := by
  constructor
  intro W R hR
  have h₁ := (MorphismProperty.Over.forget @Etale ⊤ Y).coverPreserving_restrictedTopology
    (Y.overGrothendieckTopology @Etale)
  have h₂ := GrothendieckTopology.coverPreserving_overPullback Scheme.etaleTopology f
  have hR' : Sieve.functorPushforward
      (Etale.pullback f ⋙ MorphismProperty.Over.forget @Etale ⊤ X) R ∈
      (Scheme.overGrothendieckTopology (@Etale) X) ((Etale.pullback f ⋙
        MorphismProperty.Over.forget @Etale ⊤ X).obj W) :=
    (CoverPreserving.comp _ _ h₁ h₂).cover_preserve hR
  change _ ∈ X.smallGrothendieckTopology (P := @Etale) _
  rw [Functor.mem_restrictedTopology_iff]
  rwa [Sieve.functorPushforward_comp] at hR'

instance : (Etale.pullback f).IsContinuous Y.smallEtaleTopology X.smallEtaleTopology :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    (coverPreserving_pullback f)

/-- Auxiliary functor from the affine étale site of `Y` to the étale site of `X`: the inverse
image functor is constructed as a left Kan extension along it. -/
noncomputable abbrev affinePullback : Y.AffineEtale ⥤ X.Etale :=
  Scheme.AffineEtale.Spec Y ⋙ Etale.pullback f

instance : (affinePullback f).IsContinuous (Scheme.AffineEtale.topology Y)
    X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

instance (V : X.Etaleᵒᵖ) (F : Y.AffineEtaleᵒᵖ ⥤ Type u) :
    (affinePullback f).op.HasPointwiseLeftKanExtensionAt F V := by
  have : HasColimitsOfShape (CostructuredArrow (affinePullback f).op V) (Type u) :=
    hasColimitsOfShape_of_essentiallySmall.{u} _ _
  infer_instance

instance (F : Y.AffineEtaleᵒᵖ ⥤ Type u) : (affinePullback f).op.HasLeftKanExtension F := by
  have : (affinePullback f).op.HasPointwiseLeftKanExtension F := fun V ↦ inferInstance
  infer_instance

end Functor

section Comp

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- `X ×_Z W ≅ X ×_Y (Y ×_Z W)`, naturally in `W` étale over `Z`. -/
noncomputable def pullbackComp :
    Etale.pullback (f ≫ g) ≅ Etale.pullback g ⋙ Etale.pullback f :=
  MorphismProperty.Over.pullbackComp f g

lemma pullbackComp_hom_app_left (W : Z.Etale) :
    ((pullbackComp f g).hom.app W).left =
      (pullbackLeftPullbackSndIso W.hom g f).inv := by
  simp [pullbackComp, Etale.pullback]

@[reassoc (attr := simp)]
lemma pullbackComp_hom_app_left_snd (W : Z.Etale) :
    ((pullbackComp f g).hom.app W).left ≫
      Limits.pullback.snd ((Etale.pullback g).obj W).hom f =
      Limits.pullback.snd W.hom (f ≫ g) := by
  rw [pullbackComp_hom_app_left]
  exact pullbackLeftPullbackSndIso_inv_snd_snd W.hom g f

@[reassoc (attr := simp)]
lemma pullbackComp_hom_app_left_fst_fst (W : Z.Etale) :
    ((pullbackComp f g).hom.app W).left ≫
      Limits.pullback.fst ((Etale.pullback g).obj W).hom f ≫ Limits.pullback.fst W.hom g =
        Limits.pullback.fst W.hom (f ≫ g) := by
  rw [pullbackComp_hom_app_left]
  exact pullbackLeftPullbackSndIso_inv_fst W.hom g f

@[reassoc (attr := simp)]
lemma pullbackComp_hom_app_left_fst_snd (W : Z.Etale) :
    ((pullbackComp f g).hom.app W).left ≫
      Limits.pullback.fst ((Etale.pullback g).obj W).hom f ≫ Limits.pullback.snd W.hom g =
        Limits.pullback.snd W.hom (f ≫ g) ≫ f := by
  rw [pullbackComp_hom_app_left]
  exact pullbackLeftPullbackSndIso_inv_fst_snd W.hom g f

@[reassoc (attr := simp)]
lemma pullbackComp_inv_app_left_snd (W : Z.Etale) :
    ((pullbackComp f g).inv.app W).left ≫ Limits.pullback.snd W.hom (f ≫ g) =
      Limits.pullback.snd ((Etale.pullback g).obj W).hom f := by
  simp [pullbackComp, Etale.pullback]
  rfl

@[reassoc (attr := simp)]
lemma pullbackComp_inv_app_left_fst (W : Z.Etale) :
    ((pullbackComp f g).inv.app W).left ≫ Limits.pullback.fst W.hom (f ≫ g) =
      Limits.pullback.fst ((Etale.pullback g).obj W).hom f ≫ Limits.pullback.fst W.hom g := by
  simp [pullbackComp, Etale.pullback]
  rfl

instance : (Etale.pullback g ⋙ Etale.pullback f).IsContinuous Z.smallEtaleTopology
    X.smallEtaleTopology :=
  Functor.isContinuous_comp _ _ _ Y.smallEtaleTopology _

end Comp

end Etale

section Sheaves

variable (f : X ⟶ Y)

/-- The direct image `f_*` of étale sheaves of sets: `(f_* F)(W) = F(X ×_Y W)`. -/
noncomputable def etalePushforward :
    Sheaf X.smallEtaleTopology (Type u) ⥤ Sheaf Y.smallEtaleTopology (Type u) :=
  (Etale.pullback f).sheafPushforwardContinuous (Type u) _ _

instance : (etalePushforward f).IsRightAdjoint := by
  let E := (Scheme.AffineEtale.Spec Y).sheafPushforwardContinuous (Type u)
    (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology
  let e := Functor.sheafPushforwardContinuousComp (Scheme.AffineEtale.Spec Y)
    (Etale.pullback f) (Type u) (Scheme.AffineEtale.topology Y) Y.smallEtaleTopology
    X.smallEtaleTopology
  have e' : etalePushforward f ≅ (Etale.affinePullback f).sheafPushforwardContinuous (Type u)
        (Scheme.AffineEtale.topology Y) X.smallEtaleTopology ⋙ E.inv :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ E.asEquivalence.unitIso ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight e _
  exact Functor.isRightAdjoint_of_iso e'.symm

instance : ((Etale.pullback f).sheafPushforwardContinuous (Type u) Y.smallEtaleTopology
    X.smallEtaleTopology).IsRightAdjoint :=
  inferInstanceAs (etalePushforward f).IsRightAdjoint

/-- The inverse image `f^*` of étale sheaves of sets, the left adjoint of `f_*`. -/
noncomputable def etalePullback :
    Sheaf Y.smallEtaleTopology (Type u) ⥤ Sheaf X.smallEtaleTopology (Type u) :=
  (Etale.pullback f).sheafPullback (Type u) _ _

/-- The adjunction `f^* ⊣ f_*`. -/
noncomputable def etaleAdjunction : etalePullback f ⊣ etalePushforward f :=
  (Etale.pullback f).sheafAdjunctionContinuous (Type u) _ _

instance : (etalePullback f).IsLeftAdjoint :=
  (etaleAdjunction f).isLeftAdjoint

lemma etalePushforward_obj_obj (F : Sheaf X.smallEtaleTopology (Type u)) (W : Y.Etaleᵒᵖ) :
    ((etalePushforward f).obj F).obj.obj W = F.obj.obj (Opposite.op
      ((Etale.pullback f).obj W.unop)) :=
  rfl

end Sheaves

section Comp

variable (f : X ⟶ Y) (g : Y ⟶ Z)

/-- `(f ≫ g)_* ≅ f_* ⋙ g_*`. -/
noncomputable def etalePushforwardComp :
    etalePushforward (f ≫ g) ≅ etalePushforward f ⋙ etalePushforward g :=
  Functor.sheafPushforwardContinuousIso (Etale.pullbackComp f g) (Type u) _ _

/-- `f^* ∘ g^* ≅ (f ≫ g)^*`, the conjugate of `etalePushforwardComp`. -/
noncomputable def etalePullbackComp :
    etalePullback g ⋙ etalePullback f ≅ etalePullback (f ≫ g) :=
  (conjugateIsoEquiv (etaleAdjunction (f ≫ g))
    ((etaleAdjunction g).comp (etaleAdjunction f))).symm (etalePushforwardComp f g)

lemma conjugateEquiv_etalePullbackComp_hom :
    conjugateEquiv (etaleAdjunction (f ≫ g)) ((etaleAdjunction g).comp (etaleAdjunction f))
      (etalePullbackComp f g).hom = (etalePushforwardComp f g).hom :=
  Equiv.apply_symm_apply _ _

lemma conjugateEquiv_etalePullbackComp_inv :
    conjugateEquiv ((etaleAdjunction g).comp (etaleAdjunction f)) (etaleAdjunction (f ≫ g))
      (etalePullbackComp f g).inv = (etalePushforwardComp f g).inv :=
  Equiv.apply_symm_apply _ _

end Comp

end AlgebraicGeometry.Scheme
