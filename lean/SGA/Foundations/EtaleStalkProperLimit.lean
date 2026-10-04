/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import SGA.Foundations.EtaleStalkProperRepresentable
import SGA.Foundations.StrictLocalizationLimit

/-!
# Sections of étale schemes over `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}`

Let `f : X ⟶ Y` be quasi-compact and quasi-separated, `ȳ` a geometric point of `Y` and `E` an
étale `X`-scheme. Since `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}` is the limit of the `X ×_Y V` over the affine
étale neighbourhoods `(V, v)` of `ȳ`
(`AlgebraicGeometry.Scheme.Hom.isLimitAffineEtaleNbhdPullbackCone`), with affine transition
morphisms, every `X`-morphism `X ×_Y Spec 𝒪^{sh}_{Y,ȳ} ⟶ E` comes from an `X`-morphism
`X ×_Y V ⟶ E` (`AlgebraicGeometry.Scheme.Hom.exists_etaleNbhd_hom_of_strictLocalization`;
EGA IV 8.8.2, mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`). This is
SGA 4 VII 5.7 in degree `0` for the sheaf represented by `E`, at a strict localization.

Consequently, to extend an `X`-morphism from the geometric fibre `X_ȳ` to an étale neighbourhood
(`AlgebraicGeometry.Scheme.ExtendsAlongGeometricFibres`), it suffices to extend it to
`X ×_Y Spec 𝒪^{sh}_{Y,ȳ}`
(`AlgebraicGeometry.Scheme.extendsAlongGeometricFibres_of_strictLocalization`).

## References

* [EGA IV, 8.8.2][ega-iv-3]
* [SGA 4, Exposé VII, 5.7][sga4]
* [Stacks Project, Tag 01ZC](https://stacks.math.columbia.edu/tag/01ZC)
-/

universe u

open CategoryTheory Limits Opposite

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace AlgebraicGeometry.Scheme

namespace Hom

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (y : Spec (.of Ω) ⟶ Y)

/-- The transition morphisms `X ×_Y V_k ⟶ X ×_Y V_{k'}` are base changes of the morphisms
`V_k ⟶ V_{k'}` of affine schemes, hence affine. -/
instance {k k' : y.AffineEtaleNbhd} (g : k ⟶ k') :
    IsAffineHom ((y.affineEtaleNbhdPullbackDiagram f).map g) := by
  have hsq : IsPullback (pullback.fst k.nbhd.hom f) ((y.affineEtaleNbhdPullbackDiagram f).map g)
      (y.affineEtaleNbhdDiagram.map g) (pullback.fst k'.nbhd.hom f) := by
    refine IsPullback.of_bot (h₃₁ := f) (v₂₁ := pullback.snd k'.nbhd.hom f)
      (v₂₂ := k'.nbhd.hom) ?_ ?_ (IsPullback.of_hasPullback k'.nbhd.hom f)
    · have hg : y.affineEtaleNbhdDiagram.map g ≫ k'.nbhd.hom = k.nbhd.hom :=
        Over.w ((Etale.forget Y).map (y.affineEtaleNbhdFunctor.map g).1)
      simp only [affineEtaleNbhdPullbackDiagram_map, pullback.lift_snd, hg]
      exact IsPullback.of_hasPullback k.nbhd.hom f
    · simp
  have : IsAffine ((𝟭 Scheme).obj k.nbhd.left) := inferInstanceAs (IsAffine k.nbhd.left)
  have : IsAffine ((𝟭 Scheme).obj k'.nbhd.left) := inferInstanceAs (IsAffine k'.nbhd.left)
  exact MorphismProperty.of_isPullback hsq (isAffineHom_of_isAffine _)

instance [QuasiCompact f] (k : y.AffineEtaleNbhd) :
    CompactSpace ((y.affineEtaleNbhdPullbackDiagram f).obj k) :=
  have : IsAffine ((𝟭 Scheme).obj k.nbhd.left) := inferInstanceAs (IsAffine k.nbhd.left)
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst k.nbhd.hom f)

instance [QuasiSeparated f] (k : y.AffineEtaleNbhd) :
    QuasiSeparatedSpace ((y.affineEtaleNbhdPullbackDiagram f).obj k) :=
  have : IsAffine ((𝟭 Scheme).obj k.nbhd.left) := inferInstanceAs (IsAffine k.nbhd.left)
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst k.nbhd.hom f)

/-- **Passage to the limit for represented sheaves** (EGA IV 8.8.2, SGA 4 VII 5.7 in degree `0`):
for `f` quasi-compact and quasi-separated and `E` étale over `X`, every `X`-morphism
`X ×_Y Spec 𝒪^{sh}_{Y,ȳ} ⟶ E` comes from an `X`-morphism `X ×_Y V ⟶ E` for some affine étale
neighbourhood `(V, v)` of `ȳ`. -/
theorem exists_etaleNbhd_hom_of_strictLocalization [QuasiCompact f] [QuasiSeparated f]
    (E : X.Etale) (τ : pullback y.fromSpecStrictLocalization f ⟶ E.left)
    (hτ : τ ≫ E.hom = pullback.snd y.fromSpecStrictLocalization f) :
    ∃ (k : y.AffineEtaleNbhd) (s : (Etale.pullback f).obj k.nbhd ⟶ E),
      (y.affineEtaleNbhdPullbackCone f).π.app k ≫ s.left = τ := by
  let D := y.affineEtaleNbhdPullbackDiagram f
  let t : D ⟶ (Functor.const _).obj X :=
    { app k := pullback.snd k.nbhd.hom f
      naturality k k' g := by simp [D] }
  obtain ⟨k, a, hπa, ha⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t
    E.hom (y.affineEtaleNbhdPullbackCone f) (y.isLimitAffineEtaleNbhdPullbackCone f) τ (by
      ext k
      simp [t, hτ])
  exact ⟨k, MorphismProperty.Over.homMk a ha trivial, hπa⟩

/-- The morphism from the geometric fibre `X_ȳ = X ×_Y Spec Ω` to `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}`. -/
def geometricFibreToStrictLocalization :
    pullback f y ⟶ pullback y.fromSpecStrictLocalization f :=
  pullback.lift (pullback.snd f y ≫ y.toSpecStrictLocalization) (pullback.fst f y)
    (by simp [pullback.condition])

omit [IsSepClosed Ω] in
@[reassoc (attr := simp)]
lemma geometricFibreToStrictLocalization_fst :
    f.geometricFibreToStrictLocalization y ≫ pullback.fst y.fromSpecStrictLocalization f =
      pullback.snd f y ≫ y.toSpecStrictLocalization :=
  pullback.lift_fst _ _ _

omit [IsSepClosed Ω] in
@[reassoc (attr := simp)]
lemma geometricFibreToStrictLocalization_snd :
    f.geometricFibreToStrictLocalization y ≫ pullback.snd y.fromSpecStrictLocalization f =
      pullback.fst f y :=
  pullback.lift_snd _ _ _

lemma geometricFibreToStrictLocalization_π (k : y.AffineEtaleNbhd) :
    f.geometricFibreToStrictLocalization y ≫ (y.affineEtaleNbhdPullbackCone f).π.app k =
      f.geometricFibreToPullback k.point := by
  apply pullback.hom_ext
  · simp [pullback.map, geometricFibreToStrictLocalization]
  · simp [pullback.map, geometricFibreToStrictLocalization]

end Hom

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/-- To extend `X`-morphisms from the geometric fibres of `f` to étale neighbourhoods, it suffices
to extend them to `X ×_Y Spec 𝒪^{sh}_{Y,ȳ}` (for `f` quasi-compact and quasi-separated). -/
theorem extendsAlongGeometricFibres_of_strictLocalization [QuasiCompact f] [QuasiSeparated f]
    (E : X.Etale)
    (h : ∀ ⦃Ω : Type u⦄ [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
      (τ : pullback f y ⟶ E.left), τ ≫ E.hom = pullback.fst f y →
      ∃ τ₁ : pullback y.fromSpecStrictLocalization f ⟶ E.left,
        τ₁ ≫ E.hom = pullback.snd y.fromSpecStrictLocalization f ∧
          f.geometricFibreToStrictLocalization y ≫ τ₁ = τ) :
    ExtendsAlongGeometricFibres f E := by
  intro Ω _ _ y τ hτ
  obtain ⟨τ₁, hτ₁, hτ₁'⟩ := h y τ hτ
  obtain ⟨k, s, hs⟩ := f.exists_etaleNbhd_hom_of_strictLocalization y E τ₁ hτ₁
  refine ⟨k.nbhd, k.point, s, ?_⟩
  rw [← f.geometricFibreToStrictLocalization_π y k, Category.assoc, hs, hτ₁']

end AlgebraicGeometry.Scheme
