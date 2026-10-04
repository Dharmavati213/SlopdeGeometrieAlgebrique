/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.MorphismComparisonIso

/-!
# SGA 1, Exposé XII, 3.1 (xi): `f` is an open immersion iff `f^an` is

For a quasi-compact morphism `f : X → Y` of separated `ℂ`-schemes locally of finite type, `f` is
an open immersion iff `f^an : X^an → Y^an` is an open immersion of locally ringed spaces
(`AnalyticGluing.isOpenImmersion_iff_isOpenImmersion_analyticMap`).

* Direct implication (`AnalyticGluing.isOpenImmersion_analyticMap`, no quasi-compactness): near a
  point of `X^an`, `f` is the inclusion of a basic open `D(t)` of an affine open `V` of `Y`, so
  `f^an` is, in the charts, the analytification of the localization `Γ(V) → Γ(V)_t`, an open
  immersion (`isOpenImmersion_affineAnalytificationMap_of_isLocalization`); and `f^an` is
  injective (`injective_analyticMap_of_injective`).
* Converse: the stalk maps of `f^an` are isomorphisms, so `f` is étale (XII.3.1 (iii)), and
  `f^an` is injective, so `f` is injective on `ℂ`-points. Then `f` is an isomorphism onto its
  image, an open subscheme, by XII.3.1 (ix) on the scheme side (`isIso_of_bijective_map`): the
  corestriction is étale, quasi-compact and bijective on `ℂ`-points. SGA argues the same way:
  "an open immersion is nothing other than an injective étale morphism (EGA IV 17.9.1), so (xi)
  follows from (iii) and (vii)".
-/

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing Topology

namespace SGA.SGA1.ExposeXII

namespace AnalyticGluing

open AffineAnalytification SchemePoints

/-- For an open immersion `f : X → Y`, an affine open `V` of `Y` and `t ∈ Γ(Y, V)` with
`D(t) ⊆ f(X)`, the map `Γ(Y, V) → Γ(X, f⁻¹ D(t))` is the localization at `t`. -/
lemma isLocalization_appLE_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]
    {V : Y.Opens} (hV : IsAffineOpen V) (t : Γ(Y, V)) (ht : Y.basicOpen t ≤ f.opensRange) :
    letI := (f.appLE V (f ⁻¹ᵁ Y.basicOpen t) (f.preimage_mono (Y.basicOpen_le t))).hom.toAlgebra
    IsLocalization.Away t Γ(X, f ⁻¹ᵁ Y.basicOpen t) := by
  have := f.isIso_app (Y.basicOpen t) ht
  have h := (IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers t)
    (asIso (f.app (Y.basicOpen t))).commRingCatIsoToRingEquiv).mp (hV.isLocalization_basicOpen t)
  convert h using 1
  apply Algebra.algebra_ext
  intro a
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
  change (f.appLE V (f ⁻¹ᵁ Y.basicOpen t) _).hom a =
    (f.app (Y.basicOpen t)).hom ((Y.presheaf.map (homOfLE (Y.basicOpen_le t)).op).hom a)
  rw [← CommRingCat.comp_apply, Scheme.Hom.app_eq_appLE, Scheme.Hom.map_appLE]

attribute [local instance] sectionsAlgebra finitePresentation_sections

variable {X Y : Scheme.{0}} [X.Over (Spec (.of ℂ))] [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
  [IsSeparated (X ↘ Spec (.of ℂ))] [Y.Over (Spec (.of ℂ))]
  [LocallyOfFiniteType (Y ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of ℂ))]

omit [IsSeparated (Y ↘ Spec (.of ℂ))] in
/-- For `f` an open immersion, every point of `X^an` lies in a chart `U^an` on which `f^an` is an
open immersion `U^an → V^an` of charts (`U = f⁻¹ D(t)` for a basic open `D(t) ⊆ f(X)` of an
affine open `V` of `Y`). -/
lemma exists_chart_of_isOpenImmersion [IsOpenImmersion f] (x : analyticSpace X) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens) (e : (U : X.Opens) ≤ f ⁻¹ᵁ V),
      x ∈ Set.range (ι U).base ∧ LocallyRingedSpace.IsOpenImmersion (chartHom f e) := by
  set p := (toScheme X).base x with hp
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f p)) isOpen_univ
  obtain ⟨t, ht, hyt⟩ := hV.exists_basicOpen_le (V := f.opensRange) ⟨f p, ⟨p, rfl⟩⟩ hyV
  let U : X.affineOpens := ⟨f ⁻¹ᵁ Y.basicOpen t, (hV.basicOpen t).preimage_of_isOpenImmersion f ht⟩
  let V' : Y.affineOpens := ⟨V, hV⟩
  have e : (U : X.Opens) ≤ f ⁻¹ᵁ V' := f.preimage_mono (Y.basicOpen_le t)
  refine ⟨U, V', e, ?_, ?_⟩
  · have hpU : p ∈ closedPoints X ∩ (U : Set X) := by
      refine ⟨?_, hyt⟩
      rw [← range_toScheme_base]
      exact ⟨x, rfl⟩
    obtain ⟨z, hz⟩ := closedPoints_inter_subset_range_chartToScheme_base U hpU
    refine ⟨z, injective_toScheme_base ?_⟩
    have h1 : (toScheme X).base ((ι U).base z) = (chartToScheme U).base z := by
      rw [← ι_toScheme]
      rfl
    rw [h1, hz, hp]
  · have := finitePresentation_sections Y V'
    have := finitePresentation_sections X U
    exact isOpenImmersion_affineAnalytificationMap_of_isLocalization
      (appLEAlgHom (K := ℂ) f e) t (isLocalization_appLE_of_isOpenImmersion f hV t ht)

/-- XII.3.1 (xi), direct implication: if `f` is an open immersion, so is `f^an`. -/
theorem isOpenImmersion_analyticMap [IsOpenImmersion f] :
    LocallyRingedSpace.IsOpenImmersion (analyticMap f) := by
  have hcomp : ∀ (U : X.affineOpens) (V : Y.affineOpens) (e : (U : X.Opens) ≤ f ⁻¹ᵁ V),
      LocallyRingedSpace.IsOpenImmersion (chartHom f e) →
        LocallyRingedSpace.IsOpenImmersion (ι U ≫ analyticMap f) := by
    intro U V e h
    rw [ι_analyticMap f e]
    infer_instance
  have hstalk (x : analyticSpace X) : IsIso ((analyticMap f).stalkMap x) := by
    obtain ⟨U, V, e, ⟨y, rfl⟩, h⟩ := exists_chart_of_isOpenImmersion f x
    have := hcomp U V e h
    have : IsIso ((ι U ≫ analyticMap f).stalkMap y) := inferInstance
    rw [LocallyRingedSpace.stalkMap_comp] at this
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this
  have hopen : IsOpenEmbedding (analyticMap f).base := by
    refine .of_continuous_injective_isOpenMap (analyticMap f).base.hom.continuous
      (injective_analyticMap_of_injective f f.isOpenEmbedding.injective)
      (isOpenMap_iff_nhds_le.mpr fun x ↦ ?_)
    obtain ⟨U, V, e, ⟨y, rfl⟩, h⟩ := exists_chart_of_isOpenImmersion f x
    have o₁ : IsOpenEmbedding (ι U).base :=
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (ι U)).base_open
    have o₂ : IsOpenEmbedding (ι U ≫ analyticMap f).base :=
      (hcomp U V e h).base_open
    have e₁ := o₁.map_nhds_eq y
    have e₂ := o₂.map_nhds_eq y
    have e₂' : Filter.map ((analyticMap f).base ∘ (ι U).base) (𝓝 y) =
        𝓝 ((analyticMap f).base ((ι U).base y)) := e₂
    rw [← e₁, Filter.map_map, e₂']
  exact LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _ hopen

omit [IsSeparated (X ↘ Spec (.of ℂ))] [IsSeparated (Y ↘ Spec (.of ℂ))] in
/-- On the scheme side: an étale, quasi-compact, quasi-separated morphism of `ℂ`-schemes locally of
finite type which is injective on `ℂ`-points is an open immersion (it is an isomorphism onto its
image, an open subscheme, by `SchemePoints.isIso_of_bijective_map`). -/
theorem isOpenImmersion_of_injective_map [Etale f] [QuasiCompact f] [QuasiSeparated f]
    (h : Function.Injective (SchemePoints.map (K := ℂ) f)) : IsOpenImmersion f := by
  have : UniversallyOpen f := UniversallyOpen.of_flat f
  let V : Y.Opens := ⟨Set.range f, f.isOpenMap.isOpen_range⟩
  let : V.toScheme.Over (Spec (.of ℂ)) := ⟨V.ι ≫ (Y ↘ Spec (.of ℂ))⟩
  have : V.ι.IsOver (Spec (.of ℂ)) := ⟨rfl⟩
  have : LocallyOfFiniteType (V.toScheme ↘ Spec (.of ℂ)) :=
    inferInstanceAs (LocallyOfFiniteType (V.ι ≫ (Y ↘ Spec (.of ℂ))))
  let g : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι f (by simp [V])
  have hg : g ≫ V.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : g.IsOver (Spec (.of ℂ)) := ⟨by
    change g ≫ V.ι ≫ _ = _
    rw [← Category.assoc, hg, CategoryTheory.comp_over]⟩
  have : Etale (g ≫ V.ι) := by rw [hg]; infer_instance
  have : Etale g := Etale.of_comp g V.ι
  have : QuasiCompact (g ≫ V.ι) := by rw [hg]; infer_instance
  have : QuasiCompact g := QuasiCompact.of_comp g V.ι
  have : QuasiSeparated (g ≫ V.ι) := by rw [hg]; infer_instance
  have : QuasiSeparated g := QuasiSeparated.of_comp g V.ι
  have hsurj : Function.Surjective g := by
    rintro ⟨_, ⟨x, rfl⟩⟩
    refine ⟨x, V.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hg]
    rfl
  have hbij : Function.Bijective (SchemePoints.map (K := ℂ) g) := by
    refine ⟨fun a b hab => ?_, (SchemePoints.surjective_map_iff g).mpr hsurj⟩
    have hab' : a.1 ≫ g = b.1 ≫ g := congrArg Subtype.val hab
    apply h
    apply SchemePoints.ext
    change a.1 ≫ f = b.1 ≫ f
    rw [← hg, ← Category.assoc, hab', Category.assoc]
  have : IsIso g := SchemePoints.isIso_of_bijective_map g hbij
  rw [← hg]
  infer_instance

/-- XII.3.1 (xi), converse: for `f` quasi-compact, if `f^an` is an open immersion, so is `f`.
Deviations from SGA: SGA does not assume `X`, `Y` separated (here `X^an` is only built for
separated schemes) nor `f` quasi-compact. -/
theorem isOpenImmersion_of_isOpenImmersion_analyticMap [QuasiCompact f]
    [LocallyRingedSpace.IsOpenImmersion (analyticMap f)] : IsOpenImmersion f := by
  have hét : Etale f := by
    refine (etale_iff_forall_analyticMap f).mpr fun x => ?_
    have hbij : Function.Bijective ((analyticMap f).stalkMap x).hom :=
      ConcreteCategory.bijective_of_isIso ((analyticMap f).stalkMap x)
    exact ⟨RingHom.Flat.of_bijective hbij, map_maximalIdeal_of_surjective _ hbij.2⟩
  have hinj : Function.Injective (SchemePoints.map (K := ℂ) f) := by
    have h : Function.Injective (analyticMap f).base :=
      (inferInstance : LocallyRingedSpace.IsOpenImmersion (analyticMap f)).base_open.injective
    rw [analyticMap_base_eq] at h
    have h' := ((pointsHomeomorph Y).injective.comp h).comp (pointsHomeomorph X).symm.injective
    convert h' using 1
    funext p
    simp
  have : IsSeparated (f ≫ (Y ↘ Spec (.of ℂ))) := by
    rw [CategoryTheory.comp_over]
    infer_instance
  have : IsSeparated f := IsSeparated.of_comp f (Y ↘ Spec (.of ℂ))
  exact isOpenImmersion_of_injective_map f hinj

/-- **XII.3.1 (xi)**: a quasi-compact morphism `f` of separated `ℂ`-schemes locally of finite
type is an open immersion iff `f^an` is an open immersion of locally ringed spaces. Deviations
from SGA: SGA does not assume `X`, `Y` separated nor `f` quasi-compact (the direct implication,
`isOpenImmersion_analyticMap`, does not need quasi-compactness). -/
theorem isOpenImmersion_iff_isOpenImmersion_analyticMap [QuasiCompact f] :
    IsOpenImmersion f ↔ LocallyRingedSpace.IsOpenImmersion (analyticMap f) :=
  ⟨fun _ => isOpenImmersion_analyticMap f,
    fun _ => isOpenImmersion_of_isOpenImmersion_analyticMap f⟩

end AnalyticGluing

end SGA.SGA1.ExposeXII
