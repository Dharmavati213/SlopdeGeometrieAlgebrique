/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.EtaleSpreadingOut
import SGA.Foundations.Limits.PropertiesLimitClosedImmersion
import SGA.Foundations.Limits.SpreadingOutGluing

/-!
# Étale and smooth morphisms over a limit descend to a finite level

EGA IV 17.7.8 (Stacks 07RP for étale, 0CN2 for smooth): let `c.pt = lim E i` be the limit of a
cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition maps,
`X_j ⟶ E j` of finite presentation. If `X_j ×_{E j} c.pt ⟶ c.pt` is étale (resp. smooth), then
`X_j ×_{E j} E k ⟶ E k` is étale (resp. smooth) for some `k`.

The proof works for every property `P` of morphisms given by a property `Q` of ring maps
(`HasRingHomProperty P Q`), implying local finite presentation, stable under base change, and such
that `Q`-algebras over a filtered colimit of rings descend to a member of the diagram
(`CommRingCat.ColimitDescendsStatement Q`):

* `AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_isAffine_of_hasRingHomProperty`: over a
  diagram of affine schemes, an affine `Y ⟶ c.pt` with `P` is the base change of an affine
  `Y_j ⟶ E j` with `P`.
* `AlgebraicGeometry.Scheme.limitDescendsAffine_of_isAffine_source`: properties local on the source
  reduce to affine `X_j` (cover `X_j` by finitely many affine opens).
* `AlgebraicGeometry.Scheme.limitDescends_of_hasRingHomProperty`: then `P` descends. For affine
  `X_j` and affine members, `X_j ×_{E j} c.pt` has a model with `P` over some `E k`, and two models
  of the same scheme become isomorphic at a finite level (EGA IV 8.8.2 (i),
  `Scheme.exists_iso_of_isPullback`).
* `CommRingCat.colimitDescends_smooth`, `CommRingCat.colimitDescends_etale`: smooth (resp.
  étale) algebras descend along filtered colimits (from mathlib's
  `Algebra.Smooth.exists_subalgebra_fg`, resp. `CommRingCat.exists_etale_isPushout_of_isColimit`).
* `AlgebraicGeometry.Scheme.limitDescends_etale`, `Scheme.limitDescends_smooth`: EGA IV 17.7.8.

## References

* [EGA IV₄, 17.7.8][EGA4]
* [Stacks Project, Tag 07RP](https://stacks.math.columbia.edu/tag/07RP),
  [Tag 0CN2](https://stacks.math.columbia.edu/tag/0CN2)
-/

universe u

open CategoryTheory Limits TensorProduct

namespace CommRingCat

/-- Algebras with the property `Q` descend along filtered colimits of rings: for
`R = colim Rⱼ` and `φ : R ⟶ B` with `Q`, there are `j`, `φⱼ : Rⱼ ⟶ Bⱼ` with `Q` and a pushout
square `Rⱼ ⟶ R, Rⱼ ⟶ Bⱼ, R ⟶ B, Bⱼ ⟶ B` (i.e. `B ≅ R ⊗_{Rⱼ} Bⱼ`). -/
def ColimitDescendsStatement (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) :
    Prop :=
  ∀ ⦃J : Type u⦄ [SmallCategory J] [IsFiltered J] {F : J ⥤ CommRingCat.{u}} {c : Cocone F}
    (_ : IsColimit c) {B : CommRingCat.{u}} (φ : c.pt ⟶ B), Q φ.hom →
      ∃ (j : J) (Bj : CommRingCat.{u}) (φj : F.obj j ⟶ Bj) (ψ : Bj ⟶ B),
        Q φj.hom ∧ IsPushout (c.ι.app j) φj φ ψ

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 17.7.8 for algebras (Stacks 0CN2): smooth algebras descend along filtered colimits. -/
theorem colimitDescends_smooth : ColimitDescendsStatement.{u} @RingHom.Smooth := by
  intro J _ _ F c hc B φ hφ
  algebraize [φ.hom]
  obtain ⟨A₀, B₀, _, _, hA₀, hB₀, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ c.pt B
  obtain ⟨j, _, ψ, H⟩ := exists_isPushout_of_isColimit_of_subalgebra hc φ A₀ hA₀ B₀
    e.toRingEquiv (fun x ↦ by
      change e (algebraMap c.pt B x) = _
      rw [AlgEquiv.commutes]
      rfl)
  exact ⟨j, _, _, ψ, RingHom.smooth_algebraMap.mpr inferInstance, H⟩

/-- EGA IV 17.7.8 for algebras (Stacks 07RP): étale algebras descend along filtered colimits. -/
theorem colimitDescends_etale : ColimitDescendsStatement.{u} @RingHom.Etale :=
  fun _ _ _ _ _ hc _ φ hφ ↦ exists_etale_isPushout_of_isColimit hc φ hφ

@[deprecated (since := "2026-10-04")] alias ColimitDescends := ColimitDescendsStatement
@[deprecated (since := "2026-10-04")] alias exists_smooth_isPushout_of_isColimit :=
  colimitDescends_smooth

end CommRingCat

namespace AlgebraicGeometry

variable {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (ii) with a property `P` given by a property `Q` of ring maps that descends along
filtered colimits (affine case): over the limit of a cofiltered diagram of affine schemes, an affine
scheme `Y` with `P` over the limit is the base change of an affine scheme with `P` over some member
of the diagram. -/
theorem Scheme.exists_isPullback_of_isLimit_of_isAffine_of_hasRingHomProperty
    {P : MorphismProperty Scheme.{u}} {Q : ∀ {R S : Type u} [CommRing R] [CommRing S],
      (R →+* S) → Prop} [HasRingHomProperty P Q]
    (hQ : CommRingCat.ColimitDescendsStatement.{u} Q)
    [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, IsAffine (E.obj i)]
    (hc : IsLimit c) {Y : Scheme.{u}} [IsAffine Y] (q : Y ⟶ c.pt) (hq : P q) :
    ∃ (j : I) (Yj : Scheme.{u}) (qj : Yj ⟶ E.obj j) (e : Y ⟶ Yj),
      IsAffine Yj ∧ P qj ∧ IsPullback e q qj (c.π.app j) := by
  have hΓ := (nonempty_isColimit_Γ_mapCocone E c hc).some
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  let φ : Γ(c.pt, ⊤) ⟶ Γ(Y, ⊤) := q.appTop
  have hφ : Q φ.hom := HasRingHomProperty.iff_of_isAffine.mp hq
  obtain ⟨j, Bj, φj, ψ, hφj, H⟩ := hQ hΓ φ hφ
  have hSpec := isPullback_SpecMap_of_isPushout _ _ _ _ H
  have hP : P (Spec.map φj) := HasRingHomProperty.Spec_iff.mpr hφj
  refine ⟨j.unop, Spec Bj, Spec.map φj ≫ (E.obj j.unop).isoSpec.inv, Y.isoSpec.hom ≫ Spec.map ψ,
    inferInstance, (MorphismProperty.cancel_right_of_respectsIso P _ _).mpr hP, ?_⟩
  refine hSpec.flip.of_iso Y.isoSpec.symm (Iso.refl _) c.pt.isoSpec.symm
    (E.obj j.unop).isoSpec.symm (by simp) ?_ (by simp) ?_
  · simp only [Iso.symm_hom]
    exact Scheme.isoSpec_inv_naturality q
  · simp only [Iso.symm_hom]
    exact Scheme.isoSpec_inv_naturality (X := c.pt) (c.π.app j.unop)

set_option backward.isDefEq.respectTransparency false in
/-- The pieces `U_a ×_Z Y ⟶ X ×_Z Y` of the cover of `X ×_Z Y` induced by an open cover `{U_a}` of
`X`, followed by the projection to `Y`, are the projections `U_a ×_Z Y ⟶ Y`. -/
@[reassoc]
lemma Scheme.pullbackCoverOfLeft_f_comp_snd {X Y Z : Scheme.{u}} (𝒰 : X.OpenCover) (f : X ⟶ Z)
    (g : Y ⟶ Z) (a : 𝒰.I₀) :
    (𝒰.pullbackCoverOfLeft f g).f a ≫ pullback.snd f g = pullback.snd (𝒰.f a ≫ f) g := by
  change pullback.map _ _ _ _ (𝒰.f a) (𝟙 Y) (𝟙 Z) (by simp) (by simp) ≫ pullback.snd f g = _
  simp

/-- EGA IV 8.10.5 for `P` over diagrams of affine schemes, for affine `X_j`: as
`Scheme.LimitDescendsAffineStatement P` with `X_j` affine. -/
def Scheme.LimitDescendsAffineSourceStatement (P : MorphismProperty Scheme.{u}) : Prop :=
  ∀ ⦃I : Type u⦄ [Category.{u} I] [IsCofiltered I] (E : I ⥤ Scheme.{u})
    [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, IsAffine (E.obj i)] (c : Cone E)
    (_ : IsLimit c) ⦃j : I⦄ ⦃Xj : Scheme.{u}⦄ [IsAffine Xj] (qj : Xj ⟶ E.obj j)
    [LocallyOfFinitePresentation qj], P (pullback.snd qj (c.π.app j)) →
      ∃ (k : I) (g : k ⟶ j), P (pullback.snd qj (E.map g))

set_option backward.isDefEq.respectTransparency false in
/-- For a property local on the source and stable under base change, EGA IV 8.10.5 over diagrams
of affine schemes reduces to affine `X_j`: cover `X_j` by finitely many affine opens. -/
theorem Scheme.limitDescendsAffine_of_isAffine_source {P : MorphismProperty Scheme.{u}}
    [IsZariskiLocalAtSource P] [P.IsStableUnderBaseChange]
    (H : Scheme.LimitDescendsAffineSourceStatement.{u} P) :
    Scheme.LimitDescendsAffineStatement.{u} P := by
  intro I _ _ E _ _ c hc j X Xj qj _ _ _ e q h hq
  classical
  have hq₀ : P (pullback.snd qj (c.π.app j)) :=
    (MorphismProperty.cancel_left_of_respectsIso P h.isoPullback.hom _).mp
      (by rw [h.isoPullback_hom_snd]; exact hq)
  have : CompactSpace Xj := QuasiCompact.compactSpace_of_compactSpace qj
  let 𝒰 := Xj.affineCover.finiteSubcover
  -- the restrictions of `qj` to the pieces of `𝒰`
  have key (a : 𝒰.I₀) : ∃ (k : I) (g : k ⟶ j), P (pullback.snd (𝒰.f a ≫ qj) (E.map g)) := by
    have : IsAffine (𝒰.X a) := inferInstanceAs (IsAffine (Spec _))
    have h₁ : P ((𝒰.pullbackCoverOfLeft qj (c.π.app j)).f a ≫ pullback.snd qj (c.π.app j)) :=
      IsZariskiLocalAtSource.comp hq₀ _
    rw [Scheme.pullbackCoverOfLeft_f_comp_snd] at h₁
    exact H E c hc (𝒰.f a ≫ qj) h₁
  choose k g hg using key
  -- a common level `m₀` below all the `k a`, compatibly with the `g a`
  obtain ⟨m₀, φ₁, hφ₁⟩ := IsCofiltered.inf_exists (insert j (Finset.univ.image k))
    (Finset.univ.image fun a : 𝒰.I₀ ↦
      (⟨k a, j, by simp, by simp, g a⟩ : Σ' (X Y : I) (_ : X ∈ insert j (Finset.univ.image k))
        (_ : Y ∈ insert j (Finset.univ.image k)), X ⟶ Y))
  refine ⟨m₀, φ₁ (by simp), IsZariskiLocalAtSource.of_openCover (𝒰.pullbackCoverOfLeft qj _)
    fun (a : 𝒰.I₀) ↦ ?_⟩
  have ht : φ₁ (X := k a) (by simp) ≫ g a = φ₁ (X := j) (by simp) :=
    hφ₁ (by simp) (by simp) (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  have := Scheme.pullback_snd_comp_of_isStableUnderBaseChange (𝒰.f a ≫ qj)
    (E.map (φ₁ (X := k a) (by simp))) (E.map (g a)) (hg a)
  rw [← E.map_comp, ht] at this
  rwa [Scheme.pullbackCoverOfLeft_f_comp_snd]

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 for `P = Q`-locally, over diagrams of affine schemes and for affine `X_j`: the
base change `Y = X_j ×_{E j} c.pt` has a model `Y_k` with `P` over some `E k`
(`exists_isPullback_of_isLimit_of_isAffine_of_hasRingHomProperty`), and the two models `X_j` and
`Y_k` of `Y` become isomorphic at a finite level (EGA IV 8.8.2 (i)). -/
theorem Scheme.limitDescendsAffineSource_of_hasRingHomProperty {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    [P.IsStableUnderBaseChange]
    (hP : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → LocallyOfFinitePresentation f)
    (hQ : CommRingCat.ColimitDescendsStatement.{u} Q) :
    Scheme.LimitDescendsAffineSourceStatement.{u} P := by
  intro I _ _ E _ _ c hc j Xj _ qj _ hq
  have : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have : IsAffineHom qj := isAffineHom_of_isAffine qj
  have : IsAffineHom (pullback.snd qj (c.π.app j)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  have : IsAffine (pullback qj (c.π.app j)) :=
    @isAffine_of_isAffineHom _ c.pt (pullback.snd qj (c.π.app j)) _ ‹IsAffine c.pt›
  -- `Y = X_j ×_{E j} c.pt` has a model with `P`
  obtain ⟨k, Yk, pk, eY, _, hpk, hY⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_isAffine_of_hasRingHomProperty hQ hc
      (pullback.snd qj (c.π.app j)) hq
  have : LocallyOfFinitePresentation pk := hP pk hpk
  have : IsAffineHom pk := isAffineHom_of_isAffine pk
  -- the two models at a common level become isomorphic
  let M₁ : Scheme.LimitModel c (pullback.snd qj (c.π.app j)) j :=
    { obj := Xj, hom := qj, proj := pullback.fst _ _, isPullback := IsPullback.of_hasPullback _ _ }
  let M₂ : Scheme.LimitModel c (pullback.snd qj (c.π.app j)) k :=
    { obj := Yk, hom := pk, proj := eY, isPullback := hY }
  let N₁ := M₁.lower (IsCofiltered.minToLeft j k)
  let N₂ := M₂.lower (IsCofiltered.minToRight j k)
  obtain ⟨l, θ, hθ, -⟩ := Scheme.exists_iso_of_isPullback hc N₁.isPullback N₂.isPullback
  have h₂ : P (pullback.snd N₂.hom (E.map l.hom)) :=
    MorphismProperty.pullback_snd _ _ (MorphismProperty.pullback_snd _ _ hpk)
  have h₁ : P (pullback.snd N₁.hom (E.map l.hom)) := by
    rw [← hθ]
    exact (MorphismProperty.cancel_left_of_respectsIso P _ _).mpr h₂
  refine ⟨l.left, l.hom ≫ IsCofiltered.minToLeft j k, ?_⟩
  have := (MorphismProperty.arrow_mk_iso_iff P (Scheme.pullbackSndCompArrowIso qj (E.map l.hom)
    (E.map (IsCofiltered.minToLeft j k)))).mpr h₁
  exact Scheme.of_pullback_snd_eq (E.map_comp _ _).symm this

/-- EGA IV 8.10.5 for a property `P` of morphisms given by a property `Q` of ring maps
(`HasRingHomProperty P Q`) which implies local finite presentation, is stable under base change,
and descends along filtered colimits of rings (`CommRingCat.ColimitDescendsStatement Q`). -/
theorem Scheme.limitDescends_of_hasRingHomProperty {P : MorphismProperty Scheme.{u}}
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop} [HasRingHomProperty P Q]
    [P.IsStableUnderBaseChange]
    (hP : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → LocallyOfFinitePresentation f)
    (hQ : CommRingCat.ColimitDescendsStatement.{u} Q) : Scheme.LimitDescendsStatement.{u} P :=
  Scheme.limitDescends_of_affine (Scheme.limitDescendsAffine_of_isAffine_source
    (Scheme.limitDescendsAffineSource_of_hasRingHomProperty hP hQ))

/-- **EGA IV 17.7.8 for étale morphisms** (Stacks 07RP): over the limit of a cofiltered diagram
of quasi-compact and quasi-separated schemes with affine transition maps, étaleness of a morphism
of finite presentation descends to a finite stage. -/
@[stacks 07RP]
theorem Scheme.limitDescends_etale : Scheme.LimitDescendsStatement.{u} @Etale :=
  Scheme.limitDescends_of_hasRingHomProperty (fun _ _ _ _ ↦ inferInstance)
    CommRingCat.colimitDescends_etale

/-- **EGA IV 17.7.8 for smooth morphisms** (Stacks 0CN2): over the limit of a cofiltered diagram
of quasi-compact and quasi-separated schemes with affine transition maps, smoothness of a morphism
of finite presentation descends to a finite stage. -/
@[stacks 0CN2]
theorem Scheme.limitDescends_smooth : Scheme.LimitDescendsStatement.{u} @Smooth :=
  Scheme.limitDescends_of_hasRingHomProperty (fun _ _ _ _ ↦ inferInstance)
    CommRingCat.colimitDescends_smooth

end AlgebraicGeometry
