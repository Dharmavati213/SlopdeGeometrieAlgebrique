/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.NoetherianApproximation
import SGA.SGA1.ExposeIX.FiniteEffectiveDescent


/-!
# SGA 1, Exposé IX, 4.10: topological invariance of the étale site

IX.4.10 (`isEquivalence_pullback_etale_of_isFinite`): for `g : S' ⟶ S` finite, radicial,
surjective and of finite presentation, base change along `g` is an equivalence from étale
`S`-schemes to étale `S'`-schemes.

Full faithfulness is IX.3 (`fullyFaithfulPullbackEtale`). For essential surjectivity we follow
SGA: along the radicial `g`, an étale `S'`-scheme carries a unique descent datum
(`DescentDatum.act_eq_of_universallyInjective`), which is effective as soon as the scheme is a base
change (`DescentDatum.isEffective_of_isPullback`), and effectiveness is local on `S` and on the
étale scheme (`DescentDatum.isEffective_of_universallyInjective_of_affine`). In the affine case
(`exists_isPullback_etale_of_isFinite_of_isAffine`), `S = Spec A`, `S' = Spec A'` and the étale
scheme is `Spec B'`; by the limit methods of EGA IV 8
(`Algebra.exists_finite_model_of_isNilpotent`, `Algebra.Etale.exists_model_of_subset_range`) the
situation descends to a finitely generated subring `A₀ ⊆ A`, and over the noetherian `Spec A₀`
the statement is IX.4.10 in the noetherian case
(`isEquivalence_pullback_etale_of_isFinite_of_isLocallyNoetherian`, from IX.4.7).
-/

universe u

open CategoryTheory Limits MorphismProperty TensorProduct

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

set_option backward.isDefEq.respectTransparency false in
/-- The descent datum on `X'` induced by a cartesian square `X' = X ×_S S'`. -/
noncomputable def DescentDatum.ofIsPullback {X : Scheme.{u}} {b : X ⟶ S} {v : X' ⟶ X}
    (hv : IsPullback v a b g) : DescentDatum g a where
  act := hv.lift (pullback.fst (a ≫ g) g ≫ v) (pullback.snd (a ≫ g) g) (by
    rw [Category.assoc, hv.w, pullback.condition])
  act_comp := hv.lift_snd _ _ _
  unit := by
    apply hv.hom_ext
    · simp only [Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc, Category.id_comp]
    · simp
  assoc := by
    apply hv.hom_ext
    · simp only [Category.assoc, IsPullback.lift_fst, pullback.lift_fst_assoc]
    · simp only [Category.assoc, IsPullback.lift_snd, pullback.lift_snd]

lemma DescentDatum.ofIsPullback_act_v {X : Scheme.{u}} {b : X ⟶ S} {v : X' ⟶ X}
    (hv : IsPullback v a b g) :
    (DescentDatum.ofIsPullback hv).act ≫ v = pullback.fst (a ≫ g) g ≫ v :=
  hv.lift_fst _ _ _

/-- Along a radicial `g`, a descent datum on an étale `S'`-scheme `X'` is effective as soon as
`X'` is the base change of some `S`-scheme. -/
lemma DescentDatum.isEffective_of_isPullback [UniversallyInjective g] [Etale a]
    (D : DescentDatum g a) {P : MorphismProperty Scheme.{u}} {X : Scheme.{u}} {b : X ⟶ S}
    {v : X' ⟶ X} (hv : IsPullback v a b g) (hb : P b) : D.IsEffective P :=
  ⟨X, b, v, hb, hv, by
    rw [DescentDatum.act_eq_of_universallyInjective D (DescentDatum.ofIsPullback hv),
      DescentDatum.ofIsPullback_act_v]⟩

end SGA.SGA1.ExposeIX

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.10, affine case (EGA IV 8 reduction to IX.4.10 over a noetherian base): let
`h : T' ⟶ T` be finite, radicial, surjective and of finite presentation with `T` affine. Every
affine étale `T'`-scheme is the base change of an étale `T`-scheme. -/
theorem exists_isPullback_etale_of_isFinite_of_isAffine {T T' W : Scheme.{u}} [IsAffine T]
    (h : T' ⟶ T) [IsFinite h] [UniversallyInjective h] [Surjective h]
    [LocallyOfFinitePresentation h] [IsAffine W] (w : W ⟶ T') [Etale w] :
    ∃ (X : Scheme.{u}) (b : X ⟶ T) (v : W ⟶ X), Etale b ∧ IsPullback v w b h := by
  have : IsAffine T' := isAffine_of_isAffineHom h
  let A := Γ(T, ⊤)
  let A' := Γ(T', ⊤)
  let B' := Γ(W, ⊤)
  let : Algebra A A' := h.appTop.hom.toAlgebra
  let : Algebra A' B' := w.appTop.hom.toAlgebra
  have hh : h = T'.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫
      T.isoSpec.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality h).symm
  have hw : w = W.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫
      T'.isoSpec.inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact (Scheme.isoSpec_hom_naturality w).symm
  -- properties of `A → A'` and `A' → B'`
  have : Module.Finite A A' := h.finite_appTop
  have : Algebra.FinitePresentation A A' :=
    HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) h inferInstance
  have : Algebra.Etale A' B' := HasRingHomProperty.appTop (P := @Etale) w inferInstance
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap A A')) =
      T'.isoSpec.inv ≫ h ≫ T.isoSpec.hom := by
    rw [hh]; simp
  have hsurj : ∀ a : A, algebraMap A A' a = 0 → IsNilpotent a :=
    isNilpotent_of_algebraMap_eq_zero_of_surjective (by rw [hφ]; infer_instance)
  have hrad : ∀ x ∈ KaehlerDifferential.ideal A A', IsNilpotent x :=
    universallyInjective_specMap_iff.mp (by
      rw [hφ, MorphismProperty.cancel_left_of_respectsIso @UniversallyInjective,
        MorphismProperty.cancel_right_of_respectsIso @UniversallyInjective]
      infer_instance)
  -- noetherian models
  obtain ⟨T₀, hT₀, hmodel⟩ := Algebra.Etale.exists_model_of_subset_range (A' := A') (B' := B')
  obtain ⟨A₀, A'₀, _, _, hA₀, hfin₀, hfp₀, hsurj₀, hrad₀, e₁, hT⟩ :=
    Algebra.exists_finite_model_of_isNilpotent hsurj hrad T₀ hT₀
  let φ₁ : A'₀ →+* A' :=
    (e₁ : A ⊗[A₀] A'₀ →+* A').comp Algebra.TensorProduct.includeRight.toRingHom
  let : Algebra A'₀ A' := φ₁.toAlgebra
  obtain ⟨C, _, _, hC, ⟨e₂⟩⟩ := hmodel A'₀ fun t ht ↦ by
    obtain ⟨y, hy⟩ := hT ht
    exact ⟨y, hy⟩
  -- IX.4.10 over the noetherian ring `A₀`
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hA₀
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  let g₀ := Spec.map (CommRingCat.ofHom (algebraMap A₀ A'₀))
  have : IsFinite g₀ := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfin₀)
  have : Surjective g₀ := surjective_specMap_of_isIntegral hsurj₀
  have : UniversallyInjective g₀ := universallyInjective_specMap_iff.mpr hrad₀
  have := isEquivalence_pullback_etale_of_isFinite_of_isLocallyNoetherian (g := g₀)
  let c₀ := Spec.map (CommRingCat.ofHom (algebraMap A'₀ C))
  have hc₀ : Etale c₀ :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr (RingHom.etale_algebraMap.mpr hC)
  obtain ⟨X₀, ⟨i⟩⟩ := Functor.EssSurj.mem_essImage (F := MorphismProperty.Over.pullback @Etale ⊤ g₀)
    (MorphismProperty.Over.mk ⊤ c₀ hc₀)
  have : Etale X₀.hom := X₀.prop
  let j := (MorphismProperty.Over.forget @Etale ⊤ _ ⋙ CategoryTheory.Over.forget _).mapIso i
  have hj : j.hom ≫ c₀ = pullback.snd X₀.hom g₀ :=
    CategoryTheory.Over.w ((MorphismProperty.Over.forget @Etale ⊤ _).map i.hom)
  have P3 : IsPullback (j.inv ≫ pullback.fst X₀.hom g₀) c₀ X₀.hom g₀ := by
    refine (IsPullback.of_hasPullback X₀.hom g₀).of_iso j (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp
    · simpa using hj.symm
  -- the pushout squares of rings, and the cartesian squares of their spectra
  have sq1 : IsPushout (CommRingCat.ofHom (algebraMap A₀ A))
      (CommRingCat.ofHom (algebraMap A₀ A'₀)) (CommRingCat.ofHom (algebraMap A A'))
      (CommRingCat.ofHom φ₁) := by
    refine (CommRingCat.isPushout_tensorProduct A₀ A A'₀).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) e₁.toRingEquiv.toCommRingCatIso (by simp) (by simp) ?_ rfl
    ext x
    exact e₁.commutes x
  have sq2 : IsPushout (CommRingCat.ofHom φ₁) (CommRingCat.ofHom (algebraMap A'₀ C))
      (CommRingCat.ofHom (algebraMap A' B'))
      (CommRingCat.ofHom ((e₂ : A' ⊗[A'₀] C →+* B').comp
        Algebra.TensorProduct.includeRight.toRingHom)) := by
    refine (CommRingCat.isPushout_tensorProduct A'₀ A' C).of_iso (Iso.refl _) (Iso.refl _)
      (Iso.refl _) e₂.toRingEquiv.toCommRingCatIso
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]; rfl) (by simp) ?_ rfl
    ext x
    exact e₂.commutes x
  have P1 := isPullback_SpecMap_of_isPushout _ _ _ _ sq1
  have P2 := isPullback_SpecMap_of_isPushout _ _ _ _ sq2
  let sA := Spec.map (CommRingCat.ofHom (algebraMap A₀ A))
  have hout := P2.flip.paste_horiz P3
  have hw₀ : Spec.map (CommRingCat.ofHom φ₁) ≫ g₀ =
      Spec.map (CommRingCat.ofHom (algebraMap A A')) ≫ sA := P1.w.symm
  rw [hw₀] at hout
  let v₀ : Spec (.of B') ⟶ pullback X₀.hom sA :=
    pullback.lift (Spec.map (CommRingCat.ofHom ((e₂ : A' ⊗[A'₀] C →+* B').comp
        Algebra.TensorProduct.includeRight.toRingHom)) ≫ j.inv ≫ pullback.fst X₀.hom g₀)
      (Spec.map (CommRingCat.ofHom (algebraMap A' B')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A A'))) (by rw [hout.w, Category.assoc])
  have hv₀ : IsPullback v₀ (Spec.map (CommRingCat.ofHom (algebraMap A' B')))
      (pullback.snd X₀.hom sA) (Spec.map (CommRingCat.ofHom (algebraMap A A'))) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact hout) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback X₀.hom sA)
  refine ⟨pullback X₀.hom sA, pullback.snd X₀.hom sA ≫ T.isoSpec.inv, W.isoSpec.hom ≫ v₀,
    inferInstance, ?_⟩
  refine hv₀.of_iso W.isoSpec.symm (Iso.refl _) T'.isoSpec.symm T.isoSpec.symm (by simp) ?_
    (by simp) ?_
  · rw [hw]; simp
  · rw [hh]; simp

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10, essential surjectivity: for `g : S' ⟶ S` finite, radicial, surjective and of finite
presentation, every étale `S'`-scheme is the base change of an étale `S`-scheme. As in SGA,
every étale `S'`-scheme carries a unique descent datum relative to `g`, and effectiveness is local
on `S` and on the étale scheme; in the affine case one reduces by EGA IV 8 to a noetherian base,
where the statement follows from IX.4.7. -/
theorem essSurj_pullback_etale_of_isFinite {S' S : Scheme.{u}} (g : S' ⟶ S) [IsFinite g]
    [UniversallyInjective g] [Surjective g] [LocallyOfFinitePresentation g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g).EssSurj :=
  essSurj_pullback_etale_of_isEffective fun _ _ _ D ↦
    D.isEffective_of_universallyInjective_of_affine fun U W _ w _ E ↦ by
      have : IsAffine U.1 := U.2
      have : UniversallyInjective (pullback.snd g U.1.ι) := MorphismProperty.pullback_snd _ _ ‹_›
      obtain ⟨X, b, v, hb, hv⟩ :=
        exists_isPullback_etale_of_isFinite_of_isAffine (pullback.snd g U.1.ι) w
      exact E.isEffective_of_isPullback hv hb

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.10 (topological invariance of the étale site): for `g : S' ⟶ S` finite, radicial,
surjective and of finite presentation, base change along `g` is an equivalence from étale
`S`-schemes to étale `S'`-schemes. -/
theorem isEquivalence_pullback_etale_of_isFinite {S' S : Scheme.{u}} (g : S' ⟶ S) [IsFinite g]
    [UniversallyInjective g] [Surjective g] [LocallyOfFinitePresentation g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsEquivalence :=
  have := essSurj_pullback_etale_of_isFinite g
  have := (fullyFaithfulPullbackEtale g).full
  have := (fullyFaithfulPullbackEtale g).faithful
  { }

end SGA.SGA1.ExposeIX
