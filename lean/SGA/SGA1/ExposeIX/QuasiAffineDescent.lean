/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.EffectiveGluing
import SGA.SGA1.ExposeVIII.Effectiveness

/-!
# SGA 1, Exposé IX, §4: effective descent along faithfully flat quasi-compact morphisms

IX.4.1: a faithfully flat quasi-compact morphism is an effective descent morphism for étale
separated schemes of finite type. As in SGA, an étale separated morphism of finite type is
quasi-finite, hence quasi-affine (VIII.6.2), and quasi-affine schemes descend (VIII.7.9).

The descent data of Exposé VIII are given as equivalence pairs `X'' ⇉ X'`
(`SGA.SGA1.ExposeVIII.DescentDatum`); a descent datum in the sense of this exposé (an action of
the groupoid `S' ×_S S' ⇉ S'`) gives one with `X'' = X' ×_S S'`, `q₁` the projection and `q₂`
the action (`DescentDatum.toEquivalencePair`), with the same effectiveness.

We deduce IX.4.11 (radicial faithfully flat quasi-compact morphisms induce equivalences of étale
sites).
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc pullback.condition pullback.condition_assoc

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

namespace DescentDatum

variable (D : DescentDatum g a)

/-- The morphism `X' ×_S S' ⟶ S' ×_S S'`, `(x', s') ↦ (a(x'), s')`. -/
noncomputable abbrev toPair : pullback (a ≫ g) g ⟶ pullback g g :=
  pullback.map _ _ _ _ a (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma swapAct_toPair :
    D.swapAct ≫ toPair = toPair ≫ (pullbackSymmetry g g).hom := by
  apply pullback.hom_ext <;> simp [D.act_comp]

lemma isPullback_fst_toPair :
    IsPullback (pullback.fst (a ≫ g) g) toPair a (pullback.fst g g) :=
  IsPullback.of_bot (h₂₁ := pullback.fst g g) (v₂₁ := pullback.snd g g) (v₂₂ := g) (h₃₁ := g)
    (by simpa using IsPullback.of_hasPullback (a ≫ g) g) (by simp)
    (IsPullback.of_hasPullback g g)

lemma isPullback_act_toPair :
    IsPullback D.act toPair a (pullback.snd g g) := by
  let e : pullback (a ≫ g) g ≅ pullback (a ≫ g) g :=
    ⟨D.swapAct, D.swapAct, D.swapAct_swapAct, D.swapAct_swapAct⟩
  refine (isPullback_fst_toPair (g := g) (a := a)).of_iso e.symm (Iso.refl _)
    (pullbackSymmetry g g) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp [e]
  · simp [e]
  · simp
  · simp

/-- The descent datum of Exposé VIII (an equivalence pair `X' ×_S S' ⇉ X'`, the first projection
and the action) defined by a descent datum of this exposé. -/
noncomputable def toEquivalencePair : ExposeVIII.DescentDatum g where
  X' := X'
  a := a
  X'' := pullback (a ≫ g) g
  b := toPair
  q₁ := pullback.fst (a ≫ g) g
  q₂ := D.act
  isPullback₁ := isPullback_fst_toPair
  isPullback₂ := D.isPullback_act_toPair
  refl T x := ⟨x ≫ pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a (by simp), by simp,
    by rw [Category.assoc, D.unit, Category.comp_id]⟩
  symm T r := ⟨r ≫ D.swapAct, by simp, by simp⟩
  trans T r r' h := by
    have hs : r ≫ pullback.snd (a ≫ g) g ≫ g = (r' ≫ pullback.snd (a ≫ g) g) ≫ g := by
      have := congrArg (· ≫ a ≫ g) h
      simp only [Category.assoc, reassoc_of% D.act_comp] at this
      rw [this, Category.assoc, pullback.condition]
    have key := D.act_lift_act r (r' ≫ pullback.snd (a ≫ g) g) hs
    have hr' : pullback.lift (f := a ≫ g) (g := g) (r ≫ D.act) (r' ≫ pullback.snd (a ≫ g) g)
        (by rw [Category.assoc, reassoc_of% D.act_comp, hs]) = r' := by
      apply pullback.hom_ext <;> simp [h]
    refine ⟨pullback.lift (f := a ≫ g) (g := g) (r ≫ pullback.fst _ _)
      (r' ≫ pullback.snd _ _) (by simpa using hs), by simp, ?_⟩
    rw [← key, hr']

/-- The descent datum of Exposé VIII defined by `D` is effective iff `D` is effective (in the
fibred category of all schemes). -/
lemma isEffective_toEquivalencePair_iff :
    D.toEquivalencePair.IsEffective ↔ D.IsEffective ⊤ :=
  ⟨fun ⟨X, f, h, hh, hq⟩ ↦ ⟨X, f, h, trivial, hh, hq.symm⟩,
    fun ⟨X, b, v, _, hv, hact⟩ ↦ ⟨X, b, v, hv, hact.symm⟩⟩

end DescentDatum

/-! ### IX.4.1 -/

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.1, effectiveness: along a faithfully flat quasi-compact `g`, every descent datum on an
`S'`-scheme étale, separated and of finite type is effective. Such a scheme is quasi-affine over
`S'` (VIII.6.2), and quasi-affine schemes descend (VIII.7.9). -/
theorem DescentDatum.isEffective_of_flat' [Flat g] [QuasiCompact g] [Surjective g]
    (D : DescentDatum g a) (ha : etaleSeparatedFiniteType a) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨⟨ha₁, ha₂⟩, ha₃⟩ := ha
  have : Etale a := ha₁
  have : IsSeparated a := ha₂
  have : QuasiCompact a := ha₃
  have : LocallyQuasiFinite a := locallyQuasiFinite_of_formallyUnramified a
  have : IsQuasiAffineHom D.toEquivalencePair.a := ExposeVIII.isQuasiAffineHom_of_quasiFinite a
  exact D.isEffective_of_flat ⟨⟨ha₁, ha₂⟩, ha₃⟩
    ((D.isEffective_toEquivalencePair_iff).mp D.toEquivalencePair.isEffective_of_isQuasiAffineHom)

/-- IX.4.1: a faithfully flat quasi-compact morphism is an effective descent morphism for the
fibred category of étale, separated schemes of finite type. -/
theorem isEffectiveDescentMorphism_of_flat (g : S' ⟶ S) [Flat g] [QuasiCompact g]
    [Surjective g] : IsEffectiveDescentMorphism g etaleSeparatedFiniteType :=
  ⟨isDescentMorphism_of_flat, fun _ _ D ha ↦ D.isEffective_of_flat' ha⟩

/-! ### IX.4.10 and IX.4.11 -/

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.11, essential surjectivity: along a faithfully flat, quasi-compact, radicial `g`, every
étale `S'`-scheme is the base change of an étale `S`-scheme. As in IX.4.10, every étale
`S'`-scheme carries a unique descent datum; it is effective by IX.4.1 applied over affine opens
of `S` to affine opens of `X'` (every open is stable since `g` is radicial), and gluing (IX.4.3). -/
theorem essSurj_pullback_etale_of_flat_of_universallyInjective (g : S' ⟶ S) [Flat g]
    [QuasiCompact g] [Surjective g] [UniversallyInjective g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g).EssSurj := by
  refine essSurj_pullback_etale_of_isEffective fun X' a _ D ↦
    D.isEffective_of_universallyInjective_of_affine fun U W _ w _ E ↦ ?_
  have : IsAffine U.1 := U.2
  have : UniversallyInjective (pullback.snd g U.1.ι) := MorphismProperty.pullback_snd _ _ ‹_›
  have : IsSeparated (pullback.snd g U.1.ι) :=
    isSeparated_of_injective _ (pullback.snd g U.1.ι).injective
  have : QuasiSeparatedSpace (pullback g U.1.ι : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.snd g U.1.ι)
  exact (E.isEffective_of_flat' ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩).of_le
    etaleSeparatedFiniteType_le_etale

set_option backward.isDefEq.respectTransparency.types false in
/-- IX.4.11: for `g` faithfully flat, quasi-compact and radicial, base change along `g` is an
equivalence between the categories of étale schemes over `S` and over `S'`. -/
theorem isEquivalence_pullback_etale_of_flat (g : S' ⟶ S) [Flat g] [QuasiCompact g]
    [Surjective g] [UniversallyInjective g] :
    (MorphismProperty.Over.pullback @Etale ⊤ g).IsEquivalence :=
  have := essSurj_pullback_etale_of_flat_of_universallyInjective g
  have := (fullyFaithfulPullbackEtale g).full
  have := (fullyFaithfulPullbackEtale g).faithful
  { }

end SGA.SGA1.ExposeIX
