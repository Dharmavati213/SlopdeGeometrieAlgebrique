/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FiniteEtaleEquivalence
import SGA.SGA1.ExposeIX.FiniteEtaleLimit
import SGA.SGA1.ExposeIX.NilImmersion

/-!
# SGA 1, Exposé IX, 1.10: étale coverings of a proper scheme over a complete local ring

IX.1.10: let `A` be a complete noetherian local ring with residue field `k`, `X` proper over
`S = Spec A` and `X₀ = X ⊗_A k` its closed fibre. Then `X' ↦ X' ×_X X₀` is an equivalence from
the étale coverings of `X` to those of `X₀` (`EtaleCoveringsOfClosedFibreStatement`).

The comparison with the formal completion and Grothendieck's existence theorem are in
`SGA.Foundations.Cohomology.FiniteEtaleEquivalence`, which assumes I.8.3 (base change along a
surjective closed immersion is an equivalence on étale coverings). We discharge this hypothesis
by IX.1.7 (`isEquivalence_finiteEtale_pullback_of_isClosedImmersion`) and obtain:

* full faithfulness for every proper `X` (`full_pullback_closedFibre`,
  `faithful_pullback_closedFibre`); SGA notes that this half does not use the existence theorem;
* the equivalence when `X` is projective over `A`, i.e. closed in some `ℙ(τ; Spec A)` with `τ`
  finite (`isEquivalence_pullback_closedFibre_of_isClosedImmersion`);
* the reduction of the general statement to the essential surjectivity along the first
  thickening `X ⊗_A A/𝔪 ⟶ X` (`etaleCoveringsOfClosedFibreStatement_of_essSurj`), the form in
  which the proper case of the existence theorem is stated in the foundations.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

open Scheme (FiniteEtale)

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.7 (I.8.3) for étale coverings: base change along a surjective closed immersion is an
equivalence of the categories of étale coverings. -/
theorem isEquivalence_finiteEtale_pullback_of_isClosedImmersion {S₀ S : Scheme.{u}} (i : S₀ ⟶ S)
    [IsClosedImmersion i] [Surjective i] : (FiniteEtale.pullback i).IsEquivalence := by
  have hff := fullyFaithfulOverPullbackOfUniversallyInjective i Scheme.finiteEtaleHom
    (fun _ _ _ h ↦ h.2)
  have := hff.full
  have := hff.faithful
  have := essSurj_pullback_etale_of_isClosedImmersion i
  have : (FiniteEtale.pullback i).EssSurj := ⟨fun Y ↦ by
    have : IsFinite Y.hom := Y.prop.1
    have : Etale Y.hom := Y.prop.2
    obtain ⟨Z, q, e, hq, hq', h⟩ := exists_isPullback_of_essSurj_pullback_etale i Y.hom
    exact ⟨MorphismProperty.Over.mk ⊤ q ⟨hq, hq'⟩,
      ⟨(MorphismProperty.Over.isoMk h.isoPullback (IsPullback.isoPullback_hom_snd h)).symm⟩⟩⟩
  exact { }

/-- I.8.3 in the form of the hypothesis `h83` of `SGA.Foundations.Cohomology.FiniteEtaleEquivalence`
(proved by IX.1.7). -/
theorem finiteEtale_h83 : ∀ ⦃X Y : Scheme.{u}⦄ (i : X ⟶ Y), IsClosedImmersion i → Surjective i →
    (FiniteEtale.pullback i).IsEquivalence := fun _ _ i _ _ ↦
  isEquivalence_finiteEtale_pullback_of_isClosedImmersion i

section ClosedFibre

open IsLocalRing CohomologyAux

variable (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The closed fibre `X₀ = X ⊗_A k ⟶ X` of a scheme over a local ring. -/
noncomputable abbrev closedFibreι :
    pullback f (Spec.map (CommRingCat.ofHom (residue A))) ⟶ X :=
  pullback.fst _ _

/-- `A/𝔪¹ ≅ k`. -/
noncomputable def quotResidueIso :
    CommRingCat.of (A ⧸ maximalIdeal A ^ (0 + 1)) ≅ CommRingCat.of (ResidueField A) :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).toCommRingCatIso

lemma quotResidueIso_hom :
    CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (0 + 1))) ≫ (quotResidueIso A).hom =
      CommRingCat.ofHom (residue A) := by
  ext a
  rfl

/-- The identification of the closed fibre with the first thickening `X ⊗_A A/𝔪 ⟶ X`. -/
noncomputable def closedFibreToThickening :
    pullback f (Spec.map (CommRingCat.ofHom (residue A))) ⟶
      thickening (A := .of A) f (maximalIdeal A) 0 :=
  pullback.map _ _ _ _ (𝟙 X) (Spec.map (quotResidueIso A).hom) (𝟙 _) (by simp)
    (by rw [← quotResidueIso_hom, Spec.map_comp, Category.comp_id])

lemma closedFibreToThickening_ι :
    closedFibreToThickening A f ≫ thickening.ι (A := .of A) f (maximalIdeal A) 0 =
      closedFibreι A f :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

instance : IsIso (Spec.map (quotResidueIso A).hom) :=
  ⟨Spec.map (quotResidueIso A).inv, by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id],
    by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]⟩

instance : IsIso (closedFibreToThickening A f) := by
  unfold closedFibreToThickening
  exact pullback.map_isIso (i₁ := 𝟙 X) (i₂ := Spec.map (quotResidueIso A).hom)
    (i₃ := 𝟙 (Spec (.of A))) ..

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Base change to the closed fibre is base change to the first thickening followed by an
equivalence. -/
noncomputable def pullbackClosedFibreIso :
    FiniteEtale.pullback (closedFibreι A f) ≅
      FiniteEtale.pullback (thickening.ι (A := .of A) f (maximalIdeal A) 0) ⋙
        FiniteEtale.pullback (closedFibreToThickening A f) :=
  (MorphismProperty.Over.pullbackCongr (closedFibreToThickening_ι A f)).symm ≪≫
    MorphismProperty.Over.pullbackComp _ _

instance : (FiniteEtale.pullback (closedFibreToThickening A f)).IsEquivalence :=
  finiteEtale_h83 _ inferInstance inferInstance

variable [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsProper f]

/-- IX.1.10, faithfulness, for every proper `X`: two morphisms of étale coverings of `X` which
agree on the closed fibre are equal. -/
theorem faithful_pullback_closedFibre : (FiniteEtale.pullback (closedFibreι A f)).Faithful := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹_›
  have : IsAdicComplete (maximalIdeal A) (CommRingCat.of A) := ‹_›
  have := faithful_pullback_thickening (A := .of A) (maximalIdeal A) f finiteEtale_h83
  exact Functor.Faithful.of_iso (pullbackClosedFibreIso A f).symm

/-- IX.1.10, fullness, for every proper `X`: every morphism between the restrictions to the closed
fibre of two étale coverings of `X` comes from a morphism of étale coverings. (SGA notes that
this half of IX.1.10 does not use the existence theorem.) -/
theorem full_pullback_closedFibre : (FiniteEtale.pullback (closedFibreι A f)).Full := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹_›
  have : IsAdicComplete (maximalIdeal A) (CommRingCat.of A) := ‹_›
  have := full_pullback_thickening (A := .of A) (maximalIdeal A) f finiteEtale_h83
  exact Functor.Full.of_iso (pullbackClosedFibreIso A f).symm

omit [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsProper f] in
/-- If base change to the first thickening `X ⊗_A A/𝔪 ⟶ X` is essentially surjective on étale
coverings, so is base change to the closed fibre. -/
theorem essSurj_pullback_closedFibre_of_essSurj
    (h : (FiniteEtale.pullback (thickening.ι (A := .of A) f (maximalIdeal A) 0)).EssSurj) :
    (FiniteEtale.pullback (closedFibreι A f)).EssSurj :=
  Functor.essSurj_of_iso (pullbackClosedFibreIso A f).symm

/-- IX.1.10, given the essential surjectivity along the first thickening. -/
theorem isEquivalence_pullback_closedFibre_of_essSurj
    (h : (FiniteEtale.pullback (thickening.ι (A := .of A) f (maximalIdeal A) 0)).EssSurj) :
    (FiniteEtale.pullback (closedFibreι A f)).IsEquivalence :=
  have := faithful_pullback_closedFibre A f
  have := full_pullback_closedFibre A f
  have := essSurj_pullback_closedFibre_of_essSurj A f h
  { }

end ClosedFibre

section Projective

open IsLocalRing CohomologyAux

set_option backward.isDefEq.respectTransparency false in
/-- **IX.1.10 for `X` projective over `A`** (and X.2.1): let `A` be a complete noetherian local
ring and `X` a closed subscheme of `ℙ(τ; Spec A)`, `τ` finite. Then base change to the closed
fibre `X₀ = X ⊗_A k` is an equivalence from the étale coverings of `X` to those of `X₀`. -/
theorem isEquivalence_pullback_closedFibre_of_isClosedImmersion (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}}
    {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec (.of A))) [IsClosedImmersion κ]
    (f : X ⟶ Spec (.of A)) (hf : f = κ ≫ ℙ(τ; Spec (.of A)) ↘ Spec (.of A)) :
    (MorphismProperty.Over.pullback etaleCovering ⊤ (closedFibreι A f)).IsEquivalence := by
  subst hf
  exact isEquivalence_pullback_closedFibre A κ finiteEtale_h83

/-- IX.1.10 holds for `X` projective over the complete noetherian local ring `A`. -/
theorem etaleCoveringsOfClosedFibre_of_isClosedImmersion (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A))
    (hproj : ∃ (τ : Type u) (_ : Finite τ) (κ : X ⟶ ℙ(τ; Spec (.of A))),
      IsClosedImmersion κ ∧ f = κ ≫ ℙ(τ; Spec (.of A)) ↘ Spec (.of A)) :
    (MorphismProperty.Over.pullback etaleCovering ⊤
      (pullback.fst f (Spec.map (CommRingCat.ofHom (residue A))))).IsEquivalence := by
  obtain ⟨τ, _, κ, _, hf⟩ := hproj
  exact isEquivalence_pullback_closedFibre_of_isClosedImmersion A κ f hf

end Projective

set_option backward.isDefEq.respectTransparency false in
/-- IX.1.10 follows from the essential surjectivity of base change along the first thickening
`X ⊗_A A/𝔪 ⟶ X` of a proper `X` over a complete noetherian local ring `A` (the part of IX.1.10
which uses Grothendieck's existence theorem; the full faithfulness is proved). -/
theorem etaleCoveringsOfClosedFibreStatement_of_essSurj
    (h : ∀ (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
      [IsAdicComplete (IsLocalRing.maximalIdeal A) A] (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
      [IsProper f], (FiniteEtale.pullback (AlgebraicGeometry.thickening.ι (A := .of A) f
        (IsLocalRing.maximalIdeal A) 0)).EssSurj) :
    EtaleCoveringsOfClosedFibreStatement.{u} := fun A _ _ _ _ X f _ ↦
  isEquivalence_pullback_closedFibre_of_essSurj A f (h A X f)

end SGA.SGA1.ExposeIX
