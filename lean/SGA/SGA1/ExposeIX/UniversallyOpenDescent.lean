/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.HenselianQuasiFinite
import SGA.SGA1.ExposeIX.QuasiFiniteDescent

/-!
# SGA 1, Exposé IX, 4.9: descent along universally open morphisms

IX.4.9: over a locally noetherian `S`, a surjective, universally open morphism of finite type
`g : S' ⟶ S` is an effective descent morphism for étale separated schemes of finite type.

SGA's proof reduces to `S = Spec A` with `A` a complete noetherian local ring, then to `A` a
domain (base change to the finite surjective `⊔ Spec A/𝔭ᵢ`, `𝔭ᵢ` the minimal primes), and uses
a *quasi-section*: an integral subscheme of `S'`, quasi-finite over `S` at a point of the closed
fibre and dominating `S` (EGA IV 14.3.13, 14.5.4). Over the henselian ring `A` it has an open
part which is finite, hence surjective, over `S`
(`exists_opens_forall_specializes_isFinite_of_quasiFiniteAt`); after base change to it `g` has a
section, and one concludes as in IX.4.8 by IX.4.7.

The existence of quasi-sections rests on the dimension theory of universally open morphisms
(EGA IV 14), which we do not have; it is recorded as `QuasiSectionStatement`, and IX.4.9 is
proved from it (`isEffectiveDescentMorphism_of_universallyOpen`, giving
`EffectiveDescentOfUniversallyOpenStatement`). All other steps of SGA's argument are formalized.
-/

universe u

open CategoryTheory Limits MorphismProperty IsLocalRing Topology

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

/-- (statement only) Quasi-sections of universally open morphisms (EGA IV 14.3.13, 14.5.4), in the
form used in the proof of IX.4.9: let `A` be a noetherian local domain and `g : X ⟶ Spec A`
universally open and locally of finite type, with nonempty closed fibre. There are an integral
scheme `Z` and a morphism `i : Z ⟶ X` such that `i ≫ g` is locally of finite type and dominant
and is quasi-finite at some point `z` of `Z` over the closed point. (In EGA, `Z` is an integral
subscheme of `X`.) -/
def QuasiSectionStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of A)) [UniversallyOpen g] [LocallyOfFiniteType g],
    (∃ x, g x = closedPoint A) →
      ∃ (Z : Scheme.{u}) (_ : IsIntegral Z) (i : Z ⟶ X) (z : Z), LocallyOfFiniteType (i ≫ g) ∧
        IsDominant (i ≫ g) ∧ (i ≫ g) z = closedPoint A ∧ (i ≫ g).QuasiFiniteAt z

variable (H : QuasiSectionStatement.{u})
include H

set_option backward.isDefEq.respectTransparency false in
/-- Proof of IX.4.9, over a henselian noetherian local domain `A`: granting quasi-sections, a
surjective universally open `g : X ⟶ Spec A` of finite type is dominated by a finite surjective
`T ⟶ Spec A` factoring through `X`. -/
theorem exists_isFinite_surjective_of_isDomain {A : Type u} [CommRing A] [IsDomain A]
    [HenselianLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}} (g : X ⟶ Spec (.of A))
    [UniversallyOpen g] [Surjective g] [LocallyOfFiniteType g] :
    ∃ (T : Scheme.{u}) (φ : T ⟶ X), IsFinite (φ ≫ g) ∧ Surjective (φ ≫ g) := by
  obtain ⟨x, hx⟩ := g.surjective (closedPoint A)
  obtain ⟨Z, _, i, z, _, _, hz, hqf⟩ := H A g ⟨x, hx⟩
  obtain ⟨W, hzW, -, hWfin⟩ :=
    exists_opens_forall_specializes_isFinite_of_quasiFiniteAt (i ≫ g) hz hqf
  have hfin : IsFinite ((W.ι ≫ i) ≫ g) := by rw [Category.assoc]; exact hWfin
  refine ⟨W, W.ι ≫ i, hfin, ⟨fun s ↦ ?_⟩⟩
  -- the image is closed and contains the image of the generic point of `Z`, which is dense
  have hξ : genericPoint Z ∈ W :=
    ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr ⟨z, trivial, hzW⟩
  have hdense : closure {(i ≫ g) (genericPoint Z)} = Set.univ := by
    refine Set.eq_univ_of_univ_subset ((i ≫ g).denseRange.closure_eq ▸ closure_minimal ?_
      isClosed_closure)
    rintro _ ⟨w, rfl⟩
    exact specializes_iff_mem_closure.mp
      (((genericPoint_spec Z).specializes trivial).map (i ≫ g).continuous)
  have hcl : IsClosed (Set.range ((W.ι ≫ i) ≫ g)) := ((W.ι ≫ i) ≫ g).isClosedMap.isClosed_range
  have hmem : (i ≫ g) (genericPoint Z) ∈ Set.range ((W.ι ≫ i) ≫ g) :=
    ⟨⟨genericPoint Z, hξ⟩, by simp⟩
  have := closure_minimal (Set.singleton_subset_iff.mpr hmem) hcl
  rw [hdense] at this
  exact this (Set.mem_univ s)

set_option backward.isDefEq.respectTransparency false in
/-- Proof of IX.4.9, over a henselian noetherian local ring `A` (reduction to the quotients by the
minimal primes): granting quasi-sections, a surjective universally open `g : X ⟶ Spec A` of finite
type is dominated by a finite surjective `T ⟶ Spec A` factoring through `X`. -/
theorem exists_isFinite_surjective_of_universallyOpen {A : Type u} [CommRing A]
    [HenselianLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}} (g : X ⟶ Spec (.of A))
    [UniversallyOpen g] [Surjective g] [LocallyOfFiniteType g] :
    ∃ (T : Scheme.{u}) (φ : T ⟶ X), IsFinite (φ ≫ g) ∧ Surjective (φ ≫ g) := by
  classical
  let P := ↥(minimalPrimes A)
  have : Finite P := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  have : Fintype P := Fintype.ofFinite P
  have hprime (p : P) : p.1.IsPrime := p.2.1.1
  let j (p : P) : Spec (.of (A ⧸ p.1)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.1))
  have hT (p : P) : ∃ (T : Scheme.{u}) (φ : T ⟶ pullback g (j p)),
      IsFinite (φ ≫ pullback.snd g (j p)) ∧ Surjective (φ ≫ pullback.snd g (j p)) := by
    have := hprime p
    have : Nontrivial (A ⧸ p.1) := Ideal.Quotient.nontrivial_iff.mpr this.ne_top
    have : HenselianLocalRing (A ⧸ p.1) :=
      HenselianLocalRing.of_surjective (Ideal.Quotient.mk p.1) Ideal.Quotient.mk_surjective
    have : UniversallyOpen (pullback.snd g (j p)) := MorphismProperty.pullback_snd _ _ ‹_›
    have : Surjective (pullback.snd g (j p)) := MorphismProperty.pullback_snd _ _ ‹_›
    exact exists_isFinite_surjective_of_isDomain H (pullback.snd g (j p))
  choose T φ hφf hφs using hT
  have hj (p : P) : IsFinite (j p) := by
    have : IsClosedImmersion (j p) :=
      IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  have hfin (p : P) : IsFinite ((φ p ≫ pullback.fst g (j p)) ≫ g) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    infer_instance
  obtain ⟨p₀, hp₀⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A))
    (J := maximalIdeal A) bot_le
  obtain ⟨T', φ', hφ', hsub⟩ := exists_isFinite_of_finset g T (fun p ↦ φ p ≫ pullback.fst g (j p))
    hfin Finset.univ ⟨⟨p₀, hp₀.1⟩, Finset.mem_univ _⟩
  refine ⟨T', φ', hφ', ⟨fun s ↦ ?_⟩⟩
  obtain ⟨p, hp, hps⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal A)) (J := s.asIdeal) bot_le
  have hrange : s ∈ Set.range (j ⟨p, hp⟩) := by
    have := range_comap_of_surjective (hf := Ideal.Quotient.mk_surjective (I := p))
    change s ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk p))
    rw [this, Ideal.mk_ker]
    exact hps
  obtain ⟨t, rfl⟩ := hrange
  have := hφs ⟨p, hp⟩
  obtain ⟨w, hw⟩ := (φ ⟨p, hp⟩ ≫ pullback.snd g (j ⟨p, hp⟩)).surjective t
  refine hsub ⟨p, hp⟩ (Finset.mem_univ _) ⟨w, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, Scheme.Hom.comp_apply, hw]

variable {S' X' : Scheme.{u}} in
set_option backward.isDefEq.respectTransparency false in
/-- IX.4.9 over a henselian noetherian local base, granting quasi-sections: the datum becomes
effective after base change to a finite surjective `T ⟶ Spec A` factoring through `S'` (where
`g` has a section), and one concludes by IX.4.7 and the sorites of descent, as in IX.4.8. -/
theorem DescentDatum.isEffective_of_universallyOpen_of_henselianLocalRing {A : Type u}
    [CommRing A] [HenselianLocalRing A] [IsNoetherianRing A] {g : S' ⟶ Spec (.of A)}
    [UniversallyOpen g] [Surjective g] [LocallyOfFiniteType g] {a : X' ⟶ S'}
    (D : DescentDatum g a) (ha : etaleSeparatedFiniteType a) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨T, φ, _, _⟩ := exists_isFinite_surjective_of_universallyOpen H g
  have hsec : pullback.lift φ (𝟙 T) (by simp) ≫ pullback.snd g (φ ≫ g) = 𝟙 T :=
    pullback.lift_snd _ _ _
  have hT := (D.baseChange (φ ≫ g)).isEffective_of_section hsec etaleSeparatedFiniteType
    (MorphismProperty.pullback_snd _ _ ha)
  exact D.isEffective_of_isEffective_baseChange (φ ≫ g) isEffectiveDescentMorphism_of_isFinite
    ha hT

variable {S' S : Scheme.{u}} in
set_option backward.isDefEq.respectTransparency false in
/-- IX.4.9, granting quasi-sections (`QuasiSectionStatement`, EGA IV 14.5.4): over a locally
noetherian `S`, a surjective universally open morphism of finite type is an effective descent
morphism for étale separated schemes of finite type. -/
theorem isEffectiveDescentMorphism_of_universallyOpen [IsLocallyNoetherian S] (g : S' ⟶ S)
    [LocallyOfFiniteType g] [QuasiCompact g] [Surjective g] [UniversallyOpen g] :
    IsEffectiveDescentMorphism g etaleSeparatedFiniteType := by
  refine ⟨isDescentMorphism_of_universallyOpen (g := g), fun X' a D ha ↦ ?_⟩
  have := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := ha
  have : Etale a := h₁
  have : IsSeparated a := h₂
  have : QuasiCompact a := h₃
  have ha' : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecCompletedStalk ha']
    intro x
    let Â := AdicCompletion (maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x)
    have : HenselianLocalRing Â := HenselianLocalRing.of_henselianRing Â
    have : UniversallyOpen (pullback.snd g (fromSpecCompletedStalk S x)) :=
      MorphismProperty.pullback_snd _ _ ‹_›
    exact (DescentDatum.isEffective_of_universallyOpen_of_henselianLocalRing H
      (D.baseChange (fromSpecCompletedStalk S x))
      (MorphismProperty.pullback_snd _ _ ⟨⟨h₁, h₂⟩, h₃⟩)).of_le fun _ _ f h ↦
        have : IsSeparated f := h.1.2; ⟨⟨h.1.1, h.2⟩, inferInstance⟩
  exact D.isEffective_etaleSeparatedFiniteType_of_etale ⟨⟨h₁, h₂⟩, h₃⟩
    (hfp.of_le fun _ _ _ h ↦ h.1.1)

/-- IX.4.9 (`EffectiveDescentOfUniversallyOpenStatement`), granting quasi-sections. -/
theorem effectiveDescentOfUniversallyOpen : EffectiveDescentOfUniversallyOpenStatement.{u} :=
  fun _ _ g _ _ _ _ _ ↦ isEffectiveDescentMorphism_of_universallyOpen H g

end SGA.SGA1.ExposeIX
