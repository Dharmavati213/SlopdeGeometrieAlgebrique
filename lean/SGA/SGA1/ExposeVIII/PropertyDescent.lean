/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Finiteness.Descent

/-!
# SGA 1, Exposé VIII, §3: descent of set-theoretic and finiteness properties

SGA considers an `S`-morphism `f : X ⟶ Y`, a change of base `g : S' ⟶ S`, and the
base change `f' : X ×_S S' ⟶ Y ×_S S'`, and asks when a property of `f'` implies it for
`f`. As SGA notes, `f'` is also the base change of `f` along `Y ×_S S' ⟶ Y`, so it is enough
to treat `S = Y`; this is mathlib's `MorphismProperty.DescendsAlong`. The lemma
`of_pullback_map_of_descendsAlong` turns such an instance back into the statement over `S`.

* VIII.3.1: surjective and radicial (`UniversallyInjective`) morphisms descend along surjective
  morphisms.
* VIII.3.2: injective and bijective maps descend along surjective morphisms.
* VIII.3.3: quasi-compact morphisms descend along surjective quasi-compact morphisms; morphisms of
  finite type descend along faithfully flat quasi-compact morphisms (mathlib does
  `LocallyOfFiniteType`).
* VIII.3.4 is mathlib's `Algebra.FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`.
* VIII.3.5: quasi-finite morphisms (of finite type with finite fibers) descend.
* VIII.3.6: morphisms of finite presentation (locally of finite presentation, quasi-compact,
  quasi-separated) descend. For affine `X`, the equivalence of (i) and finite presentation
  (every algebra of finite presentation comes from an algebra of finite type over a noetherian
  ring) is proved; the equivalence (i) ⇔ (ii) for non-affine `X` is not formalized.

Faithfully flat quasi-compact is written `@Surjective ⊓ @Flat ⊓ @QuasiCompact`, as in mathlib.
-/

universe u

namespace SGA.SGA1.ExposeVIII

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MorphismProperty TensorProduct

variable {X Y S S' : Scheme.{u}}

section General

set_option backward.isDefEq.respectTransparency.types false in
/-- The base change `f' : X ×_S S' ⟶ Y ×_S S'` of an `S`-morphism `f : X ⟶ Y` is the
base change of `f` along `Y ×_S S' ⟶ Y`. -/
theorem isPullback_pullback_map (f : X ⟶ Y) (p : Y ⟶ S) (g : S' ⟶ S) :
    IsPullback (pullback.map (f ≫ p) g p g f (𝟙 S') (𝟙 S) (by simp) (by simp))
      (pullback.fst (f ≫ p) g) (pullback.fst p g) f := by
  refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback p g).flip
  rw [pullback.lift_snd, Category.comp_id]
  exact (IsPullback.of_hasPullback (f ≫ p) g).flip

/-- The form in which SGA states descent results: if `P` descends along `Q` and
`g : S' ⟶ S` satisfies `Q`, then for an `S`-morphism `f : X ⟶ Y`, `P` holds for `f` as soon
as it holds for the base change `f' : X ×_S S' ⟶ Y ×_S S'`. -/
theorem of_pullback_map_of_descendsAlong {P Q : MorphismProperty Scheme.{u}} [P.DescendsAlong Q]
    [Q.IsStableUnderBaseChange] (f : X ⟶ Y) (p : Y ⟶ S) {g : S' ⟶ S} (hg : Q g)
    (h : P (pullback.map (f ≫ p) g p g f (𝟙 S') (𝟙 S) (by simp) (by simp))) : P f :=
  of_isPullback_of_descendsAlong (isPullback_pullback_map f p g) (Q.pullback_fst _ _ hg) h

/-- The `iff` form of `of_pullback_map_of_descendsAlong` for properties stable under base
change. -/
theorem pullback_map_iff_of_descendsAlong {P Q : MorphismProperty Scheme.{u}}
    [P.DescendsAlong Q] [P.IsStableUnderBaseChange] [Q.IsStableUnderBaseChange]
    (f : X ⟶ Y) (p : Y ⟶ S) {g : S' ⟶ S} (hg : Q g) :
    P (pullback.map (f ≫ p) g p g f (𝟙 S') (𝟙 S) (by simp) (by simp)) ↔ P f :=
  iff_of_isPullback (isPullback_pullback_map f p g) (Q.pullback_fst _ _ hg)

end General

section SetTheoretic

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.3.1 (surjective): surjectivity descends along surjective morphisms. -/
instance surjective_descendsAlong_surjective : DescendsAlong @Surjective @Surjective where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := ⟨fun z ↦ by
    obtain ⟨x, rfl⟩ := hf.surj z
    obtain ⟨a, rfl⟩ := hfst.surj x
    exact ⟨snd a, by rw [← Scheme.Hom.comp_apply, ← h.w, Scheme.Hom.comp_apply]⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.3.1 (radicial): radicial (universally injective) morphisms descend along surjective
morphisms. Radicial means that the diagonal is surjective, which reduces this to the surjective
case. -/
instance universallyInjective_descendsAlong_surjective :
    DescendsAlong @UniversallyInjective @Surjective := by
  rw [universallyInjective_eq_diagonal]
  infer_instance

/-- VIII.3.1: for a surjective change of base `g : S' ⟶ S` and an `S`-morphism `f`, `f` is
surjective if and only if `f' : X ×_S S' ⟶ Y ×_S S'` is. -/
theorem surjective_pullback_map_iff (f : X ⟶ Y) (p : Y ⟶ S) (g : S' ⟶ S) [Surjective g] :
    Surjective (pullback.map (f ≫ p) g p g f (𝟙 S') (𝟙 S) (by simp) (by simp)) ↔
      Surjective f :=
  pullback_map_iff_of_descendsAlong (P := @Surjective) (Q := @Surjective) f p ‹_›

/-- VIII.3.1: for a surjective change of base `g : S' ⟶ S` and an `S`-morphism `f`, `f` is
radicial if and only if `f' : X ×_S S' ⟶ Y ×_S S'` is. -/
theorem universallyInjective_pullback_map_iff (f : X ⟶ Y) (p : Y ⟶ S) (g : S' ⟶ S)
    [Surjective g] :
    UniversallyInjective (pullback.map (f ≫ p) g p g f (𝟙 S') (𝟙 S) (by simp) (by simp)) ↔
      UniversallyInjective f :=
  pullback_map_iff_of_descendsAlong (P := @UniversallyInjective) (Q := @Surjective) f p ‹_›

variable {A Z : Scheme.{u}} {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}

/-- VIII.3.2 (injective): if `f` is surjective and the base change of `g` along `f` is
injective, then `g` is injective. -/
theorem injective_of_isPullback (h : IsPullback fst snd f g) [Surjective f]
    (hfst : Function.Injective fst) : Function.Injective g := by
  intro y₁ y₂ e
  obtain ⟨x, hx⟩ := f.surjective (g y₁)
  obtain ⟨a₁, ha₁, rfl⟩ := Scheme.exists_preimage_of_isPullback h x y₁ hx
  obtain ⟨a₂, ha₂, rfl⟩ := Scheme.exists_preimage_of_isPullback h x y₂ (hx.trans e)
  rw [hfst (ha₁.trans ha₂.symm)]

/-- VIII.3.2 (bijective): if `f` is surjective and the base change of `g` along `f` is
bijective, then `g` is bijective. -/
theorem bijective_of_isPullback (h : IsPullback fst snd f g) [Surjective f]
    (hfst : Function.Bijective fst) : Function.Bijective g :=
  ⟨injective_of_isPullback h hfst.1,
    (of_isPullback_of_descendsAlong (P := @Surjective) (Q := @Surjective) h ‹_›
      ⟨hfst.2⟩).surj⟩

/-- VIII.3.5, the fiber part: if `f` is surjective and the fibers of the base change of `g`
along `f` are finite, then the fibers of `g` are finite. Only the surjectivity of `f` is used. -/
theorem finite_preimage_singleton_of_isPullback (h : IsPullback fst snd f g) [Surjective f]
    (hfst : ∀ x, (fst ⁻¹' {x}).Finite) (z : Z) : (g ⁻¹' {z}).Finite := by
  obtain ⟨x, hx⟩ := f.surjective z
  refine ((hfst x).image snd).subset fun y (hy : g y = z) ↦ ?_
  obtain ⟨a, ha, rfl⟩ := Scheme.exists_preimage_of_isPullback h x y (hx.trans hy.symm)
  exact ⟨a, ha, rfl⟩

end SetTheoretic

section Finiteness

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.3.3 (quasi-compact): quasi-compact morphisms descend along surjective quasi-compact
morphisms. If `X ×_Z Y ⟶ X ⟶ Z` is quasi-compact, the inverse image in `Y` of a quasi-compact
open of `Z` is the image of a quasi-compact set under the surjection `X ×_Z Y ⟶ Y`. -/
instance quasiCompact_descendsAlong_surjective_inf_quasiCompact :
    DescendsAlong @QuasiCompact (@Surjective ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have : Surjective f := hf.1
    have : QuasiCompact f := hf.2
    have : QuasiCompact fst := hfst
    have : Surjective snd := MorphismProperty.of_isPullback h ‹_›
    refine ⟨fun U hU hU' ↦ ?_⟩
    have hA : IsCompact ((fst ≫ f) ⁻¹' U) := QuasiCompact.isCompact_preimage _ hU hU'
    have e : snd '' ((fst ≫ f) ⁻¹' U) = g ⁻¹' U := by
      rw [h.w, Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp,
        Set.image_preimage_eq _ snd.surjective]
    exact e ▸ hA.image snd.continuous

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.3.3 (quasi-compact): quasi-compact morphisms descend along faithfully flat
quasi-compact morphisms. -/
instance quasiCompact_descendsAlong_fpqc :
    DescendsAlong @QuasiCompact (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  .of_le (Q := @Surjective ⊓ @QuasiCompact) fun _ _ _ h ↦ ⟨h.1.1, h.2⟩

/-- VIII.3.3 (finite type): morphisms of finite type descend along faithfully flat
quasi-compact morphisms. -/
instance finiteType_descendsAlong_fpqc :
    DescendsAlong (@LocallyOfFiniteType ⊓ @QuasiCompact) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  DescendsAlong.inf

/-- VIII.3.4: a base change of an algebra along a faithfully flat ring map is of finite type
only if the algebra is. -/
theorem finiteType_of_finiteType_tensorProduct {R R' B : Type u} [CommRing R] [CommRing R']
    [CommRing B] [Algebra R R'] [Algebra R B] [Module.FaithfullyFlat R R']
    [Algebra.FiniteType R' (R' ⊗[R] B)] : Algebra.FiniteType R B :=
  .of_finiteType_tensorProduct_of_faithfullyFlat R'

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.3.5: quasi-finite morphisms (of finite type with finite fibers) descend along faithfully
flat quasi-compact morphisms. In mathlib's terms, for a morphism of finite type being
`LocallyQuasiFinite` is having finite fibers. -/
instance quasiFinite_descendsAlong_fpqc :
    DescendsAlong (@LocallyOfFiniteType ⊓ @QuasiCompact ⊓ @LocallyQuasiFinite)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    have hg : (@LocallyOfFiniteType ⊓ @QuasiCompact) g :=
      finiteType_descendsAlong_fpqc.of_isPullback h hf hfst.1
    have : LocallyOfFiniteType g := hg.1
    have : QuasiCompact g := hg.2
    have : Surjective f := hf.1.1
    have : LocallyOfFiniteType fst := hfst.1.1
    have : QuasiCompact fst := hfst.1.2
    have : LocallyQuasiFinite fst := hfst.2
    refine ⟨hg, (locallyQuasiFinite_iff_finite_preimage_singleton (f := g)).mpr ?_⟩
    exact finite_preimage_singleton_of_isPullback h fst.finite_preimage_singleton

/-- VIII.3.6, affine case: an `A`-algebra `B` is of finite presentation iff it is obtained by
base change from an algebra of finite type over a noetherian ring `A₀ ⟶ A`. The ring `A₀` can be
taken to be a subring of finite type of `A` (mathlib's `Algebra.Presentation.Core`). -/
theorem finitePresentation_iff_exists_noetherian {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] :
    Algebra.FinitePresentation A B ↔
      ∃ (A₀ : Type u) (_ : CommRing A₀) (_ : Algebra A₀ A) (B₀ : Type u) (_ : CommRing B₀)
        (_ : Algebra A₀ B₀), IsNoetherianRing A₀ ∧ Algebra.FiniteType A₀ B₀ ∧
          Nonempty (A ⊗[A₀] B₀ ≃ₐ[A] B) := by
  constructor
  · intro
    let P := Algebra.Presentation.ofFinitePresentation A B
    have : IsNoetherianRing P.Core := Algebra.FiniteType.isNoetherianRing ℤ _
    exact ⟨P.Core, inferInstance, inferInstance, P.ModelOfHasCoeffs P.Core, inferInstance,
      inferInstance, this, inferInstance, ⟨P.tensorModelOfHasCoeffsEquiv P.Core⟩⟩
  · rintro ⟨A₀, _, _, B₀, _, _, _, hB₀, ⟨e⟩⟩
    have : Algebra.FinitePresentation A₀ B₀ := Algebra.FinitePresentation.of_finiteType.mp hB₀
    exact .equiv e

set_option backward.isDefEq.respectTransparency.types false in
/-- VIII.3.6: quasi-separated morphisms descend along faithfully flat quasi-compact morphisms,
since the diagonal of a base change is a base change of the diagonal. -/
instance quasiSeparated_descendsAlong_fpqc :
    DescendsAlong @QuasiSeparated (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [quasiSeparated_eq_diagonal_is_quasiCompact]
  infer_instance

/-- VIII.3.6: morphisms of finite presentation (locally of finite presentation, quasi-compact
and quasi-separated) descend along faithfully flat quasi-compact morphisms. -/
instance finitePresentation_descendsAlong_fpqc :
    DescendsAlong (@LocallyOfFinitePresentation ⊓ @QuasiCompact ⊓ @QuasiSeparated)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  have : DescendsAlong (@LocallyOfFinitePresentation ⊓ @QuasiCompact)
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := DescendsAlong.inf
  DescendsAlong.inf

end Finiteness

end SGA.SGA1.ExposeVIII
