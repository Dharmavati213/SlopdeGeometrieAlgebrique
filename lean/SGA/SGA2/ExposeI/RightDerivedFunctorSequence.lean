/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSections
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Right-derived sequences from exactness on injectives

A short complex of additive functors, short exact on injective objects,
gives a genuine long exact sequence of its actual right-derived functors.
The connecting maps come from the short exact sequence of complexes on an
actual injective resolution. Their naturality is proved using resolution
lifts and naturality of the genuine homology connecting maps.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]

/-- The actual sequence of complexes obtained by applying three additive
functors and the given natural transformations degreewise. -/
def functorSequenceComplex (S : ShortComplex (C ⥤ D))
    [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    (K : CochainComplex C ℕ) : ShortComplex (CochainComplex D ℕ) :=
  ShortComplex.mk ((S.f.mapHomologicalComplex _).app K)
    ((S.g.mapHomologicalComplex _).app K) (by
      ext n
      exact congrArg (fun α => α.app (K.X n)) S.zero)

/-- A genuine map of coefficient complexes gives a map of the actual
three-term sequences. -/
def functorSequenceComplexMap (S : ShortComplex (C ⥤ D))
    [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
    {K L : CochainComplex C ℕ} (φ : K ⟶ L) :
    functorSequenceComplex S K ⟶ functorSequenceComplex S L where
  τ₁ := (S.X₁.mapHomologicalComplex _).map φ
  τ₂ := (S.X₂.mapHomologicalComplex _).map φ
  τ₃ := (S.X₃.mapHomologicalComplex _).map φ
  comm₁₂ := (S.f.mapHomologicalComplex _).naturality φ
  comm₂₃ := (S.g.mapHomologicalComplex _).naturality φ

variable (S : ShortComplex (C ⥤ D))
  [S.X₁.Additive] [S.X₂.Additive] [S.X₃.Additive]
  (hS : ∀ (I : C) [Injective I], (S.map ((evaluation C D).obj I)).ShortExact)

include hS in
/-- Exactness on injective objects proves actual short exactness of the
sequence on any injective resolution; it is not supplied as an assumption. -/
theorem functorSequenceComplex_shortExact {X : C} (I : InjectiveResolution X) :
    (functorSequenceComplex S I.cocomplex).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  exact hS (I.cocomplex.X n)

/-- Actual connecting morphism on a chosen resolution. -/
def functorSequenceResolutionBoundary {X : C} (I : InjectiveResolution X) (n : ℕ) :
    ((S.X₃.mapHomologicalComplex _).obj I.cocomplex).homology n ⟶
      ((S.X₁.mapHomologicalComplex _).obj I.cocomplex).homology (n + 1) :=
  (functorSequenceComplex_shortExact S hS I).δ n (n + 1) (by simp)

/-- Naturality of the actual resolution connecting maps for every genuine
chain map, without any additional comparison hypothesis. -/
@[reassoc]
theorem functorSequenceResolutionBoundary_naturality
    {X Y : C} (I : InjectiveResolution X) (J : InjectiveResolution Y)
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℕ) :
    functorSequenceResolutionBoundary S hS I n ≫
        homologyMap ((S.X₁.mapHomologicalComplex _).map φ) (n + 1) =
      homologyMap ((S.X₃.mapHomologicalComplex _).map φ) n ≫
        functorSequenceResolutionBoundary S hS J n :=
  HomologicalComplex.HomologySequence.δ_naturality (functorSequenceComplexMap S φ)
    (functorSequenceComplex_shortExact S hS I)
    (functorSequenceComplex_shortExact S hS J) n (n + 1) (by simp)

variable [HasInjectiveResolutions C]

/-- The connecting map between actual right-derived objects, constructed
using their original injective-resolution comparisons. -/
def rightDerivedFunctorBoundaryObj (X : C) (n : ℕ) :
    (S.X₃.rightDerived n).obj X ⟶ (S.X₁.rightDerived (n + 1)).obj X :=
  ((injectiveResolution X).isoRightDerivedObj S.X₃ n).hom ≫
    functorSequenceResolutionBoundary S hS (injectiveResolution X) n ≫
      ((injectiveResolution X).isoRightDerivedObj S.X₁ (n + 1)).inv

/-- The constructed connecting morphism is genuinely natural in coefficients. -/
@[reassoc]
theorem rightDerivedFunctorBoundaryObj_naturality {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (S.X₃.rightDerived n).map f ≫ rightDerivedFunctorBoundaryObj S hS Y n =
      rightDerivedFunctorBoundaryObj S hS X n ≫ (S.X₁.rightDerived (n + 1)).map f := by
  let I := injectiveResolution X
  let J := injectiveResolution Y
  let φ := InjectiveResolution.desc f J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f J I
  simp only [rightDerivedFunctorBoundaryObj, Category.assoc]
  rw [← Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ S.X₃ n,
    Category.assoc]
  erw [← functorSequenceResolutionBoundary_naturality_assoc S hS I J φ n]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ S.X₁ (n + 1)]

/-- The genuine connecting natural transformation between the original
right-derived functors. -/
def rightDerivedFunctorBoundary (n : ℕ) :
    S.X₃.rightDerived n ⟶ S.X₁.rightDerived (n + 1) where
  app X := rightDerivedFunctorBoundaryObj S hS X n
  naturality _ _ f := rightDerivedFunctorBoundaryObj_naturality S hS f n

variable {S hS}

/-- The actual right-derived map of a natural transformation, normalized
against the original homology comparison on a chosen injective resolution. -/
@[reassoc]
theorem rightDerived_natTrans_comp_resolutionIso
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {X : C} (I : InjectiveResolution X) (n : ℕ) :
    (α.rightDerived n).app X ≫ (I.isoRightDerivedObj G n).hom =
      (I.isoRightDerivedObj F n).hom ≫
        homologyMap ((α.mapHomologicalComplex _).app I.cocomplex) n := by
  rw [InjectiveResolution.rightDerived_app_eq α I n]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

variable (S hS)

/-- The connecting morphism is the genuine homology boundary after the
original chosen-resolution comparison. -/
@[reassoc]
theorem rightDerivedFunctorBoundary_comp_resolutionIso (X : C) (n : ℕ) :
    (rightDerivedFunctorBoundary S hS n).app X ≫
        ((injectiveResolution X).isoRightDerivedObj S.X₁ (n + 1)).hom =
      ((injectiveResolution X).isoRightDerivedObj S.X₃ n).hom ≫
        functorSequenceResolutionBoundary S hS (injectiveResolution X) n := by
  simp only [rightDerivedFunctorBoundary, rightDerivedFunctorBoundaryObj,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

include hS in
/-- Exactness at the second actual right-derived functor in every degree. -/
theorem rightDerivedFunctorSequence_exact₂ (X : C) (n : ℕ) :
    (ComposableArrows.mk₂ ((S.f.rightDerived n).app X)
      ((S.g.rightDerived n).app X)).Exact := by
  let I := injectiveResolution X
  let T := functorSequenceComplex S I.cocomplex
  have h := (functorSequenceComplex_shortExact S hS I).homology_exact₂ n
  let e := ComposableArrows.isoMk₂ (f := ComposableArrows.mk₂
      ((S.f.rightDerived n).app X) ((S.g.rightDerived n).app X))
    (g := ComposableArrows.mk₂ (homologyMap T.f n) (homologyMap T.g n))
    (I.isoRightDerivedObj S.X₁ n) (I.isoRightDerivedObj S.X₂ n)
    (I.isoRightDerivedObj S.X₃ n)
    (rightDerived_natTrans_comp_resolutionIso S.f I n)
    (rightDerived_natTrans_comp_resolutionIso S.g I n)
  exact (ComposableArrows.exact_iff_of_iso e).mpr h.exact_toComposableArrows

/-- Exactness at the third actual right-derived functor. -/
theorem rightDerivedFunctorSequence_exact₃ (X : C) (n : ℕ) :
    (ComposableArrows.mk₂ ((S.g.rightDerived n).app X)
      ((rightDerivedFunctorBoundary S hS n).app X)).Exact := by
  let I := injectiveResolution X
  let T := functorSequenceComplex S I.cocomplex
  have h := (functorSequenceComplex_shortExact S hS I).homology_exact₃ n (n + 1) (by simp)
  let e := ComposableArrows.isoMk₂ (f := ComposableArrows.mk₂
      ((S.g.rightDerived n).app X) ((rightDerivedFunctorBoundary S hS n).app X))
    (g := ComposableArrows.mk₂ (homologyMap T.g n)
      (functorSequenceResolutionBoundary S hS I n))
    (I.isoRightDerivedObj S.X₂ n) (I.isoRightDerivedObj S.X₃ n)
    (I.isoRightDerivedObj S.X₁ (n + 1))
    (rightDerived_natTrans_comp_resolutionIso S.g I n)
    (rightDerivedFunctorBoundary_comp_resolutionIso S hS X n)
  exact (ComposableArrows.exact_iff_of_iso e).mpr h.exact_toComposableArrows

/-- Exactness at the next-degree first actual right-derived functor. -/
theorem rightDerivedFunctorSequence_exact₁ (X : C) (n : ℕ) :
    (ComposableArrows.mk₂ ((rightDerivedFunctorBoundary S hS n).app X)
      ((S.f.rightDerived (n + 1)).app X)).Exact := by
  let I := injectiveResolution X
  let T := functorSequenceComplex S I.cocomplex
  have h := (functorSequenceComplex_shortExact S hS I).homology_exact₁ n (n + 1) (by simp)
  let e := ComposableArrows.isoMk₂ (f := ComposableArrows.mk₂
      ((rightDerivedFunctorBoundary S hS n).app X) ((S.f.rightDerived (n + 1)).app X))
    (g := ComposableArrows.mk₂ (functorSequenceResolutionBoundary S hS I n)
      (homologyMap T.f (n + 1)))
    (I.isoRightDerivedObj S.X₃ n) (I.isoRightDerivedObj S.X₁ (n + 1))
    (I.isoRightDerivedObj S.X₂ (n + 1))
    (rightDerivedFunctorBoundary_comp_resolutionIso S hS X n)
    (rightDerived_natTrans_comp_resolutionIso S.f I (n + 1))
  exact (ComposableArrows.exact_iff_of_iso e).mpr h.exact_toComposableArrows

/-- Six consecutive terms of the actual long exact right-derived sequence. -/
def rightDerivedFunctorSequence (X : C) (n : ℕ) : ComposableArrows D 5 :=
  ComposableArrows.mk₅ ((S.f.rightDerived n).app X) ((S.g.rightDerived n).app X)
    ((rightDerivedFunctorBoundary S hS n).app X)
    ((S.f.rightDerived (n + 1)).app X) ((S.g.rightDerived (n + 1)).app X)

/-- Exactness of every six-term segment, using the actual derived maps
and the constructed natural connecting transformation. -/
theorem rightDerivedFunctorSequence_exact (X : C) (n : ℕ) :
    (rightDerivedFunctorSequence S hS X n).Exact :=
  ComposableArrows.exact_of_δ₀ (rightDerivedFunctorSequence_exact₂ S hS X n)
    (ComposableArrows.exact_of_δ₀ (rightDerivedFunctorSequence_exact₃ S hS X n)
      (ComposableArrows.exact_of_δ₀ (rightDerivedFunctorSequence_exact₁ S hS X n)
        (rightDerivedFunctorSequence_exact₂ S hS X (n + 1))))

include hS in
/-- The sequence starts with a monomorphism in degree zero. Exactness on
injectives suffices; no extra left-exactness hypothesis is needed here. -/
theorem rightDerivedFunctorSequence_zero_mono (X : C) :
    Mono ((S.f.rightDerived 0).app X) := by
  let I := injectiveResolution X
  let T := functorSequenceComplex S I.cocomplex
  have : Mono (T.f.f 0) := (hS (I.cocomplex.X 0)).mono_f
  have : Mono (homologyMap T.f 0) :=
    HomologicalComplex.mono_homologyMap_of_mono_of_not_rel T.f 0 (by intro i; simp)
  have hm : Mono ((S.f.rightDerived 0).app X ≫ (I.isoRightDerivedObj S.X₂ 0).hom) := by
    rw [rightDerived_natTrans_comp_resolutionIso]
    exact inferInstanceAs (Mono ((I.isoRightDerivedObj S.X₁ 0).hom ≫ homologyMap T.f 0))
  exact mono_of_mono _ (I.isoRightDerivedObj S.X₂ 0).hom

end SGA.SGA2.ExposeI
