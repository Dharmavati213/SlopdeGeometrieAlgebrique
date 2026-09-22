/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionComplement
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# SGA 2, VI.1.9: the relative module Ext sequence

The original nested-support sequence is transported to closed-supported
Ext, ordinary Ext on the ambient module category, and ordinary Ext on the
open complement. The support maps and connecting maps retain their original
derived construction. Comparison of the positive-degree restriction with
`Ext.mapExactFunctor` is a separate compatibility statement.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- The full ambient support used in the specialization of VI.1.8. -/
abbrev moduleRelativeTotalSupport : ExposeI.LocallyClosedIn X :=
  ExposeI.LocallyClosedIn.ofOpenClosed ⊤ ⊤

@[simp]
theorem moduleRelativeTotalSupport_asSet :
    (moduleRelativeTotalSupport (X := X)).asSet = Set.univ := by
  simp [moduleRelativeTotalSupport, ExposeI.LocallyClosedIn.ofOpenClosed_asSet]

/-- A closed subset of the actual full support space. -/
def moduleRelativeClosedInTotal (Z : Closeds X) :
    Closeds (moduleRelativeTotalSupport (X := X)).asSet :=
  Z.preimage continuous_subtype_val

/-- The closed endpoint has exactly the prescribed ambient support. -/
theorem moduleRelativeClosedSupport_asSet (Z : Closeds X) :
    (ExposeI.nestedClosedSupportWitness moduleRelativeTotalSupport
      (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
        (moduleRelativeClosedInTotal Z))).asSet =
        (Z : Set X) := by
  rw [ExposeI.nestedClosedSubspace_support_asSet]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨x, by simp⟩, hx, rfl⟩

/-- The difference endpoint is the actual open complement of `Z`. -/
theorem moduleRelativeOpenSupport_asSet (Z : Closeds X) :
    (ExposeI.nestedDifferenceSupportWitness moduleRelativeTotalSupport
      (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
        (moduleRelativeClosedInTotal Z))).asSet =
        (Z.compl : Set X) := by
  rw [ExposeI.nestedDifferenceSupportWitness_asSet, moduleRelativeClosedSupport_asSet,
    moduleRelativeTotalSupport_asSet]
  ext x
  simp

@[simp]
theorem moduleRelativeTotalSupport_closedHull :
    (moduleRelativeTotalSupport (X := X)).closedHull = ⊤ := by
  apply Closeds.ext
  change closure (moduleRelativeTotalSupport (X := X)).asSet = Set.univ
  rw [moduleRelativeTotalSupport_asSet, closure_univ]

@[simp]
theorem moduleRelativeClosedSupport_closedHull (Z : Closeds X) :
    (ExposeI.nestedClosedSupportWitness moduleRelativeTotalSupport
      (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
        (moduleRelativeClosedInTotal Z))).closedHull = Z := by
  apply Closeds.ext
  change closure _ = (Z : Set X)
  rw [moduleRelativeClosedSupport_asSet, Z.isClosed.closure_eq]

variable (R : Sheaf RingCat.{u} X) (F : SheafOfModules.{u} R) (Z : Closeds X)

/-- The closed term is the original closed-supported module Ext functor. -/
def moduleRelativeExtClosedIso (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F
      (ExposeI.nestedClosedSupportWitness moduleRelativeTotalSupport
        (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
          (moduleRelativeClosedInTotal Z))) n ≅
      moduleSupportedExtFunctor R F Z n :=
  moduleLocallyClosedSupportedExtClosedIsoOfAsSet R F Z (moduleRelativeClosedSupport_asSet Z) n

/-- The full-space term is ordinary Ext in the ambient module category. -/
def moduleRelativeExtOrdinaryIso (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F moduleRelativeTotalSupport n ≅
      Abelian.extFunctorObj F n :=
  moduleLocallyClosedSupportedExtTopIso R F n

/-- The open term is ordinary Ext of the actual restricted module sheaves. -/
def moduleRelativeExtOpenIso (n : ℕ) :
    moduleLocallyClosedSupportedExtFunctor R F
      (ExposeI.nestedDifferenceSupportWitness moduleRelativeTotalSupport
        (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
          (moduleRelativeClosedInTotal Z))) n ≅
      moduleOpenRestriction R Z.compl ⋙ Abelian.extFunctorObj (F.over Z.compl) n :=
  moduleLocallyClosedSupportedExtOpenIsoOfAsSet R F Z.compl (moduleRelativeOpenSupport_asSet Z) n

/-- The original derived support-increasing map, with ordinary Ext as target. -/
def moduleRelativeExtSupportMap (n : ℕ) :
    moduleSupportedExtFunctor R F Z n ⟶ Abelian.extFunctorObj F n :=
  (moduleRelativeExtClosedIso R F Z n).inv ≫
    moduleNestedSupportedExtInclusion R F moduleRelativeTotalSupport
      (moduleRelativeClosedInTotal Z) n ≫
      (moduleRelativeExtOrdinaryIso R F n).hom

/-- The actual derived support-restriction map, expressed in ordinary Ext
on the ambient space and its open complement. -/
def moduleRelativeExtRestriction (n : ℕ) :
    Abelian.extFunctorObj F n ⟶
      moduleOpenRestriction R Z.compl ⋙ Abelian.extFunctorObj (F.over Z.compl) n :=
  (moduleRelativeExtOrdinaryIso R F n).inv ≫
    moduleNestedSupportedExtRestriction R F moduleRelativeTotalSupport
      (moduleRelativeClosedInTotal Z) n ≫
      (moduleRelativeExtOpenIso R F Z n).hom

/-- The original derived connecting map, with its open term expressed as Ext. -/
def moduleRelativeExtBoundary (n : ℕ) :
    moduleOpenRestriction R Z.compl ⋙ Abelian.extFunctorObj (F.over Z.compl) n ⟶
      moduleSupportedExtFunctor R F Z (n + 1) :=
  (moduleRelativeExtOpenIso R F Z n).inv ≫
    moduleNestedSupportedExtBoundary R F moduleRelativeTotalSupport
      (moduleRelativeClosedInTotal Z) n ≫
      (moduleRelativeExtClosedIso R F Z (n + 1)).hom

/-- Six consecutive actual Ext terms of VI.1.9. -/
def moduleRelativeExtSequence (G : SheafOfModules.{u} R) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅ ((moduleRelativeExtSupportMap R F Z n).app G)
    ((moduleRelativeExtRestriction R F Z n).app G)
    ((moduleRelativeExtBoundary R F Z n).app G)
    ((moduleRelativeExtSupportMap R F Z (n + 1)).app G)
    ((moduleRelativeExtRestriction R F Z (n + 1)).app G)

/-- The endpoint comparisons intertwine every original derived arrow. -/
def moduleRelativeExtSequenceIso (G : SheafOfModules.{u} R) (n : ℕ) :
    moduleNestedSupportedExtSequence R F moduleRelativeTotalSupport
      (moduleRelativeClosedInTotal Z) G n ≅ moduleRelativeExtSequence R F Z G n := by
  refine ComposableArrows.isoMk₅
    ((moduleRelativeExtClosedIso R F Z n).app G)
    ((moduleRelativeExtOrdinaryIso R F n).app G)
    ((moduleRelativeExtOpenIso R F Z n).app G)
    ((moduleRelativeExtClosedIso R F Z (n + 1)).app G)
    ((moduleRelativeExtOrdinaryIso R F (n + 1)).app G)
    ((moduleRelativeExtOpenIso R F Z (n + 1)).app G) ?_ ?_ ?_ ?_ ?_
  all_goals
    simp [moduleNestedSupportedExtSequence, moduleRelativeExtSequence,
      moduleRelativeExtSupportMap, moduleRelativeExtRestriction, moduleRelativeExtBoundary,
      ComposableArrows.Precomp.map]

/-- **VI.1.9:** the relative sequence of actual module Ext groups is exact. -/
theorem moduleRelativeExtSequence_exact (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleRelativeExtSequence R F Z G n).Exact :=
  ComposableArrows.exact_of_iso (moduleRelativeExtSequenceIso R F Z G n)
    (moduleNestedSupportedExtSequence_exact R F moduleRelativeTotalSupport
      (moduleRelativeClosedInTotal Z) G n)

/-- The relative sequence begins with an injection in degree zero. -/
theorem moduleRelativeExtSupportMap_zero_mono (G : SheafOfModules.{u} R) :
    Mono ((moduleRelativeExtSupportMap R F Z 0).app G) := by
  let := moduleNestedSupportedExtInclusion_zero_mono R F moduleRelativeTotalSupport
    (moduleRelativeClosedInTotal Z) G
  dsimp [moduleRelativeExtSupportMap]
  infer_instance

/-- The connecting maps commute with the actual coefficient morphisms. -/
@[reassoc]
theorem moduleRelativeExtBoundary_naturality {G H : SheafOfModules.{u} R}
    (a : G ⟶ H) (n : ℕ) :
    (moduleOpenRestriction R Z.compl ⋙ Abelian.extFunctorObj (F.over Z.compl) n).map a ≫
        (moduleRelativeExtBoundary R F Z n).app H =
      (moduleRelativeExtBoundary R F Z n).app G ≫
        (moduleSupportedExtFunctor R F Z (n + 1)).map a :=
  (moduleRelativeExtBoundary R F Z n).naturality a

/-- The actual restriction of module morphisms, as a natural transformation. -/
def moduleRelativeHomRestriction :
    preadditiveCoyoneda.obj (op F) ⟶
      moduleOpenRestriction R Z.compl ⋙ preadditiveCoyoneda.obj (op (F.over Z.compl)) where
  app G := AddCommGrpCat.ofHom
    { toFun f := f.over Z.compl
      map_zero' := rfl
      map_add' _ _ := rfl }
  naturality _ _ f := by ext g; rfl

private def moduleGammaRestrictionMap (B : Closeds X) {V V' : Opens X} (i : V' ⟶ V) :
    ExposeI.gammaZSectionsFunctor B V ⟶ ExposeI.gammaZSectionsFunctor B V' where
  app A := AddCommGrpCat.ofHom (ExposeI.gammaZSectionsRestriction A B i)
  naturality A A' f := by
    ext s
    apply Subtype.ext
    exact (f.hom.naturality_apply i.op s.val).symm

/-- The concrete full-support section restriction to the open complement. -/
def moduleRelativeGammaRestriction :
    ExposeI.gammaZSectionsFunctor (⊤ : Closeds X) ⊤ ⟶
      ExposeI.gammaZSectionsFunctor (⊤ : Closeds X) Z.compl :=
  moduleGammaRestrictionMap ⊤ (homOfLE le_top)

private theorem moduleGammaRestrictionMap_congr
    (B : Closeds X) (V V' : Opens X) (i : V' ⟶ V)
    (hB : B = ⊤) (hV : V = ⊤) (hV' : V' = Z.compl) :
    moduleGammaRestrictionMap B i ≫
        (eqToIso (show ExposeI.gammaZSectionsFunctor B V' =
          ExposeI.gammaZSectionsFunctor ⊤ Z.compl by rw [hB, hV'])).hom =
      (eqToIso (show ExposeI.gammaZSectionsFunctor B V =
          ExposeI.gammaZSectionsFunctor ⊤ ⊤ by rw [hB, hV])).hom ≫
        moduleRelativeGammaRestriction Z := by
  subst B V V'
  rfl

/-- Ambient coordinates for the full-support Hom term. -/
def moduleRelativeHomMiddleCoordinates :
    moduleLocallyClosedSupportedHomFunctor R F moduleRelativeTotalSupport ≅
      moduleSupportedHomFunctor R F (⊤ : Closeds X) :=
  moduleLocallyClosedSupportedHomGammaIso R F moduleRelativeTotalSupport ≪≫
    Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.nestedGammaMiddleIso moduleRelativeTotalSupport ≪≫
        eqToIso (by rw [moduleRelativeTotalSupport_closedHull]; rfl))

/-- Ambient coordinates for the complementary-support Hom term. -/
def moduleRelativeHomRightCoordinates :
    moduleLocallyClosedSupportedHomFunctor R F
      (ExposeI.nestedDifferenceSupportWitness moduleRelativeTotalSupport
        (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport (moduleRelativeClosedInTotal Z))) ≅
      moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F ⋙
        ExposeI.gammaZSectionsFunctor (⊤ : Closeds X) Z.compl :=
  moduleLocallyClosedSupportedHomGammaIso R F _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
      (ExposeI.nestedGammaRightIso moduleRelativeTotalSupport
        (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport (moduleRelativeClosedInTotal Z)) ≪≫
      eqToIso (by rw [moduleRelativeTotalSupport_closedHull, moduleRelativeClosedSupport_closedHull]
                  change ExposeI.gammaZSectionsFunctor ⊤ (⊤ ⊓ Z.compl) = _
                  rw [top_inf_eq]))

/-- The original support restriction becomes the actual section restriction
under the proved ambient coordinate comparisons. -/
theorem moduleRelativeHom_coordinates_restriction :
    moduleNestedSupportedHomRestriction R F moduleRelativeTotalSupport
        (moduleRelativeClosedInTotal Z) ≫
        (moduleRelativeHomRightCoordinates R F Z).hom =
      (moduleRelativeHomMiddleCoordinates R F).hom ≫
        Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
          (moduleRelativeGammaRestriction Z) := by
  have h :
      moduleNestedSupportedHomRestriction R F moduleRelativeTotalSupport
          (moduleRelativeClosedInTotal Z) ≫
        (moduleLocallyClosedSupportedHomGammaIso R F _ ≪≫
          Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
            (ExposeI.nestedGammaRightIso moduleRelativeTotalSupport
              (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
                (moduleRelativeClosedInTotal Z)))).hom =
      (moduleLocallyClosedSupportedHomGammaIso R F moduleRelativeTotalSupport ≪≫
        Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
          (ExposeI.nestedGammaMiddleIso moduleRelativeTotalSupport)).hom ≫
        Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
          (ExposeI.nestedSupportRestriction
            (ExposeI.nestedClosedSupportWitness moduleRelativeTotalSupport
              (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
                (moduleRelativeClosedInTotal Z))).closedHull
            (moduleRelativeTotalSupport (X := X)).closedHull ⊤) := by
    apply NatTrans.ext
    funext G
    simp [moduleNestedSupportedHomRestriction, ExposeI.locallyClosedNestedGammaRestriction,
      Category.assoc]
    rfl
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, ← Category.assoc] at h
  dsimp only [moduleRelativeHomMiddleCoordinates, moduleRelativeHomRightCoordinates,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  rw [Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc]
  erw [h]
  have hc := moduleGammaRestrictionMap_congr Z (moduleRelativeTotalSupport (X := X)).closedHull ⊤
    (⊤ ⊓ (ExposeI.nestedClosedSupportWitness moduleRelativeTotalSupport
      (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport
        (moduleRelativeClosedInTotal Z))).closedHull.compl)
    (homOfLE inf_le_left) moduleRelativeTotalSupport_closedHull rfl
    (by rw [moduleRelativeClosedSupport_closedHull]; exact top_inf_eq _)
  have hw := congrArg
    (Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)) hc
  simp only [Functor.whiskerLeft_comp] at hw
  simpa only [Category.assoc, moduleGammaRestrictionMap, ExposeI.nestedSupportRestriction,
    ExposeI.nestedSupportSectionsRestriction] using congrArg
    (fun k => (moduleLocallyClosedSupportedHomGammaIso R F moduleRelativeTotalSupport).hom ≫
      Functor.whiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
        (ExposeI.nestedGammaMiddleIso moduleRelativeTotalSupport).hom ≫ k) hw

/-- The full-support original Hom term is the actual ambient module Hom. -/
def moduleRelativeHomOrdinaryIso :
    moduleLocallyClosedSupportedHomFunctor R F moduleRelativeTotalSupport ≅
      preadditiveCoyoneda.obj (op F) :=
  moduleRelativeHomMiddleCoordinates R F ≪≫ moduleSupportedHomTopIso R F

/-- The complementary-support original Hom term is Hom of actual open restrictions. -/
def moduleRelativeHomOpenIso :
    moduleLocallyClosedSupportedHomFunctor R F
      (ExposeI.nestedDifferenceSupportWitness moduleRelativeTotalSupport
        (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport (moduleRelativeClosedInTotal Z))) ≅
      moduleOpenRestriction R Z.compl ⋙ preadditiveCoyoneda.obj (op (F.over Z.compl)) :=
  moduleRelativeHomRightCoordinates R F Z ≪≫ moduleFullSupportHomSectionsIso R F Z.compl ≪≫
    moduleHomSectionsRestrictionIso R F Z.compl

/-- The original degree-zero support restriction is exactly restriction
of the actual module morphism to the open complement. -/
theorem moduleRelativeHomRestriction_original :
    moduleNestedSupportedHomRestriction R F moduleRelativeTotalSupport
        (moduleRelativeClosedInTotal Z) ≫
        (moduleRelativeHomOpenIso R F Z).hom =
      (moduleRelativeHomOrdinaryIso R F).hom ≫ moduleRelativeHomRestriction R F Z := by
  dsimp only [moduleRelativeHomOpenIso, moduleRelativeHomOrdinaryIso, Iso.trans_hom]
  rw [← Category.assoc, ← Category.assoc, moduleRelativeHom_coordinates_restriction]
  simp only [Category.assoc]
  congr 1

/-- Degree-zero ordinary Ext comparison induced by the original derived
full-support functor and its actual Hom identification. -/
def moduleRelativeExtOrdinaryZeroIso :
    Abelian.extFunctorObj F 0 ≅ preadditiveCoyoneda.obj (op F) :=
  (moduleRelativeExtOrdinaryIso R F 0).symm ≪≫
    moduleLocallyClosedSupportedExtZeroIso R F moduleRelativeTotalSupport ≪≫
      moduleRelativeHomOrdinaryIso R F

/-- Degree-zero open Ext comparison induced by the original derived
support functor and its actual restricted Hom identification. -/
def moduleRelativeExtOpenZeroIso :
    moduleOpenRestriction R Z.compl ⋙ Abelian.extFunctorObj (F.over Z.compl) 0 ≅
      moduleOpenRestriction R Z.compl ⋙ preadditiveCoyoneda.obj (op (F.over Z.compl)) :=
  (moduleRelativeExtOpenIso R F Z 0).symm ≪≫
    moduleLocallyClosedSupportedExtZeroIso R F _ ≪≫ moduleRelativeHomOpenIso R F Z

/-- The actual degree-zero derived arrow becomes `Hom.over` under the
degree-zero comparisons from the original supported functors. -/
@[reassoc]
theorem moduleRelativeExtRestriction_zero (G : SheafOfModules.{u} R) :
    (moduleRelativeExtRestriction R F Z 0).app G ≫
        (moduleRelativeExtOpenZeroIso R F Z).hom.app G =
      (moduleRelativeExtOrdinaryZeroIso R F).hom.app G ≫
        (moduleRelativeHomRestriction R F Z).app G := by
  simp only [moduleRelativeExtRestriction, moduleRelativeExtOpenZeroIso,
    moduleRelativeExtOrdinaryZeroIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc _ _ ((moduleRelativeHomOpenIso R F Z).hom.app G),
    moduleNestedSupportedExtRestriction_zero, Category.assoc]
  rw [← NatTrans.comp_app, moduleRelativeHomRestriction_original]
  simp only [NatTrans.comp_app]

/-- Standard restriction of derived-category Ext by the actual exact open
restriction functor. Its comparison with `moduleRelativeExtRestriction`
requires compatibility of the resolution and derived-category Ext comparisons. -/
def moduleRelativeFunctorExtRestriction (n : ℕ) :
    Abelian.extFunctorObj F n ⟶
      moduleOpenRestriction R Z.compl ⋙ Abelian.extFunctorObj (F.over Z.compl) n where
  app G := AddCommGrpCat.ofHom ((moduleOpenRestriction R Z.compl).mapExtAddHom F G n)
  naturality G H a := by
    ext e
    change (e.comp (Abelian.Ext.mk₀ a) (add_zero n)).mapExactFunctor
        (moduleOpenRestriction R Z.compl) =
      (e.mapExactFunctor (moduleOpenRestriction R Z.compl)).comp
        (Abelian.Ext.mk₀ ((moduleOpenRestriction R Z.compl).map a)) (add_zero n)
    rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]

/-- The standard Ext restriction also sends each degree-zero morphism to
its actual restriction, under the usual `Ext.mk₀` identification. -/
theorem moduleRelativeFunctorExtRestriction_mk₀ {G : SheafOfModules.{u} R} (a : F ⟶ G) :
    (moduleRelativeFunctorExtRestriction R F Z 0).app G (Abelian.Ext.mk₀ a) =
      Abelian.Ext.mk₀ (a.over Z.compl) :=
  Abelian.Ext.mapExactFunctor_mk₀ (moduleOpenRestriction R Z.compl) a

end SGA.SGA2.ExposeVI
