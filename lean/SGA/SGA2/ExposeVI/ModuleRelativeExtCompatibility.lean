/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleRelativeExtSequence
import SGA.SGA2.ExposeI.ExtRightDerivedMap

/-!
# Standard Ext comparisons for the relative module Ext sequence

We compare the actual endpoint identifications of the relative sequence
with the standard `Ext⁰ = Hom` isomorphism and exact-functor restriction.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
    (F : SheafOfModules.{u} R) (Z : Closeds X)

private theorem gammaAmbientIso_congr (W : ExposeI.LocallyClosedIn X)
    (B B' : Closeds X) (hB : B = B')
    (h : ExposeI.closedSupportOnOpen B W.V = W.ZV)
    (h' : ExposeI.closedSupportOnOpen B' W.V = W.ZV) :
    ExposeI.gammaLocallyClosedAmbientIso W B h ≪≫
        eqToIso (congrArg (fun T => ExposeI.gammaZSectionsFunctor T W.V) hB) =
      ExposeI.gammaLocallyClosedAmbientIso W B' h' := by
  subst B'
  simp

private theorem gammaAmbientIso_ofOpenClosed (U : Opens X) (B : Closeds X) :
    ExposeI.gammaLocallyClosedAmbientIso (ExposeI.LocallyClosedIn.ofOpenClosed U B) B rfl =
      ExposeI.gammaZSectionsLocallyClosedIso B U := by
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply AddCommGrpCat.hom_ext
  ext s
  rfl

private theorem moduleHomIndependenceIso_of_eq
    {W W' : ExposeI.LocallyClosedIn X} (e : W = W') (h : W.asSet = W'.asSet) :
    moduleLocallyClosedSupportedHomIndependenceIso R F h =
      eqToIso (congrArg (moduleLocallyClosedSupportedHomFunctor R F) e) := by
  subst W'
  simp [moduleLocallyClosedSupportedHomIndependenceIso,
    ExposeI.gammaLocallyClosedIndependenceIso]

private theorem moduleAmbientHomWitnessEq (W : ExposeI.LocallyClosedIn X)
    (U : Opens X) (B : Closeds X) (hB : B = ⊤)
    (hW : W = ExposeI.LocallyClosedIn.ofOpenClosed U ⊤)
    (h : ExposeI.closedSupportOnOpen B W.V = W.ZV) :
    moduleLocallyClosedSupportedHomGammaIso R F W ≪≫
        Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
          (ExposeI.gammaLocallyClosedAmbientIso W B h ≪≫
            eqToIso (show ExposeI.gammaZSectionsFunctor B W.V =
              ExposeI.gammaZSectionsFunctor ⊤ U by rw [hB, hW]; rfl)) =
      eqToIso (congrArg (moduleLocallyClosedSupportedHomFunctor R F) hW) ≪≫
        moduleLocallyClosedSupportedHomGammaIso R F (ExposeI.LocallyClosedIn.ofOpenClosed U ⊤) ≪≫
          Functor.isoWhiskerLeft (moduleSheafHomAbFunctor (Opens.grothendieckTopology X) F)
            (ExposeI.gammaZSectionsLocallyClosedIso (⊤ : Closeds X) U) := by
  subst B W
  simp only [eqToIso_refl, Iso.trans_refl, Iso.refl_trans, gammaAmbientIso_ofOpenClosed]

/-- The ambient Hom endpoint agrees with the canonical full-support comparison. -/
theorem moduleRelativeHomOrdinaryIso_eq :
    moduleRelativeHomOrdinaryIso R F =
      moduleLocallyClosedSupportedHomClosedIso R F ⊤ ≪≫ moduleSupportedHomTopIso R F := by
  dsimp only [moduleRelativeHomOrdinaryIso, moduleRelativeHomMiddleCoordinates,
    moduleLocallyClosedSupportedHomClosedIso, ExposeI.nestedGammaMiddleIso]
  rw [gammaAmbientIso_congr _ _ _ moduleRelativeTotalSupport_closedHull _ rfl]

/-- The original open Hom endpoint in the representation used by its Ext comparison. -/
def moduleRelativeCanonicalHomOpenIso :
    moduleLocallyClosedSupportedHomFunctor R F
      (ExposeI.nestedDifferenceSupportWitness moduleRelativeTotalSupport
        (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport (moduleRelativeClosedInTotal Z))) ≅
      moduleOpenRestriction R Z.compl ⋙ preadditiveCoyoneda.obj (op (F.over Z.compl)) :=
  moduleLocallyClosedSupportedHomIndependenceIso R F
    ((moduleRelativeOpenSupport_asSet Z).trans
      (by simp [ExposeI.LocallyClosedIn.ofOpenClosed_asSet])) ≪≫
    moduleLocallyClosedSupportedHomOpenIso R F Z.compl

/-- The open Hom endpoint agrees with the canonical witness-independence comparison. -/
theorem moduleRelativeHomOpenIso_eq :
    moduleRelativeHomOpenIso R F Z = moduleRelativeCanonicalHomOpenIso R F Z := by
  have hW : ExposeI.nestedDifferenceSupportWitness moduleRelativeTotalSupport
      (ExposeI.nestedClosedSubspace moduleRelativeTotalSupport (moduleRelativeClosedInTotal Z)) =
      ExposeI.LocallyClosedIn.ofOpenClosed Z.compl ⊤ := by
    dsimp only [ExposeI.nestedDifferenceSupportWitness]
    rw [moduleRelativeTotalSupport_closedHull, moduleRelativeClosedSupport_closedHull]
    change ExposeI.LocallyClosedIn.ofOpenClosed (⊤ ⊓ Z.compl) ⊤ = _
    rw [top_inf_eq]
  dsimp only [moduleRelativeHomOpenIso, moduleRelativeHomRightCoordinates,
    moduleRelativeCanonicalHomOpenIso, moduleLocallyClosedSupportedHomOpenIso,
    ExposeI.nestedGammaRightIso]
  rw [moduleHomIndependenceIso_of_eq R F hW]
  rw [moduleAmbientHomWitnessEq R F _ Z.compl _ moduleRelativeTotalSupport_closedHull hW]
  simp only [Iso.trans_assoc]

/-- The ambient Ext endpoint uses the standard zeroth Ext identification. -/
@[reassoc]
theorem moduleRelativeExtOrdinaryIso_zero_standard (G : SheafOfModules.{u} R) :
    (moduleRelativeExtOrdinaryIso R F 0).hom.app G ≫
        (ExposeI.extFunctorZeroIso F).hom.app G =
      (moduleLocallyClosedSupportedExtZeroIso R F moduleRelativeTotalSupport).hom.app G ≫
        (moduleRelativeHomOrdinaryIso R F).hom.app G := by
  rw [moduleRelativeHomOrdinaryIso_eq]
  have h := ExposeI.representedRightDerivedIso_zero F
    (moduleLocallyClosedSupportedHomClosedIso R F ⊤ ≪≫ moduleSupportedHomTopIso R F) G
  simpa only [moduleRelativeExtOrdinaryIso, moduleLocallyClosedSupportedExtTopIso,
    moduleLocallyClosedSupportedExtClosedIso, moduleSupportedExtTopIso,
    moduleLocallyClosedSupportedExtZeroIso, ExposeI.rightDerivedFunctorIso,
    Iso.trans_hom, NatTrans.comp_app, NatTrans.rightDerived_comp, Category.assoc] using h

/-- The open Ext endpoint also uses the standard zeroth Ext identification. -/
@[reassoc]
theorem moduleRelativeExtOpenIso_zero_standard (G : SheafOfModules.{u} R) :
    (moduleRelativeExtOpenIso R F Z 0).hom.app G ≫
        (ExposeI.extFunctorZeroIso (F.over Z.compl)).hom.app (G.over Z.compl) =
      (moduleLocallyClosedSupportedExtZeroIso R F _).hom.app G ≫
        (moduleRelativeHomOpenIso R F Z).hom.app G := by
  rw [moduleRelativeHomOpenIso_eq]
  have h := ExposeI.representedPrecomposeRightDerivedIso_zero
    (moduleOpenRestriction R Z.compl) (F.over Z.compl)
    (moduleRelativeCanonicalHomOpenIso R F Z) G
  simpa only [moduleRelativeExtOpenIso, moduleLocallyClosedSupportedExtOpenIsoOfAsSet,
    moduleLocallyClosedSupportedExtIndependenceIso, moduleLocallyClosedSupportedExtOpenIso,
    ExposeI.representedPrecomposeRightDerivedIso, moduleLocallyClosedSupportedExtZeroIso,
    moduleRelativeCanonicalHomOpenIso, ExposeI.rightDerivedFunctorIso, Iso.trans_hom,
    NatTrans.comp_app, NatTrans.rightDerived_comp, Category.assoc,
    moduleLocallyClosedSupportedExtFunctor, moduleOpenRestriction, SheafOfModules.over] using h

/-- The relative sequence's ambient zero comparison is the standard `Ext⁰ = Hom`. -/
theorem moduleRelativeExtOrdinaryZeroIso_eq :
    moduleRelativeExtOrdinaryZeroIso R F = ExposeI.extFunctorZeroIso F := by
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply (cancel_epi ((moduleRelativeExtOrdinaryIso R F 0).hom.app G)).mp
  rw [moduleRelativeExtOrdinaryIso_zero_standard]
  simp only [moduleRelativeExtOrdinaryZeroIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc]

/-- The relative sequence's open zero comparison is the standard `Ext⁰ = Hom`. -/
theorem moduleRelativeExtOpenZeroIso_eq :
    moduleRelativeExtOpenZeroIso R F Z =
      Functor.isoWhiskerLeft (moduleOpenRestriction R Z.compl)
        (ExposeI.extFunctorZeroIso (F.over Z.compl)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext G
  apply (cancel_epi ((moduleRelativeExtOpenIso R F Z 0).hom.app G)).mp
  change _ = (moduleRelativeExtOpenIso R F Z 0).hom.app G ≫
    (ExposeI.extFunctorZeroIso (F.over Z.compl)).hom.app (G.over Z.compl)
  rw [moduleRelativeExtOpenIso_zero_standard]
  simp only [moduleRelativeExtOpenZeroIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Iso.hom_inv_id_app_assoc]

/-- **VI.1.9, degree zero:** under the standard `Ext⁰ = Hom` identifications,
the restriction in the exact sequence is the actual restriction `Hom.over`. -/
theorem moduleRelativeExtRestriction_zero_standard (G : SheafOfModules.{u} R)
    (e : Abelian.Ext F G 0) :
    Abelian.Ext.homEquiv₀ ((moduleRelativeExtRestriction R F Z 0).app G e) =
      (Abelian.Ext.homEquiv₀ e).over Z.compl := by
  have h := moduleRelativeExtRestriction_zero R F Z G
  rw [moduleRelativeExtOrdinaryZeroIso_eq, moduleRelativeExtOpenZeroIso_eq] at h
  change Abelian.Ext.addEquiv₀ ((moduleRelativeExtRestriction R F Z 0).app G e) =
    (Abelian.Ext.addEquiv₀ e).over Z.compl
  exact congrArg
    (fun f : AddCommGrpCat.of (Abelian.Ext F G 0) ⟶
      AddCommGrpCat.of (F.over Z.compl ⟶ G.over Z.compl) => f.hom e) h

/-- The two independently constructed restriction maps agree in degree zero. -/
theorem moduleRelativeExtRestriction_zero_eq_functor :
    moduleRelativeExtRestriction R F Z 0 = moduleRelativeFunctorExtRestriction R F Z 0 := by
  apply NatTrans.ext
  funext G
  apply AddCommGrpCat.hom_ext
  ext e
  obtain ⟨a, rfl⟩ := (Abelian.Ext.mk₀_bijective F G).2 e
  rw [moduleRelativeFunctorExtRestriction_mk₀]
  apply Abelian.Ext.homEquiv₀.injective
  rw [moduleRelativeExtRestriction_zero_standard]
  change (Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ a)).over Z.compl =
    Abelian.Ext.addEquiv₀ (Abelian.Ext.mk₀ (a.over Z.compl))
  simp only [← Abelian.Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]

/-- The ambient endpoint is the canonical represented right-derived Hom comparison. -/
theorem moduleRelativeExtOrdinaryIso_eq (n : ℕ) :
    moduleRelativeExtOrdinaryIso R F n =
      ExposeI.rightDerivedFunctorIso (moduleRelativeHomOrdinaryIso R F) n ≪≫
        ExposeI.rightDerivedCoyonedaNatIsoExt F n := by
  rw [moduleRelativeHomOrdinaryIso_eq]
  apply Iso.ext
  simp only [moduleRelativeExtOrdinaryIso, moduleLocallyClosedSupportedExtTopIso,
    moduleLocallyClosedSupportedExtClosedIso, moduleSupportedExtTopIso,
    ExposeI.rightDerivedFunctorIso, Iso.trans_hom, NatTrans.rightDerived_comp, Category.assoc]

/-- The open endpoint is the canonical represented comparison after exact restriction. -/
theorem moduleRelativeExtOpenIso_eq (n : ℕ) :
    moduleRelativeExtOpenIso R F Z n =
      ExposeI.representedPrecomposeRightDerivedIso (moduleOpenRestriction R Z.compl)
        (F.over Z.compl) (moduleRelativeHomOpenIso R F Z) n := by
  rw [moduleRelativeHomOpenIso_eq]
  apply Iso.ext
  simp only [moduleRelativeExtOpenIso, moduleLocallyClosedSupportedExtOpenIsoOfAsSet,
    moduleLocallyClosedSupportedExtIndependenceIso, moduleLocallyClosedSupportedExtOpenIso,
    ExposeI.representedPrecomposeRightDerivedIso, moduleRelativeCanonicalHomOpenIso,
    ExposeI.rightDerivedFunctorIso, Iso.trans_hom, NatTrans.rightDerived_comp, Category.assoc]

/-- Actual `Hom.over` is the Hom map of the exact restriction functor. -/
theorem moduleRelativeHomRestriction_eq_exactFunctorHomMap :
    moduleRelativeHomRestriction R F Z =
      ExposeI.exactFunctorHomMap (moduleOpenRestriction R Z.compl) F := rfl

/-- **VI.1.9:** the restriction arrow in the proved exact sequence is the
standard map on Ext induced by the actual exact open restriction functor,
in every degree. -/
theorem moduleRelativeExtRestriction_eq_functor (n : ℕ) :
    moduleRelativeExtRestriction R F Z n = moduleRelativeFunctorExtRestriction R F Z n := by
  rw [moduleRelativeExtRestriction, moduleRelativeExtOrdinaryIso_eq, moduleRelativeExtOpenIso_eq]
  have h := moduleRelativeHomRestriction_original R F Z
  rw [moduleRelativeHomRestriction_eq_exactFunctorHomMap] at h
  exact ExposeI.representedExactFunctorMap_eq (moduleOpenRestriction R Z.compl) F
    (moduleRelativeHomOrdinaryIso R F) (moduleRelativeHomOpenIso R F Z)
    (moduleNestedSupportedHomRestriction R F moduleRelativeTotalSupport
      (moduleRelativeClosedInTotal Z)) h n

end SGA.SGA2.ExposeVI
