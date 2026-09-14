/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalPageMaps
import SGA.SGA2.ExposeI.DerivedTruncationNaturality
import SGA.SGA2.ExposeI.SpectralSequenceFirstPageNaturality

/-! # Coefficient naturality of the original supported E₂ comparison -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

private lemma coyoneda_mapIso_apply {C : Type*} [Category C] [Preadditive C]
    {A B D : C} (e : B ≅ D) (x : A ⟶ B) :
    ((preadditiveCoyoneda.obj (op A)).mapIso e).addCommGroupIsoToAddEquiv x =
      x ≫ e.hom := rfl

private lemma addCommGrp_comm_apply {A B C D : AddCommGrpCat.{u}}
    (f : A ⟶ B) (g : C ⟶ D) (i : A ⟶ C) (j : B ⟶ D)
    (h : f ≫ j = i ≫ g) (x : A) : j (f x) = g (i x) :=
  ConcreteCategory.congr_hom h x

variable {X : TopCat.{u}}

attribute [local instance] supportedE2_hasDerivedCategory

lemma supportedAbelianSpectralObjectMap_apply (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℤ) (D : ComposableArrows EInt 1)
    (x : ((supportedLocalToGlobalAbelianSpectralObject Z I).H n).obj D) :
    ((supportedAbelianSpectralObjectMap Z φ).hom n).app D x =
      x ≫ ((supportedTriangulatedSpectralObjectMap Z φ).hom.app D)⟦n⟧' := rfl

@[reassoc]
lemma supportedDerivedObjectHomologyIso_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).map
        (supportedDerivedObjectMap Z φ) ≫ (supportedDerivedObjectHomologyIso Z J q).hom =
      (supportedDerivedObjectHomologyIso Z I q).hom ≫ (derivedUnderlineGammaZ Z q).map f := by
  dsimp only [supportedDerivedObjectHomologyIso, Iso.trans_hom, Iso.app_hom]
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    extendHomologyIso_hom_naturality_assoc]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ
    (underlineGammaZFunctor Z) q]
  rfl

@[reassoc]
lemma supportedE2TruncationIso_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (supportedTriangulatedSpectralObjectMap Z φ).hom.app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) ≫ (supportedE2TruncationIso Z J q).hom =
      (supportedE2TruncationIso Z I q).hom ≫
        (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).map
          ((derivedUnderlineGammaZ Z q).map f) := by
  change derivedSingleDegreeTruncationMap (q : ℤ) (supportedDerivedObjectMap Z φ) ≫ _ = _
  dsimp only [supportedE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [derivedSingleDegreeTruncationIsoSingle_naturality_assoc]
  erw [← Functor.map_comp, supportedDerivedObjectHomologyIso_naturality Z f I J φ hφ q]
  simp only [Functor.map_comp, Category.assoc]

@[reassoc]
lemma supportedSingleTotalShiftIso_naturality {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (p q : ℤ) :
    ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) q).map f)⟦p + q⟧' ≫
        (supportedSingleTotalShiftIso G p q).hom =
      (supportedSingleTotalShiftIso F p q).hom ≫
        ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map f)⟦p⟧' := by
  let e := (DerivedCategory.singleFunctors (Sheaf AddCommGrpCat.{u} X)).shiftIso
    (p + q) (-p) q (by lia) ≪≫
      ((DerivedCategory.singleFunctors (Sheaf AddCommGrpCat.{u} X)).shiftIso
        p (-p) 0 (by lia)).symm
  exact e.hom.naturality f

lemma supportedDerivedGlobalHomSingleEquiv_naturality {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (p : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X) ⟶
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj F)⟦(p : ℤ)⟧) :
    supportedDerivedGlobalHomSingleEquiv G p
        (x ≫ ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map f)⟦(p : ℤ)⟧') =
      CategoryTheory.Sheaf.H.map f p (supportedDerivedGlobalHomSingleEquiv F p x) := by
  let : HasDerivedCategory.{u + 1}
      (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
    HasDerivedCategory.standard _
  apply (Abelian.Ext.homAddEquiv (X := constantZ X) (Y := G) (n := p)).injective
  change (Abelian.Ext.homAddEquiv.symm _).hom =
    ((Abelian.Ext.homAddEquiv.symm x).comp (Abelian.Ext.mk₀ f) (add_zero p)).hom
  rw [Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀]
  change Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm _) =
    Abelian.Ext.homAddEquiv (Abelian.Ext.homAddEquiv.symm x) ≫ _
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]

@[reassoc]
lemma supportedE2TotalShiftIso_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ) :
    ((supportedTriangulatedSpectralObjectMap Z φ).hom.app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))))⟦(p : ℤ) + (q : ℤ)⟧' ≫
      (supportedE2TotalShiftIso Z J p q).hom =
    (supportedE2TotalShiftIso Z I p q).hom ≫
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
        ((derivedUnderlineGammaZ Z q).map f))⟦(p : ℤ)⟧' := by
  dsimp only [supportedE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, supportedE2TruncationIso_naturality Z f I J φ hφ q,
    Functor.map_comp_assoc, supportedSingleTotalShiftIso_naturality]
  simp only [Category.assoc]

lemma supportedTruncationSpectralSequenceE2Equiv_apply (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ)
    (x : ((supportedTruncationSpectralSequence Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    supportedTruncationSpectralSequenceE2Equiv Z I p q x =
      supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj F) p
        ((supportedE2FirstPageIso Z I p q).hom x ≫ (supportedE2TotalShiftIso Z I p q).hom) := by
  simp only [supportedTruncationSpectralSequenceE2Equiv, AddEquiv.trans_apply]
  apply congrArg (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj F) p)
  exact (coyoneda_mapIso_apply (supportedE2TotalShiftIso Z I p q) _).trans
    (congrArg (fun y => y ≫ (supportedE2TotalShiftIso Z I p q).hom)
      (Iso.addCommGroupIsoToAddEquiv_apply (supportedE2FirstPageIso Z I p q) x))

@[reassoc]
lemma supportedE2FirstPageIso_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (p q : ℕ) :
    ((supportedTruncationSpectralSequenceMap Z φ).hom 2).f ((p : ℤ), (q : ℤ)) ≫
        (supportedE2FirstPageIso Z J p q).hom =
      (supportedE2FirstPageIso Z I p q).hom ≫
        ((supportedAbelianSpectralObjectMap Z φ).hom ((p : ℤ) + (q : ℤ))).app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))) :=
  SpectralObjectCoefficientMaps.firstPageMap_hom
    (supportedAbelianSpectralObjectMap Z φ)
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
    (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- The existing E₂ equivalence intertwines the actual coefficient morphism
of spectral sequences with ordinary cohomology of the original derived
supported-sheaf morphism. -/
theorem supportedTruncationSpectralSequenceE2Equiv_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ)
    (x : ((supportedTruncationSpectralSequence Z I).page 2).X ((p : ℤ), (q : ℤ))) :
    supportedTruncationSpectralSequenceE2Equiv Z J p q
        (((supportedTruncationSpectralSequenceMap Z φ).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaZ Z q).map f) p
        (supportedTruncationSpectralSequenceE2Equiv Z I p q x) := by
  let eI := supportedE2FirstPageIso Z I p q
  let eJ := supportedE2FirstPageIso Z J p q
  have hp₀ : eJ.hom (((supportedTruncationSpectralSequenceMap Z φ).hom 2).f
      ((p : ℤ), (q : ℤ)) x) =
      ((supportedAbelianSpectralObjectMap Z φ).hom ((p : ℤ) + (q : ℤ))).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) (eI.hom x) :=
    addCommGrp_comm_apply _ _ _ _ (supportedE2FirstPageIso_naturality Z φ p q) x
  have hp : eJ.hom (((supportedTruncationSpectralSequenceMap Z φ).hom 2).f
      ((p : ℤ), (q : ℤ)) x) =
    eI.hom x ≫ ((supportedTriangulatedSpectralObjectMap Z φ).hom.app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))))⟦(p : ℤ) + (q : ℤ)⟧' :=
    hp₀.trans (supportedAbelianSpectralObjectMap_apply Z φ _ _ _)
  calc
    _ = supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj G) p
        (eJ.hom (((supportedTruncationSpectralSequenceMap Z φ).hom 2).f
          ((p : ℤ), (q : ℤ)) x) ≫ (supportedE2TotalShiftIso Z J p q).hom) :=
      supportedTruncationSpectralSequenceE2Equiv_apply Z J p q _
    _ = supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj G) p
        ((eI.hom x ≫ ((supportedTriangulatedSpectralObjectMap Z φ).hom.app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))))⟦(p : ℤ) + (q : ℤ)⟧') ≫
          (supportedE2TotalShiftIso Z J p q).hom) :=
      congrArg (fun y => supportedDerivedGlobalHomSingleEquiv
        ((derivedUnderlineGammaZ Z q).obj G) p (y ≫ (supportedE2TotalShiftIso Z J p q).hom)) hp
    _ = supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj G) p
        ((eI.hom x ≫ (supportedE2TotalShiftIso Z I p q).hom) ≫
          ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
            ((derivedUnderlineGammaZ Z q).map f))⟦(p : ℤ)⟧') := by
      apply congrArg (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj G) p)
      rw [Category.assoc, supportedE2TotalShiftIso_naturality Z f I J φ hφ p q,
        ← Category.assoc]
    _ = CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaZ Z q).map f) p
        (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaZ Z q).obj F) p
          (eI.hom x ≫ (supportedE2TotalShiftIso Z I p q).hom)) :=
      supportedDerivedGlobalHomSingleEquiv_naturality ((derivedUnderlineGammaZ Z q).map f) p _
    _ = _ := congrArg (CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaZ Z q).map f) p)
      (supportedTruncationSpectralSequenceE2Equiv_apply Z I p q x).symm

end SGA.SGA2.ExposeI
