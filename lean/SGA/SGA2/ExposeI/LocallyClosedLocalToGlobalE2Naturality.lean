/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalMaps
import SGA.SGA2.ExposeI.LocalToGlobalE2Naturality

/-! # Coefficient naturality of the actual ambient locally closed E₂ comparison -/

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

lemma locallyClosedAbelianSpectralObjectMap_apply (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (n : ℤ) (D : ComposableArrows EInt 1)
    (x : ((locallyClosedLocalToGlobalAbelianSpectralObject W I).H n).obj D) :
    ((locallyClosedAbelianSpectralObjectMap W φ).hom n).app D x =
      x ≫ ((locallyClosedTriangulatedSpectralObjectMap W φ).hom.app D)⟦n⟧' := rfl

@[reassoc]
lemma locallyClosedSupportedDerivedObjectHomologyIso_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (DerivedCategory.homologyFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).map
        (locallyClosedSupportedDerivedObjectMap W φ) ≫
          (locallyClosedSupportedDerivedObjectHomologyIso W J q).hom =
      (locallyClosedSupportedDerivedObjectHomologyIso W I q).hom ≫
        (derivedUnderlineGammaLocallyClosed W q).map f := by
  dsimp only [locallyClosedSupportedDerivedObjectHomologyIso, Iso.trans_hom, Iso.app_hom]
  erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc,
    extendHomologyIso_hom_naturality_assoc]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ
    (underlineGammaLocallyClosedFunctor W) q]
  rfl

@[reassoc]
lemma locallyClosedE2TruncationIso_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (q : ℕ) :
    (locallyClosedTriangulatedSpectralObjectMap W φ).hom.app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) ≫ (locallyClosedE2TruncationIso W J q).hom =
      (locallyClosedE2TruncationIso W I q).hom ≫
        (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) (q : ℤ)).map
          ((derivedUnderlineGammaLocallyClosed W q).map f) := by
  change derivedSingleDegreeTruncationMap (q : ℤ) (locallyClosedSupportedDerivedObjectMap W φ)
    ≫ _ = _
  dsimp only [locallyClosedE2TruncationIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [derivedSingleDegreeTruncationIsoSingle_naturality_assoc]
  erw [← Functor.map_comp, locallyClosedSupportedDerivedObjectHomologyIso_naturality W f I J φ hφ q]
  simp only [Functor.map_comp, Category.assoc]

@[reassoc]
lemma locallyClosedE2TotalShiftIso_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ) :
    ((locallyClosedTriangulatedSpectralObjectMap W φ).hom.app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))))⟦(p : ℤ) + (q : ℤ)⟧' ≫
      (locallyClosedE2TotalShiftIso W J p q).hom =
    (locallyClosedE2TotalShiftIso W I p q).hom ≫
      ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
        ((derivedUnderlineGammaLocallyClosed W q).map f))⟦(p : ℤ)⟧' := by
  dsimp only [locallyClosedE2TotalShiftIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Functor.map_comp_assoc, locallyClosedE2TruncationIso_naturality W f I J φ hφ q,
    Functor.map_comp_assoc, supportedSingleTotalShiftIso_naturality]
  simp only [Category.assoc]

lemma locallyClosedTruncationSpectralSequenceE2Equiv_apply (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (p q : ℕ)
    (x : ((locallyClosedTruncationSpectralSequence W I).page 2).X ((p : ℤ), (q : ℤ))) :
    locallyClosedTruncationSpectralSequenceE2Equiv W I p q x =
      supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W q).obj F) p
        ((locallyClosedE2FirstPageIso W I p q).hom x ≫ (locallyClosedE2TotalShiftIso W I p
          q).hom) := by
  simp only [locallyClosedTruncationSpectralSequenceE2Equiv, AddEquiv.trans_apply]
  apply congrArg (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W
    q).obj F) p)
  exact (coyoneda_mapIso_apply (locallyClosedE2TotalShiftIso W I p q) _).trans
    (congrArg (fun y => y ≫ (locallyClosedE2TotalShiftIso W I p q).hom)
      (Iso.addCommGroupIsoToAddEquiv_apply (locallyClosedE2FirstPageIso W I p q) x))

@[reassoc]
lemma locallyClosedE2FirstPageIso_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) (p q : ℕ) :
    ((locallyClosedTruncationSpectralSequenceMap W φ).hom 2).f ((p : ℤ), (q : ℤ)) ≫
        (locallyClosedE2FirstPageIso W J p q).hom =
      (locallyClosedE2FirstPageIso W I p q).hom ≫
        ((locallyClosedAbelianSpectralObjectMap W φ).hom ((p : ℤ) + (q : ℤ))).app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))) :=
  SpectralObjectCoefficientMaps.firstPageMap_hom
    (locallyClosedAbelianSpectralObjectMap W φ)
    Abelian.SpectralObject.coreE₂Cohomological ((p : ℤ), (q : ℤ))
    (q : ℤ) ((q : ℤ) + 1) rfl rfl ((p : ℤ) + (q : ℤ)) rfl

/-- The existing E₂ equivalence intertwines the actual coefficient morphism
of spectral sequences with ordinary cohomology of the original derived
supported-sheaf morphism. -/
theorem locallyClosedTruncationSpectralSequenceE2Equiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (p q : ℕ)
    (x : ((locallyClosedTruncationSpectralSequence W I).page 2).X ((p : ℤ), (q : ℤ))) :
    locallyClosedTruncationSpectralSequenceE2Equiv W J p q
        (((locallyClosedTruncationSpectralSequenceMap W φ).hom 2).f ((p : ℤ), (q : ℤ)) x) =
      CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaLocallyClosed W q).map f) p
        (locallyClosedTruncationSpectralSequenceE2Equiv W I p q x) := by
  let eI := locallyClosedE2FirstPageIso W I p q
  let eJ := locallyClosedE2FirstPageIso W J p q
  have hp₀ : eJ.hom (((locallyClosedTruncationSpectralSequenceMap W φ).hom 2).f
      ((p : ℤ), (q : ℤ)) x) =
      ((locallyClosedAbelianSpectralObjectMap W φ).hom ((p : ℤ) + (q : ℤ))).app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))) (eI.hom x) :=
    addCommGrp_comm_apply _ _ _ _ (locallyClosedE2FirstPageIso_naturality W φ p q) x
  have hp : eJ.hom (((locallyClosedTruncationSpectralSequenceMap W φ).hom 2).f
      ((p : ℤ), (q : ℤ)) x) =
    eI.hom x ≫ ((locallyClosedTriangulatedSpectralObjectMap W φ).hom.app
        (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
          WithBotTop.coe_le_coe.mpr (by lia)))))⟦(p : ℤ) + (q : ℤ)⟧' :=
    hp₀.trans (locallyClosedAbelianSpectralObjectMap_apply W φ _ _ _)
  calc
    _ = supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W q).obj G) p
        (eJ.hom (((locallyClosedTruncationSpectralSequenceMap W φ).hom 2).f
          ((p : ℤ), (q : ℤ)) x) ≫ (locallyClosedE2TotalShiftIso W J p q).hom) :=
      locallyClosedTruncationSpectralSequenceE2Equiv_apply W J p q _
    _ = supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W q).obj G) p
        ((eI.hom x ≫ ((locallyClosedTriangulatedSpectralObjectMap W φ).hom.app
          (mk₁ (homOfLE (show ((q : ℤ) : EInt) ≤ ((q : ℤ) + 1 : ℤ) from
            WithBotTop.coe_le_coe.mpr (by lia)))))⟦(p : ℤ) + (q : ℤ)⟧') ≫
          (locallyClosedE2TotalShiftIso W J p q).hom) :=
      congrArg (fun y => supportedDerivedGlobalHomSingleEquiv
        ((derivedUnderlineGammaLocallyClosed W q).obj G) p (y ≫ (locallyClosedE2TotalShiftIso
          W J p q).hom)) hp
    _ = supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W q).obj G) p
        ((eI.hom x ≫ (locallyClosedE2TotalShiftIso W I p q).hom) ≫
          ((DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
            ((derivedUnderlineGammaLocallyClosed W q).map f))⟦(p : ℤ)⟧') := by
      apply congrArg (supportedDerivedGlobalHomSingleEquiv
        ((derivedUnderlineGammaLocallyClosed W q).obj G) p)
      rw [Category.assoc, locallyClosedE2TotalShiftIso_naturality W f I J φ hφ p q,
        ← Category.assoc]
    _ = CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaLocallyClosed W q).map f) p
        (supportedDerivedGlobalHomSingleEquiv ((derivedUnderlineGammaLocallyClosed W q).obj F) p
          (eI.hom x ≫ (locallyClosedE2TotalShiftIso W I p q).hom)) :=
      supportedDerivedGlobalHomSingleEquiv_naturality ((derivedUnderlineGammaLocallyClosed W
        q).map f) p _
    _ = _ := congrArg (CategoryTheory.Sheaf.H.map ((derivedUnderlineGammaLocallyClosed W
      q).map f) p)
      (locallyClosedTruncationSpectralSequenceE2Equiv_apply W I p q x).symm

end SGA.SGA2.ExposeI
