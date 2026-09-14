/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocallyClosedLocalToGlobalMaps
import SGA.SGA2.ExposeI.LocalToGlobalTotalNaturality

/-! # Naturality of the actual ambient locally closed Ext abutment -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

attribute [local instance] supportedE2_hasDerivedCategory

/-- The abutment-complex comparison commutes with every compatible map of
actual injective resolutions. -/
@[reassoc]
lemma locallyClosedSupportedGlobalSectionsComplexHomologyIso_hom_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    homologyMap (((underlineGammaLocallyClosedFunctor W ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))).mapHomologicalComplex _).map φ) n ≫
      (locallyClosedSupportedGlobalSectionsComplexHomologyIso W J n).hom =
    (locallyClosedSupportedGlobalSectionsComplexHomologyIso W I n).hom ≫
      AddCommGrpCat.ofHom (H_locallyClosed_map W f n) := by
  simp only [locallyClosedSupportedGlobalSectionsComplexHomologyIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rw [← Category.assoc]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ
    (underlineGammaLocallyClosedFunctor W ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))) n]
  rw [Category.assoc]
  exact congrArg (fun k =>
    (I.isoRightDerivedObj (underlineGammaLocallyClosedFunctor W ⋙
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (op (⊤ : Opens X))) n).inv ≫ k)
      ((derivedLocallyClosedSupportedGlobalSectionsIsoExt W n).hom.naturality f)

def locallyClosedSupportedGlobalSectionsComplexMap (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    locallyClosedSupportedGlobalSectionsComplex W I ⟶
      locallyClosedSupportedGlobalSectionsComplex W J :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).mapHomologicalComplex _).map (locallyClosedSupportedSheafResolutionMap W φ)

@[reassoc]
lemma locallyClosedSupportedHomComplexIsoGlobalSections_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    homComplexPostcomp
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
        (locallyClosedSupportedSheafResolutionIntMap W φ) ≫
      (locallyClosedSupportedHomComplexIsoGlobalSections W J).hom =
    (locallyClosedSupportedHomComplexIsoGlobalSections W I).hom ≫
      extendMap (locallyClosedSupportedGlobalSectionsComplexMap W φ)
        ComplexShape.embeddingUpNat := by
  have hm := mapExtendIso_naturality
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))
    ComplexShape.embeddingUpNat (locallyClosedSupportedSheafResolutionMap W φ)
  dsimp only [locallyClosedSupportedHomComplexIsoGlobalSections, Iso.trans_hom]
  rw [homComplexFromSingleIso_naturality_assoc]
  simp only [Iso.app_hom]
  erw [NatTrans.naturality_assoc]
  erw [hm]
  simp only [Category.assoc]
  rfl

/-- The Hom-complex homology comparison used by the existing total
equivalence, exposed as a categorical isomorphism. -/
def locallyClosedHomComplexHomologyIsoExt (W : LocallyClosedIn X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
      (locallyClosedSupportedSheafResolutionInt W I)).homology (n : ℤ) ≅ AddCommGrpCat.of
        (H_locallyClosed W F n) :=
  (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (locallyClosedSupportedHomComplexIsoGlobalSections W I) ≪≫
    (locallyClosedSupportedGlobalSectionsComplex W I).extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl ≪≫
    locallyClosedSupportedGlobalSectionsComplexHomologyIso W I n

@[reassoc]
lemma locallyClosedHomComplexHomologyIsoExt_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
      (locallyClosedSupportedSheafResolutionIntMap W φ)) (n : ℤ) ≫
        (locallyClosedHomComplexHomologyIsoExt W J n).hom =
      (locallyClosedHomComplexHomologyIsoExt W I n).hom ≫ AddCommGrpCat.ofHom
        (H_locallyClosed_map W f n) := by
  have h := congrArg (fun ψ => homologyMap ψ (n : ℤ))
    (locallyClosedSupportedHomComplexIsoGlobalSections_naturality W φ)
  simp only [homologyMap_comp] at h
  dsimp only [locallyClosedHomComplexHomologyIsoExt, Iso.trans_hom, Functor.mapIso_hom]
  erw [← Category.assoc, h, Category.assoc]
  erw [extendHomologyIso_hom_naturality_assoc]
  erw [locallyClosedSupportedGlobalSectionsComplexHomologyIso_hom_naturality W f I J φ hφ n]
  simp only [Category.assoc]
  rfl

/-- The existing actual derived-Hom-to-`H_locallyClosed` equivalence respects every
compatible map of actual injective resolutions. -/
theorem locallyClosedDerivedTotalHomEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X) ⟶
      (locallyClosedSupportedDerivedObject W I)⟦(n : ℤ)⟧) :
    locallyClosedDerivedTotalHomEquiv W J n (x ≫ (locallyClosedSupportedDerivedObjectMap W
      φ)⟦(n : ℤ)⟧') =
      H_locallyClosed_map W f n (locallyClosedDerivedTotalHomEquiv W I n x) := by
  let K := (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)
  obtain ⟨y, rfl⟩ := (homComplexHomologyDerivedHomEquiv K
    (locallyClosedSupportedSheafResolutionInt W I) (n : ℤ)).surjective x
  erw [← homComplexHomologyDerivedHomEquiv_naturality]
  simp only [K, locallyClosedDerivedTotalHomEquiv, AddEquiv.trans_apply]
  erw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  change (locallyClosedHomComplexHomologyIsoExt W J n).hom
      (homologyMap (homComplexPostcomp K (locallyClosedSupportedSheafResolutionIntMap W φ)) (n
        : ℤ) y) =
    H_locallyClosed_map W f n ((locallyClosedHomComplexHomologyIsoExt W I n).hom y)
  exact ConcreteCategory.congr_hom
    (locallyClosedHomComplexHomologyIsoExt_naturality W f I J φ hφ n) y

/-- The actual spectral-object morphism on its total interval intertwines
the already constructed total equivalence with the original `H_locallyClosed_map`. -/
theorem locallyClosedSpectralObjectTotalEquiv_naturality (W : LocallyClosedIn X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ)
    (x : ((locallyClosedLocalToGlobalAbelianSpectralObject W I).H (n : ℤ)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le)))) :
    locallyClosedSpectralObjectTotalEquiv W J n
        (((locallyClosedAbelianSpectralObjectMap W φ).hom (n : ℤ)).app
          (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) x) =
      H_locallyClosed_map W f n (locallyClosedSpectralObjectTotalEquiv W I n x) :=
  locallyClosedDerivedTotalHomEquiv_naturality W f I J φ hφ n x

end SGA.SGA2.ExposeI
