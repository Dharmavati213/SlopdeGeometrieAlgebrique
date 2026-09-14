/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.LocalToGlobalSpectralFunctoriality
import SGA.SGA2.ExposeI.HomComplexNaturality

/-! # Coefficient naturality of actual supported total cohomology -/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat HomologicalComplex
open ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

local instance supportedTotalNaturality_hasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard (Sheaf AddCommGrpCat.{u} X)

def supportedGlobalSectionsComplexMap (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    supportedGlobalSectionsComplex Z I ⟶ supportedGlobalSectionsComplex Z J :=
  (((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op (⊤ : Opens X))).mapHomologicalComplex _).map (supportedSheafResolutionMap Z φ)

@[reassoc]
lemma supportedHomComplexIsoGlobalSections_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} {I : InjectiveResolution F} {J : InjectiveResolution G}
    (φ : I.cocomplex ⟶ J.cocomplex) :
    homComplexPostcomp
        ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
        (supportedSheafResolutionIntMap Z φ) ≫
      (supportedHomComplexIsoGlobalSections Z J).hom =
    (supportedHomComplexIsoGlobalSections Z I).hom ≫
      extendMap (supportedGlobalSectionsComplexMap Z φ) ComplexShape.embeddingUpNat := by
  have hm := mapExtendIso_naturality
    ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op (⊤ : Opens X)))
    ComplexShape.embeddingUpNat (supportedSheafResolutionMap Z φ)
  dsimp only [supportedHomComplexIsoGlobalSections, Iso.trans_hom]
  rw [homComplexFromSingleIso_naturality_assoc]
  simp only [Iso.app_hom]
  erw [NatTrans.naturality_assoc]
  erw [hm]
  simp only [Category.assoc]
  rfl

/-- The Hom-complex homology comparison used by the existing total
equivalence, exposed as a categorical isomorphism. -/
def supportedHomComplexHomologyIsoH_Z (Z : Closeds X)
    {F : Sheaf AddCommGrpCat.{u} X} (I : InjectiveResolution F) (n : ℕ) :
    (CochainComplex.HomComplex
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
      (supportedSheafResolutionInt Z I)).homology (n : ℤ) ≅ AddCommGrpCat.of (H_Z Z F n) :=
  (homologyFunctor AddCommGrpCat.{u} (ComplexShape.up ℤ) (n : ℤ)).mapIso
      (supportedHomComplexIsoGlobalSections Z I) ≪≫
    (supportedGlobalSectionsComplex Z I).extendHomologyIso ComplexShape.embeddingUpNat
      (j := n) (j' := (n : ℤ)) rfl ≪≫
    supportedGlobalSectionsComplexHomologyIso Z I n

@[reassoc]
lemma supportedHomComplexHomologyIsoH_Z_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ) :
    homologyMap (homComplexPostcomp
      ((CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X))
      (supportedSheafResolutionIntMap Z φ)) (n : ℤ) ≫
        (supportedHomComplexHomologyIsoH_Z Z J n).hom =
      (supportedHomComplexHomologyIsoH_Z Z I n).hom ≫ AddCommGrpCat.ofHom (H_Z_map Z f n) := by
  have h := congrArg (fun ψ => homologyMap ψ (n : ℤ))
    (supportedHomComplexIsoGlobalSections_naturality Z φ)
  simp only [homologyMap_comp] at h
  dsimp only [supportedHomComplexHomologyIsoH_Z, Iso.trans_hom, Functor.mapIso_hom]
  erw [← Category.assoc, h, Category.assoc]
  erw [extendHomologyIso_hom_naturality_assoc]
  erw [supportedGlobalSectionsComplexHomologyIso_hom_naturality Z f I J φ hφ n]
  simp only [Category.assoc]
  rfl

/-- The existing actual derived-Hom-to-`H_Z` equivalence respects every
compatible map of actual injective resolutions. -/
theorem supportedDerivedTotalHomEquivH_Z_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ)
    (x : (DerivedCategory.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X) ⟶
      (supportedDerivedObject Z I)⟦(n : ℤ)⟧) :
    supportedDerivedTotalHomEquivH_Z Z J n (x ≫ (supportedDerivedObjectMap Z φ)⟦(n : ℤ)⟧') =
      H_Z_map Z f n (supportedDerivedTotalHomEquivH_Z Z I n x) := by
  let K := (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).obj (constantZ X)
  obtain ⟨y, rfl⟩ := (homComplexHomologyDerivedHomEquiv K
    (supportedSheafResolutionInt Z I) (n : ℤ)).surjective x
  erw [← homComplexHomologyDerivedHomEquiv_naturality]
  simp only [K, supportedDerivedTotalHomEquivH_Z, AddEquiv.trans_apply]
  erw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  change (supportedHomComplexHomologyIsoH_Z Z J n).hom
      (homologyMap (homComplexPostcomp K (supportedSheafResolutionIntMap Z φ)) (n : ℤ) y) =
    H_Z_map Z f n ((supportedHomComplexHomologyIsoH_Z Z I n).hom y)
  exact ConcreteCategory.congr_hom
    (supportedHomComplexHomologyIsoH_Z_naturality Z f I J φ hφ n) y

/-- The actual spectral-object morphism on its total interval intertwines
the already constructed total equivalence with the original `H_Z_map`. -/
theorem supportedSpectralObjectTotalEquivH_Z_naturality (Z : Closeds X)
    {F G : Sheaf AddCommGrpCat.{u} X} (f : F ⟶ G)
    (I : InjectiveResolution F) (J : InjectiveResolution G)
    (φ : I.cocomplex ⟶ J.cocomplex) (hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0) (n : ℕ)
    (x : ((supportedLocalToGlobalAbelianSpectralObject Z I).H (n : ℤ)).obj
      (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le)))) :
    supportedSpectralObjectTotalEquivH_Z Z J n
        (((supportedAbelianSpectralObjectMap Z φ).hom (n : ℤ)).app
          (mk₁ (homOfLE (show (⊥ : EInt) ≤ ⊤ from bot_le))) x) =
      H_Z_map Z f n (supportedSpectralObjectTotalEquivH_Z Z I n x) :=
  supportedDerivedTotalHomEquivH_Z_naturality Z f I J φ hφ n x

end SGA.SGA2.ExposeI
