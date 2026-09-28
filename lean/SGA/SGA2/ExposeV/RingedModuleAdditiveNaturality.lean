/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleAdditiveCohomology

/-!
# Naturality of the original module-to-additive supported-cohomology comparison

The resolution comparisons commute up to actual cochain homotopy: after
localization their augmentations determine the same map into a K-injective
complex. Supported sections preserve homotopies, so their homology comparisons
commute with the original coefficient maps.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

local instance : HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

local instance {F : Sheaf AddCommGrpCat.{u} X} (J : InjectiveResolution F) :
    J.cochainComplex.IsKInjective := by
  dsimp [InjectiveResolution.cochainComplex]
  infer_instance

/-- The underlying augmentation retains every actual morphism of module resolutions. -/
@[reassoc]
theorem moduleUnderlyingResolutionι_naturality
    {M N : SheafOfModules.{u} R} {a : M ⟶ N}
    {I : InjectiveResolution M} {I' : InjectiveResolution N}
    (α : InjectiveResolution.Hom I I' a) :
    moduleUnderlyingResolutionι R I ≫
        ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map α.hom' =
      (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
          ((SheafOfModules.toSheaf R).map a) ≫ moduleUnderlyingResolutionι R I' := by
  unfold moduleUnderlyingResolutionι
  rw [Category.assoc, ← Functor.map_comp, α.ι'_comp_hom', Functor.map_comp,
    ← Category.assoc]
  exact congrArg (fun b ↦ b ≫
      ((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map I'.ι')
    ((singleMapHomologicalComplex (SheafOfModules.toSheaf R)
      (ComplexShape.up ℤ) 0).inv.naturality a).symm

/-- Comparison of module and additive resolutions is natural up to genuine cochain homotopy. -/
def moduleAdditiveResolutionCompareHomotopy
    {M N : SheafOfModules.{u} R} {a : M ⟶ N}
    {I : InjectiveResolution M} {I' : InjectiveResolution N}
    {J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)}
    {J' : InjectiveResolution ((SheafOfModules.toSheaf R).obj N)}
    (α : InjectiveResolution.Hom I I' a)
    (β : InjectiveResolution.Hom J J' ((SheafOfModules.toSheaf R).map a)) :
    Homotopy
      (((SheafOfModules.toSheaf R).mapHomologicalComplex (ComplexShape.up ℤ)).map α.hom' ≫
        moduleAdditiveResolutionCompare R I' J')
      (moduleAdditiveResolutionCompare R I J ≫ β.hom') := by
  apply ExposeI.homotopyOfQMapEq.{u + 1, u, u + 1}
    (C := Sheaf AddCommGrpCat.{u} X)
  simp only [Functor.map_comp, Q_map_moduleAdditiveResolutionCompare]
  apply (cancel_epi (DerivedCategory.Q.map (moduleUnderlyingResolutionι R I))).mp
  rw [← Category.assoc, ← Functor.map_comp, moduleUnderlyingResolutionι_naturality R α,
    Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  symm
  rw [← Functor.map_comp]
  erw [InjectiveResolution.Hom.ι'_comp_hom' (C := Sheaf AddCommGrpCat.{u} X) β]
  rw [Functor.map_comp]

/-- Supported homology makes the actual resolution-comparison square commute. -/
@[reassoc]
theorem moduleAdditiveResolutionHomologyMap_naturality
    (Z : Closeds X) (U : Opens X)
    {M N : SheafOfModules.{u} R} {a : M ⟶ N}
    {I : InjectiveResolution M} {I' : InjectiveResolution N}
    {J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M)}
    {J' : InjectiveResolution ((SheafOfModules.toSheaf R).obj N)}
    (α : InjectiveResolution.Hom I I' a)
    (β : InjectiveResolution.Hom J J' ((SheafOfModules.toSheaf R).map a)) (n : ℤ) :
    homologyMap
      (((SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map α.hom') n ≫
      homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (moduleAdditiveResolutionCompare R I' J')) n =
    homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (moduleAdditiveResolutionCompare R I J)) n ≫
      homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex
        (ComplexShape.up ℤ)).map β.hom') n := by
  have h := ((ExposeI.gammaZSectionsFunctor Z U).mapHomotopy
    (moduleAdditiveResolutionCompareHomotopy R α β)).homologyMap_eq n
  simp only [Functor.map_comp, homologyMap_comp] at h
  exact h

/-- The original resolution-based supported-cohomology isomorphisms commute
with every coefficient map, for arbitrary choices of the four resolutions. -/
@[reassoc]
theorem moduleAdditiveResolutionHomologyIso_naturality
    (Z : Closeds X) (U : Opens X)
    {M N : SheafOfModules.{u} R} (a : M ⟶ N)
    (I : InjectiveResolution M) (I' : InjectiveResolution N)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (J' : InjectiveResolution ((SheafOfModules.toSheaf R).obj N)) (n : ℕ) :
    ((SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U).rightDerived n).map a ≫
        (moduleAdditiveResolutionHomologyIso R Z U I' J' n).hom =
      (moduleAdditiveResolutionHomologyIso R Z U I J n).hom ≫
        (ExposeI.derivedGammaZSections Z U n).map ((SheafOfModules.toSheaf R).map a) := by
  let α : InjectiveResolution.Hom I I' a :=
    ⟨InjectiveResolution.desc a I' I, InjectiveResolution.desc_commutes_zero a I' I⟩
  let β : InjectiveResolution.Hom J J' ((SheafOfModules.toSheaf R).map a) :=
    ⟨InjectiveResolution.desc ((SheafOfModules.toSheaf R).map a) J' J,
      InjectiveResolution.desc_commutes_zero ((SheafOfModules.toSheaf R).map a) J' J⟩
  have hα := ExposeI.injectiveResolutionIntHomologyIso_naturality
    (SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U)
    a I I' α.hom α.ι_f_zero_comp_hom_f_zero n
  have hβ := ExposeI.injectiveResolutionIntHomologyIso_naturality
    (ExposeI.gammaZSectionsFunctor Z U) ((SheafOfModules.toSheaf R).map a)
    J J' β.hom β.ι_f_zero_comp_hom_f_zero n
  have hc := moduleAdditiveResolutionHomologyMap_naturality R Z U α β (n : ℤ)
  apply (cancel_epi (ExposeI.injectiveResolutionIntHomologyIso
    (SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U) I n).hom).mp
  dsimp only [moduleAdditiveResolutionHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [← Category.assoc]
  rw [← hα]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  erw [hc]
  rw [Category.assoc]
  erw [hβ]
  rfl

/-- The existing flasque-resolution comparisons form a natural isomorphism. -/
def moduleAdditiveResolutionHomologyNatIso (Z : Closeds X) (U : Opens X) (n : ℕ) :
    (SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U).rightDerived n ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.derivedGammaZSections Z U n :=
  NatIso.ofComponents
    (fun M ↦ moduleAdditiveResolutionHomologyIso R Z U (injectiveResolution M)
      (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) n)
    (fun a ↦ moduleAdditiveResolutionHomologyIso_naturality R Z U a _ _ _ _ n)

/-- Forgetting scalars in module-supported cohomology agrees naturally, in every
degree and on every open, with the original additive-sheaf supported cohomology. -/
def derivedModuleGammaZSectionsForgetIso (Z : Closeds X) (U : Opens X) (n : ℕ) :
    derivedModuleGammaZSections R Z U n ⋙
        forget₂ (ModuleCat (R.obj.obj (op U))) AddCommGrpCat ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.derivedGammaZSections Z U n :=
  (ExposeI.rightDerivedPostcomposeIso (moduleGammaZSectionsFunctor R Z U)
    (forget₂ _ AddCommGrpCat) n).symm ≪≫
    ExposeI.rightDerivedFunctorIso (moduleGammaZSectionsForgetIso R Z U) n ≪≫
    moduleAdditiveResolutionHomologyNatIso R Z U n

/-- The natural comparison retains exactly the previously constructed objectwise maps. -/
@[simp]
theorem derivedModuleGammaZSectionsForgetIso_app (Z : Closeds X) (U : Opens X)
    (n : ℕ) (M : SheafOfModules.{u} R) :
    (derivedModuleGammaZSectionsForgetIso R Z U n).app M =
      derivedModuleGammaZSectionsObjForgetIso R Z U M n := rfl

/-- Naturality for the original, unchanged objectwise module-to-additive comparison. -/
@[reassoc]
theorem derivedModuleGammaZSectionsObjForgetIso_naturality
    (Z : Closeds X) (U : Opens X) (n : ℕ)
    {M N : SheafOfModules.{u} R} (a : M ⟶ N) :
    (forget₂ (ModuleCat (R.obj.obj (op U))) AddCommGrpCat).map
        ((derivedModuleGammaZSections R Z U n).map a) ≫
          (derivedModuleGammaZSectionsObjForgetIso R Z U N n).hom =
      (derivedModuleGammaZSectionsObjForgetIso R Z U M n).hom ≫
        (ExposeI.derivedGammaZSections Z U n).map ((SheafOfModules.toSheaf R).map a) :=
  (derivedModuleGammaZSectionsForgetIso R Z U n).hom.naturality a

/-- Global module-supported cohomology naturally recovers the preexisting Ext-defined `H_Z`. -/
def derivedModuleGammaZSectionsIsoH_Z (Z : Closeds X) (n : ℕ) :
    derivedModuleGammaZSections R Z ⊤ n ⋙
        forget₂ (ModuleCat (R.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat ≅
      SheafOfModules.toSheaf R ⋙ Abelian.extFunctorObj (ExposeI.zZX_closed Z) n :=
  derivedModuleGammaZSectionsForgetIso R Z ⊤ n ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.toSheaf R) (ExposeI.derivedGammaZSectionsIsoH_Z Z n)

/-- The natural global comparison is the original objectwise comparison with `H_Z`. -/
@[simp]
theorem derivedModuleGammaZSectionsIsoH_Z_app (Z : Closeds X)
    (n : ℕ) (M : SheafOfModules.{u} R) :
    (derivedModuleGammaZSectionsIsoH_Z R Z n).app M =
      derivedModuleGammaZSectionsObjIsoH_Z R Z M n := rfl

/-- The original module-derived and Ext-defined coefficient maps commute in all degrees. -/
@[reassoc]
theorem derivedModuleGammaZSectionsObjIsoH_Z_naturality
    (Z : Closeds X) (n : ℕ) {M N : SheafOfModules.{u} R} (a : M ⟶ N) :
    (forget₂ (ModuleCat (R.obj.obj (op (⊤ : Opens X)))) AddCommGrpCat).map
        ((derivedModuleGammaZSections R Z ⊤ n).map a) ≫
          (derivedModuleGammaZSectionsObjIsoH_Z R Z N n).hom =
      (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).hom ≫
        AddCommGrpCat.ofHom (ExposeI.H_Z_map Z ((SheafOfModules.toSheaf R).map a) n) :=
  (derivedModuleGammaZSectionsIsoH_Z R Z n).hom.naturality a

end SGA.SGA2.ExposeV
