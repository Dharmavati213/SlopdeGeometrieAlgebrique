/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ModuleComplexScalarHomology
import SGA.SGA2.ExposeI.NaturalTransformationCohomology

/-!
# Actual scalar actions through the original supported-cohomology comparison

Scalar endomorphisms of the underlying additive module resolution retain its
augmentation. Their comparison with additive-injective resolution maps is a
genuine cochain homotopy. Thus the original supported-cohomology comparison,
not a transported replacement, retains the structure-ring scalar action.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

local instance cohomologyScalarsHasDerivedCategory :
    HasDerivedCategory.{u + 1} (Sheaf AddCommGrpCat.{u} X) :=
  HasDerivedCategory.standard _

local instance cohomologyScalarsResolutionKInjective
    {F : Sheaf AddCommGrpCat.{u} X} (J : InjectiveResolution F) :
    J.cochainComplex.IsKInjective := by
  dsimp [InjectiveResolution.cochainComplex]
  infer_instance

/-- The original additive augmentation intertwines global scalar multiplication. -/
@[reassoc]
theorem moduleUnderlyingResolutionι_scalar {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M) (r : R.obj.obj (op (⊤ : Opens X))) :
    moduleUnderlyingResolutionι R I ≫ moduleUnderlyingComplexGlobalScalar R I.cochainComplex r =
      (CochainComplex.singleFunctor (Sheaf AddCommGrpCat.{u} X) 0).map
        (moduleUnderlyingGlobalScalarHom R M r) ≫ moduleUnderlyingResolutionι R I := by
  dsimp only [moduleUnderlyingResolutionι, moduleUnderlyingComplexGlobalScalar]
  rw [Category.assoc]
  erw [((moduleUnderlyingGlobalScalar R r).mapHomologicalComplex
    (ComplexShape.up ℤ)).naturality I.ι']
  rw [← Category.assoc]
  erw [← ExposeI.singleMapHomologicalComplex_natTrans (moduleUnderlyingGlobalScalar R r)
    (ComplexShape.up ℤ) 0 M]
  rfl

/-- The original resolution comparison retains scalar maps up to actual cochain homotopy. -/
def moduleAdditiveResolutionCompareScalarHomotopy {M : SheafOfModules.{u} R}
    (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (r : R.obj.obj (op (⊤ : Opens X)))
    (β : InjectiveResolution.Hom J J (moduleUnderlyingGlobalScalarHom R M r)) :
    Homotopy
      (moduleUnderlyingComplexGlobalScalar R I.cochainComplex r ≫
        moduleAdditiveResolutionCompare R I J)
      (moduleAdditiveResolutionCompare R I J ≫ β.hom') := by
  apply ExposeI.homotopyOfQMapEq.{u + 1, u, u + 1} (C := Sheaf AddCommGrpCat.{u} X)
  simp only [Functor.map_comp, Q_map_moduleAdditiveResolutionCompare]
  apply (cancel_epi (DerivedCategory.Q.map (moduleUnderlyingResolutionι R I))).mp
  rw [← Category.assoc, ← Functor.map_comp, moduleUnderlyingResolutionι_scalar,
    Functor.map_comp]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  symm
  rw [← Functor.map_comp]
  erw [InjectiveResolution.Hom.ι'_comp_hom' (C := Sheaf AddCommGrpCat.{u} X) β]
  rw [Functor.map_comp]

/-- Supported homology turns the scalar comparison homotopy into the original commuting square. -/
@[reassoc]
theorem moduleAdditiveResolutionHomologyMap_scalar (Z : Closeds X) (U : Opens X)
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (r : R.obj.obj (op (⊤ : Opens X)))
    (β : InjectiveResolution.Hom J J (moduleUnderlyingGlobalScalarHom R M r)) (n : ℤ) :
    homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex _).map
      (moduleUnderlyingComplexGlobalScalar R I.cochainComplex r)) n ≫
        homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex _).map
          (moduleAdditiveResolutionCompare R I J)) n =
      homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex _).map
        (moduleAdditiveResolutionCompare R I J)) n ≫
          homologyMap (((ExposeI.gammaZSectionsFunctor Z U).mapHomologicalComplex _).map
            β.hom') n := by
  have h := ((ExposeI.gammaZSectionsFunctor Z U).mapHomotopy
    (moduleAdditiveResolutionCompareScalarHomotopy R I J r β)).homologyMap_eq n
  simp only [Functor.map_comp, homologyMap_comp] at h
  exact h

/-- The original flasque-resolution isomorphism retains scalar natural transformations. -/
@[reassoc]
theorem moduleAdditiveResolutionHomologyIso_scalar (Z : Closeds X) (U : Opens X)
    {M : SheafOfModules.{u} R} (I : InjectiveResolution M)
    (J : InjectiveResolution ((SheafOfModules.toSheaf R).obj M))
    (r : R.obj.obj (op (⊤ : Opens X))) (n : ℕ) :
    ((Functor.whiskerRight (moduleUnderlyingGlobalScalar R r)
        (ExposeI.gammaZSectionsFunctor Z U)).rightDerived n).app M ≫
        (moduleAdditiveResolutionHomologyIso R Z U I J n).hom =
      (moduleAdditiveResolutionHomologyIso R Z U I J n).hom ≫
        (ExposeI.derivedGammaZSections Z U n).map (moduleUnderlyingGlobalScalarHom R M r) := by
  let a := moduleUnderlyingGlobalScalarHom R M r
  let β : InjectiveResolution.Hom J J a :=
    ⟨InjectiveResolution.desc a J J, InjectiveResolution.desc_commutes_zero a J J⟩
  have hI := ExposeI.injectiveResolutionIntHomologyIso_natTrans
    (Functor.whiskerRight (moduleUnderlyingGlobalScalar R r)
      (ExposeI.gammaZSectionsFunctor Z U)) I n
  have hJ := ExposeI.injectiveResolutionIntHomologyIso_naturality
    (ExposeI.gammaZSectionsFunctor Z U) a J J β.hom β.ι_f_zero_comp_hom_f_zero n
  have hc := moduleAdditiveResolutionHomologyMap_scalar R Z U I J r β (n : ℤ)
  apply (cancel_epi (ExposeI.injectiveResolutionIntHomologyIso
    (SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U) I n).hom).mp
  dsimp only [moduleAdditiveResolutionHomologyIso, Iso.trans_hom, Iso.symm_hom, asIso_hom]
  simp only [← Category.assoc]
  rw [← hI]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc]
  erw [hc]
  rw [Category.assoc]
  erw [hJ]
  rfl

/-- The supported-section forgetful isomorphism intertwines the actual global scalar maps. -/
@[reassoc]
theorem moduleGammaZSectionsForgetIso_scalar (Z : Closeds X)
    (r : R.obj.obj (op (⊤ : Opens X))) :
    Functor.whiskerLeft (moduleGammaZSectionsFunctor R Z ⊤)
        (ModuleCat.smulNatTrans (R.obj.obj (op (⊤ : Opens X))) r) ≫
        (moduleGammaZSectionsForgetIso R Z ⊤).hom =
      (moduleGammaZSectionsForgetIso R Z ⊤).hom ≫
        Functor.whiskerRight (moduleUnderlyingGlobalScalar R r)
          (ExposeI.gammaZSectionsFunctor Z ⊤) := by
  apply NatTrans.ext
  funext M
  ext x
  apply Subtype.ext
  let y : M.val.obj (op (⊤ : Opens X)) := x.val
  change r • y = R.obj.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op r • y
  rw [show (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op = 𝟙 (op ⊤) from Subsingleton.elim _ _,
    R.obj.map_id]
  rfl

/-- The original module-to-additive derived supported-cohomology comparison retains scalars. -/
@[reassoc]
theorem derivedModuleGammaZSectionsObjForgetIso_scalar (Z : Closeds X)
    (M : SheafOfModules.{u} R) (r : R.obj.obj (op (⊤ : Opens X))) (n : ℕ) :
    ((derivedModuleGammaZSections R Z ⊤ n).obj M).smul r ≫
        (derivedModuleGammaZSectionsObjForgetIso R Z ⊤ M n).hom =
      (derivedModuleGammaZSectionsObjForgetIso R Z ⊤ M n).hom ≫
        (ExposeI.derivedGammaZSections Z ⊤ n).map (moduleUnderlyingGlobalScalarHom R M r) := by
  let P := (ExposeI.rightDerivedPostcomposeIso (moduleGammaZSectionsFunctor R Z ⊤)
    (forget₂ _ AddCommGrpCat) n).app M
  have hP := ExposeI.rightDerivedPostcomposeIso_natTrans
    (moduleGammaZSectionsFunctor R Z ⊤)
    (ModuleCat.smulNatTrans (R.obj.obj (op (⊤ : Opens X))) r) M n
  have hE := congrArg (fun τ ↦ (τ.rightDerived n).app M)
    (moduleGammaZSectionsForgetIso_scalar R Z r)
  simp only [NatTrans.rightDerived_comp, NatTrans.comp_app] at hE
  have hC := moduleAdditiveResolutionHomologyIso_scalar R Z ⊤
    (injectiveResolution M) (injectiveResolution ((SheafOfModules.toSheaf R).obj M)) r n
  apply (cancel_epi P.hom).mp
  dsimp only [derivedModuleGammaZSectionsObjForgetIso, Iso.trans_hom, Iso.symm_hom,
    Iso.app_inv, Iso.app_hom]
  simp only [Category.assoc]
  change P.hom ≫ ((derivedModuleGammaZSections R Z ⊤ n).obj M).smul r ≫
      P.inv ≫ _ = P.hom ≫ P.inv ≫ _
  erw [← Category.assoc, ← hP]
  simp only [P, Iso.app_hom, Iso.app_inv, Category.assoc, Iso.hom_inv_id_app_assoc]
  change _ ≫ (ExposeI.rightDerivedFunctorIso (moduleGammaZSectionsForgetIso R Z ⊤) n).hom.app M ≫
      _ = _
  erw [← Category.assoc, hE, Category.assoc, hC]
  rfl

/-- The unchanged comparison to preexisting Ext-defined supported cohomology respects scalars. -/
@[reassoc]
theorem derivedModuleGammaZSectionsObjIsoH_Z_scalar (Z : Closeds X)
    (M : SheafOfModules.{u} R) (r : R.obj.obj (op (⊤ : Opens X))) (n : ℕ) :
    ((derivedModuleGammaZSections R Z ⊤ n).obj M).smul r ≫
        (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).hom =
      (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).hom ≫
        AddCommGrpCat.ofHom (ExposeI.H_Z_map Z (moduleUnderlyingGlobalScalarHom R M r) n) := by
  dsimp only [derivedModuleGammaZSectionsObjIsoH_Z, Iso.trans_hom]
  rw [derivedModuleGammaZSectionsObjForgetIso_scalar_assoc]
  erw [(ExposeI.derivedGammaZSectionsIsoH_Z Z n).hom.naturality
    (moduleUnderlyingGlobalScalarHom R M r)]
  rfl

theorem derivedModuleGammaZSectionsObjIsoH_Z_scalar_apply (Z : Closeds X)
    (M : SheafOfModules.{u} R) (r : R.obj.obj (op (⊤ : Opens X))) (n : ℕ)
    (x : (derivedModuleGammaZSections R Z ⊤ n).obj M) :
    (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).hom
        (r • x : (derivedModuleGammaZSections R Z ⊤ n).obj M) =
      ExposeI.H_Z_map Z (moduleUnderlyingGlobalScalarHom R M r) n
        ((derivedModuleGammaZSectionsObjIsoH_Z R Z M n).hom x) := by
  have h := ConcreteCategory.congr_hom (derivedModuleGammaZSectionsObjIsoH_Z_scalar R Z M r n) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

/-- The inverse of the original supported-cohomology comparison retains scalars. -/
@[reassoc]
theorem derivedModuleGammaZSectionsObjIsoH_Z_inv_scalar (Z : Closeds X)
    (M : SheafOfModules.{u} R) (r : R.obj.obj (op (⊤ : Opens X))) (n : ℕ) :
    AddCommGrpCat.ofHom (ExposeI.H_Z_map Z (moduleUnderlyingGlobalScalarHom R M r) n) ≫
        (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).inv =
      (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).inv ≫
        ((derivedModuleGammaZSections R Z ⊤ n).obj M).smul r := by
  rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp]
  exact (derivedModuleGammaZSectionsObjIsoH_Z_scalar R Z M r n).symm

theorem derivedModuleGammaZSectionsObjIsoH_Z_inv_scalar_apply (Z : Closeds X)
    (M : SheafOfModules.{u} R) (r : R.obj.obj (op (⊤ : Opens X))) (n : ℕ)
    (x : ExposeI.H_Z Z ((SheafOfModules.toSheaf R).obj M) n) :
    (derivedModuleGammaZSectionsObjIsoH_Z R Z M n).inv
        (ExposeI.H_Z_map Z (moduleUnderlyingGlobalScalarHom R M r) n x) =
      (AddCommGrpCat.Hom.hom (((derivedModuleGammaZSections R Z ⊤ n).obj M).smul r))
        ((derivedModuleGammaZSectionsObjIsoH_Z R Z M n).inv x) := by
  have h := ConcreteCategory.congr_hom
    (derivedModuleGammaZSectionsObjIsoH_Z_inv_scalar R Z M r n) x
  simp only [ConcreteCategory.comp_apply] at h
  exact h

end SGA.SGA2.ExposeV
