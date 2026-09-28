/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.RingedModuleExactForget
import SGA.SGA2.ExposeI.DerivedSupportedSections

/-!
# SGA 2, V.3.2: supported sections as modules

For an arbitrary sheaf of rings `R`, sections of an `R`-module sheaf over an
open `U` supported in a closed set form an actual `R(U)`-submodule. The
coefficient maps are linear, and forgetting scalars recovers the supported
sections of Exposé I, naturally. In particular this functor is left exact.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat
open TopCat.Sheaf (IsFlasque)

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The submodule of sections on `U` vanishing on the complement of the support. -/
def moduleGammaZSections (Z : Closeds X) (U : Opens X) (M : SheafOfModules.{u} R) :
    Submodule (R.obj.obj (op U)) (M.val.obj (op U)) :=
  (M.val.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op).hom.ker

@[simp]
theorem mem_moduleGammaZSections_iff (Z : Closeds X) (U : Opens X)
    (M : SheafOfModules.{u} R) (s : M.val.obj (op U)) :
    s ∈ moduleGammaZSections R Z U M ↔
      M.val.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op s = 0 := Iff.rfl

/-- The underlying additive subgroup is the original supported-section subgroup. -/
theorem moduleGammaZSections_toAddSubgroup (Z : Closeds X) (U : Opens X)
    (M : SheafOfModules.{u} R) :
    (moduleGammaZSections R Z U M).toAddSubgroup =
      ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj M) Z U := rfl

/-- Coefficient morphisms induce linear maps on supported sections. -/
def moduleGammaZSectionsMap {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    (Z : Closeds X) (U : Opens X) :
    moduleGammaZSections R Z U M →ₗ[R.obj.obj (op U)] moduleGammaZSections R Z U N where
  toFun s := ⟨φ.val.app (op U) s.val,
    ExposeI.map_mem_gammaZSections _ ((SheafOfModules.toSheaf R).map φ) s.property⟩
  map_add' s t := Subtype.ext (map_add _ s.val t.val)
  map_smul' r s := Subtype.ext ((φ.val.app (op U)).hom.map_smul r s.val)

@[simp]
theorem moduleGammaZSectionsMap_apply {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    (Z : Closeds X) (U : Opens X) (s : moduleGammaZSections R Z U M) :
    (moduleGammaZSectionsMap R φ Z U s).val = φ.val.app (op U) s.val := rfl

/-- Supported sections on `U`, with their actual `R(U)`-module structure. -/
def moduleGammaZSectionsFunctor (Z : Closeds X) (U : Opens X) :
    SheafOfModules.{u} R ⥤ ModuleCat.{u} (R.obj.obj (op U)) where
  obj M := ModuleCat.of _ (moduleGammaZSections R Z U M)
  map φ := ModuleCat.ofHom (moduleGammaZSectionsMap R φ Z U)
  map_id _ := by ext s; rfl
  map_comp _ _ := by ext s; rfl

instance (Z : Closeds X) (U : Opens X) :
    (moduleGammaZSectionsFunctor R Z U).Additive where
  map_add := by intros; ext s; rfl

/-- Supported sections of the underlying additive sheaf are additive in coefficients. -/
instance moduleUnderlyingSupportedSections_additive (Z : Closeds X) (U : Opens X) :
    (SheafOfModules.toSheaf.{u} R ⋙ ExposeI.gammaZSectionsFunctor Z U).Additive := by
  have : (SheafOfModules.toSheaf.{u} R).Additive := inferInstance
  have : (ExposeI.gammaZSectionsFunctor Z U).Additive := inferInstance
  infer_instance

/-- Forgetting scalars recovers the original supported-section functor of Exposé I. -/
def moduleGammaZSectionsForgetIso (Z : Closeds X) (U : Opens X) :
    moduleGammaZSectionsFunctor R Z U ⋙ forget₂ _ AddCommGrpCat ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsFunctor Z U :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The module-valued supported-section functor is left exact. -/
instance moduleGammaZSectionsFunctor_preservesFiniteLimits (Z : Closeds X) (U : Opens X) :
    PreservesFiniteLimits (moduleGammaZSectionsFunctor R Z U) := by
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) := inferInstance
  have : PreservesFiniteLimits (ExposeI.gammaZSectionsFunctor Z U) := inferInstance
  have : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} R ⋙ ExposeI.gammaZSectionsFunctor Z U) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits
      (moduleGammaZSectionsFunctor R Z U ⋙ forget₂ _ AddCommGrpCat) :=
    preservesFiniteLimits_of_natIso (moduleGammaZSectionsForgetIso R Z U).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleGammaZSectionsFunctor R Z U) (forget₂ _ AddCommGrpCat)

/-- Supported sections of a short exact sequence with flasque kernel remain
short exact as modules, not just as additive groups. -/
theorem moduleGammaZSectionsFunctor_map_shortExact
    {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact)
    [IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] (Z : Closeds X) (U : Opens X) :
    (S.map (moduleGammaZSectionsFunctor R Z U)).ShortExact := by
  have : ExposeI.IsFlasque (S.map (SheafOfModules.toSheaf R)).X₁ :=
    ‹IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (moduleGammaZSectionsFunctor R Z U)).mp inferInstance S hS
  refine { exact := hleft.1, mono_f := hleft.2, epi_g := ?_ }
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact ExposeI.surjective_gammaZSectionsMap_of_shortExact
    (moduleToSheaf_map_shortExact R hS) Z U

end SGA.SGA2.ExposeV
