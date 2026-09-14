/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.RingedModuleSupportedSections
import SGA.SGA2.ExposeI.SupportedSheafSections

/-!
# The actual module sheaf of sections supported in a closed subset

The section modules are the original restriction kernels. Their sheaf condition
comes from the proved comparison with the additive supported-section sheaf.
This supplies the coefficient module sheaf in VI.1.4.3.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The original supported-section presheaf with its actual local module structures. -/
def moduleGammaZPresheaf (Z : Closeds X) (M : SheafOfModules.{u} R) :
    PresheafOfModules.{u} R.obj := by
  let P := ExposeI.gammaZSectionsPresheaf ((SheafOfModules.toSheaf R).obj M) Z
  let (U : (Opens X)ᵒᵖ) : Module (R.obj.obj U) (P.obj U) :=
    inferInstanceAs (Module (R.obj.obj U) (ExposeV.moduleGammaZSections R Z U.unop M))
  exact PresheafOfModules.ofPresheaf P (fun {U V} i r s ↦
    Subtype.ext (M.val.map_smul i r s.val))

/-- Forgetting the module structures gives exactly the concrete supported-section presheaf. -/
def moduleGammaZPresheafForgetIso (Z : Closeds X) (M : SheafOfModules.{u} R) :
    (moduleGammaZPresheaf R Z M).presheaf ≅
      ExposeI.gammaZSectionsPresheaf ((SheafOfModules.toSheaf R).obj M) Z := Iso.refl _

/-- The supported local modules satisfy the sheaf condition. -/
def moduleGammaZSheaf (Z : Closeds X) (M : SheafOfModules.{u} R) :
    SheafOfModules.{u} R where
  val := moduleGammaZPresheaf R Z M
  isSheaf := (Presheaf.isSheaf_of_iso_iff (moduleGammaZPresheafForgetIso R Z M)).mpr
    ((Presheaf.isSheaf_of_iso_iff
      ((ExposeI.underlineGammaZPresheafFunctorIso Z).app ((SheafOfModules.toSheaf R).obj M))).mp
        (ExposeI.underlineGammaZ ((SheafOfModules.toSheaf R).obj M) Z).property)

/-- Coefficient maps act by the original linear maps on supported sections. -/
def moduleGammaZSheafMap (Z : Closeds X) {M N : SheafOfModules.{u} R} (a : M ⟶ N) :
    moduleGammaZSheaf R Z M ⟶ moduleGammaZSheaf R Z N :=
  ⟨PresheafOfModules.homMk
    ((ExposeI.gammaZSectionsPresheafFunctor Z).map ((SheafOfModules.toSheaf R).map a))
      (fun U r s ↦ Subtype.ext ((a.val.app U).hom.map_smul r s.val))⟩

/-- The actual module-valued supported-sheaf coefficient functor. -/
def moduleGammaZSheafFunctor (Z : Closeds X) : SheafOfModules.{u} R ⥤ SheafOfModules.{u} R where
  obj M := moduleGammaZSheaf R Z M
  map a := moduleGammaZSheafMap R Z a
  map_id _ := by ext U s; rfl
  map_comp _ _ := by ext U s; rfl

instance (Z : Closeds X) : (moduleGammaZSheafFunctor R Z).Additive where
  map_add := by intros; ext U s; rfl

/-- Forgetting the support-module structure preserves the actual presheaf comparison. -/
def moduleGammaZSheafPresheafIso (Z : Closeds X) :
    moduleGammaZSheafFunctor R Z ⋙ SheafOfModules.toSheaf R ⋙
        sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.gammaZSectionsPresheafFunctor Z :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- The underlying additive sheaf is naturally the original supported kernel sheaf. -/
def moduleGammaZSheafForgetIso (Z : Closeds X) :
    moduleGammaZSheafFunctor R Z ⋙ SheafOfModules.toSheaf R ≅
      SheafOfModules.toSheaf R ⋙ ExposeI.underlineGammaZFunctor Z :=
  ((fullyFaithfulSheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).whiskeringRight
    (SheafOfModules.{u} R)).preimageIso
      (moduleGammaZSheafPresheafIso R Z ≪≫
        (Functor.isoWhiskerLeft (SheafOfModules.toSheaf R)
          (ExposeI.underlineGammaZPresheafFunctorIso Z)).symm)

/-- The inclusion is the original subtype map on every open. -/
def moduleGammaZSheafι (Z : Closeds X) (M : SheafOfModules.{u} R) :
    moduleGammaZSheaf R Z M ⟶ M :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        (ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj M) Z U.unop).subtype
      naturality := by intros; rfl }
    (by intros; rfl)⟩

/-- The actual supported-sheaf inclusion is natural in the coefficient module. -/
@[reassoc (attr := simp)]
theorem moduleGammaZSheafMap_comp_ι (Z : Closeds X)
    {M N : SheafOfModules.{u} R} (a : M ⟶ N) :
    moduleGammaZSheafMap R Z a ≫ moduleGammaZSheafι R Z N =
      moduleGammaZSheafι R Z M ≫ a := by ext U s; rfl

instance (Z : Closeds X) (M : SheafOfModules.{u} R) : Mono (moduleGammaZSheafι R Z M) := by
  constructor
  intro N a b h
  ext U x
  apply Subtype.ext
  exact ConcreteCategory.congr_hom
    (congrArg (fun f ↦ f.val.app U) h) x

/-- A supported section on an open contained in the complement is zero. -/
theorem moduleGammaZSheaf_section_eq_zero (Z : Closeds X) (M : SheafOfModules.{u} R)
    {U : Opens X} (hU : U ≤ Z.compl) (s : (moduleGammaZSheaf R Z M).val.obj (op U)) :
    s.val = 0 := by
  let i : U ⊓ Z.compl ⟶ U := homOfLE inf_le_left
  have : IsIso i := ⟨homOfLE (le_inf le_rfl hU), by constructor <;> rfl⟩
  let f := ExposeI.restrictToComplement ((SheafOfModules.toSheaf R).obj M) Z U
  have : IsIso f := by
    change IsIso (M.val.presheaf.map i.op)
    infer_instance
  apply ((AddCommGrpCat.mono_iff_injective f).mp inferInstance)
  exact s.property.trans (map_zero f.hom).symm

/-- The actual module-valued supported-sheaf functor is left exact. -/
instance moduleGammaZSheafFunctor_preservesFiniteLimits (Z : Closeds X) :
    PreservesFiniteLimits (moduleGammaZSheafFunctor R Z) := by
  have : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} R) := inferInstance
  have : PreservesFiniteLimits (ExposeI.underlineGammaZFunctor Z) := inferInstance
  have : PreservesFiniteLimits
      (SheafOfModules.toSheaf.{u} R ⋙ ExposeI.underlineGammaZFunctor Z) :=
    comp_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (moduleGammaZSheafFunctor R Z ⋙ SheafOfModules.toSheaf R) :=
    preservesFiniteLimits_of_natIso (moduleGammaZSheafForgetIso R Z).symm
  exact preservesFiniteLimits_of_reflects_of_preserves
    (moduleGammaZSheafFunctor R Z) (SheafOfModules.toSheaf R)

end SGA.SGA2.ExposeVI
