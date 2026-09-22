/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleSupportedHom
import SGA.SGA2.ExposeVI.ModuleOpenSubpresheaf
import SGA.SGA2.ExposeI.ClosedSupportHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# The structure module supported on a closed subset

Before sheafification, extend the structure module on the open complement
by zero: its sections are all scalars on opens contained in the complement,
and zero on other opens. The cokernel of its inclusion into the structure
module, followed by sheafification, is the closed support module. Its Hom
representation of actual supported sections is proved from this presentation.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Membership in an open subpresheaf is the explicit zero-or-open relation. -/
theorem moduleOpenSubpresheaf_mem_iff (F : PresheafOfModules.{u} R.obj) (U : Opens X)
    (V : (Opens X)ᵒᵖ) (x : F.obj V) :
    x ∈ (moduleOpenSubpresheaf F U).obj V ↔ x = 0 ∨ V.unop ≤ U := by
  classical
  by_cases h : V.unop ≤ U <;> simp [moduleOpenSubpresheaf, h]

/-- The presheaf extension by zero of the structure module on an open. -/
def moduleOpenStructureSubpresheaf (U : Opens X) :
    (PresheafOfModules.unit R.obj).Submodule :=
  moduleOpenSubpresheaf (PresheafOfModules.unit R.obj) U

/-- The actual closed-support structure-module presentation before sheafification. -/
def moduleClosedSupportPresheaf (Z : Closeds X) : PresheafOfModules.{u} R.obj :=
  cokernel (moduleOpenStructureSubpresheaf R Z.compl).ι

/-- The closed support module `O_(X,Z)`, defined by its extension-by-zero presentation. -/
def moduleClosedSupport (Z : Closeds X) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (moduleClosedSupportPresheaf R Z)

/-- The structure-module map determined by a global section. -/
def moduleUnitMapOfSection (G : SheafOfModules.{u} R) (s : G.val.obj (op (⊤ : Opens X))) :
    PresheafOfModules.unit R.obj ⟶ G.val where
  app U := ModuleCat.ofHom
    { toFun r := r • G.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s
      map_add' r t := add_smul _ _ _
      map_smul' r t := mul_smul _ _ _ }
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    change R.obj.map i r • G.val.map (homOfLE (le_top : V.unop ≤ ⊤)).op s =
      G.val.map i (r • G.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s)
    rw [G.val.map_smul, ← G.val.map_comp_apply]
    rfl

/-- Evaluation at one recovers the section used to construct the structure-module map. -/
@[simp]
theorem moduleUnitMapOfSection_apply_one (G : SheafOfModules.{u} R)
    (s : G.val.obj (op (⊤ : Opens X))) :
    ((moduleUnitMapOfSection R G s).app (op ⊤)).hom (1 : R.obj.obj (op ⊤)) = s := by
  dsimp [moduleUnitMapOfSection]
  rw [one_smul]
  exact ConcreteCategory.congr_hom (G.val.presheaf.map_id (op ⊤)) s

/-- A structure-module morphism is determined by its global value at one. -/
theorem moduleUnitMapOfSection_eval_one (G : SheafOfModules.{u} R)
    (φ : PresheafOfModules.unit R.obj ⟶ G.val) :
    moduleUnitMapOfSection R G (φ.app (op ⊤) (1 : R.obj.obj (op ⊤))) = φ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r • G.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op
    (φ.app (op ⊤) (1 : R.obj.obj (op ⊤))) = φ.app U r
  rw [← PresheafOfModules.naturality_apply]
  have h : (PresheafOfModules.unit R.obj).map
      (homOfLE (le_top : U.unop ≤ ⊤)).op (1 : R.obj.obj (op ⊤)) =
        (1 : R.obj.obj U) := PresheafOfModules.unit_map_one R.obj _
  rw [h, ← (φ.app U).hom.map_smul]
  change φ.app U ((show R.obj.obj U from r) * 1) = φ.app U r
  rw [mul_one]

/-- A supported section kills the open-complement subpresheaf. -/
theorem moduleUnitMapOfSupportedSection_kills_complement (Z : Closeds X)
    (G : SheafOfModules.{u} R)
    (s : ExposeI.gammaZ ((SheafOfModules.toSheaf R).obj G) Z) :
    (moduleOpenStructureSubpresheaf R Z.compl).ι ≫ moduleUnitMapOfSection R G s.val = 0 := by
  ext U r
  change r.val • G.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s.val = 0
  rcases (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp r.property with hr | hU
  · rw [hr, zero_smul]
  · rw [show G.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op s.val = 0 from
      ExposeI.supportedSection_restrict_eq_zero ((SheafOfModules.toSheaf R).obj G) Z s hU,
      smul_zero]

/-- A supported section induces a morphism out of the constructed support module. -/
def moduleClosedSupportHomOfSection (Z : Closeds X) (G : SheafOfModules.{u} R)
    (s : ExposeI.gammaZ ((SheafOfModules.toSheaf R).obj G) Z) :
    moduleClosedSupport R Z ⟶ G :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (cokernel.desc (moduleOpenStructureSubpresheaf R Z.compl).ι
      (moduleUnitMapOfSection R G s.val)
      (moduleUnitMapOfSupportedSection_kills_complement R Z G s))

/-- A map out of the actual support presentation yields a supported section. -/
def moduleClosedSupportSectionOfHom (Z : Closeds X) (G : SheafOfModules.{u} R)
    (φ : moduleClosedSupport R Z ⟶ G) :
    ExposeI.gammaZ ((SheafOfModules.toSheaf R).obj G) Z := by
  let f : moduleClosedSupportPresheaf R Z ⟶ G.val :=
    PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ
  let g : PresheafOfModules.unit R.obj ⟶ G.val :=
    cokernel.π (moduleOpenStructureSubpresheaf R Z.compl).ι ≫ f
  refine ⟨g.app (op ⊤) (1 : R.obj.obj (op ⊤)), ?_⟩
  change G.val.map (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ Z.compl ≤ ⊤)).op
    (g.app (op ⊤) (1 : R.obj.obj (op ⊤))) = 0
  rw [← PresheafOfModules.naturality_apply]
  have h1 : (PresheafOfModules.unit R.obj).map
      (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ Z.compl ≤ ⊤)).op
        (1 : R.obj.obj (op ⊤)) = (1 : R.obj.obj (op ((⊤ : Opens X) ⊓ Z.compl))) :=
    PresheafOfModules.unit_map_one R.obj _
  rw [h1]
  have h := cokernel.condition_assoc (moduleOpenStructureSubpresheaf R Z.compl).ι f
  rw [zero_comp] at h
  exact congrArg (fun a ↦ a.app (op ((⊤ : Opens X) ⊓ Z.compl))
    (⟨(1 : R.obj.obj (op ((⊤ : Opens X) ⊓ Z.compl))),
      mem_moduleOpenSubpresheaf _ _ inf_le_right _⟩ :
      (moduleOpenStructureSubpresheaf R Z.compl).obj
        (op ((⊤ : Opens X) ⊓ Z.compl)))) h

/-- The Hom representation of supported sections for the constructed module support object. -/
def moduleClosedSupportHomEquiv (Z : Closeds X) (G : SheafOfModules.{u} R) :
    (moduleClosedSupport R Z ⟶ G) ≃+
      ExposeI.gammaZ ((SheafOfModules.toSheaf R).obj G) Z where
  toFun := moduleClosedSupportSectionOfHom R Z G
  invFun := moduleClosedSupportHomOfSection R Z G
  left_inv φ := by
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective
    apply (cancel_epi (cokernel.π (moduleOpenStructureSubpresheaf R Z.compl).ι)).mp
    change cokernel.π (moduleOpenStructureSubpresheaf R Z.compl).ι ≫
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj))
          ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm _) = _
    rw [Equiv.apply_symm_apply, cokernel.π_desc]
    exact moduleUnitMapOfSection_eval_one R G _
  right_inv s := by
    apply Subtype.ext
    change ((cokernel.π (moduleOpenStructureSubpresheaf R Z.compl).ι ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj))
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm _)).app (op ⊤))
          (1 : R.obj.obj (op ⊤)) = s.val
    rw [Equiv.apply_symm_apply, cokernel.π_desc]
    exact moduleUnitMapOfSection_apply_one R G s.val
  map_add' φ ψ := by
    apply Subtype.ext
    rfl

/-- The support Hom representation respects the original coefficient maps. -/
theorem moduleClosedSupportHomEquiv_naturality (Z : Closeds X)
    {G H : SheafOfModules.{u} R} (a : G ⟶ H) (φ : moduleClosedSupport R Z ⟶ G) :
    moduleClosedSupportHomEquiv R Z H (φ ≫ a) =
      ExposeI.gammaZSectionsMap ((SheafOfModules.toSheaf R).map a) Z ⊤
        (moduleClosedSupportHomEquiv R Z G φ) := by
  apply Subtype.ext
  rfl

end SGA.SGA2.ExposeVI
