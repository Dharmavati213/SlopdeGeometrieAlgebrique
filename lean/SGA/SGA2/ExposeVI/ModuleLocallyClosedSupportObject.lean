/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleClosedSupportObject
import SGA.SGA2.ExposeI.LocallyClosedSupportInternalHom

/-!
# Structure modules for arbitrary locally closed supports

For an open `U` and closed `Z`, take the sheafification of the cokernel of
the inclusion of the structure presheaf extended by zero from `U ∩ Zᶜ`
into the one extended by zero from `U`. Its morphisms recover the original
sections on `U` supported on `Z`. Applying this to a locally closed witness
constructs its structure support module on the ambient space.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- Inclusions of opens give inclusions of their actual extended structure presheaves. -/
theorem moduleOpenStructureSubpresheaf_le {U V : Opens X} (h : U ≤ V) :
    moduleOpenStructureSubpresheaf R U ≤ moduleOpenStructureSubpresheaf R V := by
  intro W r hr
  exact (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mpr
    (((moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp hr).imp_right (fun hr ↦ hr.trans h))

/-- Evaluation against a section of a module sheaf on the chosen open. -/
def moduleOpenUnitMapApp (U : Opens X) (G : SheafOfModules.{u} R)
    (s : G.val.obj (op U)) (V : (Opens X)ᵒᵖ) :
    (moduleOpenStructureSubpresheaf R U).toPresheafOfModules.obj V ⟶ G.val.obj V := by
  classical
  exact if h : V.unop ≤ U then
    ModuleCat.ofHom
      (X := (moduleOpenStructureSubpresheaf R U).toPresheafOfModules.obj V) (Y := G.val.obj V)
      { toFun r := (show R.obj.obj V from r.val) • G.val.map (homOfLE h).op s
        map_add' r t := add_smul _ _ _
        map_smul' r t := mul_smul _ _ _ }
  else 0

/-- A section on an open gives a map from the actual structure presheaf extended by zero. -/
def moduleOpenUnitMapOfSection (U : Opens X) (G : SheafOfModules.{u} R)
    (s : G.val.obj (op U)) : (moduleOpenStructureSubpresheaf R U).toPresheafOfModules ⟶ G.val where
  app := moduleOpenUnitMapApp R U G s
  naturality {V W} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := (leOfHom i.unop).trans hV
      change moduleOpenUnitMapApp R U G s W
          ((moduleOpenStructureSubpresheaf R U).toPresheafOfModules.map i r) =
        G.val.map i (moduleOpenUnitMapApp R U G s V r)
      dsimp only [moduleOpenUnitMapApp]
      rw [dite_eq_left hV, dite_eq_left hW]
      change R.obj.map i r.val • G.val.map (homOfLE hW).op s =
        G.val.map i (r.val • G.val.map (homOfLE hV).op s)
      rw [G.val.map_smul, ← G.val.map_comp_apply]
      rfl
    · have hr : r = 0 :=
        Subtype.ext (((moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp r.property).resolve_right hV)
      subst r
      simp

/-- Evaluation at one recovers the original section on the open. -/
theorem moduleOpenUnitMapOfSection_apply_one (U : Opens X) (G : SheafOfModules.{u} R)
    (s : G.val.obj (op U)) :
    (moduleOpenUnitMapOfSection R U G s).app (op U)
      (⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩ :
        (moduleOpenStructureSubpresheaf R U).obj (op U)) =
        s := by
  dsimp only [moduleOpenUnitMapOfSection, moduleOpenUnitMapApp]
  rw [dite_eq_left (le_rfl : U ≤ U)]
  dsimp
  rw [one_smul]
  exact ConcreteCategory.congr_hom (G.val.presheaf.map_id (op U)) s

/-- Maps from the extended structure presheaf are determined by their value at one. -/
theorem moduleOpenUnitMapOfSection_eval_one (U : Opens X) (G : SheafOfModules.{u} R)
    (φ : (moduleOpenStructureSubpresheaf R U).toPresheafOfModules ⟶ G.val) :
    moduleOpenUnitMapOfSection R U G
      (φ.app (op U) ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩) = φ := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  by_cases hV : V.unop ≤ U
  · change moduleOpenUnitMapApp R U G
      (φ.app (op U) ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩) V r =
        φ.app V r
    dsimp only [moduleOpenUnitMapApp]
    rw [dite_eq_left hV]
    change r.val • G.val.map (homOfLE hV).op
      (φ.app (op U) ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩) = φ.app V r
    rw [← PresheafOfModules.naturality_apply]
    have h1 : (moduleOpenStructureSubpresheaf R U).toPresheafOfModules.map (homOfLE hV).op
        ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩ =
          (⟨(1 : R.obj.obj V), mem_moduleOpenSubpresheaf _ _ hV _⟩ :
            (moduleOpenStructureSubpresheaf R U).obj V) :=
      Subtype.ext (PresheafOfModules.unit_map_one R.obj _)
    rw [h1, ← (φ.app V).hom.map_smul]
    congr 1
    apply Subtype.ext
    exact mul_one (show R.obj.obj V from r.val)
  · have hr : r = 0 :=
        Subtype.ext (((moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp r.property).resolve_right hV)
    subst r
    simp

/-- The inclusion of the structure presheaf on the part outside the closed support. -/
def moduleRelativeSupportRelation (U : Opens X) (Z : Closeds X) :
    (moduleOpenStructureSubpresheaf R (U ⊓ Z.compl)).toPresheafOfModules ⟶
      (moduleOpenStructureSubpresheaf R U).toPresheafOfModules :=
  PresheafOfModules.Submodule.homOfLE (moduleOpenStructureSubpresheaf_le R inf_le_left)

/-- The support module for a closed subset of a specified ambient open. -/
def moduleRelativeSupport (U : Opens X) (Z : Closeds X) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj (cokernel (moduleRelativeSupportRelation R U Z))

/-- A section supported on `Z` vanishes on every smaller open in the complement. -/
theorem moduleSupportedLocalSection_restrict_eq_zero (U : Opens X) (Z : Closeds X)
    (G : SheafOfModules.{u} R)
    (s : ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj G) Z U)
    {V : Opens X} (hV : V ≤ U ⊓ Z.compl) :
    G.val.map (homOfLE (hV.trans inf_le_left)).op s.val = 0 := by
  have h := congrArg (G.val.map (homOfLE hV).op) s.property
  change G.val.map (homOfLE hV).op
    (G.val.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op s.val) = _ at h
  simpa only [← G.val.map_comp_apply, map_zero, ← op_comp, homOfLE_comp] using h

/-- The local support condition annihilates exactly the presented complement relation. -/
theorem moduleOpenUnitMapOfSupportedSection_kills_relation (U : Opens X) (Z : Closeds X)
    (G : SheafOfModules.{u} R)
    (s : ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj G) Z U) :
    moduleRelativeSupportRelation R U Z ≫ moduleOpenUnitMapOfSection R U G s.val = 0 := by
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  rcases (moduleOpenSubpresheaf_mem_iff R _ _ _ _).mp r.property with hr | hV
  · have hr0 : r = 0 := Subtype.ext hr
    subst r
    simp
  · change moduleOpenUnitMapApp R U G s.val V _ = 0
    dsimp only [moduleOpenUnitMapApp]
    rw [dite_eq_left (hV.trans inf_le_left)]
    change r.val • G.val.map (homOfLE (hV.trans inf_le_left)).op s.val = 0
    rw [moduleSupportedLocalSection_restrict_eq_zero R U Z G s hV, smul_zero]

/-- A local supported section gives a morphism from the presented support module. -/
def moduleRelativeSupportHomOfSection (U : Opens X) (Z : Closeds X)
    (G : SheafOfModules.{u} R)
    (s : ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj G) Z U) :
    moduleRelativeSupport R U Z ⟶ G :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm
    (cokernel.desc (moduleRelativeSupportRelation R U Z) (moduleOpenUnitMapOfSection R U G s.val)
      (moduleOpenUnitMapOfSupportedSection_kills_relation R U Z G s))

/-- Evaluation at one turns a support-object morphism into an actual local supported section. -/
def moduleRelativeSupportSectionOfHom (U : Opens X) (Z : Closeds X)
    (G : SheafOfModules.{u} R) (φ : moduleRelativeSupport R U Z ⟶ G) :
    ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj G) Z U := by
  let f : cokernel (moduleRelativeSupportRelation R U Z) ⟶ G.val :=
    PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) φ
  let g := cokernel.π (moduleRelativeSupportRelation R U Z) ≫ f
  refine ⟨g.app (op U) ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩, ?_⟩
  change G.val.map (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op
    (g.app (op U) ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩) = 0
  rw [← PresheafOfModules.naturality_apply]
  have h1 : (moduleOpenStructureSubpresheaf R U).toPresheafOfModules.map
      (homOfLE (inf_le_left : U ⊓ Z.compl ≤ U)).op
        ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩ =
      (⟨(1 : R.obj.obj (op (U ⊓ Z.compl))), mem_moduleOpenSubpresheaf _ _ inf_le_left _⟩ :
        (moduleOpenStructureSubpresheaf R U).obj (op (U ⊓ Z.compl))) :=
    Subtype.ext (PresheafOfModules.unit_map_one R.obj _)
  rw [h1]
  have h := cokernel.condition_assoc (moduleRelativeSupportRelation R U Z) f
  rw [zero_comp] at h
  exact congrArg (fun a ↦ a.app (op (U ⊓ Z.compl))
    (⟨(1 : R.obj.obj (op (U ⊓ Z.compl))), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩ :
      (moduleOpenStructureSubpresheaf R (U ⊓ Z.compl)).obj (op (U ⊓ Z.compl)))) h

/-- The actual relative support object represents local sections with closed support. -/
def moduleRelativeSupportHomEquiv (U : Opens X) (Z : Closeds X) (G : SheafOfModules.{u} R) :
    (moduleRelativeSupport R U Z ⟶ G) ≃+
      ExposeI.gammaZSections ((SheafOfModules.toSheaf R).obj G) Z U where
  toFun := moduleRelativeSupportSectionOfHom R U Z G
  invFun := moduleRelativeSupportHomOfSection R U Z G
  left_inv φ := by
    apply (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective
    apply (cancel_epi (cokernel.π (moduleRelativeSupportRelation R U Z))).mp
    change cokernel.π (moduleRelativeSupportRelation R U Z) ≫
        (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj))
          ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm _) = _
    rw [Equiv.apply_symm_apply, cokernel.π_desc]
    exact moduleOpenUnitMapOfSection_eval_one R U G _
  right_inv s := by
    apply Subtype.ext
    change ((cokernel.π (moduleRelativeSupportRelation R U Z) ≫
      (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj))
        ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm _)).app (op U))
          ⟨(1 : R.obj.obj (op U)), mem_moduleOpenSubpresheaf _ _ le_rfl _⟩ = s.val
    rw [Equiv.apply_symm_apply, cokernel.π_desc]
    exact moduleOpenUnitMapOfSection_apply_one R U G s.val
  map_add' φ ψ := by apply Subtype.ext; rfl

/-- The relative support comparison respects coefficient maps. -/
theorem moduleRelativeSupportHomEquiv_naturality (U : Opens X) (Z : Closeds X)
    {G H : SheafOfModules.{u} R} (a : G ⟶ H) (φ : moduleRelativeSupport R U Z ⟶ G) :
    moduleRelativeSupportHomEquiv R U Z H (φ ≫ a) =
      ExposeI.gammaZSectionsMap ((SheafOfModules.toSheaf R).map a) Z U
        (moduleRelativeSupportHomEquiv R U Z G φ) := by apply Subtype.ext; rfl

/-- The structure module of a locally closed subset, constructed on the ambient space. -/
def moduleLocallyClosedSupport (W : ExposeI.LocallyClosedIn X) : SheafOfModules.{u} R :=
  moduleRelativeSupport R W.V W.closedHull

/-- The original locally closed supported sections are represented by the actual module object. -/
def moduleLocallyClosedSupportHomEquiv (W : ExposeI.LocallyClosedIn X)
    (G : SheafOfModules.{u} R) :
    (moduleLocallyClosedSupport R W ⟶ G) ≃+ W.gamma ((SheafOfModules.toSheaf R).obj G) :=
  (moduleRelativeSupportHomEquiv R W.V W.closedHull G).trans
    (ExposeI.locallyClosedGammaAmbientEquiv W W.closedHull W.closedSupportOnOpen_closedHull
      ((SheafOfModules.toSheaf R).obj G)).symm

/-- The locally closed support representation is natural in the actual module sheaf. -/
theorem moduleLocallyClosedSupportHomEquiv_naturality (W : ExposeI.LocallyClosedIn X)
    {G H : SheafOfModules.{u} R} (a : G ⟶ H) (φ : moduleLocallyClosedSupport R W ⟶ G) :
    moduleLocallyClosedSupportHomEquiv R W H (φ ≫ a) =
      (ExposeI.gammaLocallyClosedFunctor W).map ((SheafOfModules.toSheaf R).map a)
        (moduleLocallyClosedSupportHomEquiv R W G φ) := by
  apply (ExposeI.locallyClosedGammaAmbientEquiv W W.closedHull
    W.closedSupportOnOpen_closedHull ((SheafOfModules.toSheaf R).obj H)).injective
  dsimp only [moduleLocallyClosedSupportHomEquiv, AddEquiv.trans_apply]
  rw [AddEquiv.apply_symm_apply, ExposeI.locallyClosedGammaAmbientEquiv_naturality,
    AddEquiv.apply_symm_apply]
  exact moduleRelativeSupportHomEquiv_naturality R W.V W.closedHull a φ

end SGA.SGA2.ExposeVI
