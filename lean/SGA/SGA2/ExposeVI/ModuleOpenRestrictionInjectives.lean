/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ModuleHomInjectiveFlasque
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-!
# Open restriction of module sheaves preserves injectives

An arbitrary module presheaf on the opens contained in `U` extends by zero
as a presheaf. This extension preserves monomorphisms. The explicit
extension and restriction of morphisms therefore show that restriction
preserves injectives, first for module presheaves and then for module sheaves.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}} (U : Opens X)

/-- Restriction of module presheaves to the opens contained in `U`. -/
abbrev moduleOpenRestrictionPresheaf := PresheafOfModules.pushforward₀ (Over.forget U) R

/-- The sections of extension by zero before sheafification. The proof
index has one element inside `U` and no elements otherwise. -/
def moduleOpenExtensionObj
    (M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)) (V : (Opens X)ᵒᵖ) :
    ModuleCat.{u} (R.obj V) :=
  ModuleCat.of _ ((h : PLift (V.unop ≤ U)) → M.obj (op (Over.mk (homOfLE h.down))))

/-- Restriction maps of presheaf extension by zero. -/
def moduleOpenExtensionMap
    (M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R))
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    moduleOpenExtensionObj U M V ⟶
      (ModuleCat.restrictScalars (R.map i).hom).obj (moduleOpenExtensionObj U M W) := by
  classical
  refine ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map i).hom).obj (moduleOpenExtensionObj U M W))
    { toFun := fun x hW => if hV : V.unop ≤ U then
        M.map (Over.homMk i.unop : Over.mk (homOfLE hW.down) ⟶ Over.mk (homOfLE hV)).op (x ⟨hV⟩)
        else 0
      map_add' := ?_
      map_smul' := ?_ }
  · intro x y
    funext hW
    change (if hV : V.unop ≤ U then
      M.map (Over.homMk i.unop : Over.mk (homOfLE hW.down) ⟶ Over.mk (homOfLE hV)).op
        (x ⟨hV⟩ + y ⟨hV⟩) else 0) =
      (if hV : V.unop ≤ U then
        M.map (Over.homMk i.unop : Over.mk (homOfLE hW.down) ⟶ Over.mk (homOfLE hV)).op
          (x ⟨hV⟩) else 0) +
      (if hV : V.unop ≤ U then
        M.map (Over.homMk i.unop : Over.mk (homOfLE hW.down) ⟶ Over.mk (homOfLE hV)).op
          (y ⟨hV⟩) else 0)
    split_ifs
    · exact (M.map _).hom.map_add _ _
    · simp
  · intro r x
    funext hW
    change (if hV : V.unop ≤ U then
      M.map (Over.homMk i.unop : Over.mk (homOfLE hW.down) ⟶ Over.mk (homOfLE hV)).op
        (r • x ⟨hV⟩) else 0) =
      R.map i r • (if hV : V.unop ≤ U then
        M.map (Over.homMk i.unop : Over.mk (homOfLE hW.down) ⟶ Over.mk (homOfLE hV)).op
          (x ⟨hV⟩) else 0)
    split_ifs <;> simp

@[simp]
theorem moduleOpenExtensionMap_apply
    (M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R))
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (x : moduleOpenExtensionObj U M V)
    (hV : V.unop ≤ U) (hW : W.unop ≤ U) :
    moduleOpenExtensionMap U M i x ⟨hW⟩ =
      M.map (Over.homMk i.unop : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE hV)).op (x ⟨hV⟩) := by
  classical
  simp [moduleOpenExtensionMap, hV]

@[simp]
theorem moduleOpenExtensionMap_apply_of_not_le
    (M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R))
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (x : moduleOpenExtensionObj U M V)
    (hV : ¬ V.unop ≤ U) (hW : W.unop ≤ U) :
    moduleOpenExtensionMap U M i x ⟨hW⟩ = 0 := by
  classical
  simp [moduleOpenExtensionMap, hV]

/-- Extension by zero of an arbitrary module presheaf on `Over U`. -/
def moduleOpenExtensionPresheaf
    (M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)) : PresheafOfModules.{u} R where
  obj := moduleOpenExtensionObj U M
  map := moduleOpenExtensionMap U M
  map_id V := by
    ext x
    funext hV
    obtain ⟨hV⟩ := hV
    rw [moduleOpenExtensionMap_apply U M _ x hV hV]
    exact congrArg (fun f => f (x ⟨hV⟩)) (M.map_id (op (Over.mk (homOfLE hV))))
  map_comp {V W T} i j := by
    classical
    ext x
    funext hT
    obtain ⟨hT⟩ := hT
    change moduleOpenExtensionMap U M (i ≫ j) x ⟨hT⟩ =
      moduleOpenExtensionMap U M j (moduleOpenExtensionMap U M i x) ⟨hT⟩
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := le_trans (leOfHom i.unop) hV
      simp only [moduleOpenExtensionMap_apply U M _ _ hV hT,
        moduleOpenExtensionMap_apply U M _ _ hW hT,
        moduleOpenExtensionMap_apply U M _ _ hV hW]
      exact M.map_comp_apply
        (Over.homMk i.unop : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE hV)).op
        (Over.homMk j.unop : Over.mk (homOfLE hT) ⟶ Over.mk (homOfLE hW)).op (x ⟨hV⟩)
    · by_cases hW : W.unop ≤ U
      · rw [moduleOpenExtensionMap_apply_of_not_le U M _ _ hV,
          moduleOpenExtensionMap_apply U M _ _ hW hT,
          moduleOpenExtensionMap_apply_of_not_le U M _ _ hV]
        exact (M.map (Over.homMk j.unop :
          Over.mk (homOfLE hT) ⟶ Over.mk (homOfLE hW)).op).hom.map_zero.symm
      · simp [moduleOpenExtensionMap_apply_of_not_le U M _ _ hV,
          moduleOpenExtensionMap_apply_of_not_le U M _ _ hW]

/-- Extension of morphisms is pointwise on the opens contained in `U`. -/
def moduleOpenExtensionHom
    {M N : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)} (f : M ⟶ N) :
    moduleOpenExtensionPresheaf U M ⟶ moduleOpenExtensionPresheaf U N where
  app V := ModuleCat.ofHom
    { toFun := fun x h => f.app (op (Over.mk (homOfLE h.down))) (x h)
      map_add' := by intro x y; ext h; exact (f.app _).hom.map_add _ _
      map_smul' := by intro r x; ext h; exact (f.app _).hom.map_smul _ _ }
  naturality {V W} i := by
    ext x
    funext hW
    obtain ⟨hW⟩ := hW
    change f.app (op (Over.mk (homOfLE hW))) (moduleOpenExtensionMap U M i x ⟨hW⟩) =
      moduleOpenExtensionMap U N i
        (fun h => f.app (op (Over.mk (homOfLE h.down))) (x h)) ⟨hW⟩
    by_cases hV : V.unop ≤ U
    · rw [moduleOpenExtensionMap_apply U M _ _ hV,
        moduleOpenExtensionMap_apply U N _ _ hV]
      exact PresheafOfModules.naturality_apply f
        (Over.homMk i.unop : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE hV)).op (x ⟨hV⟩)
    · rw [moduleOpenExtensionMap_apply_of_not_le U M _ _ hV,
        moduleOpenExtensionMap_apply_of_not_le U N _ _ hV]
      exact (f.app _).hom.map_zero

/-- Presheaf extension by zero preserves monomorphisms. -/
instance moduleOpenExtensionHom_mono
    {M N : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)} (f : M ⟶ N) [Mono f] :
    Mono (moduleOpenExtensionHom U f) := by
  apply PresheafOfModules.mono_of_injective
  intro V x y h
  funext hV
  exact PresheafOfModules.injective_of_mono f _ (congrFun h hV)

/-- A morphism on `U` gives a global morphism from the presheaf extension by zero. -/
def moduleOpenExtensionDesc
    {M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)} {N : PresheafOfModules.{u} R}
    (f : M ⟶ (moduleOpenRestrictionPresheaf U).obj N) :
    moduleOpenExtensionPresheaf U M ⟶ N where
  app V := by
    classical
    exact if hV : V.unop ≤ U then ModuleCat.ofHom
      { toFun := fun x => f.app (op (Over.mk (homOfLE hV))) (x ⟨hV⟩)
        map_add' := fun x y => (f.app _).hom.map_add _ _
        map_smul' := fun r x => (f.app _).hom.map_smul _ _ }
      else 0
  naturality {V W} i := by
    classical
    ext x
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := le_trans (leOfHom i.unop) hV
      dsimp only
      simp only [dite_eq_left hV, dite_eq_left hW, ModuleCat.hom_comp, LinearMap.coe_comp,
        Function.comp_apply]
      change f.app (op (Over.mk (homOfLE hW))) (moduleOpenExtensionMap U M i x ⟨hW⟩) =
        N.map i (f.app (op (Over.mk (homOfLE hV))) (x ⟨hV⟩))
      rw [moduleOpenExtensionMap_apply U M _ _ hV]
      exact PresheafOfModules.naturality_apply f
        (Over.homMk i.unop : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE hV)).op (x ⟨hV⟩)
    · have hx : x = 0 := by funext h; exact (hV h.down).elim
      subst x
      simp

@[simp]
theorem moduleOpenExtensionDesc_app_apply
    {M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)} {N : PresheafOfModules.{u} R}
    (f : M ⟶ (moduleOpenRestrictionPresheaf U).obj N)
    (V : (Opens X)ᵒᵖ) (hV : V.unop ≤ U) (x : moduleOpenExtensionObj U M V) :
    (moduleOpenExtensionDesc U f).app V x =
      f.app (op (Over.mk (homOfLE hV))) (x ⟨hV⟩) := by
  classical
  simp only [moduleOpenExtensionDesc, dite_eq_left hV, ModuleCat.hom_ofHom, LinearMap.coe_mk,
    AddHom.coe_mk]

/-- A global morphism from an extension by zero restricts back to the
original module presheaf on `U`. -/
def moduleOpenExtensionRestrict
    {M : PresheafOfModules.{u} ((Over.forget U).op ⋙ R)} {N : PresheafOfModules.{u} R}
    (f : moduleOpenExtensionPresheaf U M ⟶ N) :
    M ⟶ (moduleOpenRestrictionPresheaf U).obj N where
  app V := ModuleCat.ofHom
    { toFun := fun x => f.app (op V.unop.left) (fun _ => x)
      map_add' := fun x y => (f.app _).hom.map_add _ _
      map_smul' := fun r x => (f.app _).hom.map_smul _ _ }
  naturality {V W} i := by
    ext x
    change f.app (op W.unop.left) (fun _ => M.map i x) =
      N.map i.unop.left.op (f.app (op V.unop.left) (fun _ => x))
    rw [← PresheafOfModules.naturality_apply f i.unop.left.op]
    congr 1
    funext hW
    exact (moduleOpenExtensionMap_apply U M i.unop.left.op (fun _ => x)
      (leOfHom V.unop.hom) hW.down).symm

/-- Restriction of an injective module presheaf to an open is injective. -/
theorem moduleOpenRestrictionPresheaf_injective (N : PresheafOfModules.{u} R) [Injective N] :
    Injective ((moduleOpenRestrictionPresheaf U).obj N) where
  factors {M M'} g f _ := by
    let g' := moduleOpenExtensionDesc U g
    let f' := moduleOpenExtensionHom U f
    let h := Injective.factorThru g' f'
    refine ⟨moduleOpenExtensionRestrict U h, ?_⟩
    apply PresheafOfModules.hom_ext
    rintro ⟨V⟩
    obtain ⟨V, iV, rfl⟩ := V.mk_surjective
    ext x
    have hfac := congrArg
      (fun k : moduleOpenExtensionPresheaf U M ⟶ N =>
        k.app (op V) (fun _ => x)) (Injective.comp_factorThru g' f')
    change h.app (op V) (fun _ => f.app (op (Over.mk iV)) x) = g.app (op (Over.mk iV)) x
    have hV : V ≤ U := leOfHom iV
    change h.app (op V) ((moduleOpenExtensionHom U f).app (op V) (fun _ => x)) =
      (moduleOpenExtensionDesc U g).app (op V) (fun _ => x) at hfac
    rw [moduleOpenExtensionDesc_app_apply U g _ hV] at hfac
    exact hfac

variable (S : Sheaf RingCat.{u} X)

/-- **VI.1.2 input:** the actual restriction of an injective module sheaf
to the open site `Over U` is injective. -/
theorem moduleOpenRestriction_injective (N : SheafOfModules.{u} S) [Injective N] :
    Injective ((SheafOfModules.overFunctor S U).obj N) := by
  let : Injective N.val := ExposeV.injective_modulePresheaf_of_injective S N
  let F : SheafOfModules.{u} (S.over U) ⥤ PresheafOfModules.{u} (S.over U).obj :=
    SheafOfModules.forget (S.over U)
  let : PreservesFiniteLimits F := inferInstance
  apply F.injective_of_map_injective
  exact moduleOpenRestrictionPresheaf_injective U N.val

end SGA.SGA2.ExposeVI
