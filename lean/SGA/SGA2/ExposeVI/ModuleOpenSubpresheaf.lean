/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleGlobalHom
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule

/-!
# Extending local linear maps from an open subpresheaf

For an open `U`, the subpresheaf of a module presheaf `F` with value `F(V)`
when `V ≤ U` and zero otherwise embeds into `F`. A local linear map from
`F` to `G` over `U` defines a morphism from this subpresheaf to `G`.
This is a presheaf construction; no sheaf condition on the subpresheaf is claimed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} {R : (Opens X)ᵒᵖ ⥤ RingCat.{u}}

/-- The subpresheaf equal to `F` on opens contained in `U` and zero elsewhere. -/
def moduleOpenSubpresheaf (F : PresheafOfModules.{u} R) (U : Opens X) : F.Submodule := by
  classical
  exact
    { obj V := if V.unop ≤ U then ⊤ else ⊥
      map {V W} i := by
        intro x hx
        change F.map i x ∈
          (if W.unop ≤ U then ⊤ else ⊥ : Submodule (R.obj W) (F.obj W))
        by_cases h : V.unop ≤ U
        · simp [le_trans (leOfHom i.unop) h]
        · have hx0 : x = 0 := by simpa [h] using hx
          subst x
          simp }

/-- Over the designated open, every original section belongs to the open subpresheaf. -/
theorem mem_moduleOpenSubpresheaf (F : PresheafOfModules.{u} R) (U : Opens X)
    {V : (Opens X)ᵒᵖ} (h : V.unop ≤ U) (x : F.obj V) :
    x ∈ (moduleOpenSubpresheaf F U).obj V := by
  classical
  simp [moduleOpenSubpresheaf, h]

/-- Away from the designated downward-closed collection of opens, sections are zero. -/
theorem moduleOpenSubpresheaf_eq_zero (F : PresheafOfModules.{u} R) (U : Opens X)
    {V : (Opens X)ᵒᵖ} (h : ¬ V.unop ≤ U)
    (x : (moduleOpenSubpresheaf F U).toPresheafOfModules.obj V) : x.val = 0 := by
  simpa [moduleOpenSubpresheaf, h] using x.property

/-- The component of the morphism induced by a local linear map. -/
def moduleOpenSubpresheafHomApp {F G : PresheafOfModules.{u} R} {U : Opens X}
    (φ : moduleLocalHom F G U) (V : (Opens X)ᵒᵖ) :
    (moduleOpenSubpresheaf F U).toPresheafOfModules.obj V ⟶ G.obj V := by
  classical
  exact if h : V.unop ≤ U then
    ModuleCat.ofHom
      { toFun x := φ.val.app (op (Over.mk (homOfLE h))) x.val
        map_add' x y := (φ.val.app (op (Over.mk (homOfLE h)))).hom.map_add x.val y.val
        map_smul' r x := φ.property (Over.mk (homOfLE h)) r x.val }
    else 0

@[simp]
theorem moduleOpenSubpresheafHomApp_apply {F G : PresheafOfModules.{u} R} {U : Opens X}
    (φ : moduleLocalHom F G U) (V : (Opens X)ᵒᵖ) (h : V.unop ≤ U)
    (x : (moduleOpenSubpresheaf F U).toPresheafOfModules.obj V) :
    moduleOpenSubpresheafHomApp φ V x = φ.val.app (op (Over.mk (homOfLE h))) x.val := by
  classical
  simp [moduleOpenSubpresheafHomApp, h]

/-- A local linear map induces a global morphism from the actual open subpresheaf. -/
def moduleOpenSubpresheafHom {F G : PresheafOfModules.{u} R} {U : Opens X}
    (φ : moduleLocalHom F G U) : (moduleOpenSubpresheaf F U).toPresheafOfModules ⟶ G :=
  PresheafOfModules.homMk
    { app V := (forget₂ (ModuleCat (R.obj V)) AddCommGrpCat).map
        (moduleOpenSubpresheafHomApp φ V)
      naturality {V W} i := by
        classical
        ext x
        change moduleOpenSubpresheafHomApp φ W
            ((moduleOpenSubpresheaf F U).toPresheafOfModules.map i x) =
          G.map i (moduleOpenSubpresheafHomApp φ V x)
        by_cases h : V.unop ≤ U
        · have hW : W.unop ≤ U := le_trans (leOfHom i.unop) h
          rw [moduleOpenSubpresheafHomApp_apply φ W hW,
            moduleOpenSubpresheafHomApp_apply φ V h]
          exact NatTrans.naturality_apply φ.val
            (Over.homMk i.unop : Over.mk (homOfLE hW) ⟶ Over.mk (homOfLE h)).op x.val
        · have hx : x = 0 := Subtype.ext (moduleOpenSubpresheaf_eq_zero F U h x)
          subst x
          simp }
    (fun V r x ↦ (moduleOpenSubpresheafHomApp φ V).hom.map_smul r x)

@[simp]
theorem moduleOpenSubpresheafHom_app_apply {F G : PresheafOfModules.{u} R}
    {U : Opens X} (φ : moduleLocalHom F G U) (V : (Opens X)ᵒᵖ) (h : V.unop ≤ U)
    (x : (moduleOpenSubpresheaf F U).toPresheafOfModules.obj V) :
    (moduleOpenSubpresheafHom φ).app V x = φ.val.app (op (Over.mk (homOfLE h))) x.val :=
  moduleOpenSubpresheafHomApp_apply φ V h x

end SGA.SGA2.ExposeVI
