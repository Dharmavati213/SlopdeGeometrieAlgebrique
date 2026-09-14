/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InternalHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# The additive sheaf of local module-linear morphisms

For an arbitrary sheaf of rings, the local linear maps form a subgroup of
the actual additive internal Hom. Linearity is a local condition, so this
presheaf is already a sheaf. This is the underlying additive sheaf needed
for the ringed-space supported Ext functors of VI.1.1.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [SmallCategory C] {R : Cᵒᵖ ⥤ RingCat.{u}}

local instance (G : PresheafOfModules.{u} R) (U : C) (V : Over U) :
    Module (R.obj (op V.left)) (((Over.forget U).op ⋙ G.presheaf).obj (op V)) :=
  inferInstanceAs (Module (R.obj (op V.left)) (G.obj (op V.left)))

/-- The local additive morphisms that are linear for every local structure ring. -/
def moduleLocalHom (F G : PresheafOfModules.{u} R) (U : C) :
    AddSubgroup ((ExposeI.abelianPresheafHom F.presheaf G.presheaf).obj (op U)) where
  carrier := {φ | ∀ (V : Over U) (r : R.obj (op V.left)) (x : F.obj (op V.left)),
    φ.app (op V) (r • x) = r • φ.app (op V) x}
  zero_mem' := by
    intro V r x
    change (0 : G.obj (op V.left)) = r • (0 : G.obj (op V.left))
    simp
  add_mem' := by
    intro φ ψ hφ hψ V r x
    change φ.app (op V) (r • x) + ψ.app (op V) (r • x) =
      r • (φ.app (op V) x + ψ.app (op V) x)
    rw [hφ, hψ, smul_add]
  neg_mem' := by
    intro φ hφ V r x
    change -(φ.app (op V) (r • x)) = r • -(φ.app (op V) x)
    rw [hφ, smul_neg]

/-- Local linear morphisms are determined by their values on every local section. -/
@[ext]
theorem moduleLocalHom_ext {F G : PresheafOfModules.{u} R} {U : C}
    {φ ψ : moduleLocalHom F G U}
    (h : ∀ (V : Over U) (x : F.obj (op V.left)), φ.val.app (op V) x = ψ.val.app (op V) x) :
    φ = ψ := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  exact h V.unop

/-- Restriction preserves local module-linearity. -/
def moduleLocalHomRestrict (F G : PresheafOfModules.{u} R) {U V : C}
    (f : V ⟶ U) : moduleLocalHom F G U →+ moduleLocalHom F G V where
  toFun φ := ⟨Functor.whiskerLeft (Over.map f).op φ.val,
    fun W r x ↦ φ.property ((Over.map f).obj W) r x⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual presheaf of local linear morphisms, with its additive structure. -/
def moduleHomPresheafAb (F G : PresheafOfModules.{u} R) : Cᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (moduleLocalHom F G U.unop)
  map f := AddCommGrpCat.ofHom (moduleLocalHomRestrict F G f.unop)
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((ExposeI.abelianPresheafHom F.presheaf G.presheaf).map_id U) φ.val
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro φ
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((ExposeI.abelianPresheafHom F.presheaf G.presheaf).map_comp f g) φ.val

/-- The same local linearity condition as a subfunctor of local additive maps. -/
def moduleHomSubfunctor (F G : PresheafOfModules.{u} R) :
    Subfunctor (presheafHom F.presheaf G.presheaf) where
  obj U := (moduleLocalHom F G U.unop).carrier
  map f _ hφ := fun W r x ↦ hφ ((Over.map f.unop).obj W) r x

/-- Forgetting addition gives precisely the local-linear subfunctor. -/
def moduleHomPresheafAbForgetIso (F G : PresheafOfModules.{u} R) :
    moduleHomPresheafAb F G ⋙ forget AddCommGrpCat ≅
      (moduleHomSubfunctor F G).toFunctor := Iso.refl _

variable (J : GrothendieckTopology C)

/-- The scalar-linearity condition is local for the topology of the base site. -/
theorem moduleHomSubfunctor_isSheaf (F G : PresheafOfModules.{u} R)
    (hG : Presheaf.IsSheaf J G.presheaf) :
    Presieve.IsSheaf J (moduleHomSubfunctor F G).toFunctor := by
  have hHom : Presieve.IsSheaf J (presheafHom F.presheaf G.presheaf) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp (hG.hom F.presheaf)
  have hGT : Presieve.IsSheaf J (G.presheaf ⋙ forget AddCommGrpCat) :=
    (isSheaf_iff_isSheaf_of_type _ _).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat)).mp hG)
  apply ((moduleHomSubfunctor F G).isSheaf_iff hHom).mpr
  intro U φ hφ V r x
  apply (hGT _ (J.pullback_stable V.hom hφ)).isSeparatedFor.ext
  intro W f hf
  let a : Over.mk (f ≫ V.hom) ⟶ V := Over.homMk f
  have hn (y : F.obj (op V.left)) := NatTrans.naturality_apply φ a.op y
  let : Module (R.obj (op W))
      (((Over.forget W).op ⋙ G.presheaf).obj (op (Over.mk (𝟙 W)))) :=
    inferInstanceAs (Module (R.obj (op W)) (G.obj (op W)))
  have hl := hf (Over.mk (𝟙 W)) (R.map f.op r) (F.map f.op x)
  change ((presheafHom F.presheaf G.presheaf).map (f ≫ V.hom).op φ).app
      (op (Over.mk (𝟙 W))) (R.map f.op r • F.map f.op x) =
    R.map f.op r • (((presheafHom F.presheaf G.presheaf).map (f ≫ V.hom).op φ).app
      (op (Over.mk (𝟙 W))) (F.map f.op x) : G.obj (op W)) at hl
  erw [presheafHom_map_app_op_mk_id] at hl
  change G.map f.op (φ.app (op V) (r • x)) = G.map f.op (r • φ.app (op V) x)
  erw [← hn, F.map_smul, G.map_smul, ← hn]
  exact hl

/-- The actual local-linear morphism presheaf is already an additive sheaf. -/
def moduleSheafHomAb {R : Sheaf J RingCat.{u}} (F G : SheafOfModules.{u} R) :
    Sheaf J AddCommGrpCat.{u} where
  obj := moduleHomPresheafAb F.val G.val
  property := (Presheaf.isSheaf_iff_isSheaf_forget J _ (forget AddCommGrpCat)).mpr
    ((Presheaf.isSheaf_of_iso_iff (moduleHomPresheafAbForgetIso F.val G.val)).mpr
      ((isSheaf_iff_isSheaf_of_type _ _).mpr
        (moduleHomSubfunctor_isSheaf J F.val G.val G.isSheaf)))

end SGA.SGA2.ExposeVI
