/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleLocallyClosedSupportedSheaf
import SGA.SGA2.ExposeVI.ModuleSupportedSheafInjective
import SGA.SGA2.ExposeVI.ModuleOpenRestrictionNested

/-!
# Locally closed supported module sheaves preserve injectives

The original intersection-section functor is naturally the composite of
closed support, restriction to the witness open, and open direct image.
The comparison uses the canonical product/intersection isomorphism of
opens and the actual restriction maps of the coefficient module sheaves.
Each of the three functors already preserves injective objects.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)

/-- The categorical product of two opens is their actual intersection. -/
def opensProductIsoInf (U V : Opens X) : U ⨯ V ≅ U ⊓ V where
  hom := homOfLE (le_inf (leOfHom Limits.prod.fst) (leOfHom Limits.prod.snd))
  inv := Limits.prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right)

variable (W : ExposeI.LocallyClosedIn X)

/-- The actual closed-support/restriction/direct-image coefficient functor. -/
def moduleLocallyClosedSupportCompositeFunctor :
    SheafOfModules.{u} R ⥤ SheafOfModules.{u} R :=
  moduleGammaZSheafFunctor R W.closedHull ⋙
    moduleOpenRestriction R W.V ⋙ moduleOpenDirectImage R W.V

/-- The comparison carries intersection sections to product sections by actual restriction. -/
def moduleGammaLocallyClosedToComposite (M : SheafOfModules.{u} R) :
    moduleGammaLocallyClosedSheaf R W M ⟶
      (moduleLocallyClosedSupportCompositeFunctor R W).obj M :=
  ⟨PresheafOfModules.homMk
    { app U := (moduleGammaZSheaf R W.closedHull M).val.presheaf.map
        (opensProductIsoInf W.V U.unop).hom.op
      naturality {U V} i := by
        change (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _ ≫
            (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _ =
          (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _ ≫
            (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1 }
    (by
      intro U r s
      let : Module (R.obj.obj (op (W.V ⊓ U.unop)))
          ((moduleGammaLocallyClosedSheaf R W M).val.obj U) :=
        inferInstanceAs (Module (R.obj.obj (op (W.V ⊓ U.unop)))
          ((moduleGammaZSheaf R W.closedHull M).val.obj (op (W.V ⊓ U.unop))))
      change (moduleGammaZSheaf R W.closedHull M).val.map
          (opensProductIsoInf W.V U.unop).hom.op
            (R.obj.map (homOfLE (inf_le_right : W.V ⊓ U.unop ≤ U.unop)).op r • s) =
        R.obj.map (Limits.prod.snd : W.V ⨯ U.unop ⟶ U.unop).op r •
          (moduleGammaZSheaf R W.closedHull M).val.map
            (opensProductIsoInf W.V U.unop).hom.op s
      rw [PresheafOfModules.map_smul]
      congr 1
      rw [← RingCat.comp_apply, ← R.obj.map_comp]
      rfl)⟩

/-- The inverse comparison is the original restriction along the inverse open isomorphism. -/
def moduleCompositeToGammaLocallyClosed (M : SheafOfModules.{u} R) :
    (moduleLocallyClosedSupportCompositeFunctor R W).obj M ⟶
      moduleGammaLocallyClosedSheaf R W M :=
  ⟨PresheafOfModules.homMk
    { app U := (moduleGammaZSheaf R W.closedHull M).val.presheaf.map
        (opensProductIsoInf W.V U.unop).inv.op
      naturality {U V} i := by
        change (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _ ≫
            (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _ =
          (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _ ≫
            (moduleGammaZSheaf R W.closedHull M).val.presheaf.map _
        rw [← Functor.map_comp, ← Functor.map_comp]
        congr 1 }
    (by
      intro U r s
      let : Module (R.obj.obj (op (W.V ⨯ U.unop)))
          (((moduleLocallyClosedSupportCompositeFunctor R W).obj M).val.obj U) :=
        inferInstanceAs (Module (R.obj.obj (op (W.V ⨯ U.unop)))
          ((moduleGammaZSheaf R W.closedHull M).val.obj (op (W.V ⨯ U.unop))))
      change (moduleGammaZSheaf R W.closedHull M).val.map
          (opensProductIsoInf W.V U.unop).inv.op
            (R.obj.map (Limits.prod.snd : W.V ⨯ U.unop ⟶ U.unop).op r • s) =
        R.obj.map (homOfLE (inf_le_right : W.V ⊓ U.unop ≤ U.unop)).op r •
          (moduleGammaZSheaf R W.closedHull M).val.map
            (opensProductIsoInf W.V U.unop).inv.op s
      rw [PresheafOfModules.map_smul]
      congr 1
      rw [← RingCat.comp_apply, ← R.obj.map_comp]
      rfl)⟩

/-- The original locally supported module sheaf is the actual three-functor composite. -/
def moduleGammaLocallyClosedCompositeIso (M : SheafOfModules.{u} R) :
    moduleGammaLocallyClosedSheaf R W M ≅
      (moduleLocallyClosedSupportCompositeFunctor R W).obj M where
  hom := moduleGammaLocallyClosedToComposite R W M
  inv := moduleCompositeToGammaLocallyClosed R W M
  hom_inv_id := by
    ext U s
    change ((moduleGammaZSheaf R W.closedHull M).val.presheaf.map
        (opensProductIsoInf W.V U.unop).hom.op ≫
      (moduleGammaZSheaf R W.closedHull M).val.presheaf.map
        (opensProductIsoInf W.V U.unop).inv.op) s = s
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id]
    exact ConcreteCategory.congr_hom
      ((moduleGammaZSheaf R W.closedHull M).val.presheaf.map_id (op (W.V ⊓ U.unop))) s
  inv_hom_id := by
    ext U s
    change ((moduleGammaZSheaf R W.closedHull M).val.presheaf.map
        (opensProductIsoInf W.V U.unop).inv.op ≫
      (moduleGammaZSheaf R W.closedHull M).val.presheaf.map
        (opensProductIsoInf W.V U.unop).hom.op) s = s
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id]
    exact ConcreteCategory.congr_hom
      ((moduleGammaZSheaf R W.closedHull M).val.presheaf.map_id (op (W.V ⨯ U.unop))) s

/-- The comparison respects the original coefficient module maps. -/
def moduleGammaLocallyClosedFunctorCompositeIso :
    moduleGammaLocallyClosedSheafFunctor R W ≅ moduleLocallyClosedSupportCompositeFunctor R W :=
  NatIso.ofComponents (fun M ↦ moduleGammaLocallyClosedCompositeIso R W M)
    (fun a ↦ by
      ext U s
      exact (PresheafOfModules.naturality_apply (moduleGammaZSheafMap R W.closedHull a).val
        (opensProductIsoInf W.V U.unop).hom.op s).symm)

/-- The three actual constituent functors preserve injectives. -/
instance moduleLocallyClosedSupportCompositeFunctor_preservesInjectiveObjects :
    (moduleLocallyClosedSupportCompositeFunctor R W).PreservesInjectiveObjects := by
  dsimp [moduleLocallyClosedSupportCompositeFunctor]
  infer_instance

/-- **I.1.4 / VI.1.5, locally closed:** the original locally supported module-sheaf
functor preserves injective objects, with no extra injectivity assumption. -/
instance moduleGammaLocallyClosedSheafFunctor_preservesInjectiveObjects :
    (moduleGammaLocallyClosedSheafFunctor R W).PreservesInjectiveObjects where
  injective_obj {M} hM := by
    let := hM
    exact Injective.of_iso (moduleGammaLocallyClosedCompositeIso R W M).symm
      (inferInstance : Injective ((moduleLocallyClosedSupportCompositeFunctor R W).obj M))

end SGA.SGA2.ExposeVI
