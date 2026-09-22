/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVI.ModuleInternalHomFunctor
import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Local linear Hom and genuine restrictions of scheme modules

Sections of the existing local-linear Hom sheaf on an open are actual
morphisms between the restricted modules, via the slice-site equivalence.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

/-- Actual local-linear maps are morphisms of module sheaves on the slice site. -/
def moduleLocalHomSheafOverEquiv {X : TopCat.{u}} {R : TopCat.Sheaf RingCat.{u} X}
    (F G : SheafOfModules.{u} R) (U : Opens X) :
    moduleLocalHom F.val G.val U ≃ (F.over U ⟶ G.over U) where
  toFun φ := ⟨PresheafOfModules.homMk φ.val (fun V r x ↦ φ.property V.unop r x)⟩
  invFun φ := ⟨(PresheafOfModules.toPresheaf _).map φ.val,
    fun V r x ↦ (φ.val.app (op V)).hom.map_smul r x⟩
  left_inv φ := by
    apply Subtype.ext
    apply NatTrans.ext
    funext V
    ext x
    rfl
  right_inv φ := by ext V x; rfl

/-- Sections of the actual Hom sheaf equal Hom of the actual open restrictions. -/
def schemeLocalHomRestrictEquiv {X : Scheme.{u}} (F G : X.Modules) (U : X.Opens) :
    moduleLocalHom F.val G.val U ≃ (F.restrict U.ι ⟶ G.restrict U.ι) :=
  (moduleLocalHomSheafOverEquiv F G U).trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app F)
        ((Scheme.Modules.overFunctorEquiv U).app G)))

/-- Vanishing of the actual internal Hom sheaf annihilates all local module morphisms. -/
theorem subsingleton_restrictHom_of_isZero_internalHom {X : Scheme.{u}}
    (F G : X.Modules)
    (h : IsZero (moduleSheafHomAb (Opens.grothendieckTopology X) F G)) (U : X.Opens) :
    Subsingleton (F.restrict U.ι ⟶ G.restrict U.ι) := by
  have hz := ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
    (op U)).map_isZero h
  exact (schemeLocalHomRestrictEquiv F G U).subsingleton_congr.mp
    (AddCommGrpCat.isZero_iff_subsingleton.mp hz)

/-- Restriction along an isomorphism of schemes is an actual equivalence of module categories. -/
def schemeModulesRestrictEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id.symm ≪≫
        Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId)

/-- Local Hom vanishing is unchanged when an affine open is presented by its spectrum. -/
theorem subsingleton_affineChartHom_of_isZero_internalHom {X : Scheme.{u}}
    (F G : X.Modules)
    (h : IsZero (moduleSheafHomAb (Opens.grothendieckTopology X) F G))
    (U : X.Opens) (hU : IsAffineOpen U) :
    Subsingleton (F.restrict hU.fromSpec ⟶ G.restrict hU.fromSpec) := by
  have := subsingleton_restrictHom_of_isZero_internalHom F G h U
  let e := (schemeModulesRestrictEquivalence hU.isoSpec.symm).fullyFaithfulFunctor.homEquiv
    (X := F.restrict U.ι) (Y := G.restrict U.ι)
  let e' := Iso.homCongr
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F).symm
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app G).symm
  exact e'.subsingleton_congr.mp (e.subsingleton_congr.mp inferInstance)

end SGA.SGA2.ExposeVI
