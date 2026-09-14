/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.RightDerivedPostcomposition
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-!
# Exact precomposition and right-derived functors

An exact functor preserving injective objects carries an actual injective
resolution to an injective resolution. This gives a natural comparison between
right derivation before and after precomposition by that functor.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]

section Resolution

variable (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]

/-- An exact functor preserving injectives maps an actual injective resolution
to an injective resolution of the image object. -/
def mapInjectiveResolution {X : C} (I : InjectiveResolution X) :
    InjectiveResolution (G.obj X) where
  cocomplex := (G.mapHomologicalComplex _).obj I.cocomplex
  injective n := by
    change Injective (G.obj (I.cocomplex.X n))
    infer_instance
  ι := ((singleMapHomologicalComplex G (ComplexShape.up ℕ) 0).inv.app X) ≫
    (G.mapHomologicalComplex _).map I.ι

/-- In degree zero, the mapped resolution inclusion is the image of the
original resolution inclusion. -/
@[simp]
lemma mapInjectiveResolution_ι_f_zero {X : C} (I : InjectiveResolution X) :
    (mapInjectiveResolution G I).ι.f 0 = G.map (I.ι.f 0) := by
  simp [mapInjectiveResolution, singleObjXSelf, singleObjXIsoOfEq]

end Resolution

section RightDerived

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]
  (G : C ⥤ D) (F : D ⥤ E)
  [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects] [F.Additive]

/-- Objectwise comparison for right derivation and exact, injective-preserving
precomposition, using the mapped injective resolution. -/
def rightDerivedPrecomposeObjIso (X : C) (n : ℕ) :
    ((G ⋙ F).rightDerived n).obj X ≅ (F.rightDerived n).obj (G.obj X) :=
  (injectiveResolution X).isoRightDerivedObj (G ⋙ F) n ≪≫
    ((mapInjectiveResolution G (injectiveResolution X)).isoRightDerivedObj F n).symm

/-- Naturality in the coefficient object of exact precomposition. -/
@[reassoc]
lemma rightDerivedPrecomposeObjIso_hom_naturality
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((G ⋙ F).rightDerived n).map f ≫ (rightDerivedPrecomposeObjIso G F Y n).hom =
      (rightDerivedPrecomposeObjIso G F X n).hom ≫ (F.rightDerived n).map (G.map f) := by
  let I := injectiveResolution X
  let J := injectiveResolution Y
  let φ := InjectiveResolution.desc f J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f J I
  have hGφ : (mapInjectiveResolution G I).ι.f 0 ≫
      ((G.mapHomologicalComplex _).map φ).f 0 =
      G.map f ≫ (mapInjectiveResolution G J).ι.f 0 := by
    simp only [mapInjectiveResolution_ι_f_zero]
    exact (G.map_comp _ _).symm.trans ((congrArg G.map hφ).trans (G.map_comp _ _))
  simp only [rightDerivedPrecomposeObjIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ (G ⋙ F) n,
    Category.assoc]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality (G.map f)
    (mapInjectiveResolution G I) (mapInjectiveResolution G J)
    ((G.mapHomologicalComplex _).map φ) hGφ F n]
  rw [Category.assoc]

/-- Right derivation commutes naturally with exact precomposition by a functor
preserving injective objects. -/
def rightDerivedPrecomposeIso (n : ℕ) :
    (G ⋙ F).rightDerived n ≅ G ⋙ F.rightDerived n :=
  NatIso.ofComponents (fun X => rightDerivedPrecomposeObjIso G F X n)
    (fun f => rightDerivedPrecomposeObjIso_hom_naturality G F f n)

end RightDerived

end SGA.SGA2.ExposeI
