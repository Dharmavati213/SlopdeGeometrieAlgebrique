/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.ExtRightDerivedSource
import SGA.SGA2.ExposeI.RightDerivedPrecomposition
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Exact functors and the right-derived Hom comparison

The canonical degree-zero derived comparison is compatible with exact
precomposition. The Hom map induced by an exact functor will be compared
with its map on derived-category Ext using actual injective resolutions.
-/

noncomputable section

open CategoryTheory Limits Opposite Abelian HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

section PrecomposeZero

variable {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    (G : C ⥤ D) (P : D ⥤ E)
    [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]
    [PreservesFiniteLimits G] [P.Additive] [PreservesFiniteLimits P]

omit [PreservesFiniteLimits G] [PreservesFiniteLimits P] in
/-- The degree-zero map to cycles is unchanged by mapping the resolution
under the exact functor. -/
theorem toRightDerivedZero'_precompose {X : C} (I : InjectiveResolution X) :
    I.toRightDerivedZero' (G ⋙ P) = (mapInjectiveResolution G I).toRightDerivedZero' P := by
  apply (cancel_mono (iCycles _ 0)).mp
  erw [InjectiveResolution.toRightDerivedZero'_comp_iCycles,
    InjectiveResolution.toRightDerivedZero'_comp_iCycles, mapInjectiveResolution_ι_f_zero]
  rfl

/-- The two canonical degree-zero homology comparisons use the same map. -/
theorem resolutionZeroHomologyIso_precompose {X : C} (I : InjectiveResolution X) :
    resolutionZeroHomologyIso (G ⋙ P) I =
      resolutionZeroHomologyIso P (mapInjectiveResolution G I) := by
  apply Iso.ext
  simp only [resolutionZeroHomologyIso, Iso.trans_hom, asIso_hom,
    toRightDerivedZero'_precompose]
  rfl

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]

omit [PreservesFiniteLimits G] [PreservesFiniteLimits P] in
/-- Exact precomposition respects the original map to zeroth right derivation. -/
@[reassoc]
theorem toRightDerivedZero_precompose (X : C) :
    (G ⋙ P).toRightDerivedZero.app X ≫ (rightDerivedPrecomposeIso G P 0).hom.app X =
      P.toRightDerivedZero.app (G.obj X) := by
  let I := injectiveResolution X
  rw [I.toRightDerivedZero_eq (G ⋙ P),
    (mapInjectiveResolution G I).toRightDerivedZero_eq P]
  dsimp only [rightDerivedPrecomposeIso, NatIso.ofComponents_hom_app,
    rightDerivedPrecomposeObjIso, Iso.trans_hom, Iso.symm_hom]
  simp only [I, Category.assoc, Iso.inv_hom_id_assoc]
  rw [toRightDerivedZero'_precompose]
  rfl

/-- The standard zeroth derived isomorphism commutes with exact precomposition. -/
@[reassoc]
theorem rightDerivedPrecomposeIso_zero (X : C) :
    (rightDerivedPrecomposeIso G P 0).hom.app X ≫
        P.rightDerivedZeroIsoSelf.hom.app (G.obj X) =
      (G ⋙ P).rightDerivedZeroIsoSelf.hom.app X := by
  apply (cancel_epi ((G ⋙ P).toRightDerivedZero.app X)).mp
  rw [← Category.assoc, toRightDerivedZero_precompose]
  simp only [Functor.rightDerivedZeroIsoSelf_inv_hom_id_app]
  rfl

end PrecomposeZero

section HomMap

universe v u u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] (G : C ⥤ D) [G.Additive]

/-- Applying an additive functor to actual morphisms, naturally in the coefficient. -/
def exactFunctorHomMap (A : C) :
    preadditiveCoyoneda.obj (op A) ⟶ G ⋙ preadditiveCoyoneda.obj (op (G.obj A)) where
  app B := AddCommGrpCat.ofHom (G.mapAddHom : (A ⟶ B) →+ (G.obj A ⟶ G.obj B))
  naturality B B' f := by ext g; exact G.map_comp g f

end HomMap

section ExtZero

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

/-- The standard `Ext⁰ = Hom` equivalence as a natural isomorphism. -/
def extFunctorZeroIso (A : C) :
    extFunctorObj A 0 ≅ preadditiveCoyoneda.obj (op A) :=
  NatIso.ofComponents (fun B => (Ext.addEquiv₀ (X := A) (Y := B)).toAddCommGrpIso)
    (fun {B B'} f => by
      ext e
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A B).2 e
      change Ext.addEquiv₀ ((Ext.mk₀ g).comp (Ext.mk₀ f) (add_zero 0)) =
        Ext.addEquiv₀ (Ext.mk₀ g) ≫ f
      rw [Ext.mk₀_comp_mk₀]
      simp only [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply])

variable [HasInjectiveResolutions C]

/-- The resolution comparison uses the standard identification in degree zero. -/
@[reassoc]
theorem rightDerivedCoyonedaNatIsoExt_zero (A : C) :
    (rightDerivedCoyonedaNatIsoExt A 0).hom ≫ (extFunctorZeroIso A).hom =
      (preadditiveCoyoneda.obj (op A)).rightDerivedZeroIsoSelf.hom := by
  apply NatTrans.ext
  funext B
  apply AddCommGrpCat.hom_ext
  ext x
  exact Ext.addEquiv₀.apply_symm_apply _

/-- A represented derived functor has the standard degree-zero Hom comparison. -/
@[reassoc]
theorem representedRightDerivedIso_zero
    {P : C ⥤ AddCommGrpCat.{v}} [P.Additive] [PreservesFiniteLimits P]
    (A : C) (e : P ≅ preadditiveCoyoneda.obj (op A)) (B : C) :
    ((rightDerivedFunctorIso e 0 ≪≫ rightDerivedCoyonedaNatIsoExt A 0).hom.app B) ≫
        (extFunctorZeroIso A).hom.app B =
      P.rightDerivedZeroIsoSelf.hom.app B ≫ e.hom.app B := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.comp_app, rightDerivedCoyonedaNatIsoExt_zero]
  exact rightDerivedZeroIsoSelf_natTrans e.hom B

end ExtZero

section PrecomposeHomZero

universe v u u'

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} D]
    [HasInjectiveResolutions C] [HasInjectiveResolutions D]
    (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]
    [PreservesFiniteLimits G]
    {P : C ⥤ AddCommGrpCat.{v}} [P.Additive] [PreservesFiniteLimits P]

/-- The canonical comparison for a Hom functor represented after exact precomposition. -/
def representedPrecomposeRightDerivedIso (A : D)
    (e : P ≅ G ⋙ preadditiveCoyoneda.obj (op A)) (n : ℕ) :
    P.rightDerived n ≅ G ⋙ extFunctorObj A n :=
  rightDerivedFunctorIso e n ≪≫
    rightDerivedPrecomposeIso G (preadditiveCoyoneda.obj (op A)) n ≪≫
      Functor.isoWhiskerLeft G (rightDerivedCoyonedaNatIsoExt A n)

/-- Exact precomposition and the resolution-to-Ext comparison both retain
the standard `Ext⁰ = Hom` isomorphism. -/
@[reassoc]
theorem representedPrecomposeRightDerivedIso_zero (A : D)
    (e : P ≅ G ⋙ preadditiveCoyoneda.obj (op A)) (B : C) :
    (representedPrecomposeRightDerivedIso G A e 0).hom.app B ≫
        (extFunctorZeroIso A).hom.app (G.obj B) =
      P.rightDerivedZeroIsoSelf.hom.app B ≫ e.hom.app B := by
  simp only [representedPrecomposeRightDerivedIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.assoc]
  rw [← NatTrans.comp_app, rightDerivedCoyonedaNatIsoExt_zero,
    rightDerivedPrecomposeIso_zero]
  exact rightDerivedZeroIsoSelf_natTrans e.hom B

end PrecomposeHomZero

end SGA.SGA2.ExposeI
