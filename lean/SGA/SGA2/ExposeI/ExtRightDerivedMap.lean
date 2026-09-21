/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.ExactFunctorExtCocycles

/-!
# The canonical right-derived Hom comparison preserves exact-functor maps

The map of actual injective-resolution Hom complexes induced by an exact
functor agrees with its canonical map on derived-category Ext.
-/

noncomputable section

universe v u u'

open CategoryTheory Limits Opposite Abelian HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
    [Abelian C] [Abelian D] [HasExt.{v} C] [HasExt.{v} D]
    (G : C ⥤ D) [G.Additive] [G.PreservesHomology] [G.PreservesInjectiveObjects]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The actual map of resolution Hom complexes induced by the functor. -/
def injectiveCoyonedaExactFunctorMap (A : C) {B : C} (I : InjectiveResolution B) :
    injectiveCoyonedaComplex A I ⟶
      injectiveCoyonedaComplex (G.obj A) (mapInjectiveResolution G I) :=
  ((exactFunctorHomMap G A).mapHomologicalComplex _).app I.cocomplex

/-- The induced map on the original Ext-valued homology data. -/
def injectiveCoyonedaExactFunctorHomologyMapData (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ) n (n + 1) (n + 2)).map
        (injectiveCoyonedaExactFunctorMap G A I))
      (injectiveCoyonedaExtHomologyData A I n)
      (injectiveCoyonedaExtHomologyData (G.obj A) (mapInjectiveResolution G I) n) where
  φK := AddCommGrpCat.ofHom
    { toFun x := ⟨G.map x.val, by
        change G.map x.val ≫ G.map (I.cocomplex.d (n + 1) (n + 2)) = 0
        have hx : x.val ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := x.property
        rw [← G.map_comp, hx, G.map_zero]⟩
      map_zero' := Subtype.ext (G.map_zero _ _)
      map_add' x y := Subtype.ext G.map_add }
  φH := AddCommGrpCat.ofHom (G.mapExtAddHom A B (n + 1))
  commi := by ext x; rfl
  commf' := by
    ext x
    apply Subtype.ext
    exact G.map_comp x (I.cocomplex.d n (n + 1))
  commπ := by
    ext x
    exact extMk_mapExactFunctor I G x.val (n + 2) rfl x.property

/-- The positive-degree Hom-complex comparison retains exact-functor maps on Ext. -/
@[reassoc]
theorem injectiveCoyonedaHomologyIsoExtSucc_mapExactFunctor (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    homologyMap (injectiveCoyonedaExactFunctorMap G A I) (n + 1) ≫
        (injectiveCoyonedaHomologyIsoExtSucc (G.obj A) (mapInjectiveResolution G I) n).hom =
      (injectiveCoyonedaHomologyIsoExtSucc A I n).hom ≫
        AddCommGrpCat.ofHom (G.mapExtAddHom A B (n + 1)) := by
  let ψ := injectiveCoyonedaExactFunctorMap G A I
  have h := congrArg (fun q => ShortComplex.homologyMap q)
    ((natIsoSc' AddCommGrpCat (ComplexShape.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality ψ)
  dsimp only [injectiveCoyonedaHomologyIsoExtSucc, Iso.trans_hom]
  rw [← Category.assoc]
  have h' : homologyMap ψ (n + 1) ≫
      ((injectiveCoyonedaComplex (G.obj A) (mapInjectiveResolution G I)).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)).hom =
      ((injectiveCoyonedaComplex A I).homologyIsoSc'
        n (n + 1) (n + 2) (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap
        ((shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) (n + 2)).map ψ) := by
    simpa only [ShortComplex.homologyMap_comp, homologyIsoSc',
      ShortComplex.homologyMapIso_hom, homologyMap, isoSc', Iso.app_hom] using h
  rw [h', Category.assoc,
    (injectiveCoyonedaExactFunctorHomologyMapData G A I n).homologyMap_comm]
  rfl

section ResolutionComparison

variable [HasInjectiveResolutions C]

/-- The canonical Ext comparison can be computed on any actual injective resolution. -/
@[reassoc]
theorem isoRightDerivedObj_comp_extComparison (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) (n + 1)).hom ≫
        (injectiveCoyonedaHomologyIsoExtSucc A I n).hom =
      (rightDerivedCoyonedaIsoExt A B (n + 1)).hom := by
  let J := injectiveResolution B
  let φ : InjectiveResolution.Hom J I (𝟙 B) :=
    { hom := InjectiveResolution.desc (𝟙 B) I J
      ι_f_zero_comp_hom_f_zero := by simp }
  have h₁ : (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) (n + 1)).hom =
      (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) (n + 1)).hom ≫
        homologyMap (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).map φ.hom)
          (n + 1) := by
    have h := InjectiveResolution.isoRightDerivedObj_hom_naturality (𝟙 B) J I φ.hom
      (by simp [φ]) (preadditiveCoyoneda.obj (op A)) (n + 1)
    erw [((preadditiveCoyoneda.obj (op A)).rightDerived (n + 1)).map_id B,
      Category.id_comp] at h
    exact h
  have h₂ : homologyMap
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).map φ.hom) (n + 1) ≫
        (injectiveCoyonedaHomologyIsoExtSucc A I n).hom =
      (injectiveCoyonedaHomologyIsoExtSucc A J n).hom := by
    have h := injectiveCoyonedaHomologyIsoExtSucc_naturality A φ n
    erw [(extFunctorObj A (n + 1)).map_id B, Category.comp_id] at h
    exact h
  erw [h₁, Category.assoc, h₂]
  rfl

end ResolutionComparison

/-- Standard exact-functor restriction on Ext, naturally in the coefficient. -/
def exactFunctorExtMap (A : C) (n : ℕ) :
    extFunctorObj A n ⟶ G ⋙ extFunctorObj (G.obj A) n where
  app B := AddCommGrpCat.ofHom (G.mapExtAddHom A B n)
  naturality B B' f := by
    ext e
    change (e.comp (Ext.mk₀ f) (add_zero n)).mapExactFunctor G =
      (e.mapExactFunctor G).comp (Ext.mk₀ (G.map f)) (add_zero n)
    rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]

omit [G.PreservesHomology] [G.PreservesInjectiveObjects] in
/-- Standard exact-functor maps retain the usual `Ext⁰ = Hom` identification. -/
@[reassoc]
theorem exactFunctorExtMap_zero (A B : C) :
    (exactFunctorExtMap G A 0).app B ≫ (extFunctorZeroIso (G.obj A)).hom.app (G.obj B) =
      (extFunctorZeroIso A).hom.app B ≫ (exactFunctorHomMap G A).app B := by
  apply AddCommGrpCat.hom_ext
  ext e
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective A B).2 e
  change Ext.addEquiv₀ ((Ext.mk₀ f).mapExactFunctor G) = G.map (Ext.addEquiv₀ (Ext.mk₀ f))
  rw [Ext.mapExactFunctor_mk₀]
  simp only [← Ext.addEquiv₀_symm_apply, AddEquiv.apply_symm_apply]

variable [HasInjectiveResolutions C] [HasInjectiveResolutions D]

/-- The genuine right-derived map of Hom induced by the exact functor. -/
def rightDerivedExactFunctorHomMap (A : C) (n : ℕ) :
    (preadditiveCoyoneda.obj (op A)).rightDerived n ⟶
      G ⋙ (preadditiveCoyoneda.obj (op (G.obj A))).rightDerived n :=
  (exactFunctorHomMap G A).rightDerived n ≫
    (rightDerivedPrecomposeIso G (preadditiveCoyoneda.obj (op (G.obj A))) n).hom

/-- The canonical resolution-to-Ext comparison intertwines the derived
Hom map with the standard map induced by the exact functor, in every degree. -/
@[reassoc]
theorem rightDerivedCoyonedaIsoExt_mapExactFunctor (A B : C) (n : ℕ) :
    (rightDerivedExactFunctorHomMap G A n).app B ≫
        (rightDerivedCoyonedaNatIsoExt (G.obj A) n).hom.app (G.obj B) =
      (rightDerivedCoyonedaNatIsoExt A n).hom.app B ≫ (exactFunctorExtMap G A n).app B := by
  cases n with
  | zero =>
    apply (cancel_mono ((extFunctorZeroIso (G.obj A)).hom.app (G.obj B))).mp
    have hC := congrArg (fun α => α.app B) (rightDerivedCoyonedaNatIsoExt_zero A)
    have hD := congrArg (fun α => α.app (G.obj B))
      (rightDerivedCoyonedaNatIsoExt_zero (G.obj A))
    simp only [NatTrans.comp_app] at hC hD
    simp only [rightDerivedExactFunctorHomMap, NatTrans.comp_app, Category.assoc]
    rw [hD, rightDerivedPrecomposeIso_zero, rightDerivedZeroIsoSelf_natTrans,
      exactFunctorExtMap_zero, ← Category.assoc, hC]
  | succ n =>
    let I := injectiveResolution B
    let J := mapInjectiveResolution G I
    have hcmp : (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op (G.obj A))) (n + 1)).inv ≫
        (rightDerivedCoyonedaNatIsoExt (G.obj A) (n + 1)).hom.app (G.obj B) =
      (injectiveCoyonedaHomologyIsoExtSucc (G.obj A) J n).hom := by
      change _ ≫ (rightDerivedCoyonedaIsoExt (G.obj A) (G.obj B) (n + 1)).hom = _
      rw [← isoRightDerivedObj_comp_extComparison (G.obj A) J n]
      simp
    simp only [rightDerivedExactFunctorHomMap, NatTrans.comp_app,
      rightDerivedPrecomposeIso, NatIso.ofComponents_hom_app, rightDerivedPrecomposeObjIso,
      Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [I.rightDerived_app_eq (exactFunctorHomMap G A) (n + 1)]
    simp only [I, Category.assoc, Iso.inv_hom_id_assoc]
    change (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op A)) (n + 1)).hom ≫
      homologyMap (injectiveCoyonedaExactFunctorMap G A I) (n + 1) ≫
        (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op (G.obj A))) (n + 1)).inv ≫
          (rightDerivedCoyonedaNatIsoExt (G.obj A) (n + 1)).hom.app (G.obj B) = _
    rw [hcmp, injectiveCoyonedaHomologyIsoExtSucc_mapExactFunctor]
    rfl

/-- The exact-functor comparison as an equality of natural transformations. -/
theorem rightDerivedCoyonedaNatIsoExt_mapExactFunctor (A : C) (n : ℕ) :
    rightDerivedExactFunctorHomMap G A n ≫
        Functor.whiskerLeft G (rightDerivedCoyonedaNatIsoExt (G.obj A) n).hom =
      (rightDerivedCoyonedaNatIsoExt A n).hom ≫ exactFunctorExtMap G A n := by
  apply NatTrans.ext
  funext B
  exact rightDerivedCoyonedaIsoExt_mapExactFunctor G A B n

/-- A represented functor map induced by an exact functor gives precisely
its standard map on Ext after the canonical derived comparisons. -/
theorem representedExactFunctorMap_eq
    {P Q : C ⥤ AddCommGrpCat.{v}} [P.Additive] [Q.Additive]
    (A : C) (e : P ≅ preadditiveCoyoneda.obj (op A))
    (e' : Q ≅ G ⋙ preadditiveCoyoneda.obj (op (G.obj A))) (α : P ⟶ Q)
    (h : α ≫ e'.hom = e.hom ≫ exactFunctorHomMap G A) (n : ℕ) :
    (rightDerivedFunctorIso e n ≪≫ rightDerivedCoyonedaNatIsoExt A n).inv ≫
        α.rightDerived n ≫ (representedPrecomposeRightDerivedIso G (G.obj A) e' n).hom =
      exactFunctorExtMap G A n := by
  apply (cancel_epi (rightDerivedFunctorIso e n ≪≫ rightDerivedCoyonedaNatIsoExt A n).hom).mp
  simp only [Iso.hom_inv_id_assoc]
  have hd : α.rightDerived n ≫ e'.hom.rightDerived n =
      e.hom.rightDerived n ≫ (exactFunctorHomMap G A).rightDerived n := by
    simpa only [NatTrans.rightDerived_comp] using congrArg (fun β => β.rightDerived n) h
  simp only [representedPrecomposeRightDerivedIso, Iso.trans_hom,
    rightDerivedFunctorIso, Functor.isoWhiskerLeft_hom, Category.assoc]
  rw [← Category.assoc (α.rightDerived n) (e'.hom.rightDerived n), hd, Category.assoc]
  have hm := rightDerivedCoyonedaNatIsoExt_mapExactFunctor G A n
  dsimp only [rightDerivedExactFunctorHomMap] at hm
  rw [Category.assoc] at hm
  rw [hm]

end SGA.SGA2.ExposeI
