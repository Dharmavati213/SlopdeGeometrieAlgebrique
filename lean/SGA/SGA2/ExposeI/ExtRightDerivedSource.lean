/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.ExtRightDerived
import SGA.SGA2.ExposeI.RightDerivedSequenceNaturality
import SGA.SGA2.ExposeI.RightDerivedZeroNaturality

/-!
# First-variable naturality of the canonical right-derived Hom comparison

The actual comparison with derived-category Ext retains precomposition in
the source. On the injective-resolution Hom complexes this is literal
precomposition of cocycles; its compatibility with Ext is proved using the
original cocycle-to-Ext map.
-/

noncomputable section

universe v u

open CategoryTheory Limits Opposite Abelian HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]
  {A A' B : C} (f : A' ⟶ A) (I : InjectiveResolution B)

/-- Actual precomposition acts on the original Ext-valued homology data. -/
def injectiveCoyonedaPrecompHomologyMapData (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ) n (n + 1) (n + 2)).map
        (((preadditiveCoyoneda.map f.op).mapHomologicalComplex _).app I.cocomplex))
      (injectiveCoyonedaExtHomologyData A I n)
      (injectiveCoyonedaExtHomologyData A' I n) where
  φK := AddCommGrpCat.ofHom
    { toFun x := ⟨f ≫ x.val, by
        change (f ≫ x.val) ≫ I.cocomplex.d (n + 1) (n + 2) = 0
        have hx : x.val ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := x.property
        rw [Category.assoc, hx, comp_zero]⟩
      map_zero' := by apply Subtype.ext; exact comp_zero
      map_add' x y := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _) }
  φH := ((extFunctor (C := C) (n + 1)).map f.op).app B
  commi := by ext x; rfl
  commf' := by
    ext x
    apply Subtype.ext
    exact (Category.assoc f x (I.cocomplex.d n (n + 1))).symm
  commπ := by
    ext x
    exact I.mk₀_comp_extMk x.val (n + 2) rfl x.property f

/-- The original positive-degree Hom-complex comparison retains precomposition. -/
@[reassoc]
theorem injectiveCoyonedaHomologyIsoExtSucc_precomp (n : ℕ) :
    homologyMap (((preadditiveCoyoneda.map f.op).mapHomologicalComplex _).app I.cocomplex)
        (n + 1) ≫ (injectiveCoyonedaHomologyIsoExtSucc A' I n).hom =
      (injectiveCoyonedaHomologyIsoExtSucc A I n).hom ≫
        ((extFunctor (C := C) (n + 1)).map f.op).app B := by
  let ψ := ((preadditiveCoyoneda.map f.op).mapHomologicalComplex _).app I.cocomplex
  have h := congrArg (fun q ↦ ShortComplex.homologyMap q)
    ((natIsoSc' AddCommGrpCat (ComplexShape.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality ψ)
  dsimp only [injectiveCoyonedaHomologyIsoExtSucc, Iso.trans_hom]
  rw [← Category.assoc]
  have h' : homologyMap ψ (n + 1) ≫
      ((injectiveCoyonedaComplex A' I).homologyIsoSc' n (n + 1) (n + 2)
        (by simp) (by simp)).hom =
      ((injectiveCoyonedaComplex A I).homologyIsoSc' n (n + 1) (n + 2)
        (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap
        ((shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) (n + 2)).map ψ) := by
    simpa only [ShortComplex.homologyMap_comp, homologyIsoSc',
      ShortComplex.homologyMapIso_hom, homologyMap, isoSc', Iso.app_hom] using h
  rw [h', Category.assoc, (injectiveCoyonedaPrecompHomologyMapData f I n).homologyMap_comm]
  rfl

variable [HasInjectiveResolutions C]

/-- The canonical actual right-derived Hom comparison is natural in its source. -/
@[reassoc]
theorem rightDerivedCoyonedaIsoExt_precomp (B : C) (n : ℕ) :
    ((preadditiveCoyoneda.map f.op).rightDerived n).app B ≫
        (rightDerivedCoyonedaIsoExt A' B n).hom =
      (rightDerivedCoyonedaIsoExt A B n).hom ≫
        ((extFunctor (C := C) n).map f.op).app B := by
  cases n with
  | zero =>
      dsimp only [rightDerivedCoyonedaIsoExt, Iso.trans_hom, Iso.app_hom]
      erw [← Category.assoc, rightDerivedZeroIsoSelf_natTrans, Category.assoc]
      simp only [Category.assoc]
      apply congrArg (fun k ↦
        (preadditiveCoyoneda.obj (op A)).rightDerivedZeroIsoSelf.hom.app B ≫ k)
      apply AddCommGrpCat.hom_ext
      apply AddMonoidHom.ext
      intro x
      exact (Ext.mk₀_comp_mk₀ f x).symm
  | succ n =>
      dsimp only [rightDerivedCoyonedaIsoExt, Iso.trans_hom]
      rw [← Category.assoc, rightDerived_natTrans_comp_resolutionIso,
        Category.assoc, injectiveCoyonedaHomologyIsoExtSucc_precomp]
      simp only [Category.assoc]

/-- Naturality survives a genuine representation of both original functors. -/
@[reassoc]
theorem representedRightDerivedIso_precomp
    {P Q : C ⥤ AddCommGrpCat.{v}} [P.Additive] [Q.Additive]
    (e : preadditiveCoyoneda.obj (op A) ≅ P)
    (e' : preadditiveCoyoneda.obj (op A') ≅ Q) (τ : P ⟶ Q)
    (h : e.hom ≫ τ = preadditiveCoyoneda.map f.op ≫ e'.hom) (B : C) (n : ℕ) :
    (τ.rightDerived n).app B ≫
        ((rightDerivedFunctorIso e' n).symm ≪≫ rightDerivedCoyonedaNatIsoExt A' n).hom.app B =
      ((rightDerivedFunctorIso e n).symm ≪≫ rightDerivedCoyonedaNatIsoExt A n).hom.app B ≫
        ((extFunctor (C := C) n).map f.op).app B := by
  have h' := congrArg (fun α ↦ (α.rightDerived n).app B) h
  simp only [NatTrans.rightDerived_comp, NatTrans.comp_app] at h'
  apply (cancel_epi ((rightDerivedFunctorIso e n).hom.app B)).mp
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  change (e.hom.rightDerived n).app B ≫ (τ.rightDerived n).app B ≫
      (e'.inv.rightDerived n).app B ≫ (rightDerivedCoyonedaIsoExt A' B n).hom =
    (e.hom.rightDerived n).app B ≫ (e.inv.rightDerived n).app B ≫
      (rightDerivedCoyonedaIsoExt A B n).hom ≫ ((extFunctor n).map f.op).app B
  rw [← Category.assoc, h', Category.assoc]
  have he := congrArg (fun α ↦ (α.rightDerived n).app B) e.hom_inv_id
  have he' := congrArg (fun α ↦ (α.rightDerived n).app B) e'.hom_inv_id
  simp only [NatTrans.rightDerived_comp, NatTrans.comp_app, NatTrans.rightDerived_id,
    NatTrans.id_app] at he he'
  rw [← Category.assoc ((e'.hom.rightDerived n).app B) ((e'.inv.rightDerived n).app B),
    he', Category.id_comp, ← Category.assoc, he, Category.id_comp]
  exact rightDerivedCoyonedaIsoExt_precomp f B n

end SGA.SGA2.ExposeI
