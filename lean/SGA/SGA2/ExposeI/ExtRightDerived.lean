/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Ext as the actual right-derived Hom functor

The comparison is constructed from an injective resolution: its Hom cocycles
surject onto derived-category Ext, with exactly the coboundaries as kernel.
Thus Ext itself supplies homology data for the complex computing the actual
right-derived preadditive coyoneda functor.

`rightDerivedCoyonedaNatIsoExt` is natural in the coefficient object. The Ext
groups and the category's morphisms are taken in the same universe, so both
sides take values in the same category of abelian groups.
-/

noncomputable section

universe v u

open CategoryTheory Limits Opposite Abelian

namespace SGA.SGA2.ExposeI

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

/-- The Hom complex of an injective resolution. -/
abbrev injectiveCoyonedaComplex (A : C) {B : C} (I : InjectiveResolution B) :=
  ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
    I.cocomplex

/-- Three consecutive terms of the Hom complex in positive degree. -/
abbrev injectiveCoyonedaShortComplex (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :=
  (injectiveCoyonedaComplex A I).sc' n (n + 1) (n + 2)

/-- A cocycle in the Hom complex determines its actual Ext class. -/
def injectiveCoyonedaCocycleToExt (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    AddMonoidHom.ker (injectiveCoyonedaShortComplex A I n).g.hom →+
      Ext A B (n + 1) where
  toFun x := I.extMk x.1 (n + 2) rfl x.2
  map_zero' := I.extMk_zero (n + 2) rfl
  map_add' x y := (I.add_extMk x.1 y.1 (n + 2) rfl x.2 y.2).symm

lemma injectiveCoyonedaCocycleToExt_surjective (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    Function.Surjective (injectiveCoyonedaCocycleToExt A I n) := by
  intro x
  obtain ⟨f, hf, h⟩ := I.extMk_surjective x (n + 2) rfl
  exact ⟨⟨f, hf⟩, h⟩

set_option backward.isDefEq.respectTransparency false in
lemma injectiveCoyonedaCocycleToExt_eq_zero_iff (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ)
    (x : AddMonoidHom.ker (injectiveCoyonedaShortComplex A I n).g.hom) :
    injectiveCoyonedaCocycleToExt A I n x = 0 ↔
      ∃ y, (injectiveCoyonedaShortComplex A I n).abToCycles y = x := by
  change I.extMk x.1 (n + 2) rfl x.2 = 0 ↔ _
  rw [I.extMk_eq_zero_iff x.1 (n + 2) rfl x.2 n rfl]
  exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩,
    fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Ext is a choice of homology for the Hom complex of an injective resolution. -/
def injectiveCoyonedaExtHomologyData (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    (injectiveCoyonedaShortComplex A I n).LeftHomologyData where
  K := (injectiveCoyonedaShortComplex A I n).abLeftHomologyData.K
  H := AddCommGrpCat.of (Ext A B (n + 1))
  i := (injectiveCoyonedaShortComplex A I n).abLeftHomologyData.i
  π := AddCommGrpCat.ofHom (injectiveCoyonedaCocycleToExt A I n)
  wi := (injectiveCoyonedaShortComplex A I n).abLeftHomologyData.wi
  hi := (injectiveCoyonedaShortComplex A I n).abLeftHomologyData.hi
  wπ := by
    ext y
    exact (injectiveCoyonedaCocycleToExt_eq_zero_iff A I n _).mpr ⟨y, rfl⟩
  hπ := by
    apply Classical.choice
    apply (ShortComplex.exact_and_epi_g_iff_g_is_cokernel
      (ShortComplex.mk
        (AddCommGrpCat.ofHom (injectiveCoyonedaShortComplex A I n).abToCycles)
        (AddCommGrpCat.ofHom (injectiveCoyonedaCocycleToExt A I n))
        (by ext y; exact
          (injectiveCoyonedaCocycleToExt_eq_zero_iff A I n _).mpr ⟨y, rfl⟩))).mp
    constructor
    · rw [ShortComplex.ab_exact_iff]
      intro x hx
      exact (injectiveCoyonedaCocycleToExt_eq_zero_iff A I n x).mp hx
    · exact (AddCommGrpCat.epi_iff_surjective _).mpr
        (injectiveCoyonedaCocycleToExt_surjective A I n)

/-- Positive-degree homology of the injective Hom complex is Ext. -/
def injectiveCoyonedaHomologyIsoExtSucc (A : C) {B : C}
    (I : InjectiveResolution B) (n : ℕ) :
    (injectiveCoyonedaComplex A I).homology (n + 1) ≅
      AddCommGrpCat.of (Ext A B (n + 1)) :=
  (injectiveCoyonedaComplex A I).homologyIsoSc' n (n + 1) (n + 2)
    (by simp) (by simp) ≪≫ (injectiveCoyonedaExtHomologyData A I n).homologyIso

set_option backward.isDefEq.respectTransparency false in
/-- The action of a map of injective resolutions on the Ext homology data. -/
def injectiveCoyonedaExtHomologyMapData (A : C) {B B' : C}
    {I : InjectiveResolution B} {J : InjectiveResolution B'} {f : B ⟶ B'}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
        n (n + 1) (n + 2)).map
          (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).map φ.hom))
      (injectiveCoyonedaExtHomologyData A I n)
      (injectiveCoyonedaExtHomologyData A J n) where
  φK := AddCommGrpCat.ofHom
    { toFun := fun x ↦ ⟨x.1 ≫ φ.hom.f (n + 1), by
        change (x.1 ≫ φ.hom.f (n + 1)) ≫ J.cocomplex.d (n + 1) (n + 2) = 0
        have hx : x.1 ≫ I.cocomplex.d (n + 1) (n + 2) = 0 := x.2
        simp [reassoc_of% hx]⟩
      map_zero' := by ext; simp
      map_add' := by
        intro x y
        apply Subtype.ext
        exact Preadditive.add_comp _ _ _ _ _ _ }
  φH := (extFunctorObj A (n + 1)).map f
  commi := by ext; rfl
  commf' := by
    ext x
    apply Subtype.ext
    change (x ≫ I.cocomplex.d n (n + 1)) ≫ φ.hom.f (n + 1) =
      (x ≫ φ.hom.f n) ≫ J.cocomplex.d n (n + 1)
    simp
  commπ := by
    ext x
    exact InjectiveResolution.extMk_comp_mk₀ x.1 (n + 2) rfl x.2 φ

set_option backward.isDefEq.respectTransparency false in
/-- The positive-degree injective-resolution comparison respects maps of coefficients. -/
theorem injectiveCoyonedaHomologyIsoExtSucc_naturality (A : C) {B B' : C}
    {I : InjectiveResolution B} {J : InjectiveResolution B'} {f : B ⟶ B'}
    (φ : InjectiveResolution.Hom I J f) (n : ℕ) :
    HomologicalComplex.homologyMap
        (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).map φ.hom) (n + 1) ≫
      (injectiveCoyonedaHomologyIsoExtSucc A J n).hom =
    (injectiveCoyonedaHomologyIsoExtSucc A I n).hom ≫
      (extFunctorObj A (n + 1)).map f := by
  let ψ := ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).map φ.hom
  have h := congrArg (fun q ↦ ShortComplex.homologyMap q)
    ((HomologicalComplex.natIsoSc' AddCommGrpCat (ComplexShape.up ℕ)
      n (n + 1) (n + 2) (by simp) (by simp)).hom.naturality ψ)
  dsimp only [injectiveCoyonedaHomologyIsoExtSucc, Iso.trans_hom]
  rw [← Category.assoc]
  have h' : HomologicalComplex.homologyMap ψ (n + 1) ≫
      ((injectiveCoyonedaComplex A J).homologyIsoSc' n (n + 1) (n + 2)
        (by simp) (by simp)).hom =
      ((injectiveCoyonedaComplex A I).homologyIsoSc' n (n + 1) (n + 2)
        (by simp) (by simp)).hom ≫
      ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor' AddCommGrpCat (ComplexShape.up ℕ)
          n (n + 1) (n + 2)).map ψ) := by
    simpa only [ShortComplex.homologyMap_comp, HomologicalComplex.homologyIsoSc',
      ShortComplex.homologyMapIso_hom, HomologicalComplex.homologyMap,
      HomologicalComplex.isoSc', Iso.app_hom] using h
  rw [h', Category.assoc,
    (injectiveCoyonedaExtHomologyMapData A φ n).homologyMap_comm]
  rfl

variable [HasInjectiveResolutions C]

/-- The actual right-derived Hom functor agrees, objectwise in every degree,
with Ext defined using the derived category. -/
def rightDerivedCoyonedaIsoExt (A B : C) (n : ℕ) :
    ((preadditiveCoyoneda.obj (op A)).rightDerived n).obj B ≅
      AddCommGrpCat.of (Ext A B n) :=
  match n with
  | 0 => ((preadditiveCoyoneda.obj (op A)).rightDerivedZeroIsoSelf).app B ≪≫
      AddEquiv.toAddCommGrpIso Ext.addEquiv₀.symm
  | n + 1 => (injectiveResolution B).isoRightDerivedObj
      (preadditiveCoyoneda.obj (op A)) (n + 1) ≪≫
      injectiveCoyonedaHomologyIsoExtSucc A (injectiveResolution B) n

set_option backward.isDefEq.respectTransparency false in
/-- The comparison from the actual right-derived Hom functor to Ext is natural
in the coefficient object. -/
theorem rightDerivedCoyonedaIsoExt_naturality (A : C) {B B' : C}
    (f : B ⟶ B') (n : ℕ) :
    ((preadditiveCoyoneda.obj (op A)).rightDerived n).map f ≫
        (rightDerivedCoyonedaIsoExt A B' n).hom =
      (rightDerivedCoyonedaIsoExt A B n).hom ≫ (extFunctorObj A n).map f := by
  cases n with
  | zero =>
    dsimp only [rightDerivedCoyonedaIsoExt, Iso.trans_hom]
    erw [← Category.assoc,
      ((preadditiveCoyoneda.obj (op A)).rightDerivedZeroIsoSelf).hom.naturality f,
      Category.assoc]
    rw [Category.assoc]
    apply congrArg (fun q ↦
      ((preadditiveCoyoneda.obj (op A)).rightDerivedZeroIsoSelf.hom.app B) ≫ q)
    ext x
    exact (Ext.mk₀_comp_mk₀ x f).symm
  | succ n =>
    let I := injectiveResolution B
    let J := injectiveResolution B'
    let φ : InjectiveResolution.Hom I J f :=
      { hom := InjectiveResolution.desc f J I
        ι_f_zero_comp_hom_f_zero := by simp }
    dsimp only [rightDerivedCoyonedaIsoExt, Iso.trans_hom]
    rw [← Category.assoc,
      InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ.hom
        (by simp)
        (preadditiveCoyoneda.obj (op A)) (n + 1), Category.assoc]
    erw [injectiveCoyonedaHomologyIsoExtSucc_naturality A φ n]
    exact (Category.assoc _ _ _).symm

/-- Ext is naturally isomorphic to the actual right-derived Hom functor. -/
def rightDerivedCoyonedaNatIsoExt (A : C) (n : ℕ) :
    (preadditiveCoyoneda.obj (op A)).rightDerived n ≅ extFunctorObj A n :=
  NatIso.ofComponents (fun B ↦ rightDerivedCoyonedaIsoExt A B n)
    (fun f ↦ rightDerivedCoyonedaIsoExt_naturality A f n)

end SGA.SGA2.ExposeI
