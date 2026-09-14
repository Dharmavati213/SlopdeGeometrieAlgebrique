/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleExtDerivedNaturality

/-!
# Coefficient naturality of the actual Ext comparison

The existing linear comparison respects the original coefficient maps on
module-valued Ext and postcomposition by the degree-zero derived Ext class.
The proof uses actual postcomposition of projective-resolution Hom cocycles
and its compatibility with the original `ProjectiveResolution.extMk`.

No noetherianity, finiteness, or regularity hypotheses are required.  This
file does not assert compatibility with connecting homomorphisms.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomologicalComplex
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false

/-- Actual coefficient postcomposition on the original Hom cocycles. -/
def projectiveExtCocyclePostcomp {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (n : ℕ) :
    LinearMap.ker (projectiveModuleExtShortComplex P M n).g.hom →ₗ[R]
      LinearMap.ker (projectiveModuleExtShortComplex P M' n).g.hom where
  toFun x := ⟨x.val ≫ f, by
    have hx : P.complex.d (n + 2) (n + 1) ≫ x.val = 0 := x.property
    change P.complex.d (n + 2) (n + 1) ≫ x.val ≫ f = 0
    rw [← Category.assoc, hx, zero_comp]⟩
  map_add' x y := Subtype.ext (Preadditive.add_comp _ _ _ _ _ _)
  map_smul' r x := Subtype.ext (Linear.smul_comp _ _ _ _ _ _)

/-- Original Ext postcomposition is the induced map on the actual linear
Hom-complex homology data. -/
def projectiveExtPostcompHomologyData {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) {M M' : ModuleCat.{u} R}
    (f : M ⟶ M') (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
        n (n + 1) (n + 2)).map ((homCochainCoefficientFunctor P.complex).map f))
      (projectiveModuleExtLinearHomologyData P M n)
      (projectiveModuleExtLinearHomologyData P M' n) where
  φK := ModuleCat.ofHom (projectiveExtCocyclePostcomp P f n)
  φH := ModuleCat.ofHom ((Abelian.Ext.mk₀ f).postcompOfLinear R N (add_zero (n + 1)))
  commi := by ext x; rfl
  commf' := by
    apply (cancel_mono (projectiveModuleExtLinearHomologyData P M' n).i).mp
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    rw [show ModuleCat.ofHom (projectiveExtCocyclePostcomp P f n) ≫
        (projectiveModuleExtLinearHomologyData P M' n).i =
      (projectiveModuleExtLinearHomologyData P M n).i ≫
        ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
          n (n + 1) (n + 2)).map
          ((homCochainCoefficientFunctor P.complex).map f)).τ₂ by ext x; rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
      n (n + 1) (n + 2)).map
      ((homCochainCoefficientFunctor P.complex).map f)).comm₁₂.symm
  commπ := by
    ext x
    exact P.extMk_comp_mk₀ x.val (n + 2) rfl x.property f

/-- Coefficient naturality of the comparison on any actual projective
resolution, with the original coefficient cohomology maps. -/
@[reassoc]
theorem projectiveModuleHomologyLinearIsoExtSucc_naturality_coefficient
    {N : ModuleCat.{u} R} (P : ProjectiveResolution N)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') (n : ℕ) :
    ((homCohomologyBifunctor (n + 1)).obj (op P.complex)).map f ≫
        (projectiveModuleHomologyLinearIsoExtSucc P M' n).hom =
      (projectiveModuleHomologyLinearIsoExtSucc P M n).hom ≫
        ModuleCat.ofHom ((Abelian.Ext.mk₀ f).postcompOfLinear R N (add_zero (n + 1))) := by
  change homologyMap ((homCochainCoefficientFunctor P.complex).map f) (n + 1) ≫
    (projectiveModuleHomologyLinearIsoExtSucc P M' n).hom = _
  dsimp only [projectiveModuleHomologyLinearIsoExtSucc, Iso.trans_hom]
  erw [homologyIsoSc'_naturality_for_Ext_assoc, Category.assoc,
    (projectiveExtPostcompHomologyData P f n).homologyMap_comm]
  rfl

/-- The bifunctorial degree-zero comparison uses the same original
objectwise Ext-to-Hom isomorphism. -/
theorem extZeroIsoHomFunctor_app_app (N M : ModuleCat.{u} R) :
    (extZeroIsoHomFunctor.app (op N)).app M = (extZeroIsoHom M).app (op N) := by
  apply Iso.ext_inv
  rfl

/-- The original degree-zero Ext-to-Hom comparison respects coefficient maps. -/
@[reassoc]
theorem extZeroIsoHom_naturality_coefficient (N : ModuleCat.{u} R)
    {M M' : ModuleCat.{u} R} (f : M ⟶ M') :
    ((_root_.Ext R (ModuleCat.{u} R) 0).obj (op N)).map f ≫
        ((extZeroIsoHom M').app (op N)).hom =
      ((extZeroIsoHom M).app (op N)).hom ≫
        ((linearCoyoneda R (ModuleCat.{u} R)).obj (op N)).map f := by
  have h := (extZeroIsoHomFunctor.hom.app (op N)).naturality f
  change _ ≫ ((extZeroIsoHomFunctor.app (op N)).app M').hom =
    ((extZeroIsoHomFunctor.app (op N)).app M).hom ≫ _ at h
  rwa [extZeroIsoHomFunctor_app_app, extZeroIsoHomFunctor_app_app] at h

/-- The existing linear Ext comparison commutes with the actual coefficient
maps and original derived Ext postcomposition in every degree. -/
@[reassoc]
theorem moduleExtLinearIsoAbelianExt_naturality_coefficient
    (N : ModuleCat.{u} R) {M M' : ModuleCat.{u} R} (f : M ⟶ M') (i : ℕ) :
    ((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).map f ≫
        (moduleExtLinearIsoAbelianExt N M' i).hom =
      (moduleExtLinearIsoAbelianExt N M i).hom ≫
        ModuleCat.ofHom ((Abelian.Ext.mk₀ f).postcompOfLinear R N (add_zero i)) := by
  cases i with
  | zero =>
      dsimp only [moduleExtLinearIsoAbelianExt, Iso.trans_hom]
      erw [extZeroIsoHom_naturality_coefficient_assoc N f]
      simp only [Category.assoc]
      congr 1
      ext x
      exact (Abelian.Ext.mk₀_comp_mk₀ x f).symm
  | succ n =>
      dsimp only [moduleExtLinearIsoAbelianExt, Iso.trans_hom]
      rw [projectiveResolution_isoExt_coeff_naturality_assoc,
        projectiveModuleHomologyLinearIsoExtSucc_naturality_coefficient]
      simp only [Category.assoc]

/-- Pointwise coefficient naturality for the unchanged canonical linear
equivalence. -/
theorem moduleExtLinearEquivAbelianExt_naturality_coefficient
    (N : ModuleCat.{u} R) {M M' : ModuleCat.{u} R} (f : M ⟶ M') (i : ℕ)
    (x : (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj M)) :
    moduleExtLinearEquivAbelianExt N M' i
        (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).map f x) =
      (moduleExtLinearEquivAbelianExt N M i x).comp (Abelian.Ext.mk₀ f) (add_zero i) :=
  ConcreteCategory.congr_hom (moduleExtLinearIsoAbelianExt_naturality_coefficient N f i) x

end SGA.SGA2.ExposeIV
