/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleExtDerivedLinear
import SGA.SGA2.ExposeII.KoszulExtComparison

/-!
# First-variable naturality of the actual Ext comparison

The linear comparison commutes with the original contravariant Ext maps and
with precomposition by the degree-zero derived Ext class of a module map.
The proof uses genuine lifts between projective resolutions and the original
`mk₀_comp_extMk` formula on cocycle representatives.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite HomologicalComplex
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false

/-- The homology comparison with an explicit three-term complex is natural. -/
@[reassoc]
theorem homologyIsoSc'_naturality_for_Ext
    {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}
    {K L : HomologicalComplex C c} (f : K ⟶ L)
    (i j k : ι) (hi : c.prev j = i) (hk : c.next j = k) :
    homologyMap f j ≫ (L.homologyIsoSc' i j k hi hk).hom =
      (K.homologyIsoSc' i j k hi hk).hom ≫
        ShortComplex.homologyMap ((shortComplexFunctor' C c i j k).map f) := by
  subst i k
  simp only [homologyIsoSc'_eq_refl, Iso.refl_hom, Category.comp_id, Category.id_comp]
  rfl

/-- Actual precomposition of Hom cocycles by a projective-resolution lift. -/
def projectiveExtCocyclePrecomp {N N' : ModuleCat.{u} R}
    {P : ProjectiveResolution N} {Q : ProjectiveResolution N'}
    {f : N ⟶ N'} (φ : ProjectiveResolution.Hom P Q f)
    (M : ModuleCat.{u} R) (n : ℕ) :
    LinearMap.ker (projectiveModuleExtShortComplex Q M n).g.hom →ₗ[R]
      LinearMap.ker (projectiveModuleExtShortComplex P M n).g.hom where
  toFun x := ⟨φ.hom.f (n + 1) ≫ x.val, by
    have hx : Q.complex.d (n + 2) (n + 1) ≫ x.val = 0 := x.property
    change P.complex.d (n + 2) (n + 1) ≫ φ.hom.f (n + 1) ≫ x.val = 0
    rw [← φ.hom.comm_assoc, hx, comp_zero]⟩
  map_add' x y := Subtype.ext (Preadditive.comp_add _ _ _ _ _ _)
  map_smul' r x := Subtype.ext (Linear.comp_smul _ _ _ _ _ _)

/-- The original Ext precomposition is the induced map on actual linear Hom
homology data. -/
def projectiveExtPrecompHomologyData {N N' : ModuleCat.{u} R}
    {P : ProjectiveResolution N} {Q : ProjectiveResolution N'}
    {f : N ⟶ N'} (φ : ProjectiveResolution.Hom P Q f)
    (M : ModuleCat.{u} R) (n : ℕ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
        n (n + 1) (n + 2)).map
          ((homComplexFunctor (ComplexShape.down ℕ) M).map φ.hom.op))
      (projectiveModuleExtLinearHomologyData Q M n)
      (projectiveModuleExtLinearHomologyData P M n) where
  φK := ModuleCat.ofHom (projectiveExtCocyclePrecomp φ M n)
  φH := ModuleCat.ofHom ((Abelian.Ext.mk₀ f).precompOfLinear R M (zero_add (n + 1)))
  commi := by ext x; rfl
  commf' := by
    apply (cancel_mono (projectiveModuleExtLinearHomologyData P M n).i).mp
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    rw [show ModuleCat.ofHom (projectiveExtCocyclePrecomp φ M n) ≫
        (projectiveModuleExtLinearHomologyData P M n).i =
      (projectiveModuleExtLinearHomologyData Q M n).i ≫
        ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
          n (n + 1) (n + 2)).map
          ((homComplexFunctor (ComplexShape.down ℕ) M).map φ.hom.op)).τ₂ by ext x; rfl,
      ← Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((shortComplexFunctor' (ModuleCat R) (ComplexShape.up ℕ)
          n (n + 1) (n + 2)).map
          ((homComplexFunctor (ComplexShape.down ℕ) M).map φ.hom.op)).comm₁₂.symm
  commπ := by
    ext x
    exact ProjectiveResolution.mk₀_comp_extMk x.val (n + 2) rfl x.property φ

/-- Naturality on the original Hom-complex model, for any actual resolution lift. -/
@[reassoc]
theorem projectiveModuleHomologyLinearIsoExtSucc_naturality
    {N N' : ModuleCat.{u} R}
    {P : ProjectiveResolution N} {Q : ProjectiveResolution N'}
    {f : N ⟶ N'} (φ : ProjectiveResolution.Hom P Q f)
    (M : ModuleCat.{u} R) (n : ℕ) :
    homologyMap ((homComplexFunctor (ComplexShape.down ℕ) M).map φ.hom.op) (n + 1) ≫
        (projectiveModuleHomologyLinearIsoExtSucc P M n).hom =
      (projectiveModuleHomologyLinearIsoExtSucc Q M n).hom ≫
        ModuleCat.ofHom ((Abelian.Ext.mk₀ f).precompOfLinear R M (zero_add (n + 1))) := by
  dsimp only [projectiveModuleHomologyLinearIsoExtSucc, Iso.trans_hom]
  erw [homologyIsoSc'_naturality_for_Ext_assoc, Category.assoc,
    (projectiveExtPrecompHomologyData φ M n).homologyMap_comm]
  rfl

/-- The actual module-valued Ext map is carried to precomposition by its
original degree-zero derived Ext class, in every degree. -/
@[reassoc]
theorem moduleExtLinearIsoAbelianExt_naturality_first
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') (M : ModuleCat.{u} R) (i : ℕ) :
    ((_root_.Ext R (ModuleCat.{u} R) i).map f.op).app M ≫
        (moduleExtLinearIsoAbelianExt N M i).hom =
      (moduleExtLinearIsoAbelianExt N' M i).hom ≫
        ModuleCat.ofHom ((Abelian.Ext.mk₀ f).precompOfLinear R M (zero_add i)) := by
  cases i with
  | zero =>
      dsimp only [moduleExtLinearIsoAbelianExt, Iso.trans_hom]
      erw [← Category.assoc, (extZeroIsoHom M).hom.naturality f.op]
      simp only [Category.assoc]
      congr 1
      ext x
      exact (Abelian.Ext.mk₀_comp_mk₀ f x).symm
  | succ n =>
      let P := projectiveResolution N
      let Q := projectiveResolution N'
      let φ : ProjectiveResolution.Hom P Q f :=
        { hom := ProjectiveResolution.lift f P Q
          hom_f_zero_comp_π_f_zero := ProjectiveResolution.lift_commutes_zero f P Q }
      dsimp only [moduleExtLinearIsoAbelianExt, Iso.trans_hom]
      rw [projectiveResolution_isoExt_hom_naturality_assoc f P Q φ.hom
        (ProjectiveResolution.lift_commutes f P Q),
        projectiveModuleHomologyLinearIsoExtSucc_naturality]
      simp only [Category.assoc]
      rfl

/-- Pointwise form for the unchanged canonical linear equivalence. -/
theorem moduleExtLinearEquivAbelianExt_naturality_first
    {N N' : ModuleCat.{u} R} (f : N ⟶ N') (M : ModuleCat.{u} R) (i : ℕ)
    (x : (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N')).obj M)) :
    moduleExtLinearEquivAbelianExt N M i
        (((_root_.Ext R (ModuleCat.{u} R) i).map f.op).app M x) =
      (Abelian.Ext.mk₀ f).comp (moduleExtLinearEquivAbelianExt N' M i x) (zero_add i) :=
  ConcreteCategory.congr_hom (moduleExtLinearIsoAbelianExt_naturality_first f M i) x

end SGA.SGA2.ExposeIV
