/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.InjectiveResolutionSequenceComparison
import SGA.SGA2.ExposeV.InjectiveHomCovariantBoundary
import SGA.SGA2.ExposeV.HomComplexCovariantNaturality

/-! # Naturality of the fixed double-resolution Ext comparison

The already specified Hom-to-Ext equivalences intertwine actual precomposition
and postcomposition by augmentation-compatible resolution maps with the
original Ext maps. This includes model changes over identity maps, without
redefining either the comparison equivalence or the cohomology maps.
-/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

section Derived

variable [HasDerivedCategory C] {X Y : C}
  (I : InjectiveResolution X) (J : InjectiveResolution Y)

/-- The original derived augmentation isomorphism is natural for actual resolution maps. -/
@[reassoc]
theorem injectiveResolutionDerivedIso_naturality (f : X ⟶ Y)
    (φ : I.cochainComplex ⟶ J.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ J.ι') :
    (injectiveResolutionDerivedIso I).hom ≫ DerivedCategory.Q.map φ =
      (DerivedCategory.singleFunctor C 0).map f ≫ (injectiveResolutionDerivedIso J).hom := by
  change ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.app X ≫
    DerivedCategory.Q.map I.ι') ≫ DerivedCategory.Q.map φ = _
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, hφ,
    CategoryTheory.Functor.map_comp, ← Category.assoc]
  simpa only [injectiveResolutionDerivedIso, Iso.trans_hom, asIso_hom,
    Category.assoc, CategoryTheory.Functor.comp_map] using!
    ((DerivedCategory.singleFunctorIsoCompQ C 0).hom.naturality_assoc f
      (DerivedCategory.Q.map J.ι')).symm

/-- The inverse augmentation comparison is natural for the same original maps. -/
@[reassoc]
theorem injectiveResolutionDerivedIso_inv_naturality (f : X ⟶ Y)
    (φ : I.cochainComplex ⟶ J.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ J.ι') :
    DerivedCategory.Q.map φ ≫ (injectiveResolutionDerivedIso J).inv =
      (injectiveResolutionDerivedIso I).inv ≫ (DerivedCategory.singleFunctor C 0).map f := by
  apply (cancel_epi (injectiveResolutionDerivedIso I).hom).1
  rw [injectiveResolutionDerivedIso_naturality_assoc I J f φ hφ]
  simp

end Derived

variable [HasExt.{w} C] {X X' Y Y' : C}
  (I : InjectiveResolution X) (I' : InjectiveResolution X')
  (J : InjectiveResolution Y) (J' : InjectiveResolution Y')

/-- The unchanged class-level Ext comparison respects original precomposition. -/
theorem injectiveHomClassExt_precomp (f : X ⟶ X')
    (φ : I.cochainComplex ⟶ I'.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ I'.ι') (n : ℕ)
    (z : CohomologyClass I'.cochainComplex J.cochainComplex (n : ℤ)) :
    injectiveHomClassExt I J n (homComplexClassPrecomp φ J.cochainComplex n z) =
      (Abelian.Ext.mk₀ f).comp (injectiveHomClassExt I' J n z) (zero_add n) := by
  let := HasDerivedCategory.standard C
  obtain ⟨z, rfl⟩ := z.mk_surjective
  apply Abelian.Ext.ext
  simp only [homComplexClassPrecomp_mk, injectiveHomClassExt_mk_hom,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    Cocycle.equivHomShift_symm_precomp]
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [injectiveResolutionDerivedIso_naturality_assoc I I' f φ hφ]

/-- The unchanged class-level Ext comparison respects original postcomposition. -/
theorem injectiveHomClassExt_postcomp (g : Y ⟶ Y')
    (ψ : J.cochainComplex ⟶ J'.cochainComplex)
    (hψ : J.ι' ≫ ψ = (singleFunctor C 0).map g ≫ J'.ι') (n : ℕ)
    (z : CohomologyClass I.cochainComplex J.cochainComplex (n : ℤ)) :
    injectiveHomClassExt I J' n (homComplexClassPostcomp I.cochainComplex ψ n z) =
      (injectiveHomClassExt I J n z).comp (Abelian.Ext.mk₀ g) (add_zero n) := by
  let := HasDerivedCategory.standard C
  obtain ⟨z, rfl⟩ := z.mk_surjective
  apply Abelian.Ext.ext
  simp only [homComplexClassPostcomp_mk, injectiveHomClassExt_mk_hom,
    Abelian.Ext.comp_hom, Abelian.Ext.mk₀_hom, ShiftedHom.comp_mk₀,
    Cocycle.equivHomShift_symm_postcomp]
  simp only [ShiftedHom.map, CategoryTheory.Functor.map_comp, Category.assoc]
  erw [(DerivedCategory.Q.commShiftIso (n : ℤ)).hom.naturality_assoc]
  simp only [CategoryTheory.Functor.comp_map]
  rw [← CategoryTheory.Functor.map_comp,
    injectiveResolutionDerivedIso_inv_naturality J J' g ψ hψ,
    CategoryTheory.Functor.map_comp]

/-- The fixed equivalence on actual Hom-complex homology respects precomposition. -/
theorem injectiveHomologyExtAddEquiv_precomp (f : X ⟶ X')
    (φ : I.cochainComplex ⟶ I'.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ I'.ι') (n : ℕ)
    (z : (HomComplex I'.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyExtAddEquiv I J n (homologyMap (homComplexPrecomp φ J.cochainComplex) n z) =
      (Abelian.Ext.mk₀ f).comp (injectiveHomologyExtAddEquiv I' J n z) (zero_add n) := by
  simp only [injectiveHomologyExtAddEquiv_eq_class, homComplexHomologyAddEquiv_precomp]
  exact injectiveHomClassExt_precomp I I' J f φ hφ n _

/-- The fixed equivalence on actual Hom-complex homology respects postcomposition. -/
theorem injectiveHomologyExtAddEquiv_postcomp (g : Y ⟶ Y')
    (ψ : J.cochainComplex ⟶ J'.cochainComplex)
    (hψ : J.ι' ≫ ψ = (singleFunctor C 0).map g ≫ J'.ι') (n : ℕ)
    (z : (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyExtAddEquiv I J' n (homologyMap (homComplexPostcomp I.cochainComplex ψ) n z) =
      (injectiveHomologyExtAddEquiv I J n z).comp (Abelian.Ext.mk₀ g) (add_zero n) := by
  simp only [injectiveHomologyExtAddEquiv_eq_class, homComplexHomologyAddEquiv_naturality]
  exact injectiveHomClassExt_postcomp I J J' g ψ hψ n _

/-- The previously specified normalized source equivalence respects precomposition. -/
theorem sourceInjectiveHomologyExtAddEquiv_precomp (f : X ⟶ X')
    (φ : I.cochainComplex ⟶ I'.cochainComplex)
    (hφ : I.ι' ≫ φ = (singleFunctor C 0).map f ≫ I'.ι') (n : ℕ)
    (z : (sourceHomComplex I'.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I J n
        (homologyMap (sourceHomPrecomp φ J.cochainComplex) n z) =
      (Abelian.Ext.mk₀ f).comp (sourceInjectiveHomologyExtAddEquiv I' J n z) (zero_add n) := by
  simp only [sourceInjectiveHomologyExtAddEquiv_eq_class, sourceHomologyAddEquiv_precomp]
  exact injectiveHomClassExt_precomp I I' J f φ hφ n _

/-- The previously specified normalized source equivalence respects postcomposition. -/
theorem sourceInjectiveHomologyExtAddEquiv_postcomp (g : Y ⟶ Y')
    (ψ : J.cochainComplex ⟶ J'.cochainComplex)
    (hψ : J.ι' ≫ ψ = (singleFunctor C 0).map g ≫ J'.ι') (n : ℕ)
    (z : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I J' n
        (homologyMap (sourceHomPostcomp I.cochainComplex ψ) n z) =
      (sourceInjectiveHomologyExtAddEquiv I J n z).comp (Abelian.Ext.mk₀ g) (add_zero n) := by
  simp only [sourceInjectiveHomologyExtAddEquiv_eq_class, sourceHomologyAddEquiv_postcomp]
  exact injectiveHomClassExt_postcomp I J J' g ψ hψ n _

/-- Changing the first resolution leaves the value under the fixed Ext comparison unchanged. -/
theorem injectiveHomologyExtAddEquiv_precomp_modelChange (K : InjectiveResolution X)
    (φ : I.cochainComplex ⟶ K.cochainComplex) (hφ : I.ι' ≫ φ = K.ι') (n : ℕ)
    (z : (HomComplex K.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyExtAddEquiv I J n (homologyMap (homComplexPrecomp φ J.cochainComplex) n z) =
      injectiveHomologyExtAddEquiv K J n z := by
  simpa using injectiveHomologyExtAddEquiv_precomp I K J (𝟙 X) φ (by simpa using hφ) n z

/-- Changing the second resolution leaves the value under the fixed Ext comparison unchanged. -/
theorem injectiveHomologyExtAddEquiv_postcomp_modelChange (K : InjectiveResolution Y)
    (ψ : J.cochainComplex ⟶ K.cochainComplex) (hψ : J.ι' ≫ ψ = K.ι') (n : ℕ)
    (z : (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyExtAddEquiv I K n (homologyMap (homComplexPostcomp I.cochainComplex ψ) n z) =
      injectiveHomologyExtAddEquiv I J n z := by
  simpa using injectiveHomologyExtAddEquiv_postcomp I J K (𝟙 Y) ψ (by simpa using hψ) n z

/-- The normalized source comparison is unchanged by changing the first resolution. -/
theorem sourceInjectiveHomologyExtAddEquiv_precomp_modelChange (K : InjectiveResolution X)
    (φ : I.cochainComplex ⟶ K.cochainComplex) (hφ : I.ι' ≫ φ = K.ι') (n : ℕ)
    (z : (sourceHomComplex K.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I J n
        (homologyMap (sourceHomPrecomp φ J.cochainComplex) n z) =
      sourceInjectiveHomologyExtAddEquiv K J n z := by
  simpa using sourceInjectiveHomologyExtAddEquiv_precomp I K J (𝟙 X) φ
    (by simpa using hφ) n z

/-- The normalized source comparison is unchanged by changing the second resolution. -/
theorem sourceInjectiveHomologyExtAddEquiv_postcomp_modelChange (K : InjectiveResolution Y)
    (ψ : J.cochainComplex ⟶ K.cochainComplex) (hψ : J.ι' ≫ ψ = K.ι') (n : ℕ)
    (z : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I K n
        (homologyMap (sourceHomPostcomp I.cochainComplex ψ) n z) =
      sourceInjectiveHomologyExtAddEquiv I J n z := by
  simpa using sourceInjectiveHomologyExtAddEquiv_postcomp I J K (𝟙 Y) ψ
    (by simpa using hψ) n z

end SGA.SGA2.ExposeV
