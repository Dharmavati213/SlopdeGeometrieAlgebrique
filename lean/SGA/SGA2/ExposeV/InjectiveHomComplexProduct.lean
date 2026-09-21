/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.InjectiveHomComplexExt
import SGA.SGA2.ExposeV.SourceHomComplexCohomology

/-! # V.1: the actual double-resolution product and Yoneda composition -/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {X Y Z : C} (I : InjectiveResolution X) (J : InjectiveResolution Y)
  (K : InjectiveResolution Z)

/-- The class-level Ext comparison using the actual augmentation of the
first resolution and Mathlib's comparison for the second resolution. -/
def injectiveHomClassExt (n : ℕ) :
    CohomologyClass I.cochainComplex J.cochainComplex (n : ℤ) →+ Abelian.Ext X Y n :=
  J.extAddEquivCohomologyClass.symm.toAddMonoidHom.comp
    (homComplexClassPrecomp I.ι' J.cochainComplex (n : ℤ))

omit [HasExt C] in
/-- Cancelling the explicit sign and single-source isomorphisms recovers
the original precomposition map of standard Hom complexes. -/
theorem sourceInjectiveHomAugmentation_cancel :
    (sourceHomComplexIso I.cochainComplex J.cochainComplex).inv ≫
      sourceInjectiveHomAugmentation I J ≫
        (ExposeI.homComplexFromSingleIso X J.cochainComplex).inv =
      homComplexPrecomp I.ι' J.cochainComplex := by
  simp only [sourceInjectiveHomAugmentation, ← Category.assoc,
    sourceHomComplexIso_precomp]
  simp

/-- The class calculation is the previously constructed comparison on the
actual Hom-complex homology, not a new choice of Ext isomorphism. -/
theorem injectiveHomologyExtAddEquiv_eq_class (n : ℕ)
    (z : (HomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    injectiveHomologyExtAddEquiv I J n z =
      injectiveHomClassExt I J n
        (HomComplex.homologyAddEquiv I.cochainComplex J.cochainComplex (n : ℤ) z) := by
  have hc := congrArg (fun f : HomComplex I.cochainComplex J.cochainComplex ⟶
      HomComplex ((singleFunctor C 0).obj X) J.cochainComplex =>
        (homologyMap f (n : ℤ)) z)
    (sourceInjectiveHomAugmentation_cancel I J)
  simp only [homologyMap_comp, ConcreteCategory.comp_apply] at hc
  change J.extAddEquivCohomologyClass.symm
      (HomComplex.homologyAddEquiv ((singleFunctor C 0).obj X) J.cochainComplex (n : ℤ)
        ((homologyMap (ExposeI.homComplexFromSingleIso X J.cochainComplex).inv (n : ℤ))
          ((homologyMap (sourceInjectiveHomAugmentation I J) (n : ℤ))
            ((homologyMap (sourceHomComplexIso I.cochainComplex J.cochainComplex).inv
              (n : ℤ)) z)))) = _
  exact (congrArg (fun t => J.extAddEquivCohomologyClass.symm
    (HomComplex.homologyAddEquiv ((singleFunctor C 0).obj X) J.cochainComplex (n : ℤ) t))
      hc).trans (congrArg J.extAddEquivCohomologyClass.symm
        (homComplexHomologyAddEquiv_precomp I.ι' J.cochainComplex (n : ℤ) z))

/-- The class map is an additive equivalence, through the same already
specified augmentation comparison on actual homology. -/
def injectiveHomClassExtAddEquiv (n : ℕ) :
    CohomologyClass I.cochainComplex J.cochainComplex (n : ℤ) ≃+ Abelian.Ext X Y n :=
  (HomComplex.homologyAddEquiv I.cochainComplex J.cochainComplex (n : ℤ)).symm.trans
    (injectiveHomologyExtAddEquiv I J n)

@[simp]
theorem injectiveHomClassExtAddEquiv_apply (n : ℕ)
    (z : CohomologyClass I.cochainComplex J.cochainComplex (n : ℤ)) :
    injectiveHomClassExtAddEquiv I J n z = injectiveHomClassExt I J n z := by
  simp [injectiveHomClassExtAddEquiv, injectiveHomologyExtAddEquiv_eq_class]

section Derived
variable [HasDerivedCategory C]

/-- The specified resolution's original augmentation as a derived isomorphism. -/
def injectiveResolutionDerivedIso (I : InjectiveResolution X) :
    (DerivedCategory.singleFunctor C 0).obj X ≅ DerivedCategory.Q.obj I.cochainComplex :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app X ≪≫ asIso (DerivedCategory.Q.map I.ι')

/-- The Ext representative is exactly the original graded cocycle between
the two actual resolution augmentations. -/
theorem injectiveHomClassExt_mk_hom {n : ℕ}
    (z : Cocycle I.cochainComplex J.cochainComplex (n : ℤ)) :
    (injectiveHomClassExt I J n (CohomologyClass.mk z)).hom =
      (injectiveResolutionDerivedIso I).hom ≫
        ShiftedHom.map (Cocycle.equivHomShift.symm z) DerivedCategory.Q ≫
          ((injectiveResolutionDerivedIso J).inv)⟦(n : ℤ)⟧' := by
  change (J.extEquivCohomologyClass.symm
    (homComplexClassPrecomp I.ι' J.cochainComplex (n : ℤ) (CohomologyClass.mk z))).hom = _
  rw [homComplexClassPrecomp_mk, InjectiveResolution.extEquivCohomologyClass_symm_mk_hom]
  simp [injectiveResolutionDerivedIso, Cocycle.equivHomShift_symm_precomp,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc]

end Derived

/-- **V.1, formulas (11) and (1.5):** the product of the original graded
cohomology classes is carried to actual Yoneda composition by the
augmentation comparison. -/
theorem injectiveHomClassExt_comp {i j k : ℕ} (h : i + j = k)
    (z : CohomologyClass I.cochainComplex J.cochainComplex (i : ℤ))
    (w : CohomologyClass J.cochainComplex K.cochainComplex (j : ℤ)) :
    injectiveHomClassExt I K k (homClassComp (by exact_mod_cast h) z w) =
      (injectiveHomClassExt I J i z).comp (injectiveHomClassExt J K j w) h := by
  let := HasDerivedCategory.standard C
  obtain ⟨z, rfl⟩ := z.mk_surjective
  obtain ⟨w, rfl⟩ := w.mk_surjective
  apply Abelian.Ext.ext
  simp only [homClassComp_mk, injectiveHomClassExt_mk_hom, Abelian.Ext.comp_hom,
    homCocycleComp_equivHomShift, ShiftedHom.map_comp]
  simp only [ShiftedHom.comp, Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc]
  rw [← NatTrans.naturality]
  simp only [Iso.inv_hom_id_assoc, Functor.map_comp, Functor.comp_map, Category.assoc]

/-- The actual Hom-complex homology product agrees with the Yoneda product
under the previously constructed double-resolution Ext equivalence. -/
theorem injectiveHomologyExtAddEquiv_comp {i j k : ℕ} (h : i + j = k)
    (z : (HomComplex I.cochainComplex J.cochainComplex).homology (i : ℤ))
    (w : (HomComplex J.cochainComplex K.cochainComplex).homology (j : ℤ)) :
    injectiveHomologyExtAddEquiv I K k (homologyComp (by exact_mod_cast h) z w) =
      (injectiveHomologyExtAddEquiv I J i z).comp
        (injectiveHomologyExtAddEquiv J K j w) h := by
  simp only [injectiveHomologyExtAddEquiv_eq_class, homologyAddEquiv_homologyComp]
  exact injectiveHomClassExt_comp I J K h _ _

/-- The source Ext comparison is the same augmentation class map, after the
already specified sign normalization on actual source homology. -/
theorem sourceInjectiveHomologyExtAddEquiv_eq_class (n : ℕ)
    (z : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (n : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I J n z =
      injectiveHomClassExt I J n
        (sourceHomologyAddEquiv I.cochainComplex J.cochainComplex (n : ℤ) z) := by
  rw [sourceInjectiveHomologyExtAddEquiv_eq_normalized,
    injectiveHomologyExtAddEquiv_eq_class]
  rfl

/-- The literal source Hom-complex product is carried to Yoneda composition
with exactly `(-1)^(ij)` under the sign-normalized augmentation. No unsigned
product comparison is claimed for the incompatible displayed conventions. -/
theorem sourceInjectiveHomologyExtAddEquiv_comp {i j k : ℕ} (h : i + j = k)
    (z : (sourceHomComplex I.cochainComplex J.cochainComplex).homology (i : ℤ))
    (w : (sourceHomComplex J.cochainComplex K.cochainComplex).homology (j : ℤ)) :
    sourceInjectiveHomologyExtAddEquiv I K k
        (sourceHomologyComp (by exact_mod_cast h) z w) =
      ((i : ℤ) * (j : ℤ)).negOnePow •
        (sourceInjectiveHomologyExtAddEquiv I J i z).comp
          (sourceInjectiveHomologyExtAddEquiv J K j w) h := by
  simp only [sourceInjectiveHomologyExtAddEquiv_eq_class, sourceHomologyAddEquiv_comp,
    Units.smul_def, map_zsmul]
  rw [injectiveHomClassExt_comp I J K h]

end SGA.SGA2.ExposeV
