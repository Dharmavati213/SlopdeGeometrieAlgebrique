/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.HomComplexSingleComparison
import SGA.SGA2.ExposeV.SourceHomComplex

/-! # V.1: actual precomposition on Hom complexes

Precomposition by a quasi-isomorphism is a quasi-isomorphism of Hom complexes
when the target is K-injective. The proof tracks the actual cochains through
the homotopy and derived category comparisons.
-/

noncomputable section
universe w v u
open CategoryTheory Limits HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeV

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Actual precomposition, on the original graded families of morphisms. -/
def homComplexPrecomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) : HomComplex F G ⟶ HomComplex F' G where
  f n := AddCommGrpCat.ofHom
    { toFun z := (Cochain.ofHom f).comp z (zero_add n)
      map_zero' := by simp
      map_add' z w := by simp }
  comm' i j hij := by ext z; exact δ_ofHom_comp f z j

/-- The same precomposition on cohomology classes. -/
def homComplexClassPrecomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) (n : ℤ) :
    CohomologyClass F G n →+ CohomologyClass F' G n where
  toFun z := CohomologyClass.homAddEquiv.symm
    ((HomotopyCategory.quotient C _).map f ≫ CohomologyClass.homAddEquiv z)
  map_zero' := by simp
  map_add' z w := by simp [Preadditive.comp_add]

lemma homComplexClassPrecomp_mk {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) (n : ℤ) (z : Cocycle F G n) :
    homComplexClassPrecomp f G n (CohomologyClass.mk z) =
      CohomologyClass.mk (z.precomp f) := by
  apply CohomologyClass.homAddEquiv.injective
  simp [homComplexClassPrecomp, CohomologyClass.homAddEquiv, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_precomp]

/-- Compatibility with the concrete Hom-complex homology data. -/
def homComplexPrecompHomologyMapData {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
        (homComplexPrecomp f G))
      (HomComplex.leftHomologyData F G n) (HomComplex.leftHomologyData F' G n) where
  φK := AddCommGrpCat.ofHom
    { toFun z := z.precomp f
      map_zero' := by ext; simp [Cocycle.precomp]
      map_add' z w := by ext; simp [Cocycle.precomp] }
  φH := AddCommGrpCat.ofHom (homComplexClassPrecomp f G n)
  commi := rfl
  commf' := by ext z; apply Subtype.ext; exact (δ_ofHom_comp f z n).symm
  commπ := by ext z; exact homComplexClassPrecomp_mk f G n z

lemma homComplexHomologyAddEquiv_precomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) (n : ℤ) (z : (HomComplex F G).homology n) :
    HomComplex.homologyAddEquiv F' G n ((homologyMap (homComplexPrecomp f G) n) z) =
      homComplexClassPrecomp f G n (HomComplex.homologyAddEquiv F G n z) :=
  ConcreteCategory.congr_hom (homComplexPrecompHomologyMapData f G n).homologyMap_comm z

section Derived
variable [HasDerivedCategory.{w} C]

/-- The K-injective comparison is natural in the original source morphism. -/
lemma homComplexHomologyDerivedHomEquiv_precomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) [G.IsKInjective] (n : ℤ)
    (z : (HomComplex F G).homology n) :
    ExposeI.homComplexHomologyDerivedHomEquiv F' G n
        ((homologyMap (homComplexPrecomp f G) n) z) =
      DerivedCategory.Q.map f ≫ ExposeI.homComplexHomologyDerivedHomEquiv F G n z := by
  simp only [ExposeI.homComplexHomologyDerivedHomEquiv, AddEquiv.trans_apply,
    homComplexHomologyAddEquiv_precomp]
  simp only [homComplexClassPrecomp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddEquiv.apply_symm_apply]
  simp [Linear.homCongr_apply, Category.assoc]

end Derived

/-- Precomposition by a quasi-isomorphism preserves Hom-complex cohomology
when the target is K-injective. No derived-category existence hypothesis is
needed: the standard large derived category is used only in the proof. -/
instance homComplexPrecomp_quasiIso {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    [QuasiIso f] (G : CochainComplex C ℤ) [G.IsKInjective] :
    QuasiIso (homComplexPrecomp f G) := by
  let := HasDerivedCategory.standard C
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  let e := (ExposeI.homComplexHomologyDerivedHomEquiv F G n).trans
    ((Linear.homCongr ℤ (asIso (DerivedCategory.Q.map f)).symm (Iso.refl _)).toAddEquiv.trans
      (ExposeI.homComplexHomologyDerivedHomEquiv F' G n).symm)
  have he : ⇑(homologyMap (homComplexPrecomp f G) n).hom = e := by
    funext z
    apply (ExposeI.homComplexHomologyDerivedHomEquiv F' G n).injective
    simp [e, homComplexHomologyDerivedHomEquiv_precomp, Linear.homCongr_apply]
  rw [he]
  exact e.bijective

/-- Precomposition for the literal source differential, with no change of
its original cochain components. -/
def sourceHomPrecomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) : sourceHomComplex F G ⟶ sourceHomComplex F' G where
  f n := AddCommGrpCat.ofHom
    { toFun z := (Cochain.ofHom f).comp z (zero_add n)
      map_zero' := by simp
      map_add' z w := by simp }
  comm' i j hij := by
    ext z
    change sourceHomδ i j ((Cochain.ofHom f).comp z (zero_add i)) =
      (Cochain.ofHom f).comp (sourceHomδ i j z) (zero_add j)
    simp [sourceHomδ, δ_ofHom_comp]

/-- The explicit sign normalization commutes with actual precomposition. -/
@[reassoc]
lemma sourceHomComplexIso_precomp {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    (G : CochainComplex C ℤ) :
    sourceHomPrecomp f G ≫ (sourceHomComplexIso F' G).hom =
      (sourceHomComplexIso F G).hom ≫ homComplexPrecomp f G := by
  ext n z
  change Cochain F G n at z
  change sourceHomSign n • (Cochain.ofHom f).comp z (zero_add n) =
    (Cochain.ofHom f).comp (sourceHomSign n • z) (zero_add n)
  simp only [Cochain.comp_units_smul]

/-- The source convention has the same quasi-isomorphism invariance. -/
instance sourceHomPrecomp_quasiIso {F' F : CochainComplex C ℤ} (f : F' ⟶ F)
    [QuasiIso f] (G : CochainComplex C ℤ) [G.IsKInjective] :
    QuasiIso (sourceHomPrecomp f G) := by
  rw [← quasiIso_iff_comp_right (sourceHomPrecomp f G) (sourceHomComplexIso F' G).hom,
    sourceHomComplexIso_precomp]
  infer_instance

end SGA.SGA2.ExposeV
