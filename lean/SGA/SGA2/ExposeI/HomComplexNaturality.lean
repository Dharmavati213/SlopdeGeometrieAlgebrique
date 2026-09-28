/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.HomComplexSingleComparison

/-! # Naturality of the actual K-injective Hom-complex comparison -/

noncomputable section

universe w v u v' u'

open CategoryTheory Limits Opposite HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Actual postcomposition on the Hom complex. -/
def homComplexPostcomp (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ} (f : L ⟶ M) :
    HomComplex K L ⟶ HomComplex K M where
  f n := AddCommGrpCat.ofHom
    { toFun x := x.comp (Cochain.ofHom f) (add_zero n)
      map_zero' := by simp
      map_add' x y := by simp }
  comm' i j hij := by ext x; exact δ_comp_ofHom x f j

/-- The induced map of cohomology classes, written using the actual homotopy
category correspondence. -/
def homComplexClassPostcomp (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) : CohomologyClass K L n →+ CohomologyClass K M n where
  toFun x := CohomologyClass.homAddEquiv.symm
    (CohomologyClass.homAddEquiv x ≫ (HomotopyCategory.quotient C _).map (f⟦n⟧'))
  map_zero' := by simp
  map_add' x y := by simp [Preadditive.add_comp]

lemma homComplexClassPostcomp_mk (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) (x : Cocycle K L n) :
    homComplexClassPostcomp K f n (CohomologyClass.mk x) =
      CohomologyClass.mk (x.postcomp f) := by
  apply CohomologyClass.homAddEquiv.injective
  simp [homComplexClassPostcomp, CohomologyClass.homAddEquiv, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp]

/-- The class map is compatible with the chosen Hom-complex homology data. -/
def homComplexPostcompHomologyMapData (K : CochainComplex C ℤ) {L M : CochainComplex C ℤ}
    (f : L ⟶ M) (n : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℤ) n).map
        (homComplexPostcomp K f))
      (HomComplex.leftHomologyData K L n) (HomComplex.leftHomologyData K M n) where
  φK := AddCommGrpCat.ofHom
    { toFun x := x.postcomp f
      map_zero' := by ext; simp [Cocycle.postcomp]
      map_add' x y := by ext; simp [Cocycle.postcomp] }
  φH := AddCommGrpCat.ofHom (homComplexClassPostcomp K f n)
  commi := rfl
  commf' := by ext x; apply Subtype.ext; exact (δ_comp_ofHom x f n).symm
  commπ := by ext x; exact homComplexClassPostcomp_mk K f n x

lemma homComplexHomologyAddEquiv_naturality (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} (f : L ⟶ M) (n : ℤ) (x : (HomComplex K L).homology n) :
    HomComplex.homologyAddEquiv K M n ((homologyMap (homComplexPostcomp K f) n) x) =
      homComplexClassPostcomp K f n (HomComplex.homologyAddEquiv K L n x) :=
  ConcreteCategory.congr_hom (homComplexPostcompHomologyMapData K f n).homologyMap_comm x

/-- The single-source complex comparison commutes with actual coefficient maps. -/
@[reassoc]
lemma homComplexFromSingleIso_naturality (A : C) {K L : CochainComplex C ℤ} (f : K ⟶ L) :
    homComplexPostcomp ((CochainComplex.singleFunctor C 0).obj A) f ≫
        (homComplexFromSingleIso A L).hom =
      (homComplexFromSingleIso A K).hom ≫
        ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).map f := by
  ext n x
  change Cochain.fromSingleEquiv (zero_add n)
      (x.comp (Cochain.ofHom f) (add_zero n)) =
    Cochain.fromSingleEquiv (zero_add n) x ≫ f.f n
  simp [Cochain.fromSingleEquiv, Category.assoc]

/-- Extension-by-zero commutation is natural in the actual complex. -/
@[reassoc]
lemma mapExtendIso_naturality {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
    (P : C ⥤ D) [P.Additive]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') {K L : HomologicalComplex C c} (f : K ⟶ L) :
    (P.mapHomologicalComplex c').map (extendMap f e) ≫ (mapExtendIso P e L).hom =
      (mapExtendIso P e K).hom ≫ extendMap ((P.mapHomologicalComplex c).map f) e := by
  classical
  ext i
  change P.map ((extendMap f e).f i) ≫ (mapExtendXIso P e L i).hom =
    (mapExtendXIso P e K i).hom ≫ (extendMap ((P.mapHomologicalComplex c).map f) e).f i
  by_cases hi : ∃ a, e.f a = i
  · obtain ⟨a, ha⟩ := hi
    rw [mapExtendXIso_eq P e L i a ha, mapExtendXIso_eq P e K i a ha,
      extendMap_f f e ha, extendMap_f _ e ha]
    simp
  · exact (P.map_isZero (K.isZero_extend_X e i (by simpa using hi))).eq_of_src _ _

variable [HasDerivedCategory.{w} C]

/-- The actual K-injective derived-Hom comparison is natural in the target
complex. -/
lemma homComplexHomologyDerivedHomEquiv_naturality (K : CochainComplex C ℤ)
    {L M : CochainComplex C ℤ} [L.IsKInjective] [M.IsKInjective]
    (f : L ⟶ M) (n : ℤ) (x : (HomComplex K L).homology n) :
    homComplexHomologyDerivedHomEquiv K M n ((homologyMap (homComplexPostcomp K f) n) x) =
      homComplexHomologyDerivedHomEquiv K L n x ≫ (DerivedCategory.Q.map f)⟦n⟧' := by
  simp only [homComplexHomologyDerivedHomEquiv, AddEquiv.trans_apply,
    homComplexHomologyAddEquiv_naturality]
  simp only [homComplexClassPostcomp, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    AddEquiv.apply_symm_apply]
  simp [Linear.homCongr_apply, Category.assoc]

end SGA.SGA2.ExposeI
