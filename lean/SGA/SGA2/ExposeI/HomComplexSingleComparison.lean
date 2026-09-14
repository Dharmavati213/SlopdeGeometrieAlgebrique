/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-!
# Single-source Hom complexes and K-injective derived Hom

These comparisons identify genuine Hom-complex cohomology with derived Hom
into a K-injective complex. Extension by zero commutes with any additive
functor; this is an isomorphism of complexes, not an acyclicity assumption.
-/

noncomputable section

universe w v u v' u'

open CategoryTheory Limits Opposite HomologicalComplex CochainComplex
open CochainComplex.HomComplex

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Hom complex from a sheaf in degree zero is the ordinary complex
obtained by applying additive Hom degree by degree. -/
def homComplexFromSingleIso (A : C) (K : CochainComplex C ℤ) :
    HomComplex ((CochainComplex.singleFunctor C 0).obj A) K ≅
      ((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex _).obj K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (Cochain.fromSingleEquiv (p := 0) (q := n) (n := n)
      (zero_add n)).toAddCommGrpIso)
    (by
      intro i j hij
      ext x
      obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x i (zero_add i)
      change Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk f (zero_add i)) ≫
          K.d i j =
        Cochain.fromSingleEquiv (zero_add j)
          (δ i j (Cochain.fromSingleMk f (zero_add i)))
      rw [Cochain.δ_fromSingleMk _ _ j j (zero_add j)]
      simp)

variable [HasDerivedCategory.{w} C]

/-- K-injectivity gives an actual additive equivalence from Hom-complex
cohomology to morphisms in the derived category. -/
def homComplexHomologyDerivedHomEquiv (K L : CochainComplex C ℤ)
    [L.IsKInjective] (n : ℤ) :
    (HomComplex K L).homology n ≃+
      (DerivedCategory.Q.obj K ⟶ (DerivedCategory.Q.obj L)⟦n⟧) :=
  (HomComplex.homologyAddEquiv K L n).trans
    (CohomologyClass.homAddEquiv.trans
      ((AddEquiv.ofBijective (DerivedCategory.Qh.mapAddHom)
        (CochainComplex.IsKInjective.Qh_map_bijective
          ((HomotopyCategory.quotient C _).obj K) (L⟦n⟧))).trans
        (Linear.homCongr ℤ
          ((DerivedCategory.quotientCompQhIso C).app K)
          ((DerivedCategory.quotientCompQhIso C).app (L⟦n⟧) ≪≫
            (DerivedCategory.Q.commShiftIso n).app L)).toAddEquiv))

end

section

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (P : C ⥤ D) [P.Additive]
  {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
  (e : c.Embedding c') (K : HomologicalComplex C c)

/-- Components of the canonical commutation of an additive functor with
extension by zero. -/
def mapExtendXIso (i : ι') :
    P.obj ((K.extend e).X i) ≅
      ((((P.mapHomologicalComplex c).obj K).extend e).X i) := by
  classical
  by_cases h : ∃ a, e.f a = i
  · exact P.mapIso (K.extendXIso e (Classical.choose_spec h)) ≪≫
      (((P.mapHomologicalComplex c).obj K).extendXIso e (Classical.choose_spec h)).symm
  · exact (P.map_isZero (K.isZero_extend_X e i (by simpa using h))).iso
      (((P.mapHomologicalComplex c).obj K).isZero_extend_X e i (by simpa using h))

lemma mapExtendXIso_eq (i : ι') (a : ι) (ha : e.f a = i) :
    mapExtendXIso P e K i = P.mapIso (K.extendXIso e ha) ≪≫
      (((P.mapHomologicalComplex c).obj K).extendXIso e ha).symm := by
  classical
  unfold mapExtendXIso
  rw [dite_eq_left ⟨a, ha⟩]
  have h : Classical.choose (show ∃ a, e.f a = i from ⟨a, ha⟩) = a :=
    e.injective_f ((Classical.choose_spec (show ∃ a, e.f a = i from ⟨a, ha⟩)).trans ha.symm)
  have hs : (⟨Classical.choose (show ∃ a, e.f a = i from ⟨a, ha⟩),
      Classical.choose_spec (show ∃ a, e.f a = i from ⟨a, ha⟩)⟩ : {b // e.f b = i}) =
      ⟨a, ha⟩ := Subtype.ext h
  exact congrArg (fun b : {b // e.f b = i} => P.mapIso (K.extendXIso e b.2) ≪≫
    (((P.mapHomologicalComplex c).obj K).extendXIso e b.2).symm) hs

/-- Applying an additive functor commutes with extension by zero as actual
complexes. -/
def mapExtendIso :
    (P.mapHomologicalComplex c').obj (K.extend e) ≅
      ((P.mapHomologicalComplex c).obj K).extend e :=
  HomologicalComplex.Hom.isoOfComponents (mapExtendXIso P e K) (by
    classical
    intro i j hij
    by_cases hi : ∃ a, e.f a = i
    · obtain ⟨a, ha⟩ := hi
      by_cases hj : ∃ b, e.f b = j
      · obtain ⟨b, hb⟩ := hj
        rw [mapExtendXIso_eq P e K i a ha, mapExtendXIso_eq P e K j b hb]
        change _ ≫ (((P.mapHomologicalComplex c).obj K).extend e).d i j =
          P.map ((K.extend e).d i j) ≫ _
        rw [HomologicalComplex.extend_d_eq _ _ ha hb,
          HomologicalComplex.extend_d_eq _ _ ha hb]
        simp
      · exact (((P.mapHomologicalComplex c).obj K).isZero_extend_X e j
          (by simpa using hj)).eq_of_tgt _ _
    · exact (P.map_isZero (K.isZero_extend_X e i
        (by simpa using hi))).eq_of_src _ _)

end

end SGA.SGA2.ExposeI
