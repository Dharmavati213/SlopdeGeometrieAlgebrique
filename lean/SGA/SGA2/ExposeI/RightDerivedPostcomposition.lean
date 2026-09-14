/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.DerivedSupportedSections
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Exact postcomposition and right-derived functors

An exact functor commutes with the actual homology objects of an injective
resolution. The resulting comparison is natural in the coefficient object;
it does not require the exact functor to preserve injectives.
-/

noncomputable section

open CategoryTheory Limits

namespace SGA.SGA2.ExposeI

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]

section Homology

variable (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
  {ι : Type*} (c : ComplexShape ι)

/-- Exact functors commute with homology of complexes. -/
def complexHomologyMapIso (K : HomologicalComplex D c) (n : ι) :
    ((G.mapHomologicalComplex c).obj K).homology n ≅ G.obj (K.homology n) :=
  (K.sc n).mapHomologyIso G

@[reassoc]
lemma complexHomologyMapIso_hom_naturality
    {K L : HomologicalComplex D c} (f : K ⟶ L) (n : ι) :
    HomologicalComplex.homologyMap ((G.mapHomologicalComplex c).map f) n ≫
        (complexHomologyMapIso G c L n).hom =
      (complexHomologyMapIso G c K n).hom ≫
        G.map (HomologicalComplex.homologyMap f n) :=
  ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor D c n).map f) G

/-- The preceding homology comparison as a natural isomorphism. -/
def complexHomologyMapNatIso (n : ι) :
    G.mapHomologicalComplex c ⋙ HomologicalComplex.homologyFunctor E c n ≅
      HomologicalComplex.homologyFunctor D c n ⋙ G :=
  NatIso.ofComponents (fun K ↦ complexHomologyMapIso G c K n)
    (fun f ↦ complexHomologyMapIso_hom_naturality G c f n)

end Homology

section RightDerived

variable [HasInjectiveResolutions C] (F : C ⥤ D) (G : D ⥤ E)
  [F.Additive] [G.Additive] [G.PreservesHomology]

/-- Exact postcomposition commutes with right derivation, at an object. -/
def rightDerivedPostcomposeObjIso (X : C) (n : ℕ) :
    ((F ⋙ G).rightDerived n).obj X ≅ G.obj ((F.rightDerived n).obj X) :=
  (injectiveResolution X).isoRightDerivedObj (F ⋙ G) n ≪≫
    complexHomologyMapIso G (ComplexShape.up ℕ)
      ((F.mapHomologicalComplex _).obj (injectiveResolution X).cocomplex) n ≪≫
    G.mapIso ((injectiveResolution X).isoRightDerivedObj F n).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma rightDerivedPostcomposeObjIso_hom_naturality
    {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    ((F ⋙ G).rightDerived n).map f ≫ (rightDerivedPostcomposeObjIso F G Y n).hom =
      (rightDerivedPostcomposeObjIso F G X n).hom ≫ G.map ((F.rightDerived n).map f) := by
  let I := injectiveResolution X
  let J := injectiveResolution Y
  let φ := InjectiveResolution.desc f J I
  have hφ : I.ι.f 0 ≫ φ.f 0 = f ≫ J.ι.f 0 :=
    InjectiveResolution.desc_commutes_zero f J I
  simp only [rightDerivedPostcomposeObjIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc]
  rw [← Category.assoc,
    InjectiveResolution.isoRightDerivedObj_hom_naturality f I J φ hφ (F ⋙ G) n,
    Category.assoc]
  erw [complexHomologyMapIso_hom_naturality_assoc G (ComplexShape.up ℕ)
    ((F.mapHomologicalComplex _).map φ) n]
  rw [← G.map_comp]
  erw [← InjectiveResolution.isoRightDerivedObj_inv_naturality f I J φ hφ F n]
  rw [G.map_comp]

/-- The natural comparison between actual right-derived functors and exact
postcomposition. -/
def rightDerivedPostcomposeIso (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F.rightDerived n ⋙ G :=
  NatIso.ofComponents (fun X ↦ rightDerivedPostcomposeObjIso F G X n)
    (fun f ↦ rightDerivedPostcomposeObjIso_hom_naturality F G f n)

end RightDerived

section Retraction

variable [HasInjectiveResolutions C] (F : C ⥤ D) (P : D ⥤ E) (L : E ⥤ D)
  [F.Additive] [P.Additive] [L.Additive] [L.PreservesHomology]

/-- A split coefficient embedding can be removed after right derivation by
applying its exact retraction. Sheafification is the principal application. -/
def rightDerivedExactRetractionIso (e : P ⋙ L ≅ 𝟭 D) (n : ℕ) :
    (F ⋙ P).rightDerived n ⋙ L ≅ F.rightDerived n :=
  (rightDerivedPostcomposeIso (F ⋙ P) L n).symm ≪≫
    rightDerivedFunctorIso
      (Functor.associator F P L ≪≫ Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F) n

end Retraction

end SGA.SGA2.ExposeI
