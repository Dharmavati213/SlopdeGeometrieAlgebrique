/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.InjectiveResolutionIntCohomology
import SGA.SGA2.ExposeI.RightDerivedPostcomposition

/-!
# Natural transformations through the original resolution comparisons

The integer-indexed resolution and exact-postcomposition comparisons retain
natural transformations of the functor being derived. This includes scalar
endomorphisms of an additive forgetful functor, without requiring the scalar
maps to be linear over a noncommutative structure ring.
-/

noncomputable section

open CategoryTheory CategoryTheory.Functor Limits HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]

/-- The original single-complex/forgetful comparison retains natural transformations. -/
@[reassoc]
theorem singleMapHomologicalComplex_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) {ι : Type*} (c : ComplexShape ι) [DecidableEq ι] (j : ι) (M : C) :
    (single D c j).map (τ.app M) ≫ (singleMapHomologicalComplex G c j).inv.app M =
      (singleMapHomologicalComplex F c j).inv.app M ≫
        (τ.mapHomologicalComplex c).app ((single C c j).obj M) := by
  apply from_single_hom_ext
  simp [single_map_f_self]

/-- Extension-by-zero commutation retains natural transformations of the additive functor. -/
@[reassoc]
theorem mapExtendIso_natTrans {F G : C ⥤ D} [F.Additive] [G.Additive]
    (τ : F ⟶ G) {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'}
    (e : c.Embedding c') (K : HomologicalComplex C c) :
    (τ.mapHomologicalComplex c').app (K.extend e) ≫ (mapExtendIso G e K).hom =
      (mapExtendIso F e K).hom ≫ extendMap ((τ.mapHomologicalComplex c).app K) e := by
  classical
  ext i
  change τ.app ((K.extend e).X i) ≫ (mapExtendXIso G e K i).hom =
    (mapExtendXIso F e K i).hom ≫ (extendMap ((τ.mapHomologicalComplex c).app K) e).f i
  by_cases hi : ∃ a, e.f a = i
  · obtain ⟨a, ha⟩ := hi
    rw [mapExtendXIso_eq G e K i a ha, mapExtendXIso_eq F e K i a ha,
      extendMap_f _ e ha]
    simp [NatTrans.naturality_assoc]
  · exact (F.map_isZero (K.isZero_extend_X e i (by simpa using hi))).eq_of_src _ _

variable [HasInjectiveResolutions C]

/-- The unchanged integer-resolution comparison retains transformations of the functor. -/
@[reassoc]
theorem injectiveResolutionIntHomologyIso_natTrans {F G : C ⥤ D}
    [F.Additive] [G.Additive] (τ : F ⟶ G) {M : C} (I : InjectiveResolution M) (n : ℕ) :
    homologyMap ((τ.mapHomologicalComplex (ComplexShape.up ℤ)).app
        (I.cocomplex.extend ComplexShape.embeddingUpNat)) (n : ℤ) ≫
        (injectiveResolutionIntHomologyIso G I n).hom =
      (injectiveResolutionIntHomologyIso F I n).hom ≫ (τ.rightDerived n).app M := by
  have h := congrArg (fun a ↦ homologyMap a (n : ℤ))
    (mapExtendIso_natTrans τ ComplexShape.embeddingUpNat I.cocomplex)
  simp only [homologyMap_comp] at h
  rw [InjectiveResolution.rightDerived_app_eq τ I n]
  dsimp only [injectiveResolutionIntHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  erw [← Category.assoc, h, Category.assoc]
  erw [extendHomologyIso_hom_naturality_assoc]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- The original exact-postcomposition comparison retains natural transformations
of the exact functor, in particular the actual scalar maps of forgetful functors. -/
@[reassoc]
theorem rightDerivedPostcomposeIso_natTrans (F : C ⥤ D) [F.Additive]
    {G H : D ⥤ E} [G.Additive] [H.Additive] [G.PreservesHomology] [H.PreservesHomology]
    (τ : G ⟶ H) (M : C) (n : ℕ) :
    ((whiskerLeft F τ).rightDerived n).app M ≫ (rightDerivedPostcomposeIso F H n).hom.app M =
      (rightDerivedPostcomposeIso F G n).hom.app M ≫ τ.app ((F.rightDerived n).obj M) := by
  let I := injectiveResolution M
  rw [InjectiveResolution.rightDerived_app_eq (whiskerLeft F τ) I n]
  dsimp only [rightDerivedPostcomposeIso, NatIso.ofComponents_hom_app,
    rightDerivedPostcomposeObjIso, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [I, Category.assoc, Iso.inv_hom_id_assoc]
  change (I.isoRightDerivedObj (F ⋙ G) n).hom ≫
      ShortComplex.homologyMap
        ((((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).sc n).mapNatTrans τ) ≫
        (complexHomologyMapIso H (ComplexShape.up ℕ)
          ((F.mapHomologicalComplex _).obj I.cocomplex) n).hom ≫
          H.map (I.isoRightDerivedObj F n).inv = _
  rw [ShortComplex.homologyMap_mapNatTrans]
  simp only [Category.assoc, complexHomologyMapIso, Iso.inv_hom_id_assoc]
  erw [← τ.naturality (I.isoRightDerivedObj F n).inv]

end SGA.SGA2.ExposeI
