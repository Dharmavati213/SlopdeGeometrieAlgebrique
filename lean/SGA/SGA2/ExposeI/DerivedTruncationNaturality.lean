/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.DerivedTruncationHomology

/-! # Naturality of the existing single-degree truncation comparison -/

noncomputable section

universe w v u

open CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

def derivedSingleDegreeTruncationMap (q : ℤ) {K L : DerivedCategory C} (f : K ⟶ L) :
    derivedSingleDegreeTruncation K q ⟶ derivedSingleDegreeTruncation L q :=
  (DerivedCategory.TStructure.t.truncGE q).map
    ((DerivedCategory.TStructure.t.truncLT (q + 1)).map f)

@[reassoc]
lemma derivedSingleDegreeTruncationHomologyIso_naturality (q : ℤ)
    {K L : DerivedCategory C} (f : K ⟶ L) :
    (DerivedCategory.homologyFunctor C q).map (derivedSingleDegreeTruncationMap q f) ≫
        (derivedSingleDegreeTruncationHomologyIso L q).hom =
      (derivedSingleDegreeTruncationHomologyIso K q).hom ≫
        (DerivedCategory.homologyFunctor C q).map f := by
  let t := DerivedCategory.TStructure.t (C := C)
  let H := DerivedCategory.homologyFunctor C q
  dsimp only [derivedSingleDegreeTruncationHomologyIso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, asIso_inv]
  rw [← cancel_epi (H.map ((t.truncGEπ q).app ((t.truncLT (q + 1)).obj K)))]
  change H.map ((t.truncGEπ q).app ((t.truncLT (q + 1)).obj K)) ≫
      H.map (derivedSingleDegreeTruncationMap q f) ≫
        inv (H.map ((t.truncGEπ q).app ((t.truncLT (q + 1)).obj L))) ≫
          H.map ((t.truncLTι (q + 1)).app L) = _
  erw [← H.map_comp_assoc, ← (t.truncGEπ q).naturality,
    H.map_comp_assoc, IsIso.hom_inv_id_assoc]
  simp only [Category.assoc]
  erw [IsIso.hom_inv_id_assoc]
  simpa only [H.map_comp, Functor.id_map] using
    congrArg H.map ((t.truncLTι (q + 1)).naturality f)

/-- The existing choice of a single-complex isomorphism is normalized by
its canonical homology map. -/
@[reassoc]
lemma derivedSingleDegreeTruncationIsoSingle_homology (K : DerivedCategory C) (q : ℤ) :
    (DerivedCategory.homologyFunctor C q).map (derivedSingleDegreeTruncationIsoSingle K q).hom ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app
          ((DerivedCategory.homologyFunctor C q).obj K) =
      (derivedSingleDegreeTruncationHomologyIso K q).hom := by
  dsimp only [derivedSingleDegreeTruncationIsoSingle, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, Category.assoc]
  erw [← Functor.comp_map, NatTrans.naturality]
  simp

/-- On single complexes in the same degree, homology detects morphisms. -/
lemma derivedSingle_homology_map_injective (q : ℤ) (A B : C) :
    Function.Injective ((DerivedCategory.homologyFunctor C q).map :
      ((DerivedCategory.singleFunctor C q).obj A ⟶
        (DerivedCategory.singleFunctor C q).obj B) → _) := by
  intro f g h
  obtain ⟨f, rfl⟩ := (DerivedCategory.singleFunctor C q).map_surjective f
  obtain ⟨g, rfl⟩ := (DerivedCategory.singleFunctor C q).map_surjective g
  have h' := congrArg (fun k => k ≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app B) h
  change (DerivedCategory.singleFunctor C q ⋙ DerivedCategory.homologyFunctor C q).map f ≫ _ =
    (DerivedCategory.singleFunctor C q ⋙ DerivedCategory.homologyFunctor C q).map g ≫ _ at h'
  rw [NatTrans.naturality, NatTrans.naturality] at h'
  exact congrArg (DerivedCategory.singleFunctor C q).map ((cancel_epi _).mp h')

/-- The existing normalized single-degree comparison is natural in the
derived object, despite using a choice of a representing single complex. -/
@[reassoc]
lemma derivedSingleDegreeTruncationIsoSingle_naturality (q : ℤ)
    {K L : DerivedCategory C} (f : K ⟶ L) :
    derivedSingleDegreeTruncationMap q f ≫ (derivedSingleDegreeTruncationIsoSingle L q).hom =
      (derivedSingleDegreeTruncationIsoSingle K q).hom ≫
        (DerivedCategory.singleFunctor C q).map ((DerivedCategory.homologyFunctor C q).map f) := by
  rw [← cancel_epi (derivedSingleDegreeTruncationIsoSingle K q).inv]
  apply derivedSingle_homology_map_injective q _ _
  rw [← cancel_mono ((DerivedCategory.singleFunctorCompHomologyFunctorIso C q).hom.app
    ((DerivedCategory.homologyFunctor C q).obj L))]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc]
  rw [derivedSingleDegreeTruncationIsoSingle_homology,
    derivedSingleDegreeTruncationHomologyIso_naturality]
  erw [← Functor.comp_map, NatTrans.naturality]
  rw [← derivedSingleDegreeTruncationIsoSingle_homology K q]
  simp

end SGA.SGA2.ExposeI
