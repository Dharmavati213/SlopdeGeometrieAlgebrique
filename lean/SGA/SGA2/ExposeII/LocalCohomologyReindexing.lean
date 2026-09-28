/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.ExtColimitSequence
import SGA.SGA2.ExposeII.FiniteGeneratorColimits

/-!
# SGA 2, Exposé II, (7.3)–(7.6): boundaries and cofinal reindexing

The coefficient boundaries on ideal-indexed Ext colimits commute with the
canonical cofinality isomorphisms. In particular, the existing comparison
between generator powers and ordinary ideal powers respects these actual
boundaries, independently of a noetherian hypothesis.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

section Diagram

variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]
  [HasColimitsOfShape Dᵒᵖ (ModuleCat.{u} R)]
  (I : D ⥤ Ideal R) (S : ShortComplex (ModuleCat.{u} R))
  (hS : S.ShortExact) (i : ℕ)

/-- The coefficient connecting maps form a morphism of ideal Ext diagrams. -/
def idealExtδDiagram :
    localCohomology.diagram I i ⋙ (evaluation _ _).obj S.X₃ ⟶
      localCohomology.diagram I (i + 1) ⋙ (evaluation _ _).obj S.X₁ where
  app j := extCoefficientδ ((localCohomology.ringModIdeals I).obj j.unop) S hS i
  naturality _ _ f :=
    (extCoefficientδ_naturality ((localCohomology.ringModIdeals I).map f.unop) S hS i).symm

/-- The actual Ext boundary, on the colimit of coefficient functors used
in mathlib's definition of local cohomology. -/
def idealExtColimitδ :
    (colimit (localCohomology.diagram I i)).obj S.X₃ ⟶
      (colimit (localCohomology.diagram I (i + 1))).obj S.X₁ :=
  (colimitObjIsoColimitCompEvaluation (localCohomology.diagram I i) S.X₃).hom ≫
    colim.map (idealExtδDiagram I S hS i) ≫
      (colimitObjIsoColimitCompEvaluation (localCohomology.diagram I (i + 1)) S.X₁).inv

/-- The colimit boundary is induced by the finite Ext boundaries. -/
@[reassoc (attr := simp)]
theorem ι_idealExtColimitδ (j : Dᵒᵖ) :
    (colimit.ι (localCohomology.diagram I i) j).app S.X₃ ≫ idealExtColimitδ I S hS i =
      extCoefficientδ ((localCohomology.ringModIdeals I).obj j.unop) S hS i ≫
        (colimit.ι (localCohomology.diagram I (i + 1)) j).app S.X₁ := by
  simp only [idealExtColimitδ, colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc,
    colimit.ι_map_assoc, idealExtδDiagram,
    colimitObjIsoColimitCompEvaluation_ι_inv]

end Diagram

section Cofinality

variable {R : Type max u v w} [CommRing R]
  {D : Type v} [SmallCategory D] {E : Type w} [SmallCategory E]
  (F : E ⥤ D) (I : D ⥤ Ideal R) [Functor.Initial F]

/-- The existing cofinality isomorphism sends each finite Ext class to its
class at the same ideal in the larger diagram. -/
@[reassoc (attr := simp)]
theorem ι_localCohomologyIsoOfFinal_hom (i : ℕ) (j : Eᵒᵖ)
    (M : ModuleCat.{max u v w} R) :
    (colimit.ι (localCohomology.diagram (F ⋙ I) i) j).app M ≫
        (localCohomology.isoOfFinal.{u, v, w} F I i).hom.app M =
      (colimit.ι (localCohomology.diagram I i) (F.op.obj j)).app M := by
  have h : colimit.ι (localCohomology.diagram (F ⋙ I) i) j ≫
      (localCohomology.isoOfFinal.{u, v, w} F I i).hom =
      colimit.ι (localCohomology.diagram I i) (F.op.obj j) := by
    simp only [localCohomology.isoOfFinal, Iso.trans_hom,
      HasColimit.isoOfNatIso_ι_hom_assoc, localCohomology.diagramComp,
      Iso.refl_hom, NatTrans.id_app, Category.id_comp,
      Functor.Final.ι_colimitIso_hom]
  exact congrArg (fun t => t.app M) h

/-- Cofinal reindexing commutes with the actual coefficient Ext boundaries. -/
@[reassoc]
theorem localCohomologyIsoOfFinal_δ
    (S : ShortComplex (ModuleCat.{max u v w} R)) (hS : S.ShortExact) (i : ℕ) :
    idealExtColimitδ (F ⋙ I) S hS i ≫
        (localCohomology.isoOfFinal.{u, v, w} F I (i + 1)).hom.app S.X₁ =
      (localCohomology.isoOfFinal.{u, v, w} F I i).hom.app S.X₃ ≫
        idealExtColimitδ I S hS i := by
  apply colimit_obj_ext (H := localCohomology.diagram (F ⋙ I) i)
  intro j
  rw [ι_idealExtColimitδ_assoc]
  rw [ι_localCohomologyIsoOfFinal_hom.{u, v, w} F I (i + 1) j S.X₁]
  rw [ι_localCohomologyIsoOfFinal_hom_assoc.{u, v, w} F I i j S.X₃]
  rw [ι_idealExtColimitδ]
  rfl

/-- The inverse cofinality isomorphism also respects the boundaries. -/
@[reassoc]
theorem localCohomologyIsoOfFinal_inv_δ
    (S : ShortComplex (ModuleCat.{max u v w} R)) (hS : S.ShortExact) (i : ℕ) :
    idealExtColimitδ I S hS i ≫
        (localCohomology.isoOfFinal.{u, v, w} F I (i + 1)).inv.app S.X₁ =
      (localCohomology.isoOfFinal.{u, v, w} F I i).inv.app S.X₃ ≫
        idealExtColimitδ (F ⋙ I) S hS i := by
  apply (cancel_epi ((localCohomology.isoOfFinal.{u, v, w} F I i).hom.app S.X₃)).mp
  rw [← localCohomologyIsoOfFinal_δ_assoc]
  simp only [Iso.hom_inv_id_app, Iso.hom_inv_id_app_assoc]
  exact Category.comp_id _

end Cofinality

section Generators

variable {R : Type u} [CommRing R]

/-- The actual coefficient connecting map for ordinary ideal-power local
cohomology. -/
def localCohomologyδ (I : Ideal R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (_root_.localCohomology I i).obj S.X₃ ⟶
      (_root_.localCohomology I (i + 1)).obj S.X₁ :=
  idealExtColimitδ (localCohomology.idealPowersDiagram I) S hS i

/-- II.(7.3)–(7.4), with coefficient boundaries: the previously constructed
generator-power cofinality isomorphism commutes with the actual Ext
connecting maps in every degree. -/
@[reassoc]
theorem generatorPowersLocalCohomologyIso_δ {ι : Type v} [Finite ι]
    (f : ι → R) (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    idealExtColimitδ (generatorPowersDiagram f) S hS i ≫
        (generatorPowersLocalCohomologyIso f (i + 1)).hom.app S.X₁ =
      (generatorPowersLocalCohomologyIso f i).hom.app S.X₃ ≫
        localCohomologyδ (Ideal.span (Set.range f)) S hS i := by
  let I := Ideal.span (Set.range f)
  let := idealPowersToSelfLERadical_initial_of_fg I
    (Submodule.fg_span (Set.finite_range f))
  have hg := localCohomologyIsoOfFinal_δ.{u, u, 0}
    (generatorPowersToSelfLERadical f) (localCohomology.selfLERadicalDiagram I) S hS i
  have hp := localCohomologyIsoOfFinal_inv_δ.{u, u, 0}
    (localCohomology.idealPowersToSelfLERadical I)
    (localCohomology.selfLERadicalDiagram I) S hS i
  dsimp only [generatorPowersLocalCohomologyIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun t => t ≫ (localCohomology.isoOfFinal.{u, u, 0}
      (localCohomology.idealPowersToSelfLERadical I)
      (localCohomology.selfLERadicalDiagram I) (i + 1)).inv.app S.X₁) hg).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t => (localCohomology.isoOfFinal.{u, u, 0}
          (generatorPowersToSelfLERadical f) (localCohomology.selfLERadicalDiagram I) i).hom.app
            S.X₃ ≫ t) hp).trans (Category.assoc _ _ _).symm)))

end Generators

end SGA.SGA2.ExposeII
