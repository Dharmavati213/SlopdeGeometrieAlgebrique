/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDiagram
import SGA.SGA2.ExposeIII.DepthLocalCohomology

/-!
# The original quotient-Ext diagram and local cohomology

The cyclic modules and quotient maps used in IV.1.3 are identified with the
actual ideal-power diagram defining algebraic local cohomology. Reindexing
its double opposite by `ℕ` gives an actual colimit comparison, retaining all
the original first-variable Ext transition maps.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The direct system defining local cohomology, reindexed from the double
opposite of the natural numbers to the natural numbers themselves. -/
def moduleExtPowerDiagram (J : Ideal R) (E : ModuleCat.{u} R) (i : ℕ) :
    ℕ ⥤ ModuleCat.{u} R :=
  (opOpEquivalence ℕ).inverse ⋙
    (extColimitDiagramFunctor
      (localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J)) i).obj E

@[simp]
theorem moduleExtPowerDiagram_obj (J : Ideal R) (E : ModuleCat.{u} R) (i n : ℕ) :
    (moduleExtPowerDiagram J E i).obj n =
      (((_root_.Ext R (ModuleCat.{u} R) i).obj
        (op (ModuleCat.of R (R ⧸ J ^ n)))).obj E) := rfl

/-- The transition is the actual Ext map induced by the original quotient
`R/Jᵐ → R/Jⁿ`, not a chosen isomorphism between its source and target. -/
theorem moduleExtPowerDiagram_map (J : Ideal R) (E : ModuleCat.{u} R) (i : ℕ)
    {n m : ℕ} (h : n ≤ m) :
    (moduleExtPowerDiagram J E i).map (homOfLE h) =
      ((_root_.Ext R (ModuleCat.{u} R) i).map
        (ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right h))).op).app E := by
  rfl

/-- The genuine direct limit of the quotient-Ext diagram is the original
algebraic local-cohomology object. This is valid for every commutative ring. -/
def moduleExtPowerColimitIsoLocalCohomology (J : Ideal R) (E : ModuleCat.{u} R) (i : ℕ) :
    colimit (moduleExtPowerDiagram J E i) ≅ (_root_.localCohomology J i).obj E :=
  Functor.Final.colimitIso (opOpEquivalence ℕ).inverse _ ≪≫
    (idealPowerExtIsoLocalCohomology J i).app E

/-- The colimit comparison preserves the actual maps from each quotient
Ext stage into local cohomology. -/
@[reassoc]
theorem moduleExtPowerColimitIsoLocalCohomology_ι
    (J : Ideal R) (E : ModuleCat.{u} R) (i n : ℕ) :
    colimit.ι (moduleExtPowerDiagram J E i) n ≫
      (moduleExtPowerColimitIsoLocalCohomology J E i).hom =
    (colimit.ι (localCohomology.diagram (localCohomology.idealPowersDiagram J) i)
      (op (op n))).app E := by
  dsimp only [moduleExtPowerColimitIsoLocalCohomology, Iso.trans_hom]
  erw [Functor.Final.ι_colimitIso_hom_assoc]
  exact colimitObjIsoColimitCompEvaluation_ι_inv
    (localCohomology.diagram (localCohomology.idealPowersDiagram J) i) (op (op n)) E

/-- The actual cyclic quotient diagram in the supported finite category
becomes exactly the quotient diagram defining local cohomology, including
the maps, after the original inclusion into modules. -/
theorem supportedRingQuotientDiagram_comp_toModule [IsNoetherianRing R] (J : Ideal R) :
    supportedRingQuotientDiagram J ⋙ supportedFiniteToModule J =
      localCohomology.ringModIdeals (localCohomology.idealPowersDiagram J) := by
  apply CategoryTheory.Functor.ext (fun _ ↦ rfl)

end SGA.SGA2.ExposeIV
