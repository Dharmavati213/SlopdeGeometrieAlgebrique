/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ModuleExtYonedaExactness
import SGA.SGA2.ExposeII.ExtColimitSequence

/-!
# Yoneda coefficient sequences on the original Ext colimits

The transported Yoneda boundaries form morphisms of the unchanged Ext
diagrams. Filtered colimits preserve the exact sequences on both sides of
these boundaries.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]
variable (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R)
  (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ)

/-- The Yoneda boundary is a map of the original quotient Ext diagrams. -/
def extColimitYonedaBoundaryDiagram :
    (extColimitDiagramFunctor Q i).obj S.X₃ ⟶
      (extColimitDiagramFunctor Q (i + 1)).obj S.X₁ where
  app j := moduleExtYonedaCovariantBoundary (Q.obj j.unop) S hS i
  naturality _ _ f :=
    moduleExtYonedaCovariantBoundary_naturality (Q.map f.unop) S hS i

@[reassoc (attr := simp)]
theorem extColimitYonedaBoundaryDiagram_comp :
    extColimitYonedaBoundaryDiagram Q S hS i ≫
      (extColimitDiagramFunctor Q (i + 1)).map S.f = 0 := by
  apply NatTrans.ext
  funext j
  exact moduleExtYonedaCovariantBoundary_comp (Q.obj j.unop) S hS i

@[reassoc (attr := simp)]
theorem comp_extColimitYonedaBoundaryDiagram :
    (extColimitDiagramFunctor Q i).map S.g ≫
      extColimitYonedaBoundaryDiagram Q S hS i = 0 := by
  apply NatTrans.ext
  funext j
  exact comp_moduleExtYonedaCovariantBoundary (Q.obj j.unop) S hS i

/-- The induced boundary on the original filtered Ext colimit. -/
def extColimitYonedaBoundary :
    (extColimitFunctor Q i).obj S.X₃ ⟶ (extColimitFunctor Q (i + 1)).obj S.X₁ :=
  colim.map (extColimitYonedaBoundaryDiagram Q S hS i)

@[reassoc (attr := simp)]
theorem extColimitYonedaBoundary_comp :
    extColimitYonedaBoundary Q S hS i ≫ (extColimitFunctor Q (i + 1)).map S.f = 0 := by
  change colim.map _ ≫ colim.map _ = 0
  rw [← Functor.map_comp, extColimitYonedaBoundaryDiagram_comp, Functor.map_zero]

@[reassoc (attr := simp)]
theorem comp_extColimitYonedaBoundary :
    (extColimitFunctor Q i).map S.g ≫ extColimitYonedaBoundary Q S hS i = 0 := by
  change colim.map _ ≫ colim.map _ = 0
  rw [← Functor.map_comp, comp_extColimitYonedaBoundaryDiagram, Functor.map_zero]

/-- Exactness after the Yoneda boundary in the original Ext colimit. -/
theorem extColimitYoneda_exact₁ :
    (ShortComplex.mk _ _ (extColimitYonedaBoundary_comp Q S hS i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (ShortComplex.mk _ _ (extColimitYonedaBoundaryDiagram_comp Q S hS i))
    (fun j => moduleExtYoneda_covariant_exact₁ (Q.obj j.unop) S hS i)

/-- Exactness before the Yoneda boundary in the original Ext colimit. -/
theorem extColimitYoneda_exact₃ :
    (ShortComplex.mk _ _ (comp_extColimitYonedaBoundary Q S hS i)).Exact :=
  exact_colimit_of_module_diagram_evaluations
    (ShortComplex.mk _ _ (comp_extColimitYonedaBoundaryDiagram Q S hS i))
    (fun j => moduleExtYoneda_covariant_exact₃ (Q.obj j.unop) S hS i)

end SGA.SGA2.ExposeV
