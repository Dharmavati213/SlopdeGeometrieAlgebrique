/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.LocalDualityFiniteFree
import SGA.SGA2.ExposeII.HomologyLinear
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# Scalar linearity of original local cohomology

Linearity passes from actual Hom cochains through the projective-resolution
comparison to Ext, and then through the original ideal-power colimit.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

instance homCochainCoefficientFunctor_linear (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (homCochainCoefficientFunctor K).Linear R where
  map_smul f r := by
    ext i t
    rfl

instance homCohomologyBifunctor_obj_linear (i : ℕ)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((homCohomologyBifunctor i).obj (op K)).Linear R where
  map_smul f r := by
    change HomologicalComplex.homologyMap ((homCochainCoefficientFunctor K).map (r • f)) i = _
    rw [Functor.map_smul, homologyMap_smul]
    rfl

instance extCoefficient_linear (X : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).Linear R :=
  Functor.linear_of_iso R (projectiveResolutionExtNatIso (projectiveResolution X) i).symm

instance extColimitDiagramFunctor_linear (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    (extColimitDiagramFunctor Q i).Linear R where
  map_smul f r := by
    apply NatTrans.ext
    funext j
    exact ((Ext R (ModuleCat.{u} R) i).obj (op (Q.obj j.unop))).map_smul r f

instance extColimitFunctor_linear (Q : ℕᵒᵖ ⥤ ModuleCat.{u} R) (i : ℕ) :
    (extColimitFunctor Q i).Linear R where
  map_smul f r := by
    apply colimit.hom_ext
    intro j
    change colimit.ι _ j ≫ colim.map ((extColimitDiagramFunctor Q i).map (r • f)) =
      colimit.ι _ j ≫ (r • colim.map ((extColimitDiagramFunctor Q i).map f))
    simp only [Linear.comp_smul, colimit.ι_map, Functor.map_smul,
      NatTrans.app_smul, Linear.smul_comp]

/-- Actual coefficient scalar multiplication induces the same scalar
multiplication on the original local-cohomology objects. -/
instance localCohomology_linear (J : Ideal R) (i : ℕ) :
    (_root_.localCohomology J i).Linear R :=
  Functor.linear_of_iso R (idealPowerExtIsoLocalCohomology J i)

end SGA.SGA2.ExposeV
