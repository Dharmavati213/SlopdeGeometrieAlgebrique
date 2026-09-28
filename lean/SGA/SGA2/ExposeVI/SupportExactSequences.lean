/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeVI.ExtSequenceFirstVariable

/-!
# SGA 2, VI.1.8: exact sequences of actual supported Ext

The groups below are right-derived in the category of module sheaves.
The support maps derive the original supported-Hom inclusion and restriction;
the boundary is induced by their short exact sequence on an injective module
resolution. All maps are natural in the coefficient module, and the boundary
also commutes with original source precomposition.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeVI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}} (R : Sheaf RingCat.{u} X)
  (F : SheafOfModules.{u} R) (W : ExposeI.LocallyClosedIn X) (T : Closeds W.asSet)

/-- **VI.1.8:** the original supported Ext long exact sequence in every degree. -/
theorem VI_1_8_exact (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleNestedSupportedExtSequence R F W T G n).Exact :=
  moduleNestedSupportedExtSequence_exact R F W T G n

/-- **VI.1.8:** exactness at the original middle-support Ext group. -/
theorem VI_1_8_exact_middle (G : SheafOfModules.{u} R) (n : ℕ) :
    Function.Exact ((moduleNestedSupportedExtInclusion R F W T n).app G).hom
      ((moduleNestedSupportedExtRestriction R F W T n).app G).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    ((moduleNestedSupportedExtSequence_exact R F W T G n).exact 0)

/-- **VI.1.8:** exactness at Ext with support in the difference. -/
theorem VI_1_8_exact_difference (G : SheafOfModules.{u} R) (n : ℕ) :
    Function.Exact ((moduleNestedSupportedExtRestriction R F W T n).app G).hom
      ((moduleNestedSupportedExtBoundary R F W T n).app G).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    ((moduleNestedSupportedExtSequence_exact R F W T G n).exact 1)

/-- **VI.1.8:** exactness at the next smaller-support Ext group. -/
theorem VI_1_8_exact_left (G : SheafOfModules.{u} R) (n : ℕ) :
    Function.Exact ((moduleNestedSupportedExtBoundary R F W T n).app G).hom
      ((moduleNestedSupportedExtInclusion R F W T (n + 1)).app G).hom :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    ((moduleNestedSupportedExtSequence_exact R F W T G n).exact 2)

/-- **VI.1.8:** the original sequence starts injectively in degree zero. -/
theorem VI_1_8_zero_injective (G : SheafOfModules.{u} R) :
    Function.Injective ((moduleNestedSupportedExtInclusion R F W T 0).app G).hom :=
  (AddCommGrpCat.mono_iff_injective _).mp
    (moduleNestedSupportedExtInclusion_zero_mono R F W T G)

/-- The same construction gives the original supported sheaf Ext sequence. -/
theorem VI_1_8_sheaf_exact (G : SheafOfModules.{u} R) (n : ℕ) :
    (moduleNestedSheafExtSequence R F W T G n).Exact :=
  moduleNestedSheafExtSequence_exact R F W T G n

end SGA.SGA2.ExposeVI
