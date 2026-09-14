/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.Algebra.Homology.Linear
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# SGA 2, Exposé II, Lemma 11: scalar maps on homology

Scalar multiplication of chain maps induces the same scalar multiplication
on homology. This identifies scalar cofiber maps and their power transitions
in the induction in II.11.
-/

open CategoryTheory

namespace SGA.SGA2.ExposeII

variable {R C : Type*} [Semiring R] [Category* C] [Preadditive C] [Linear R C]
variable {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c}

set_option backward.isDefEq.respectTransparency false in
/-- Scalar multiplication commutes with passing from a chain map to homology. -/
@[simp]
theorem homologyMap_smul (r : R) (φ : K ⟶ L) (i : ι)
    [K.HasHomology i] [L.HasHomology i] :
    HomologicalComplex.homologyMap (r • φ) i =
      r • HomologicalComplex.homologyMap φ i :=
  ShortComplex.homologyMap_smul ((HomologicalComplex.shortComplexFunctor C c i).map φ) r

end SGA.SGA2.ExposeII
