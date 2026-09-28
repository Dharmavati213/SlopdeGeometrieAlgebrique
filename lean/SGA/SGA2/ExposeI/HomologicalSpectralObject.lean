/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Triangulated.SpectralObject
import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Algebra.Homology.SpectralObject.Basic

/-!
# Applying a homological functor to a triangulated spectral object

The connecting morphisms and all three exactness assertions are inherited
from the actual long exact sequence of every distinguished triangle.
-/

noncomputable section

open CategoryTheory Limits ComposableArrows

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA2.ExposeI

variable {C A ι : Type*} [Category C] [Category A] [Category ι]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [Abelian A]

/-- A genuine triangulated spectral object becomes an abelian spectral
object after applying a homological functor and all its shifts. -/
def homologicalSpectralObject (S : Triangulated.SpectralObject C ι)
    (F : C ⥤ A) [F.IsHomological] [F.ShiftSequence ℤ] :
    Abelian.SpectralObject A ι where
  H n := S.ω₁ ⋙ F.shift n
  δ' n₀ n₁ h :=
    { app D := F.homologySequenceδ (S.ω₂.obj D) n₀ n₁ h
      naturality {D E} f :=
        F.homologySequenceδ_naturality (S.ω₂.obj D) (S.ω₂.obj E) (S.ω₂.map f) n₀ n₁ h }
  exact₁' n₀ n₁ h D :=
    (F.homologySequence_exact₁ (S.ω₂.obj D)
      (S.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows
  exact₂' n D :=
    (F.homologySequence_exact₂ (S.ω₂.obj D)
      (S.ω₂_obj_distinguished D) n).exact_toComposableArrows
  exact₃' n₀ n₁ h D :=
    (F.homologySequence_exact₃ (S.ω₂.obj D)
      (S.ω₂_obj_distinguished D) n₀ n₁ h).exact_toComposableArrows

end SGA.SGA2.ExposeI
