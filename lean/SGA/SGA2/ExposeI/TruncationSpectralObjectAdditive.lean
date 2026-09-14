/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.SpectralObjectPreadditive
import SGA.SGA2.ExposeI.LocalToGlobalSpectralFunctoriality

/-! # Additivity of the genuine canonical-truncation spectral-object construction -/

noncomputable section

open CategoryTheory Limits ComposableArrows

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C A : Type*} [Category C] [Category A]
  [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C] [Abelian A]

/-- Canonical truncations and the original cohomological functor, together as one functor. -/
def truncationAbelianSpectralObjectFunctor (t : Triangulated.TStructure C)
    (P : C ⥤ A) [P.IsHomological] [P.ShiftSequence ℤ] : C ⥤ Abelian.SpectralObject A EInt :=
  t.spectralObjectFunctor ⋙ homologicalSpectralObjectFunctor P

/-- This actual construction is additive, so it transports full ring actions on coefficients. -/
instance truncationAbelianSpectralObjectFunctor_additive (t : Triangulated.TStructure C)
    (P : C ⥤ A) [P.IsHomological] [P.ShiftSequence ℤ] :
    (truncationAbelianSpectralObjectFunctor t P).Additive where
  map_add {K L} a b := by
    apply Abelian.SpectralObject.Hom.ext
    funext n
    apply NatTrans.ext
    funext D
    have : (t.ω₁.obj D).Additive := by
      dsimp [Triangulated.TStructure.ω₁]
      infer_instance
    change (P.shift n).map ((t.ω₁.obj D).map (a + b)) =
      (P.shift n).map ((t.ω₁.obj D).map a) + (P.shift n).map ((t.ω₁.obj D).map b)
    rw [Functor.map_add, Functor.map_add]

end SGA.SGA2.ExposeI
