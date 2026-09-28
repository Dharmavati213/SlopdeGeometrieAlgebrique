/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.MatlisCompleteDuality
import SGA.SGA2.ExposeIV.MatlisArtinianCompletion
import SGA.SGA2.ExposeIV.CompletionDualizingTransfer
import SGA.SGA2.ExposeIV.NoetherianCompletion

/-!
# Matlis duality with finite modules over the actual completed ring

The actual completion is proved noetherian, not assumed to be so. Combining
the original `CA` completion equivalence with the actual complete-base Hom
duality identifies `CA(R)` oppositely with finite modules over the completion.
Both functors are specified composites of original scalar change and Hom.
-/

noncomputable section
universe u
open CategoryTheory Opposite ModuleCat

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable (H : ModuleCat.{u} R) (hH : SupportedDualizingModule H)

/-- The actual dualizing coefficient after tensor extension to the completion. -/
abbrev matlisCompletedCoefficient :
    ModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (extendScalars (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).obj H

/-- Finite modules over the actual completion are dual to original locally
Artinian finite-socle modules. Completed-ring noetherianity is a theorem. -/
def matlisCompletedRingAntiEquivalence :
    (MatlisArtinianModuleCat R)ᵒᵖ ≌
      FGModuleCat.{u} (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  (matlisArtinianCompletionEquivalence (R := R)).op.trans
    (matlisCompleteAntiEquivalence (matlisCompletedCoefficient H) hH.completion)

/-- The forward functor is actual tensor extension followed by actual Hom
over the completed ring, not a chosen objectwise correspondence. -/
theorem matlisCompletedRingAntiEquivalence_functor :
    (matlisCompletedRingAntiEquivalence H hH).functor =
      (matlisArtinianCompletionEquivalence (R := R)).functor.op ⋙
        matlisArtinianHom (matlisCompletedCoefficient H) hH.completion := rfl

/-- The inverse is actual completed-ring Hom followed by original scalar restriction. -/
theorem matlisCompletedRingAntiEquivalence_inverse :
    (matlisCompletedRingAntiEquivalence H hH).inverse =
      (matlisFiniteHom (matlisCompletedCoefficient H) hH.completion).rightOp ⋙
        (matlisArtinianCompletionEquivalence (R := R)).inverse.op := rfl

end SGA.SGA2.ExposeIV
