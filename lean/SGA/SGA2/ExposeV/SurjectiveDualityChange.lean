/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.SurjectiveScalarChange
import SGA.SGA2.ExposeIV.SupportedDualizingTransfers

/-!
# V, formula (20): Hom duality under a surjective change of local rings

The actual coinduced source-ring dualizing module is dualizing over the
target ring. Choosing one isomorphism from a specified target-ring dualizing
module gives the source's noncanonical comparison, naturally in every
original coefficient module. The canonical coinduction comparison itself
is evaluation at `1`.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S]
variable [IsNoetherianRing R] [IsNoetherianRing S] [IsLocalRing R] [IsLocalRing S]
variable (σ : R →+* S) (hσ : Function.Surjective σ)

include hσ in
omit [IsNoetherianRing S] in
/-- A surjection makes the actual coinduced module dualizing over the target. -/
theorem surjective_coinduced_supportedDualizing (H : ModuleCat.{u} R)
    (hH : SupportedDualizingModule H) :
    SupportedDualizingModule ((ModuleCat.coextendScalars σ).obj H) := by
  let := σ.toAlgebra
  have : Module.Finite R S := Module.Finite.of_surjective (Algebra.linearMap R S) hσ
  exact hH.finite_coinduction (B := S)

/-- **V, formula (20):** the actual Hom duals agree after scalar restriction,
naturally in the original module. The choice is confined to one isomorphism
of the specified dualizing coefficient modules. -/
def surjectiveHomDualScalarChangeIso (H : ModuleCat.{u} R) (K : ModuleCat.{u} S)
    (hH : SupportedDualizingModule H) (hK : SupportedDualizingModule K) :
    moduleHomDual K ⋙ ModuleCat.restrictScalars σ ≅
      (ModuleCat.restrictScalars σ).op ⋙ moduleHomDual H := by
  let e : K ≅ (ModuleCat.coextendScalars σ).obj H :=
    (hK.nonempty_iso (surjective_coinduced_supportedDualizing σ hσ H hH)).some
  exact Functor.isoWhiskerRight ((linearYoneda S (ModuleCat S)).mapIso e)
      (ModuleCat.restrictScalars σ) ≪≫
    NatIso.ofComponents (fun M ↦ coinducedHomDualIso σ H M.unop)
      (fun f ↦ coinducedHomDualIso_naturality σ H f.unop)

/-- Combining formulas (19) and (20) compares the original duals of local
cohomology, linearly over the source ring and without a flatness assumption. -/
def surjectiveLocalCohomologyDualIso (H : ModuleCat.{u} R) (K : ModuleCat.{u} S)
    (hH : SupportedDualizingModule H) (hK : SupportedDualizingModule K)
    (M : ModuleCat.{u} S) (i : ℕ) :
    (ModuleCat.restrictScalars σ).obj
        ((moduleHomDual K).obj
          (op ((_root_.localCohomology (IsLocalRing.maximalIdeal S) i).obj M))) ≅
      (moduleHomDual H).obj
        (op ((_root_.localCohomology (IsLocalRing.maximalIdeal R) i).obj
          ((ModuleCat.restrictScalars σ).obj M))) :=
  (surjectiveHomDualScalarChangeIso σ hσ H K hH hK).app
      (op ((_root_.localCohomology (IsLocalRing.maximalIdeal S) i).obj M)) ≪≫
    (moduleHomDual H).mapIso (localRing_localCohomologyScalarChangeIso σ hσ M i).op

end SGA.SGA2.ExposeV
