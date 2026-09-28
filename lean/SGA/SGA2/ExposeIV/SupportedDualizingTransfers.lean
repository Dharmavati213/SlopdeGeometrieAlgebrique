/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes
import SGA.SGA2.ExposeIV.QuotientAnnihilatorDuality

/-!
# Named supported-dualizing transfers in IV.4.3–4.4

These corollaries retain the actual coinduced and annihilator modules.
Their support is proved by the underlying transfer theorems, rather than
being added as a new hypothesis on the resulting coefficient.
-/

noncomputable section

universe u

open CategoryTheory ModuleCat

namespace SGA.SGA2.ExposeIV

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing B] [Module.Finite A B]

/-- **IV.4.3:** finite local coinduction preserves supported dualizing modules.
Noetherianity of the target ring follows from finiteness of the algebra. -/
theorem SupportedDualizingModule.finite_coinduction {I : ModuleCat.{u} A}
    (hI : SupportedDualizingModule I) :
    SupportedDualizingModule ((coextendScalars (algebraMap A B)).obj I) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  exact finite_local_coinduction_supported_duality I hI.1 hI.2.1 hI.2.2

/-- **IV.4.4:** the literal ideal annihilator, with its ordinary quotient
action, is a supported dualizing module over the quotient local ring. -/
theorem SupportedDualizingModule.quotient_annihilator (J : Ideal A)
    [IsLocalRing (A ⧸ J)] {I : ModuleCat.{u} A} (hI : SupportedDualizingModule I) :
    SupportedDualizingModule (quotientAnnihilatorModule J I) :=
  quotientAnnihilator_supported_duality J I hI.1 hI.2.1 hI.2.2

end SGA.SGA2.ExposeIV
