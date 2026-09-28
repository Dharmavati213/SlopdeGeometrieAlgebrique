/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalCohomologyDuality
import SGA.SGA2.ExposeIV.MacaulayDualizingModule

/-!
# IV.5.5: the two actual dualizing constructions are isomorphic

When both preceding examples apply, the actual quotient-Ext colimit and the
actual coefficient-field dual colimit are isomorphic. This is the source's
initial existence assertion only: no explicit residue pairing, canonical
orientation, or parameter independence is asserted by this result.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing

namespace SGA.SGA2.ExposeIV

variable {K R : Type u} [Field K] [CommRing R] [Algebra K R]
  [IsRegularLocalRing R] [Module.Finite K (ResidueField R)]

/-- **IV.5.5, first assertion.** The actual dualizing modules of the two
preceding examples are isomorphic, without an added completeness assumption. -/
theorem regularLocalTopExtModule_nonempty_iso_macaulay (n : ℕ)
    (hdim : ringKrullDim R = n) :
    Nonempty (regularLocalTopExtModule (R := R) n ≅ macaulayModule (K := K) (A := R)) :=
  (regularLocalTopExtModule_dualizing n hdim).nonempty_iso macaulayModule_supportedDualizing

/-- The same initial assertion with the original local cohomology module
itself, rather than its canonically isomorphic quotient-Ext colimit. -/
theorem regularLocal_localCohomology_nonempty_iso_macaulay (n : ℕ)
    (hdim : ringKrullDim R = n) :
    Nonempty ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R) ≅
      macaulayModule (K := K) (A := R)) :=
  (regularLocal_localCohomology_dualizing n hdim).nonempty_iso macaulayModule_supportedDualizing

end SGA.SGA2.ExposeIV
