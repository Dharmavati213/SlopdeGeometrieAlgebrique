/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.PurityBirational
import SGA.SGA1.ExposeXI.BirationalTransfer

/-!
# XI.1.2 and XI.1.3 for a given birational map

The birational invariance of the fundamental group X.3.4 is proved
(`ExposeX.birationalInvariance`), so the consequences drawn from it in `BirationalTransfer` hold
unconditionally: a proper, integral, regular `k`-scheme birational to a simply connected one is
simply connected, and one birational to a scheme with finite fundamental group has finite
fundamental group. As in `BirationalTransfer`, the birational map is given; XI.1.2 and XI.1.3 in
SGA's form (normal varieties, rationality hypotheses on the function field) are
`rationalSimplyConnectedStatement` and `unirationalFiniteFundamentalGroupStatement`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeXI

variable {k : Type u} [Field k] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
  [IsProper sX] [IsProper sY] [IsIntegral X] [IsIntegral Y]

/-- XI.1.2, for a given birational map: a proper, integral, regular `k`-scheme birational (over
`k`) to a proper, integral, regular, simply connected `k`-scheme is simply connected. -/
theorem isSimplyConnected_of_partialIso_of_isRegularScheme (hX : ExposeX.IsRegularScheme X)
    (hY : ExposeX.IsRegularScheme Y) (φ : X.PartialIso Y) (hφ : φ.IsOver sX sY)
    (h : IsSimplyConnected Y) : IsSimplyConnected X :=
  isSimplyConnected_of_partialIso sX sY ExposeX.birationalInvariance hX hY φ hφ h

/-- XI.1.3, for a given birational map: a proper, integral, regular `k`-scheme birational (over
`k`) to a proper, integral, regular `k`-scheme with finite fundamental group has finite fundamental
group. -/
theorem hasFiniteFundamentalGroup_of_partialIso_of_isRegularScheme
    (hX : ExposeX.IsRegularScheme X) (hY : ExposeX.IsRegularScheme Y) (φ : X.PartialIso Y)
    (hφ : φ.IsOver sX sY) (h : HasFiniteFundamentalGroup Y) : HasFiniteFundamentalGroup X :=
  hasFiniteFundamentalGroup_of_partialIso sX sY ExposeX.birationalInvariance hX hY φ hφ h

end SGA.SGA1.ExposeXI
