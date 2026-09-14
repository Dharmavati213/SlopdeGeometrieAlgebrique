/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.DepthSupport

/-!
# SGA 2, XIV: depth inputs for étale Lefschetz theorems

Raynaud's Exposé XIV relates depth to Lefschetz theorems in étale
cohomology. We import the algebraic depth package of Exposé III as the
starting point.
-/

noncomputable section

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeXIV

open SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- Depth is an extended natural number (III.2.3). -/
theorem depth_def (I : Ideal R) (M : ModuleCat.{u} R) :
    depth I M = depth I M :=
  rfl

/-- Infinite depth along `I` is equivalent to disjointness of support and
`V(I)` for finite modules (III.2.7). -/
theorem depth_eq_top_iff_disjoint [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M = ⊤ ↔
      Disjoint (Module.support R M) (PrimeSpectrum.zeroLocus (I : Set R)) :=
  depth_eq_top_iff_disjoint_support I M

/-- Finite depth meets `V(I)`. -/
theorem depth_lt_top_iff_meets [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M < ⊤ ↔
      (Module.support R M ∩ PrimeSpectrum.zeroLocus (I : Set R)).Nonempty :=
  III_2_7 I M

end SGA.SGA2.ExposeXIV
