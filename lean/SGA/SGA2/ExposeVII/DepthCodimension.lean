/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.DepthSupport

/-!
# SGA 2, VII.1.4: depth versus a dimension lower bound

VII.1.4 equates the vanishing criteria of VII.1.2 with a codimension bound
when `G` is Cohen–Macaulay. Here we record the order-theoretic comparison
used in that argument together with the III.2.7 locus comparison.
-/

noncomputable section

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeVII

open SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R]

/-- If depth equals an extended natural number `d`, a threshold comparison
passes between them. This is the formal content of VII.1.4 once local
depth/dimension identification is supplied. -/
theorem depth_ge_iff_of_eq_dim (I : Ideal R) (M : ModuleCat.{u} R) (d : ℕ∞)
    (h : depth I M = d) (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔ (n : ℕ∞) ≤ d := by
  rw [h]

/-- Zero modules have infinite depth, so they never obstruct a depth bound
along a locus (VII.1.4, after III.3.3). -/
theorem depth_eq_top_of_subsingleton_coeff (I : Ideal R) (M : ModuleCat.{u} R)
    [Subsingleton M] : depth I M = ⊤ :=
  depth_eq_top_of_subsingleton I M

/-- Depth is monotone in the support ideal: enlarging `Y` can only raise
`prof_Y`. -/
theorem depth_mono_ideal {I J : Ideal R} (hIJ : I ≤ J) (M : ModuleCat.{u} R) :
    depth I M ≤ depth J M :=
  depth_mono hIJ M

/-- Finite depth detects meeting the closed set `V(I)` (III.2.7 / VII.1.4). -/
theorem depth_lt_top_iff_support_meets [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M < ⊤ ↔
      (Module.support R M ∩ PrimeSpectrum.zeroLocus (I : Set R)).Nonempty :=
  III_2_7 I M

end SGA.SGA2.ExposeVII
