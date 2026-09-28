/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.Depth
import Mathlib.Topology.Sets.Closeds

/-!
# SGA 2, III.3.3(v)/(vi): module Ext criteria for depth

On a noetherian affine, the Ext vanishing criteria of III.2.4 are the
module-valued internal Ext criteria III.3.3(v) and (vi).
-/

noncomputable section

universe u

open CategoryTheory Abelian TopologicalSpace

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- **III.3.3(v), affine:** depth at least `n` along `I` iff Ext from every
finite module of support `V(I)` vanishes below `n`. -/
theorem III_3_3_v (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔ ExtVanishesBelow I M n :=
  le_depth_iff I M n

/-- **III.3.3(vi), affine:** depth at least `n` is detected by some finite
test module of support exactly `V(I)`. -/
theorem III_3_3_vi [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∃ N : ModuleCat.{u} R, Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus I ∧
          ∀ i < n, Subsingleton (Abelian.Ext N M i) :=
  le_depth_iff_exists_test_module I M n

/-- **III.3.3(vi), cyclic test:** the quotient module `R/I` detects depth. -/
theorem III_3_3_vi_quotient [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (R ⧸ I)) M i) :=
  le_depth_iff_ext_vanishes I (ModuleCat.of R (R ⧸ I)) M
    (by simp [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]) n

end SGA.SGA2.ExposeIII
