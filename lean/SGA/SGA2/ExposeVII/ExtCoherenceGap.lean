/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.RegularSupportedExtBounds
import SGA.SGA2.ExposeVII.DimensionSetInterval
import SGA.SGA2.ExposeVII.SupportedExtCoherence
import SGA.SGA2.ExposeVII.VanishingCriteria

/-!
# SGA 2, VII.2.3: coherence of Ext outside the dimension set

Let `X` be locally noetherian regular, `Y` closed, `F` coherent, and
`P = Y ∩ Supp F ∩ (X \ Y)` (boundary of the support relative to `Y`). If
`n ∉ D(P)`, then `SheafExt^n_Y(F, O_X)` is coherent.

Proof in the exposé: locally one may assume `P` connected, so
`D(P) = [a,b[` by VII.2.2; if `n ≥ b` conclude by VII.2.1, if `n < a`
conclude by VII.1.7 (depth of `O_X` equals dimension on a regular scheme).

Affine avatar recorded here: on a regular local ring, Ext into the ring is
finite in every degree (VII.1.6); when the degree lies above the dimension
it moreover vanishes (VII.2.1); when it lies below a depth bound along the
relevant locus, VII.1.7 applies.
-/

noncomputable section

universe u

open CategoryTheory
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeV

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R]

/-- VII.2.3, high-degree case: above the dimension, Ext into the ring vanishes
(hence is coherent) on a regular local ring. -/
theorem VII_2_3_ext_ring_vanishes_above_dim [IsRegularLocalRing R]
    (m : ℕ) (hdim : ringKrullDim R = m) (M : ModuleCat.{u} R)
    (i : ℕ) (hi : m < i) :
    Subsingleton (Abelian.Ext M (ModuleCat.of R R) i) :=
  VII_2_1_ext_vanishes_above_dim m hdim M (ModuleCat.of R R) i hi

/-- VII.2.3, low-degree case input: below a depth bound, Ext is finite by
VII.1.7 / VII.1.6. -/
theorem VII_2_3_ext_finite_below_depth [IsNoetherianRing R]
    (J : Ideal R) (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N]
    (n : ℕ) (_hdepth : (n : ℕ∞) ≤ depth J N) (i : ℕ) (_hi : i < n) :
    Module.Finite R (Abelian.Ext M N i) :=
  VII_1_6_ext_finite M N i

/-- VII.2.3 branching on an interval `D(P) = Icc a b`: if `n` is outside,
either the high-degree vanishing or the low-degree coherence applies. -/
theorem VII_2_3_branch {a b : ℕ∞} (n : ℕ∞) (hn : n ∉ Set.Icc a b)
    (hab : a ≤ b) : n < a ∨ b < n :=
  not_mem_Icc hab hn

/-- Combined coherence statement: Ext into the ring is always finite for
finite modules over a noetherian ring, and vanishes when the degree exceeds
the regular dimension. -/
theorem VII_2_3_ext_ring_finite [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) :
    Module.Finite R (Abelian.Ext M (ModuleCat.of R R) i) :=
  VII_1_6_ext_finite M (ModuleCat.of R R) i

theorem VII_2_3_ext_ring_coherent_outside_dim [IsRegularLocalRing R]
    [IsNoetherianRing R] (m : ℕ) (hdim : ringKrullDim R = m)
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) :
    Module.Finite R (Abelian.Ext M (ModuleCat.of R R) i) ∧
      (m < i → Subsingleton (Abelian.Ext M (ModuleCat.of R R) i)) :=
  ⟨VII_2_3_ext_ring_finite M i,
    fun hi ↦ VII_2_3_ext_ring_vanishes_above_dim m hdim M i hi⟩

/-- Low-degree branch via local-cohomology vanishing (VII.1.2(i) ⇒ VII.1.7). -/
theorem VII_2_3_finite_of_localCohomology_vanishes [IsNoetherianRing R]
    (J : Ideal R) (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N]
    (n : ℕ) (h : LocalCohomologyVanishesBelow J N n) (i : ℕ) (hi : i < n) :
    Module.Finite R (Abelian.Ext M N i) :=
  VII_2_3_ext_finite_below_depth J M N n ((VII_1_2_i_iff_depth J N n).mp h) i hi

end SGA.SGA2.ExposeVII
