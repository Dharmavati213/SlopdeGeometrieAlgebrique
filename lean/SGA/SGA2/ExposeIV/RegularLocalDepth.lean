/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalTopExt
import SGA.SGA2.ExposeIII.Depth
import SGA.SGA2.ExposeIII.DepthLocalCohomology

/-!
# IV.5.3: actual regular-local depth and arbitrary lower Ext vanishing

The actual regular parameters imply lower Ext vanishing for every module
annihilated by a maximal-ideal power, without a finiteness assumption. The
computed nonzero top residue Ext value then makes the original ideal depth
exactly the Krull dimension. No global dimension or arbitrary-module upper
Ext vanishing is asserted here.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **IV.5.3, arbitrary nilpotent-support modules:** if a power of the
maximal ideal annihilates `N`, its Ext into the ring vanishes below the
actual dimension. `N` is not required finite or of finite length. -/
theorem regularLocal_ext_ring_subsingleton_of_maximalIdeal_pow_annihilator (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R)
    (hN : ∃ k : ℕ, maximalIdeal R ^ k ≤ Module.annihilator R N)
    (i : ℕ) (hi : i < n) : Subsingleton (Abelian.Ext N (ModuleCat.of R R) i) := by
  obtain ⟨rs, hlen, hs, hreg⟩ := regularLocal_exists_regular_parameters n hdim
  apply III_2_2_a (maximalIdeal R) N (ModuleCat.of R R) rs ?_ hreg.1 hN i (by omega)
  intro r hr
  rw [← hs]
  exact Ideal.subset_span hr

/-- The same arbitrary-module lower vanishing for the original
module-valued Ext functor used in algebraic local cohomology. -/
theorem regularLocal_moduleExt_ring_isZero_of_maximalIdeal_pow_annihilator (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R)
    (hN : ∃ k : ℕ, maximalIdeal R ^ k ≤ Module.annihilator R N)
    (i : ℕ) (hi : i < n) :
    IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj (ModuleCat.of R R)) :=
  (isZero_moduleExt_iff_subsingleton_ext N (ModuleCat.of R R) i).mpr
    (regularLocal_ext_ring_subsingleton_of_maximalIdeal_pow_annihilator n hdim N hN i hi)

/-- The actual top residue Ext group is nonzero, by its computed residue
field value rather than a supplied nonvanishing or depth assumption. -/
theorem regularLocal_topResidueExt_not_subsingleton (n : ℕ)
    (hdim : ringKrullDim R = n) :
    ¬ Subsingleton (Abelian.Ext (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n) := by
  intro h
  let e := regularLocal_topResidueExtAddEquiv n hdim
  have h01 : (0 : ResidueField R) = 1 := by
    simpa only [map_zero, AddEquiv.apply_symm_apply] using
      congrArg e (h.elim 0 (e.symm 1))
  exact zero_ne_one h01

/-- **IV.5.3:** the literal ideal depth of a regular local ring is its
actual Krull dimension, including the dimension-zero case. -/
theorem regularLocal_depth_eq (n : ℕ) (hdim : ringKrullDim R = n) :
    ExposeIII.depth (maximalIdeal R) (ModuleCat.of R R) = (n : ℕ∞) := by
  apply le_antisymm
  · rw [depth_maximalIdeal_eq_extDepth, extDepth]
    exact iInf_le_of_le n (iInf_le_of_le
      (regularLocal_topResidueExt_not_subsingleton n hdim) le_rfl)
  · apply (le_depth_iff (maximalIdeal R) (ModuleCat.of R R) n).mpr
    intro N _ hN i hi
    exact regularLocal_ext_ring_subsingleton_of_maximalIdeal_pow_annihilator n hdim N hN i hi

end SGA.SGA2.ExposeIV
