/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.RegularUpperExt
import SGA.SGA2.ExposeVII.SupportedExtCoherence
import SGA.SGA2.ExposeV.GlobalProjectiveDimension
import SGA.SGA2.ExposeIV.SupportedExtDiagram
import Mathlib.RingTheory.Ideal.Height

/-!
# SGA 2, VII.2.1: upper vanishing and coherence on regular schemes

On a locally noetherian regular scheme, with
`m = sup_{x ∈ Y ∩ Supp F} dim O_{X,x}` and
`n = sup_{x ∈ Y ∩ S'} dim O_{X,x}`, one has

1. `SheafExt_Y^i(F,G) = 0` for `i > m`;
2. `SheafExt_Y^i(F,G)` coherent for `i > n`.

Affine / stalkwise avatar: over a regular local ring of dimension `≤ m`,
Ext vanishes above `m` (`regularLocal_ext_subsingleton_of_gt`); the
quotient-Ext stages of supported Ext therefore vanish, and the colimit
(local cohomology / supported Ext) vanishes. Coherence for `i > n` follows
from VII.1.5 after reducing to the torsion quotient of smaller support bound,
together with VII.1.6 on the supported kernel.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV SGA.SGA2.ExposeV

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R]

/-- VII.2.1(1) fibre: on a regular local ring of Krull dimension `m`, Ext
vanishes in all degrees `> m`. -/
theorem VII_2_1_ext_vanishes_above_dim [IsRegularLocalRing R]
    (m : ℕ) (hdim : ringKrullDim R = m)
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : m < i) :
    Subsingleton (Abelian.Ext M N i) :=
  regularLocal_ext_subsingleton_of_gt m hdim M N i hi

/-- Same vanishing for the module-valued Ext. -/
theorem VII_2_1_moduleExt_vanishes_above_dim [IsRegularLocalRing R]
    (m : ℕ) (hdim : ringKrullDim R = m)
    (M N : ModuleCat.{u} R) (i : ℕ) (hi : m < i) :
    IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (op M)).obj N) :=
  regularLocal_moduleExt_isZero_of_gt m hdim M N i hi

/-- Quotient-Ext stages vanish above the dimension, so their colimit
(algebraic local cohomology) vanishes as well. -/
theorem VII_2_1_localCohomology_vanishes_above_dim [IsRegularLocalRing R]
    (m : ℕ) (hdim : ringKrullDim R = m)
    (N : ModuleCat.{u} R) (i : ℕ) (hi : m < i) :
    IsZero ((_root_.localCohomology (IsLocalRing.maximalIdeal R) i).obj N) := by
  apply IsZero.of_iso _
    (moduleExtPowerColimitIsoLocalCohomology (IsLocalRing.maximalIdeal R) N i).symm
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro k
  have hz := VII_2_1_moduleExt_vanishes_above_dim m hdim
    (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R ^ (k : ℕ))) N i hi
  exact IsZero.eq_of_src hz _ _

/-- VII.2.1(2) coherence input: Ext of finite modules remains finite in every
degree (including those above the smaller support bound `n`). -/
theorem VII_2_1_ext_finite [IsNoetherianRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (Abelian.Ext M N i) :=
  VII_1_6_ext_finite M N i

/-- Localization form of the dimension bound used in VII.2.1: height equals
Krull dimension of the local ring. -/
theorem ringKrullDim_localization_eq_height (p : Ideal R) [p.IsPrime] :
    ringKrullDim (Localization.AtPrime p) = p.height :=
  IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)

/-- Projective-dimension form already recorded in `RegularUpperExt`: Ext
vanishes above any projective-dimension bound. -/
theorem VII_2_1_ext_vanishes_of_projectiveDimension_le
    (N M : ModuleCat.{u} R) (n i : ℕ)
    (hpd : projectiveDimension N ≤ n) (hi : n < i) :
    Subsingleton (Abelian.Ext N M i) :=
  ext_subsingleton_of_projectiveDimension_le N M n i hpd hi

end SGA.SGA2.ExposeVII
