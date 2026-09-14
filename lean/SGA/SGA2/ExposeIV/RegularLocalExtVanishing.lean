/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.RegularLocalRegularSequence
import SGA.SGA2.ExposeIII.RegularExt
import SGA.SGA2.ExposeIII.DepthLocalCohomology
import SGA.SGA2.ExposeIV.ModuleBidualFiniteLength
import SGA.SGA2.ExposeIV.LocalArtinianSupport
import SGA.SGA2.ExposeIV.SupportedArtinianDuality
import Mathlib.RingTheory.Regular.ProjectiveDimension

/-!
# Off-degree Ext vanishing over actual regular local rings

Starting with the actual `IsRegularLocalRing` hypothesis, the regular system
of parameters identifies the residue field's projective dimension with the
Krull dimension. Genuine finite-length dévissage then bounds the projective
dimension of every finite-length module. Together with III.2.2(a), this proves
the off-degree vanishing used in IV.5.3–5.4. The value in the remaining degree
and the asserted duality are not assumed or claimed here.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Over any local ring, a projective-dimension bound for the residue field
extends through the actual short exact sequences of finite-length modules. -/
theorem local_finiteLength_hasProjectiveDimensionLE_of_residueField [IsLocalRing R]
    (n : ℕ) [HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n]
    (N : ModuleCat.{u} R) (hN : IsFiniteLength R N) : HasProjectiveDimensionLE N n := by
  apply moduleFiniteLength_induction (fun M ↦ HasProjectiveDimensionLE M n) ?_ ?_ ?_ N hN
  · intro M hM
    have := hM.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge M 0 (n + 1) (Nat.zero_le _)
  · intro M hM
    obtain ⟨J, hJ, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := M)).mp hM
    have hJ' : J = maximalIdeal R := IsLocalRing.eq_maximalIdeal hJ
    subst J
    let : HasProjectiveDimensionLT (ModuleCat.of R (R ⧸ maximalIdeal R)) (n + 1) :=
      inferInstanceAs (HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n)
    exact hasProjectiveDimensionLT_of_iso e.toModuleIso.symm (n + 1)
  · intro S hS h₁ h₃
    exact hS.hasProjectiveDimensionLT_X₂ (n + 1) h₁ h₃

variable [IsRegularLocalRing R]

/-- The residue field has projective dimension equal to the actual Krull
dimension, with no regular sequence or global dimension hypothesis supplied. -/
theorem regularLocal_residueField_projectiveDimension (n : ℕ)
    (hdim : ringKrullDim R = n) :
    projectiveDimension (ModuleCat.of R (ResidueField R)) = n := by
  obtain ⟨rs, hlen, hs, hreg⟩ := regularLocal_exists_regular_parameters n hdim
  let e : ModuleCat.of R (Shrink.{u} (R ⧸ Ideal.ofList rs)) ≅
      ModuleCat.of R (ResidueField R) :=
    (Shrink.linearEquiv R _).toModuleIso ≪≫
      (Ideal.quotientEquivAlgOfEq R hs).toLinearEquiv.toModuleIso
  have h := ModuleCat.projectiveDimension_quotient_eq_length.{u, u} rs hreg
  rw [projectiveDimension_eq_of_iso e] at h
  simpa only [hlen] using h

/-- Finite-length modules have projective dimension at most the ring's
dimension, by actual short exact dévissage from its residue field. -/
theorem regularLocal_finiteLength_hasProjectiveDimensionLE (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R) (hN : IsFiniteLength R N) :
    HasProjectiveDimensionLE N n := by
  have : HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) n :=
    (projectiveDimension_le_iff _ n).mp
      (regularLocal_residueField_projectiveDimension n hdim).le
  exact local_finiteLength_hasProjectiveDimensionLE_of_residueField n N hN

/-- Above the dimension, Ext vanishes for any coefficient module whenever
the first argument has finite length. -/
theorem regularLocal_ext_subsingleton_of_finiteLength_of_gt (n : ℕ)
    (hdim : ringKrullDim R = n) (N M : ModuleCat.{u} R) (hN : IsFiniteLength R N)
    (i : ℕ) (hi : n < i) : Subsingleton (Abelian.Ext N M i) := by
  have := regularLocal_finiteLength_hasProjectiveDimensionLE n hdim N hN
  exact HasProjectiveDimensionLT.subsingleton N (n + 1) i hi M

/-- Below the dimension, Ext into the ring vanishes by the actual regular
parameters and the maximal-ideal-power annihilation of finite-length modules. -/
theorem regularLocal_ext_ring_subsingleton_of_finiteLength_of_lt (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R) (hN : IsFiniteLength R N)
    (i : ℕ) (hi : i < n) : Subsingleton (Abelian.Ext N (ModuleCat.of R R) i) := by
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).1
  have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hN).2
  obtain ⟨rs, hlen, hs, hreg⟩ := regularLocal_exists_regular_parameters n hdim
  apply III_2_2_a (maximalIdeal R) N (ModuleCat.of R R) rs ?_ hreg.1
    (finite_artinian_exists_maximalIdeal_pow_annihilator N) i (by omega)
  intro r hr
  rw [← hs]
  exact Ideal.subset_span hr

/-- The off-degree vanishing in IV.5.3–5.4 for every finite-length first
argument, derived from the original regular-local-ring hypothesis. -/
theorem regularLocal_ext_ring_subsingleton_of_finiteLength (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R) (hN : IsFiniteLength R N)
    (i : ℕ) (hi : i ≠ n) : Subsingleton (Abelian.Ext N (ModuleCat.of R R) i) := by
  rcases lt_or_gt_of_ne hi with h | h
  · exact regularLocal_ext_ring_subsingleton_of_finiteLength_of_lt n hdim N hN i h
  · exact regularLocal_ext_subsingleton_of_finiteLength_of_gt n hdim N
      (ModuleCat.of R R) hN i h

/-- The same vanishing for the original module-valued Ext functor. -/
theorem regularLocal_moduleExt_ring_isZero_of_finiteLength (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R) (hN : IsFiniteLength R N)
    (i : ℕ) (hi : i ≠ n) :
    IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj (ModuleCat.of R R)) :=
  (isZero_moduleExt_iff_subsingleton_ext N (ModuleCat.of R R) i).mpr
    (regularLocal_ext_ring_subsingleton_of_finiteLength n hdim N hN i hi)

/-- The literal finite maximal-ideal-supported source objects of IV.5.4
satisfy the same original module-valued Ext vanishing. -/
theorem regularLocal_moduleExt_ring_isZero_of_finite_of_support (n : ℕ)
    (hdim : ringKrullDim R = n) (N : ModuleCat.{u} R) [Module.Finite R N]
    (hN : supportedModuleProperty (maximalIdeal R) N) (i : ℕ) (hi : i ≠ n) :
    IsZero (((_root_.Ext R (ModuleCat.{u} R) i).obj (op N)).obj (ModuleCat.of R R)) := by
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  exact regularLocal_moduleExt_ring_isZero_of_finiteLength n hdim N
    (isFiniteLength_of_finite_of_support (maximalIdeal R) N hN) i hi

end SGA.SGA2.ExposeIV
