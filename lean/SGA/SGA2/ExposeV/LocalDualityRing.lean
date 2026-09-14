/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalDualityUnit

/-!
# The rank-one ring case of canonical local duality

Original degree-zero self-Ext of the ring is the original ring, with the
identity class corresponding to one. The genuine canonical top-degree
local-duality map is therefore an isomorphism for the rank-one ring module.
This is the initial case in the proof of V.2.1, not the assertion for all
finite modules.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R]

/-- The original degree-zero endomorphism Ext is the original ring. -/
def moduleExtZeroEndRingEquiv :
    moduleExtValue (ModuleCat.of R R) (ModuleCat.of R R) 0 ≃ₗ[R] R :=
  (moduleExtLinearEquivAbelianExt (ModuleCat.of R R) (ModuleCat.of R R) 0).trans
    ((Abelian.Ext.linearEquiv₀ (R := R)).trans
      (ModuleCat.homLinearEquiv.trans (LinearMap.ringLmapEquivSelf R R R)))

@[simp]
theorem moduleExtZeroEndRingEquiv_identity :
    moduleExtZeroEndRingEquiv R (moduleExtIdentity (ModuleCat.of R R)) = 1 := by
  unfold moduleExtZeroEndRingEquiv moduleExtIdentity
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  have h : Abelian.Ext.linearEquiv₀ (R := R) (Abelian.Ext.mk₀ (𝟙 (ModuleCat.of R R))) =
      𝟙 (ModuleCat.of R R) :=
    (Abelian.Ext.linearEquiv₀ (R := R)).apply_symm_apply _
  rw [h]
  rfl

/-- Every original degree-zero self-Ext class is its scalar times the
original identity class. -/
theorem moduleExtZeroEndRing_eq_smul_identity
    (x : moduleExtValue (ModuleCat.of R R) (ModuleCat.of R R) 0) :
    x = moduleExtZeroEndRingEquiv R x • moduleExtIdentity (ModuleCat.of R R) := by
  apply (moduleExtZeroEndRingEquiv R).injective
  rw [map_smul, moduleExtZeroEndRingEquiv_identity, smul_eq_mul, mul_one]

/-- The canonical rank-one top-degree map is surjective, not merely an
abstract map between isomorphic values. -/
theorem localDualityMap_ring_top_surjective (J : Ideal R) (n : ℕ) :
    Function.Surjective
      (localDualityMap J (ModuleCat.of R R) (ModuleCat.of R R) n 0 n (add_zero n)) := by
  intro φ
  let e := moduleExtIdentity (ModuleCat.of R R)
  refine ⟨φ e, ?_⟩
  apply LinearMap.ext
  intro x
  rw [moduleExtZeroEndRing_eq_smul_identity R x, map_smul, map_smul]
  congr 1
  exact congrArg (fun f => f (φ e))
    (localDualityMap_identity_evaluation J (ModuleCat.of R R) n)

/-- **V.2.1, initial rank-one case:** the original canonical map is an
isomorphism, for every ideal and degree over any commutative ring. -/
instance localDualityMap_ring_top_isIso (J : Ideal R) (n : ℕ) :
    IsIso (localDualityMap J (ModuleCat.of R R) (ModuleCat.of R R) n 0 n (add_zero n)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨localDualityMap_self_top_injective J (ModuleCat.of R R) n,
      localDualityMap_ring_top_surjective R J n⟩

end SGA.SGA2.ExposeV
