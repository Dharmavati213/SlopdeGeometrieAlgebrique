/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.SupportedTopLocalCohomology
import SGA.SGA2.ExposeV.LocalRingTopNonvanishing
import SGA.SGA2.ExposeV.TopDimensionalComponents
import SGA.SGA2.ExposeIV.LinearFunctorModuleLift

/-!
# The actual top local-cohomology dual as a supported functor

Right exactness and nonvanishing identify the vanishing locus of the original
dual functor. Linearity identifies its original module structure with the
canonical one in IV's representation theorem.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

instance supportedLocalCohomologyFunctor_linear (J : Ideal R) (n : ℕ) :
    (supportedLocalCohomologyFunctor J n).Linear R := by
  unfold supportedLocalCohomologyFunctor supportedFiniteToModule
  infer_instance

/-- Original linear Hom dual of original top local cohomology, on the
actual category of finite modules supported in `V(J)`. -/
def supportedTopLocalCohomologyDual (J : Ideal R) (n : ℕ) (D : ModuleCat.{u} R) :
    (SupportedFGModuleCat J)ᵒᵖ ⥤ ModuleCat.{u} R :=
  (supportedLocalCohomologyFunctor J n).op ⋙ moduleHomDual D

instance (J : Ideal R) (n : ℕ) (D : ModuleCat.{u} R) :
    (supportedTopLocalCohomologyDual J n D).Additive := by
  unfold supportedTopLocalCohomologyDual
  infer_instance

instance (J : Ideal R) (n : ℕ) (D : ModuleCat.{u} R) :
    (supportedTopLocalCohomologyDual J n D).Linear R where
  map_smul f r := by
    apply ModuleCat.hom_ext
    ext g
    change (supportedLocalCohomologyFunctor J n).map (r • f.unop) ≫ g =
      r • ((supportedLocalCohomologyFunctor J n).map f.unop ≫ g)
    rw [(supportedLocalCohomologyFunctor J n).map_smul, Linear.smul_comp]

/-- The actual contravariant dual is left exact on the specified closed support. -/
theorem supportedTopLocalCohomologyDual_preservesFiniteLimits
    (J : Ideal R) (n : ℕ) (D : ModuleCat.{u} R)
    (hdim : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n) :
    PreservesFiniteLimits (supportedTopLocalCohomologyDual J n D) := by
  have := supportedLocalCohomologyFunctor_preservesFiniteColimits J n hdim
  have := preservesFiniteLimits_op (supportedLocalCohomologyFunctor J n)
  unfold supportedTopLocalCohomologyDual
  infer_instance

/-- The original dual detects zero objects, without completeness or
finiteness of the object, because the supported dualizing module is a cogenerator. -/
theorem moduleHomDual_isZero_iff (D X : ModuleCat.{u} R)
    (hD : SupportedDualizingModule D) :
    IsZero ((moduleHomDual D).obj (op X)) ↔ IsZero X := by
  constructor
  · intro hz
    rw [ModuleCat.isZero_iff_subsingleton]
    apply subsingleton_of_forall_eq 0
    intro x
    by_contra hx
    obtain ⟨f, hf⟩ := hD.exists_hom_apply_ne_zero X x hx
    have hss := ModuleCat.isZero_iff_subsingleton.mp hz
    have hf0 : f = 0 := hss.elim f 0
    exact hf (by rw [hf0]; rfl)
  · intro hz
    exact (moduleHomDual D).map_isZero hz.op

/-- Under a finite upper dimension bound, the original degree-`n`
local cohomology vanishes exactly when the support dimension is smaller. -/
theorem localRing_topLocalCohomology_isZero_iff_supportDim_lt
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    (hdim : Module.supportDim R M ≤ n) :
    IsZero ((_root_.localCohomology (maximalIdeal R) n).obj M) ↔
      Module.supportDim R M < n := by
  constructor
  · intro hz
    apply lt_of_le_of_ne hdim
    intro he
    have := localRing_topLocalCohomology_nontrivial n M he
    exact not_nontrivial_iff_subsingleton.mpr
      (ModuleCat.isZero_iff_subsingleton.mp hz) inferInstance
  · intro hlt
    cases n with
    | zero =>
      have hb : Module.supportDim R M = ⊥ := WithBot.lt_coe_bot.mp hlt
      have := (Module.supportDim_eq_bot_iff_subsingleton R M).mp hb
      exact (_root_.localCohomology (maximalIdeal R) 0).map_isZero
        (ModuleCat.isZero_of_subsingleton M)
    | succ n =>
      apply localRing_localCohomology_isZero_of_supportDim_le M n _ (n + 1) (by omega)
      exact (ENat.WithBot.lt_add_one_iff).mp hlt

/-- Vanishing of the actual top dual means that the coefficient support
misses every original top-dimensional component generic point. -/
theorem supportedTopLocalCohomologyDual_isZero_iff
    (J : Ideal R) (n : ℕ) (D : ModuleCat.{u} R) (hD : SupportedDualizingModule D)
    (hdim : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n)
    (M : SupportedFGModuleCat J) :
    IsZero ((supportedTopLocalCohomologyDual J n D).obj (op M)) ↔
      ∀ p ∈ topDimensionalPrimes J n, p ∉ Module.support R M.obj := by
  change IsZero ((moduleHomDual D).obj
    (op ((_root_.localCohomology (maximalIdeal R) n).obj M.obj.obj))) ↔ _
  rw [moduleHomDual_isZero_iff D _ hD,
    localRing_topLocalCohomology_isZero_iff_supportDim_lt M.obj.obj n
      ((supportedFinite_supportDim_le J M).trans hdim)]
  rw [lt_iff_le_and_ne]
  simp only [(supportedFinite_supportDim_le J M).trans hdim, true_and]
  change (¬ Module.supportDim R M.obj.obj = n) ↔ _
  rw [supportDim_eq_iff_exists_topDimensionalPrime J n hdim M.obj.obj M.property]
  push Not
  rfl

end SGA.SGA2.ExposeV
