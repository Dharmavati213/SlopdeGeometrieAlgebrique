/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.ModuleDimensionVanishing
import SGA.SGA2.ExposeV.TopLocalCohomologyExactness
import SGA.SGA2.ExposeIV.SupportedFiniteModules

/-!
# Right exact top local cohomology on the actual supported category

Upper vanishing for the actual support dimension makes local cohomology
right exact on finite modules supported on a fixed closed set of dimension
at most the chosen degree. This is the supported-category input in V.3.1(iii).
-/

noncomputable section
universe u
open CategoryTheory Limits IsLocalRing
open SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Upper vanishing from a bound on actual support dimension, including
the zero coefficient module whose support dimension is bottom. -/
theorem localRing_localCohomology_isZero_of_supportDim_le
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    (hdim : Module.supportDim R M ≤ n) (i : ℕ) (hi : n < i) :
    IsZero ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  by_cases hb : Module.supportDim R M = ⊥
  · have : Subsingleton M := (Module.supportDim_eq_bot_iff_subsingleton R M).mp hb
    exact (_root_.localCohomology (maximalIdeal R) i).map_isZero
      (ModuleCat.isZero_of_subsingleton M)
  · obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hb
    have hdt : d ≠ ⊤ := by
      intro ht
      rw [← hd, ht] at hdim
      have hn : (n : ℕ∞) < ⊤ := ENat.natCast_lt_top n
      exact (not_le_of_gt (WithBot.coe_lt_coe.mpr hn)) hdim
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hdt
    have hMk : Module.supportDim R M = k := hd.symm.trans (congrArg WithBot.some hk.symm)
    have hkn : k ≤ n := by exact_mod_cast (hMk ▸ hdim)
    exact localRing_localCohomology_isZero_of_gt_moduleDim M k hMk i (hkn.trans_lt hi)

/-- Original local cohomology restricted to the actual finite supported category. -/
def supportedLocalCohomologyFunctor (J : Ideal R) (n : ℕ) :
    SupportedFGModuleCat J ⥤ ModuleCat.{u} R :=
  supportedFiniteToModule J ⋙ _root_.localCohomology (maximalIdeal R) n

instance (J : Ideal R) (n : ℕ) : (supportedLocalCohomologyFunctor J n).Additive := by
  unfold supportedLocalCohomologyFunctor supportedFiniteToModule
  infer_instance

omit [IsNoetherianRing R] [IsLocalRing R] in
/-- The original module of a supported object has dimension bounded by
the actual closed support, using its existing support inclusion. -/
theorem supportedFinite_supportDim_le (J : Ideal R) (M : SupportedFGModuleCat J) :
    Module.supportDim R M.obj.obj ≤ Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) :=
  Order.krullDim_le_of_strictMono (fun p => ⟨p.val, M.property p.property⟩)
    (fun _ _ h => h)

/-- **V.3.1(iii), supported right exactness.** The original degree-`n`
local-cohomology functor is right exact on the actual finite modules
supported on a closed set of dimension at most `n`. -/
theorem supportedLocalCohomologyFunctor_preservesFiniteColimits
    (J : Ideal R) (n : ℕ)
    (hdim : Order.krullDim (PrimeSpectrum.zeroLocus (J : Set R)) ≤ n) :
    PreservesFiniteColimits (supportedLocalCohomologyFunctor J n) := by
  apply (Functor.preservesFiniteColimits_tfae (supportedLocalCohomologyFunctor J n)).out 1 4 |>.mp
  intro S hS
  let Q := S.map (supportedFiniteToModule J)
  have hQ : Q.ShortExact :=
    (supportedFiniteInclusion_shortExact J hS).map_of_exact (forget₂ (FGModuleCat R) (ModuleCat R))
  have hzero := localRing_localCohomology_isZero_of_supportDim_le S.X₁.obj.obj n
    ((supportedFinite_supportDim_le J S.X₁).trans hdim) (n + 1) (by omega)
  exact ⟨localCohomology_map_shortExact_exact (maximalIdeal R) n Q hQ,
    localCohomology_map_shortExact_epi (maximalIdeal R) n Q hQ hzero⟩

end SGA.SGA2.ExposeV
