/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedHomDetection

/-!
# Arbitrary supported modules are ideal-power torsion

Over a noetherian ring, actual support in `V(J)` is equivalent to every
element being killed by some power of `J`. The module need not be finite:
the finite-support annihilator criterion is applied only to each actual
cyclic submodule. This also states IV.2.1 directly with its support hypothesis.
-/

noncomputable section

universe u v

open CategoryTheory Limits
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- An arbitrary module supported on `V(J)` is ideal-power torsion.
Only its cyclic submodules are assumed finite, as proved by mathlib. -/
theorem powerTorsion_eq_top_of_support_subset_zeroLocus (J : Ideal R)
    (H : Type v) [AddCommGroup H] [Module R H]
    (hH : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    powerTorsion J H = ⊤ := by
  apply top_unique
  intro x _
  let S : Submodule R H := Submodule.span R {x}
  have hS : Module.support R S ⊆ PrimeSpectrum.zeroLocus (J : Set R) :=
    (Module.support_subset_of_injective S.subtype S.subtype_injective).trans hH
  obtain ⟨n, hn⟩ := (support_subset_zeroLocus_iff_exists_pow_le_annihilator J S).mp hS
  refine (mem_powerTorsion_iff J H x).mpr ⟨n, fun r hr ↦ ?_⟩
  exact congrArg Subtype.val
    (Module.mem_annihilator.mp (hn hr) (⟨x, Submodule.subset_span (by simp)⟩ : S))

/-- Actual module support and elementwise ideal-power torsion agree,
without a finiteness assumption on the module. -/
theorem powerTorsion_eq_top_iff_support_subset_zeroLocus (J : Ideal R)
    (H : Type v) [AddCommGroup H] [Module R H] :
    powerTorsion J H = ⊤ ↔ Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R) :=
  ⟨support_subset_zeroLocus_of_powerTorsion_eq_top J H,
    powerTorsion_eq_top_of_support_subset_zeroLocus J H⟩

/-- **IV.2.1, support formulation:** for any actual supported module,
exactness of contravariant Hom on finite supported modules characterizes
categorical injectivity in the category of all modules. -/
theorem finiteSupportedHomExact_iff_injective_of_support (J : Ideal R)
    (H : ModuleCat.{u} R)
    (hH : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    FiniteSupportedHomExact J H ↔ Injective H :=
  finiteSupportedHomExact_iff_injective J H
    (powerTorsion_eq_top_of_support_subset_zeroLocus J H hH)

end SGA.SGA2.ExposeIV
