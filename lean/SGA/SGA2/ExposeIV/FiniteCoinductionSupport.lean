/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.FiniteCoinductionDuality

/-!
# Actual support of finite coinduction

The finite source of each map `B →ₗ[A] I` makes its image a finite supported
submodule of `I`. Consequently actual coinduction has support in the
inverse image of the original support. For finite local algebras this is
the closed point, so the coefficient module remains genuinely supported.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Finite A B]

omit [IsNoetherianRing B] in
/-- Actual finite coinduction carries `V(J)`-supported coefficients to
coefficients supported in `V(JB)`. -/
theorem supported_coinduced_map (J : Ideal A) (I : ModuleCat.{u} A)
    (hI : supportedModuleProperty J I) :
    supportedModuleProperty (J.map (algebraMap A B))
      ((coextendScalars (algebraMap A B)).obj I) := by
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro g _
  have := finite_restrictScalars_of_finite (A := A) (ModuleCat.of B B)
  have hRange : Module.support A g.range ⊆ PrimeSpectrum.zeroLocus (J : Set A) :=
    (Module.support_subset_of_injective g.range.subtype g.range.subtype_injective).trans hI
  obtain ⟨n, hn⟩ :=
    (support_subset_zeroLocus_iff_exists_pow_le_annihilator J g.range).mp hRange
  have hk : (J ^ n).map (algebraMap A B) ≤
      Ideal.torsionOf B ((coextendScalars (algebraMap A B)).obj I) g := by
    apply Ideal.map_le_iff_le_comap.mpr
    intro a ha
    change algebraMap A B a • g = 0
    apply LinearMap.ext
    intro b
    have hzero := congrArg Subtype.val
      (Module.mem_annihilator.mp (hn ha) (⟨g b, ⟨b, rfl⟩⟩ : g.range))
    have hg := g.map_smul a b
    change g (algebraMap A B a * (show B from b)) = a • g b at hg
    change g ((show B from b) * algebraMap A B a) = 0
    rw [mul_comm, hg]
    exact hzero
  apply (mem_powerTorsion_iff _ _ g).mpr
  refine ⟨n, fun b hb ↦ ?_⟩
  apply hk
  rwa [Ideal.map_pow]

variable [IsLocalRing A] [IsLocalRing B]

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- Over a finite local algebra, the inverse image of the closed point
is precisely the closed point. -/
theorem zeroLocus_map_maximalIdeal_subset :
    PrimeSpectrum.zeroLocus ((maximalIdeal A).map (algebraMap A B) : Set B) ⊆
      PrimeSpectrum.zeroLocus (maximalIdeal B : Set B) := by
  intro p hp
  have hle : maximalIdeal A ≤ p.asIdeal.comap (algebraMap A B) :=
    Ideal.map_le_iff_le_comap.mp hp
  have he : p.asIdeal.comap (algebraMap A B) = maximalIdeal A :=
    ((maximalIdeal.isMaximal A).eq_of_le
      (Ideal.comap_isPrime (algebraMap A B) p.asIdeal).ne_top hle).symm
  have hm : p.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap p.asIdeal (by
      rw [he]
      infer_instance)
  change maximalIdeal B ≤ p.asIdeal
  rw [eq_maximalIdeal hm]

omit [IsNoetherianRing B] in
/-- A genuinely supported coefficient module stays supported after finite
local coinduction. This excludes invisible nonsupported summands. -/
theorem finite_local_coinduction_supported (I : ModuleCat.{u} A)
    (hI : supportedModuleProperty (maximalIdeal A) I) :
    supportedModuleProperty (maximalIdeal B)
      ((coextendScalars (algebraMap A B)).obj I) :=
  (supported_coinduced_map (maximalIdeal A) I hI).trans
    zeroLocus_map_maximalIdeal_subset

/-- **IV.4.3**, with all three original supported-dualizing conditions:
actual support, finite Hom values, and canonical biduality. -/
theorem finite_local_coinduction_supported_duality (I : ModuleCat.{u} A)
    (hI : supportedModuleProperty (maximalIdeal A) I)
    (hfin : FiniteSupportedHomValues (maximalIdeal A) I)
    (hbid : SupportedModuleBiduality (maximalIdeal A) I) :
    supportedModuleProperty (maximalIdeal B)
        ((coextendScalars (algebraMap A B)).obj I) ∧
      FiniteSupportedHomValues (maximalIdeal B)
        ((coextendScalars (algebraMap A B)).obj I) ∧
      SupportedModuleBiduality (maximalIdeal B)
        ((coextendScalars (algebraMap A B)).obj I) :=
  ⟨finite_local_coinduction_supported I hI, finite_local_coinduction_duality I hfin hbid⟩

end SGA.SGA2.ExposeIV
