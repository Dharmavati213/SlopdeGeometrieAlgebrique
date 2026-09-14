/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.PowerTorsionQuotient
import SGA.SGA2.ExposeIV.SupportedHomDetection

/-!
# Simultaneous regular elements on original torsion quotients

Prime avoidance on a finite product gives one scalar regular on both
modules. Regularity on the actual power-torsion quotient confines the
original scalar kernel to the original power-torsion submodule.
-/

noncomputable section
universe u
open CategoryTheory IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- One actual scalar can be chosen regular on both finite modules. -/
theorem exists_simultaneous_regular_of_idealRegular (I : Ideal R)
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (hM : IdealRegular M I) (hN : IdealRegular N I) :
    ∃ x ∈ I, IsSMulRegular M x ∧ IsSMulRegular N x := by
  have h : IdealRegular (M × N) I := by
    intro y hy
    apply Prod.ext
    · exact hM y.1 (fun a ha => congrArg Prod.fst (hy a ha))
    · exact hN y.2 (fun a ha => congrArg Prod.snd (hy a ha))
  obtain ⟨x, hx, hreg⟩ := (idealRegular_iff_exists_regular (M × N) I).mp h
  refine ⟨x, hx, ?_, ?_⟩
  · intro a b hab
    have he : x • (a, (0 : N)) = x • (b, (0 : N)) := Prod.ext hab rfl
    exact congrArg Prod.fst (hreg he)
  · intro a b hab
    have he : x • ((0 : M), a) = x • ((0 : M), b) := Prod.ext rfl hab
    exact congrArg Prod.snd (hreg he)

/-- For two finite modules over a local ring, choose one regular element
on both of their actual maximal-ideal torsion quotients. -/
theorem exists_simultaneous_regular_on_powerTorsion_quotients [IsLocalRing R]
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] :
    ∃ x ∈ maximalIdeal R,
      IsSMulRegular (M ⧸ powerTorsion (maximalIdeal R) M) x ∧
      IsSMulRegular (N ⧸ powerTorsion (maximalIdeal R) N) x :=
  exists_simultaneous_regular_of_idealRegular (maximalIdeal R)
    (ModuleCat.of R (M ⧸ powerTorsion (maximalIdeal R) M))
    (ModuleCat.of R (N ⧸ powerTorsion (maximalIdeal R) N))
    (idealRegular_powerTorsion_quotient (maximalIdeal R) M)
    (idealRegular_powerTorsion_quotient (maximalIdeal R) N)

omit [IsNoetherianRing R] in
/-- The actual scalar kernel is torsion if the induced scalar is regular
on the actual torsion quotient. -/
theorem ker_smul_le_powerTorsion_of_quotient_regular (I : Ideal R)
    (M : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular (M ⧸ powerTorsion I M) x) :
    LinearMap.ker (x • 𝟙 M).hom ≤ powerTorsion I M := by
  intro y hy
  apply (Submodule.Quotient.mk_eq_zero _).mp
  apply hx.right_eq_zero_of_smul
  change x • (powerTorsion I M).mkQ y = 0
  rw [← map_smul]
  change (powerTorsion I M).mkQ ((x • 𝟙 M).hom y) = 0
  rw [LinearMap.mem_ker.mp hy, map_zero]

omit [IsNoetherianRing R] in
/-- The original scalar kernel has support inside the original ideal's
zero locus whenever the scalar is regular after removing ideal-power torsion. -/
theorem support_ker_smul_subset_of_quotient_regular (I : Ideal R)
    (M : ModuleCat.{u} R) (x : R) (hx : IsSMulRegular (M ⧸ powerTorsion I M) x) :
    Module.support R (LinearMap.ker (x • 𝟙 M).hom) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  let f := Submodule.inclusion (ker_smul_le_powerTorsion_of_quotient_regular I M x hx)
  exact (Module.support_subset_of_injective f (Submodule.inclusion_injective _)).trans
    (support_powerTorsion_subset_zeroLocus I M)

end SGA.SGA2.ExposeV
