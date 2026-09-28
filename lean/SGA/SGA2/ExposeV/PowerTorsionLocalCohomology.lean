/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.PowerTorsionQuotient
import SGA.SGA2.ExposeV.KoszulAnnihilatorVanishing
import SGA.SGA2.ExposeII.KoszulLocalCohomology
import SGA.SGA2.ExposeV.TopLocalCohomologyExactness

/-!
# Positive local cohomology of the original torsion quotient

Uniform ideal-power annihilation makes the actual Koszul transitions zero
in positive degrees. The original submodule--quotient sequence then proves
that its quotient map induces an isomorphism on positive local cohomology.
-/

noncomputable section
universe u
open CategoryTheory Limits
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Uniform ideal-power annihilation kills positive local cohomology. -/
theorem localCohomology_isZero_of_pow_annihilator (I : Ideal R)
    (M : ModuleCat.{u} R) (k : ℕ) (hk : I ^ k ≤ Module.annihilator R M)
    (i : ℕ) (hi : 0 < i) :
    IsZero ((_root_.localCohomology I i).obj M) := by
  classical
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian (I ^ (k + 1))
  let gs := s.toList
  have hgs : koszulIdeal gs = I ^ (k + 1) := by
    simpa [koszulIdeal, gs] using hs
  have hann : ∀ f ∈ gs, f ∈ Module.annihilator R M := by
    intro f hf
    apply hk
    exact Ideal.pow_le_pow_right (Nat.le_succ k) (hgs ▸ Ideal.subset_span hf)
  have hr : I.radical = (koszulIdeal (gs ++ [])).radical := by
    simpa only [List.append_nil, hgs] using (I.radical_pow (Nat.succ_ne_zero k)).symm
  let e := (localCohomology.isoOfSameRadical hr i).app M ≪≫
    (localCohomologyIsoStableKoszul (gs ++ []) i).app M
  exact (stableKoszulCohomology_isZero_of_annihilating_prefix M gs [] hann i hi).of_iso e

/-- The actual finite power-torsion submodule is acyclic in positive degrees. -/
theorem localCohomology_powerTorsion_isZero (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) (hi : 0 < i) :
    IsZero ((_root_.localCohomology I i).obj (ModuleCat.of R (powerTorsion I M))) := by
  obtain ⟨k, hk⟩ := powerTorsion_exists_pow_annihilator I M
  exact localCohomology_isZero_of_pow_annihilator I _ k hk i hi

/-- The actual torsion inclusion and quotient projection. -/
def powerTorsionShortComplex (I : Ideal R) (M : ModuleCat.{u} R) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero (powerTorsion I M).subtype
    (powerTorsion I M).mkQ (by ext x; simp)

omit [IsNoetherianRing R] in
theorem powerTorsionShortComplex_shortExact (I : Ideal R) (M : ModuleCat.{u} R) :
    (powerTorsionShortComplex I M).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    ((powerTorsion I M).range_subtype.trans (powerTorsion I M).ker_mkQ.symm)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (powerTorsion I M).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (powerTorsion I M).mkQ_surjective

/-- The original quotient projection, not just some comparison, induces
an isomorphism on every positive local-cohomology module. -/
theorem localCohomology_powerTorsion_mkQ_isIso (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (i : ℕ) (hi : 0 < i) :
    IsIso ((_root_.localCohomology I i).map
      (ModuleCat.ofHom (powerTorsion I M).mkQ)) := by
  let S := powerTorsionShortComplex I M
  have hS := powerTorsionShortComplex_shortExact I M
  have : Mono ((_root_.localCohomology I i).map S.g) :=
    (localCohomology_map_shortExact_exact I i S hS).mono_g
      ((localCohomology_powerTorsion_isZero I M i hi).eq_zero_of_src _)
  have : Epi ((_root_.localCohomology I i).map S.g) :=
    localCohomology_map_shortExact_epi I i S hS
      (localCohomology_powerTorsion_isZero I M (i + 1) (by omega))
  exact isIso_of_mono_of_epi ((_root_.localCohomology I i).map S.g)

end SGA.SGA2.ExposeV
