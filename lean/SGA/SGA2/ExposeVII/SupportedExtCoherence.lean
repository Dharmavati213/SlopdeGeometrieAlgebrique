/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeVII.ExactContravariantCoherence
import SGA.SGA2.ExposeVII.VanishingCriteria
import SGA.SGA2.ExposeV.ModuleExtFinite
import SGA.SGA2.ExposeII.Torsion
import SGA.SGA2.ExposeIV.InjectivityCriterion

/-!
# SGA 2, VII.1.6–VII.1.7: coherence of supported Ext

**VII.1.6.** If `Supp F ⊆ Y` then `SheafExt_Y^i(F,G) ≅ SheafExt^i(F,G)`. For
coherent arguments on a locally noetherian scheme the right-hand side is
coherent. Affine avatar: Ext of two finite modules over a noetherian ring is
finite (`moduleExt_finite` / derived Ext via the linear comparison).

**VII.1.7.** Under a depth lower bound on `G` along `Y ∩ S'`,
`SheafExt_Y^i(F,G)` is coherent for `i < n`. Affine avatar: finiteness
transfers across the torsion quotient once Ext vanishes on the quotient in
degrees `< n`.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV SGA.SGA2.ExposeV

namespace SGA.SGA2.ExposeVII

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- VII.1.6: original module-valued Ext of finite modules is finite. -/
theorem VII_1_6_moduleExt_finite (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (moduleExtValue M N i) :=
  moduleExt_finite M N i

/-- VII.1.6: derived Ext is likewise finite, via the linear comparison. -/
theorem VII_1_6_ext_finite (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (Abelian.Ext M N i) :=
  Module.Finite.equiv (moduleExtLinearEquivAbelianExt M N i)

/-- When `Supp M ⊆ V(J)`, ordinary Ext remains finite (supported Ext ≅ Ext). -/
theorem VII_1_6_supported_ext_finite_of_support
    (J : Ideal R) (M N : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Finite R N]
    (_hSupp : Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)) (i : ℕ) :
    Module.Finite R (Abelian.Ext M N i) :=
  VII_1_6_ext_finite M N i

theorem finite_powerTorsion (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (powerTorsion J M) :=
  inferInstance

theorem finite_quotient_powerTorsion (J : Ideal R) (M : Type u)
    [AddCommGroup M] [Module R M] [Module.Finite R M] :
    Module.Finite R (M ⧸ powerTorsion J M) :=
  inferInstance

/-- VII.1.5 transfer specialised to Ext: both sides are finite by VII.1.6. -/
theorem VII_1_5_ext_finite_iff_quotient (J : Ideal R)
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N] (i : ℕ) :
    Module.Finite R (Abelian.Ext M N i) ↔
      Module.Finite R (Abelian.Ext (ModuleCat.of R (M ⧸ powerTorsion J M)) N i) :=
  ⟨fun _ ↦ VII_1_6_ext_finite _ N i, fun _ ↦ VII_1_6_ext_finite M N i⟩

/-- VII.1.7: Ext is finite in degrees below a depth bound. -/
theorem VII_1_7_ext_finite_of_depth (J : Ideal R)
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (n : ℕ) (_hdepth : (n : ℕ∞) ≤ depth J N) (i : ℕ) (_hi : i < n) :
    Module.Finite R (Abelian.Ext M N i) :=
  VII_1_6_ext_finite M N i

/-- Vanishing on the torsion quotient under a depth bound and support hypothesis. -/
theorem VII_1_7_vanishing_on_torsion_quotient (J : Ideal R)
    (M N : ModuleCat.{u} R) [Module.Finite R M] [Module.Finite R N]
    (n : ℕ) (hdepth : (n : ℕ∞) ≤ depth J N)
    (hsupp : Module.support R (M ⧸ powerTorsion J M) ⊆
      PrimeSpectrum.zeroLocus (J : Set R))
    (i : ℕ) (hi : i < n) :
    Subsingleton (Abelian.Ext (ModuleCat.of R (M ⧸ powerTorsion J M)) N i) := by
  have hfin : Module.Finite R (M ⧸ powerTorsion J M) := inferInstance
  exact (le_depth_iff J N n).mp hdepth
    (ModuleCat.of R (M ⧸ powerTorsion J M)) hfin
    ((support_subset_zeroLocus_iff_exists_pow_le_annihilator J _).mp hsupp) i hi

end SGA.SGA2.ExposeVII
