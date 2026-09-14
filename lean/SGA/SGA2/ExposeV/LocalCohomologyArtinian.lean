/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.FiniteResidueExt
import SGA.SGA2.ExposeIV.MatlisArtinianModules
import SGA.SGA2.ExposeIII.DepthLocalCohomology

/-!
# Artinian local cohomology over arbitrary noetherian local rings

Finite residue Ext implies finite socle, hence Artinian actual maximal-ideal
power torsion by the proved Matlis criterion. Actual injective envelopes
preserve finite residue Ext in their cokernels. The genuine coefficient
exact sequence and injective acyclicity therefore prove Artinianity in all
degrees by induction. In particular the result holds for every finite
module, with no regularity, completeness, or Cohen-presentation assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Finite actual socle makes maximal-ideal power torsion genuinely Artinian,
even when the ambient module itself is neither finite nor Artinian. -/
theorem maximalIdealPowerTorsion_isArtinian_of_finiteSocle (M : ModuleCat.{u} R)
    [Module.Finite R (localSocle (R := R) M)] :
    IsArtinian R (powerTorsion (maximalIdeal R) M) := by
  let T := ModuleCat.of R (powerTorsion (maximalIdeal R) M)
  have : Module.Finite R (localSocle (R := R) T) :=
    localSocle_finite_of_injective
      (ModuleCat.ofHom (powerTorsion (maximalIdeal R) M).subtype) Subtype.val_injective
  apply matlisArtinianModuleProperty_isArtinian T
  exact ⟨(moduleLocallyArtinian_iff_support_maximalIdeal T).mpr
    (support_powerTorsion_subset_zeroLocus (maximalIdeal R) M), inferInstance⟩

/-- Finite residue Ext suffices for Artinianity of every original local
cohomology module. Dimension shifting uses the constructed injective
envelope and its actual cokernel, not assumed minimal resolutions. -/
theorem FiniteResidueExt.localCohomology_isArtinian
    {M : ModuleCat.{u} R} (hM : FiniteResidueExt M) (i : ℕ) :
    IsArtinian R ((_root_.localCohomology (maximalIdeal R) i).obj M) := by
  induction i generalizing M with
  | zero =>
    have := hM.socle_finite
    have := maximalIdealPowerTorsion_isArtinian_of_finiteSocle M
    exact isArtinian_of_linearEquiv
      (localCohomologyZeroIsoPowerTorsion (maximalIdeal R) M).symm.toLinearEquiv
  | succ i ih =>
    let E := moduleInjectiveEnvelope M
    have : Mono E.ι := E.essential.mono
    let S := ShortComplex.mk _ _ (cokernel.condition E.ι)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel E.ι }
    let Q := localCohomology.ringModIdeals
      (localCohomology.idealPowersDiagram (maximalIdeal R))
    have := ih (hM.cokernel_injectiveEnvelope E)
    have : IsArtinian R ((extColimitFunctor Q i).obj S.X₃) :=
      isArtinian_of_linearEquiv
        ((idealPowerExtIsoLocalCohomology (maximalIdeal R) i).app S.X₃).symm.toLinearEquiv
    have hz : IsZero ((extColimitFunctor Q (i + 1)).obj S.X₂) :=
      (isZero_localCohomology_succ_of_injective (maximalIdeal R) E.obj i).of_iso
        ((idealPowerExtIsoLocalCohomology (maximalIdeal R) (i + 1)).app E.obj)
    have := ModuleCat.subsingleton_of_isZero hz
    have : IsArtinian R ((extColimitFunctor Q (i + 1)).obj M) :=
      isArtinian_of_range_eq_ker (extColimitδ Q S hS i).hom
        ((extColimitFunctor Q (i + 1)).map S.f).hom
        (extColimit_exact₁ Q S hS i).moduleCat_range_eq_ker
    exact isArtinian_of_linearEquiv
      ((idealPowerExtIsoLocalCohomology (maximalIdeal R) (i + 1)).app M).toLinearEquiv

/-- Over every noetherian local ring, all original local-cohomology values
of a finite module are Artinian. The base need not be regular or complete. -/
theorem localRing_localCohomology_isArtinian (M : ModuleCat.{u} R)
    [Module.Finite R M] (i : ℕ) :
    IsArtinian R ((_root_.localCohomology (maximalIdeal R) i).obj M) :=
  (finiteResidueExt_of_finite M).localCohomology_isArtinian i

end SGA.SGA2.ExposeV
