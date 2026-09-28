/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.HomQuotientAnnihilator
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes
import SGA.SGA2.ExposeIV.LocalArtinianSupport
import SGA.SGA2.ExposeIV.SupportedScalarChange

/-!
# IV.5.1: finite modules dualize into the original locally Artinian category

The original finite module is not assumed to have finite length or closed-point
support. Actual Hom into a supported coefficient is supported, because every
individual morphism has a finite supported image. Its actual ideal-power
annihilators are the duals of the original module's ideal-power quotients.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Each map from a finite module into a supported coefficient has an image
annihilated by an actual ideal power. The source need not be supported. -/
theorem finiteSource_hom_exists_pow_kill (J : Ideal R) (H M : ModuleCat.{u} R)
    [Module.Finite R M] (hH : supportedModuleProperty J H) (f : M ⟶ H) :
    ∃ n : ℕ, ∀ r ∈ J ^ n, ∀ x : M, r • f x = 0 := by
  have : Module.Finite R f.hom.range := Module.Finite.range f.hom
  have hs : supportedModuleProperty J (ModuleCat.of R f.hom.range) :=
    (Module.support_subset_of_injective f.hom.range.subtype
      f.hom.range.subtype_injective).trans hH
  obtain ⟨n, hn⟩ := finite_support_pow_annihilator_of_fg J J.fg_of_isNoetherianRing
    f.hom.range hs
  refine ⟨n, fun r hr x => ?_⟩
  exact congrArg Subtype.val (Module.mem_annihilator.mp (hn hr)
    (⟨f x, ⟨x, rfl⟩⟩ : f.hom.range))

/-- Actual Hom of an arbitrary finite source into a supported coefficient
is supported, without assuming that Hom module finite. -/
theorem finiteSource_moduleHomDual_supported (J : Ideal R) (H M : ModuleCat.{u} R)
    [Module.Finite R M] (hH : supportedModuleProperty J H) :
    supportedModuleProperty J ((moduleHomDual H).obj (op M)) := by
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro f _
  obtain ⟨n, hn⟩ := finiteSource_hom_exists_pow_kill J H M hH f
  refine (mem_powerTorsion_iff J _ f).mpr ⟨n, fun r hr => ?_⟩
  apply ModuleCat.hom_ext
  ext x
  exact hn r hr x

omit [IsNoetherianRing R] in
/-- The original ideal-power quotient of any module has actual support
on `V(J)`, regardless of the source support. -/
theorem finiteSource_powerQuotient_supported (J : Ideal R) (M : ModuleCat.{u} R)
    (n : ℕ) :
    supportedModuleProperty J
      (ModuleCat.of R (M ⧸ (J ^ n • (⊤ : Submodule R M)))) := by
  apply support_subset_zeroLocus_of_powerTorsion_eq_top
  apply top_unique
  intro x _
  refine (mem_powerTorsion_iff J _ x).mpr ⟨n, fun r hr => ?_⟩
  obtain ⟨y, rfl⟩ := (J ^ n • (⊤ : Submodule R M)).mkQ_surjective x
  rw [← map_smul]
  exact (Submodule.Quotient.mk_eq_zero _).mpr
    (Submodule.smul_mem_smul hr Submodule.mem_top)

variable [IsLocalRing R]

omit [IsNoetherianRing R] in
/-- Every actual power annihilator of the dual of a finite module is finite,
using original finite supported duality only on the corresponding quotient. -/
theorem SupportedDualizingModule.finiteSource_annihilator_finite
    {H : ModuleCat.{u} R} (hH : SupportedDualizingModule H)
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    Module.Finite R (Submodule.torsionBySet R ((moduleHomDual H).obj (op M))
      (IsLocalRing.maximalIdeal R ^ n : Ideal R)) := by
  let J := IsLocalRing.maximalIdeal R
  let Q := ModuleCat.of R (M ⧸ (J ^ n • (⊤ : Submodule R M)))
  have : Module.Finite R ((moduleHomDual H).obj (op Q)) :=
    hH.2.1 Q inferInstance (finiteSource_powerQuotient_supported J M n)
  exact Module.Finite.equiv (quotientHomIdealAnnihilatorIso (J ^ n) H M).toLinearEquiv

/-- **IV.5.1, finite-source direction:** actual Hom into the dualizing module
is locally Artinian and its actual socle is finite-dimensional. -/
theorem SupportedDualizingModule.finiteSource_dual_locallyArtinian_finiteSocle
    {H : ModuleCat.{u} R} (hH : SupportedDualizingModule H)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ModuleLocallyArtinian (R := R) ((moduleHomDual H).obj (op M)) ∧
      Module.Finite R (localSocle (R := R) ((moduleHomDual H).obj (op M))) := by
  refine ⟨(moduleLocallyArtinian_iff_support_maximalIdeal _).mpr
    (finiteSource_moduleHomDual_supported _ H M hH.1), ?_⟩
  have hs := hH.finiteSource_annihilator_finite M 1
  change Module.Finite R (Submodule.torsionBySet R ((moduleHomDual H).obj (op M))
    ((IsLocalRing.maximalIdeal R ^ 1 : Ideal R) : Set R)) at hs
  rw [pow_one] at hs
  exact hs

end SGA.SGA2.ExposeIV
