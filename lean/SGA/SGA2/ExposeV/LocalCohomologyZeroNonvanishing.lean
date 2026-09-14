/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeV.LocalCohomologyDualDimension

/-!
# Degree-zero inputs for top local-cohomology nonvanishing

On an actually supported module, the original torsion inclusion identifies
degree-zero local cohomology with the coefficient module. On the original
finite torsion quotient, degree-zero local cohomology is zero instead.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- The original degree-zero comparison followed by the actual torsion
inclusion is an isomorphism on supported coefficients. -/
def localCohomologyZeroIsoOfSupported (I : Ideal R) (M : ModuleCat.{u} R)
    (hM : supportedModuleProperty I M) : (_root_.localCohomology I 0).obj M ≅ M := by
  have ht := powerTorsion_eq_top_of_support_subset_zeroLocus I M hM
  let f := ModuleCat.ofHom (powerTorsion I M).subtype
  have : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr
    ⟨(powerTorsion I M).injective_subtype, fun x =>
      ⟨⟨x, by rw [ht]; trivial⟩, rfl⟩⟩
  exact localCohomologyZeroIsoPowerTorsion I M ≪≫ asIso f

/-- The actual finite torsion quotient has no degree-zero local cohomology. -/
theorem localCohomologyZero_powerTorsion_quotient_isZero (I : Ideal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    IsZero ((_root_.localCohomology I 0).obj (ModuleCat.of R (M ⧸ powerTorsion I M))) := by
  have : Subsingleton (powerTorsion I (M ⧸ powerTorsion I M)) := by
    rw [powerTorsion_quotient_eq_bot]
    infer_instance
  exact (ModuleCat.isZero_of_subsingleton _).of_iso
    (localCohomologyZeroIsoPowerTorsion I (ModuleCat.of R (M ⧸ powerTorsion I M)))

variable [IsLocalRing R]

/-- Every nonzero zero-dimensional finite coefficient has nonzero
original degree-zero local cohomology. -/
theorem localRing_localCohomologyZero_nontrivial_of_supportDim_eq_zero
    (M : ModuleCat.{u} R) [Module.Finite R M] (hdim : Module.supportDim R M = 0) :
    Nontrivial ((_root_.localCohomology (maximalIdeal R) 0).obj M) := by
  have : Nontrivial M := (Module.supportDim_ne_bot_iff_nontrivial R M).mp (by simp [hdim])
  exact (localCohomologyZeroIsoOfSupported (maximalIdeal R) M
    (support_of_supportDim_eq_zero R M hdim).le).toLinearEquiv.surjective.nontrivial

/-- The original degree-zero dual of a zero-dimensional finite module
has exactly dimension zero, over any noetherian local base. -/
theorem localRing_localCohomologyZero_dual_supportDim_eq_zero
    (M D : ModuleCat.{u} R) [Module.Finite R M]
    (hD : SupportedDualizingModule D) (hdim : Module.supportDim R M = 0) :
    Module.supportDim R
      ((moduleHomDual D).obj (op ((_root_.localCohomology (maximalIdeal R) 0).obj M))) = 0 := by
  have hs : supportedModuleProperty (maximalIdeal R) M :=
    (support_of_supportDim_eq_zero R M hdim).le
  have : Nontrivial M := (Module.supportDim_ne_bot_iff_nontrivial R M).mp (by simp [hdim])
  have : IsIso (moduleBidualEvaluation D M) := hD.2.2 M inferInstance hs
  have : Nontrivial ((moduleHomDual D).obj (op M)) :=
    moduleHomDual_nontrivial_of_bidually_reflexive D M
  let e := (moduleHomDual D).mapIso (localCohomologyZeroIsoOfSupported (maximalIdeal R) M hs).op
  have : Nontrivial ((moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) 0).obj M))) :=
    e.toLinearEquiv.injective.nontrivial
  have : Nonempty (Module.support R ((moduleHomDual D).obj
      (op ((_root_.localCohomology (maximalIdeal R) 0).obj M)))) :=
    Module.nonempty_support_of_nontrivial.to_subtype
  exact le_antisymm (localRing_localCohomologyZero_dual_supportDim_le M D hD)
    Order.krullDim_nonneg

end SGA.SGA2.ExposeV
