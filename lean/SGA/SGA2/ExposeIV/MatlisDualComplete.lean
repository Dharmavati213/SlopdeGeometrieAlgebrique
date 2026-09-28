/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.HomAnnihilatorQuotient
import SGA.SGA2.ExposeIV.AdicQuotientLimit
import SGA.SGA2.ExposeIV.SupportedAnnihilatorColimit
import SGA.SGA2.ExposeIV.FiniteSocleAnnihilators
import SGA.SGA2.ExposeIV.CompleteFiniteModules
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes

/-!
# IV.5.1: the actual dual of a supported module is adically complete

Restriction to the original power annihilators identifies the actual adic
quotients of the dual with the duals of those annihilators, compatibly with
every original transition. Since the original supported module is their
colimit, the dual is the limit of its actual quotients. The comparison is
proved equal to the original completion map, not merely an abstract
isomorphism with some inverse limit.

Over a noetherian local ring, a supported module with finite socle has a
dual with finite reduction modulo every maximal-ideal power. If the base
ring is complete, genuine topological Nakayama makes the original dual a
finite module.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]
variable (J : Ideal R) (hJ : J.FG) (H X : ModuleCat.{u} R) [Injective H]

/-- The original quotient-restriction isomorphisms commute with every
original quotient transition and actual annihilator inclusion. -/
def homDualQuotientAnnihilatorDiagramIso :
    adicQuotientDiagram J ((moduleHomDual H).obj (op X)) ≅
      (annihilatorFiltration J X).op ⋙ moduleHomDual H :=
  NatIso.ofComponents
    (fun n => homIdealAnnihilatorQuotientIso (J ^ n.unop) hJ.pow H X)
    (fun f => by
      apply ModuleCat.hom_ext
      ext g
      refine Quotient.inductionOn' g (fun g => ?_)
      apply ModuleCat.hom_ext
      ext x
      rfl)

/-- The literal quotient-projection cone on the original dual. -/
def homDualQuotientCone :
    Cone (adicQuotientDiagram J ((moduleHomDual H).obj (op X))) :=
  ⟨(moduleHomDual H).obj (op X),
    adicQuotientProjection J ((moduleHomDual H).obj (op X))⟩

/-- Applying the diagram comparison to the literal quotient cone gives
exactly the original restriction cone obtained by applying Hom. -/
def homDualQuotientConeIso :
    (Cone.postcompose (homDualQuotientAnnihilatorDiagramIso J hJ H X).hom).obj
      (homDualQuotientCone J H X) ≅
        (moduleHomDual H).mapCone (annihilatorFiltrationCocone J X).op :=
  Cone.ext (Iso.refl _) (fun n => by
    change 𝟙 ((moduleHomDual H).obj (op X)) ≫
      homIdealAnnihilatorRestriction (J ^ n.unop) H X = _
    rw [Category.id_comp]
    exact (homIdealAnnihilatorQuotientIso_mkQ (J ^ n.unop) hJ.pow H X).symm)

/-- The original dual is the limit of its original adic quotients. -/
def homDualQuotientConeIsLimit (hX : powerTorsion J X = ⊤) :
    IsLimit (homDualQuotientCone J H X) :=
  (IsLimit.postcomposeHomEquiv (homDualQuotientAnnihilatorDiagramIso J hJ H X) _)
    (IsLimit.ofIsoLimit (annihilatorHomIsLimit J X H hX)
      (homDualQuotientConeIso J hJ H X).symm)

/-- The actual dual is isomorphic to its actual adic completion. -/
def homDualCompletionIso (hX : powerTorsion J X = ⊤) :
    (moduleHomDual H).obj (op X) ≅
      ModuleCat.of R (AdicCompletion J ((moduleHomDual H).obj (op X))) :=
  (homDualQuotientConeIsLimit J hJ H X hX).conePointUniqueUpToIso
    (adicCompletionConeIsLimit J ((moduleHomDual H).obj (op X)))

/-- The inverse-limit comparison is the original completion map itself. -/
theorem homDualCompletionIso_hom (hX : powerTorsion J X = ⊤) :
    (homDualCompletionIso J hJ H X hX).hom =
      ModuleCat.ofHom (AdicCompletion.of J ((moduleHomDual H).obj (op X))) := by
  apply (adicCompletionConeIsLimit J ((moduleHomDual H).obj (op X))).hom_ext
  intro n
  exact ((homDualQuotientConeIsLimit J hJ H X hX).conePointUniqueUpToIso_hom_comp
    (adicCompletionConeIsLimit J ((moduleHomDual H).obj (op X))) n).trans
      (adicCompletion_of_π J ((moduleHomDual H).obj (op X)) n).symm

include hJ in
/-- The actual completion map is bijective, not only a comparison with
an abstract inverse-limit model. -/
theorem homDual_completion_of_bijective (hX : powerTorsion J X = ⊤) :
    Function.Bijective (AdicCompletion.of J ((moduleHomDual H).obj (op X))) := by
  have h := (homDualCompletionIso J hJ H X hX).toLinearEquiv.bijective
  change Function.Bijective (homDualCompletionIso J hJ H X hX).hom at h
  rwa [homDualCompletionIso_hom] at h

include hJ in
/-- The actual dual of an arbitrary power-torsion module is adically complete. -/
theorem homDual_isAdicComplete (hX : powerTorsion J X = ⊤) :
    IsAdicComplete J ((moduleHomDual H).obj (op X)) :=
  AdicCompletion.of_bijective_iff.mp (homDual_completion_of_bijective J hJ H X hX)

include hJ in
/-- The support formulation for a finitely generated ideal. -/
theorem supported_homDual_isAdicComplete (hX : supportedModuleProperty J X) :
    IsAdicComplete J ((moduleHomDual H).obj (op X)) :=
  homDual_isAdicComplete J hJ H X ((powerTorsion_eq_top_iff_support_of_fg J hJ X).mpr hX)

section Local

variable [IsNoetherianRing R] [IsLocalRing R]
variable {H}

omit [Injective H] in
/-- Supported duality supplies actual injectivity, hence completeness of
the original dual of every module supported at the closed point. -/
theorem SupportedDualizingModule.supported_dual_isAdicComplete
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X) :
    IsAdicComplete (IsLocalRing.maximalIdeal R) ((moduleHomDual H).obj (op X)) := by
  have : Injective H := injective_of_supported_bidually_reflexive _ H hH.1 hH.2.1 hH.2.2
  exact supported_homDual_isAdicComplete _ (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    H X hX

omit [Injective H] in
/-- A finite socle makes every actual power quotient of the dual finite;
only the literal finite annihilator stages are fed to finite supported duality. -/
theorem SupportedDualizingModule.finiteSocle_dual_powerQuotient_finite
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X)
    [Module.Finite R (localSocle (R := R) X)] (n : ℕ) :
    Module.Finite R (((moduleHomDual H).obj (op X)) ⧸
      ((IsLocalRing.maximalIdeal R ^ n) •
        (⊤ : Submodule R ((moduleHomDual H).obj (op X))))) := by
  let m := IsLocalRing.maximalIdeal R
  let A := ModuleCat.of R (Submodule.torsionBySet R X (m ^ n : Ideal R))
  have : Injective H := injective_of_supported_bidually_reflexive _ H hH.1 hH.2.1 hH.2.2
  have : Module.Finite R A :=
    maximalIdealAnnihilator_finite_of_finite_socle X m.fg_of_isNoetherianRing n
  have hA : supportedModuleProperty m A :=
    (Module.support_subset_of_injective
      (Submodule.torsionBySet R X (m ^ n : Ideal R)).subtype Subtype.val_injective).trans hX
  have : Module.Finite R ((moduleHomDual H).obj (op A)) := hH.2.1 A inferInstance hA
  exact Module.Finite.equiv
    (homIdealAnnihilatorQuotientIso (m ^ n) (m ^ n).fg_of_isNoetherianRing H X).toLinearEquiv.symm

omit [Injective H] in
/-- In particular the actual reduction of the dual modulo the maximal ideal is finite. -/
theorem SupportedDualizingModule.finiteSocle_dual_reduction_finite
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X)
    [Module.Finite R (localSocle (R := R) X)] :
    Module.Finite R (((moduleHomDual H).obj (op X)) ⧸
      (IsLocalRing.maximalIdeal R •
        (⊤ : Submodule R ((moduleHomDual H).obj (op X))))) := by
  have h := hH.finiteSocle_dual_powerQuotient_finite X hX 1
  rw [pow_one] at h
  exact h

omit [Injective H] in
/-- **IV.5.1, locally Artinian direction over a complete base:** the original
dual of a supported module with finite socle is genuinely a finite module. -/
theorem SupportedDualizingModule.supported_finiteSocle_dual_finite
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R)
    (hX : supportedModuleProperty (IsLocalRing.maximalIdeal R) X)
    [Module.Finite R (localSocle (R := R) X)] :
    Module.Finite R ((moduleHomDual H).obj (op X)) := by
  have := hH.supported_dual_isAdicComplete X hX
  have := hH.finiteSocle_dual_reduction_finite X hX
  exact finite_of_isHausdorff_of_finite_reduction
    (IsLocalRing.maximalIdeal R) ((moduleHomDual H).obj (op X))

omit [Injective H] in
/-- The literal locally Artinian / finite-socle formulation of the same result. -/
theorem SupportedDualizingModule.locallyArtinian_finiteSocle_dual_finite
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (hH : SupportedDualizingModule H) (X : ModuleCat.{u} R)
    (hX : ModuleLocallyArtinian (R := R) X)
    [Module.Finite R (localSocle (R := R) X)] :
    Module.Finite R ((moduleHomDual H).obj (op X)) :=
  hH.supported_finiteSocle_dual_finite X
    ((moduleLocallyArtinian_iff_support_maximalIdeal X).mp hX)

end Local

end SGA.SGA2.ExposeIV
