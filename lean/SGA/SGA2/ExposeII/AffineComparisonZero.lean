/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.AffineSupport
import SGA.SGA2.ExposeII.KoszulCohomologyZero
import SGA.SGA2.ExposeII.LocalCohomologyZero

/-!
# SGA 2, Exposé II, (5.1), (7.3), and (7.5) in degree zero

Stable Koszul cohomology and the Ext-colimit model of local cohomology in
degree zero identify with the supported global sections of the actual
associated sheaf on `Spec R`. We also express these comparisons using the
`Γ_Z` definition from Exposé I. These statements are in degree zero; no
higher sheaf cohomology comparison is assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace SGA.SGA2.ExposeII

variable {R : CommRingCat.{u}}

/-- The support ideal of a finite Koszul list is finitely generated. -/
theorem koszulIdeal_fg (fs : List R) : (koszulIdeal fs).FG := by
  rw [koszulIdeal_eq_span_get]
  exact Submodule.fg_span (Set.finite_range (fun j : Fin fs.length ↦ fs.get j))

/-- Ideal-power torsion identifies naturally with supported sections of the
associated sheaf; the target acts on maps by the actual sheaf morphisms. -/
def powerTorsionIsoAffineSupportedFunctor (I : Ideal R) (hI : I.FG) :
    powerTorsionFunctor I ≅ affineSupportedSectionsFunctor I :=
  NatIso.ofComponents
    (fun M ↦ (powerTorsionEquivAffineSupportedSections M I hI).toModuleIso) (by
      intro M N f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change powerTorsion I M at x
      apply Subtype.ext
      change (tilde.isoTop N).hom (f x) =
        (modulesSpecToSheaf.map (tilde.map f)).hom.app (op ⊤) ((tilde.isoTop M).hom x)
      exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app f ⊤) x).symm)

/-- The degree-zero Ext-colimit comparison is natural in the coefficient module. -/
def localCohomologyZeroIsoAffineSupportedFunctor (I : Ideal R) (hI : I.FG) :
    _root_.localCohomology I 0 ≅ affineSupportedSectionsFunctor I :=
  localCohomologyZeroIsoPowerTorsionFunctor I ≪≫ powerTorsionIsoAffineSupportedFunctor I hI

/-- II.(5.1), degree zero: stable Koszul cohomology is the module of sections
of the associated sheaf supported on the closed subset defined by the list. -/
def stableKoszulCohomologyZeroIsoAffineSupported (fs : List R) (M : ModuleCat.{u} R) :
    stableKoszulCohomology fs M 0 ≅ ModuleCat.of R (affineSupportedSections M (koszulIdeal fs)) :=
  stableKoszulCohomologyZeroIsoPowerTorsion fs M ≪≫
    (powerTorsionEquivAffineSupportedSections M (koszulIdeal fs) (koszulIdeal_fg fs)).toModuleIso

/-- II.(7.3), degree zero: the Ext-colimit model is the module of supported
sections of the associated sheaf for finitely generated support ideals. -/
def localCohomologyZeroIsoAffineSupported (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R) :
    (_root_.localCohomology I 0).obj M ≅ ModuleCat.of R (affineSupportedSections M I) :=
  localCohomologyZeroIsoPowerTorsion I M ≪≫
    (powerTorsionEquivAffineSupportedSections M I hI).toModuleIso

/-- II.(5.1), degree zero, using exactly the supported-section group `Γ_Z`
defined in Exposé I. -/
def stableKoszulCohomologyZeroIsoGammaZ (fs : List R) (M : ModuleCat.{u} R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (stableKoszulCohomology fs M 0) ≅
      AddCommGrpCat.of (ExposeI.gammaZ (affineTildeAbSheaf M)
        (affineSupportClosed (koszulIdeal fs))) :=
  (forget₂ (ModuleCat R) AddCommGrpCat).mapIso (stableKoszulCohomologyZeroIsoPowerTorsion fs M) ≪≫
    (powerTorsionEquivGammaZ M (koszulIdeal fs) (koszulIdeal_fg fs)).toAddCommGrpIso

/-- II.(7.3), degree zero, with the geometric target expressed as `Γ_Z`. -/
def localCohomologyZeroIsoGammaZ (I : Ideal R) (hI : I.FG) (M : ModuleCat.{u} R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj ((_root_.localCohomology I 0).obj M) ≅
      AddCommGrpCat.of (ExposeI.gammaZ (affineTildeAbSheaf M) (affineSupportClosed I)) :=
  (forget₂ (ModuleCat R) AddCommGrpCat).mapIso (localCohomologyZeroIsoPowerTorsion I M) ≪≫
    (powerTorsionEquivGammaZ M I hI).toAddCommGrpIso

end SGA.SGA2.ExposeII
