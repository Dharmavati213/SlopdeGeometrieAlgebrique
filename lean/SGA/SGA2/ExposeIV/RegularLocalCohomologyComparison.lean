/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalExtFunctor
import SGA.SGA2.ExposeIV.ModuleExtDerivedLinear
import SGA.SGA2.ExposeIV.ModuleExtDerivedNaturality
import SGA.SGA2.ExposeIV.SupportedExtDiagram
import SGA.SGA2.ExposeII.AffineCohomologyComparison

/-!
# The actual regular-local quotient-Ext colimit is local cohomology

The stage values used in the original IV.1.3 colimit have the canonical
source-induced scalar action. The actual linear Ext comparison identifies
them with the actual module-valued quotient Ext defining local cohomology.
First-variable naturality respects the original quotient transitions, so
the actual diagrams and their colimits are isomorphic. The affine comparison
also supplies the supported-sheaf-cohomology interpretation in IV.5.4's
footnote, using the original sheaf and original supported Ext groups.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- The original IV.1.3 stage and original algebraic-local-cohomology
stage agree as `R`-modules, including their actual scalar actions. -/
def regularLocalTopExtStageIso (n k : ℕ) :
    supportedFunctorStage (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) k ≅
      (moduleExtPowerDiagram (maximalIdeal R) (ModuleCat.of R R) n).obj k :=
  regularLocalTopExtValueIso n (supportedRingQuotient (maximalIdeal R) k) ≪≫
    (moduleExtLinearIsoAbelianExt (ModuleCat.of R (R ⧸ maximalIdeal R ^ k))
      (ModuleCat.of R R) n).symm

@[simp]
theorem regularLocalTopExtStageIso_hom_apply (n k : ℕ)
    (x : supportedFunctorStage (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) k) :
    (regularLocalTopExtStageIso (R := R) n k).hom x =
      (moduleExtLinearEquivAbelianExt (ModuleCat.of R (R ⧸ maximalIdeal R ^ k))
        (ModuleCat.of R R) n).symm x := rfl

/-- The original stage comparisons respect the actual quotient-induced
Ext transitions; no commutative square is imposed as a hypothesis. -/
def regularLocalTopExtDiagramIso (n : ℕ) :
    supportedFunctorDiagram (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) ≅
      moduleExtPowerDiagram (maximalIdeal R) (ModuleCat.of R R) n := by
  refine NatIso.ofComponents (regularLocalTopExtStageIso n) ?_
  intro k l h
  apply ModuleCat.hom_ext
  ext x
  let q : ModuleCat.of R (R ⧸ maximalIdeal R ^ l) ⟶
      ModuleCat.of R (R ⧸ maximalIdeal R ^ k) :=
    ModuleCat.ofHom (Submodule.factor (Ideal.pow_le_pow_right (leOfHom h)))
  apply (moduleExtLinearEquivAbelianExt (ModuleCat.of R (R ⧸ maximalIdeal R ^ l))
    (ModuleCat.of R R) n).injective
  change (moduleExtLinearEquivAbelianExt _ (ModuleCat.of R R) n)
      ((moduleExtLinearEquivAbelianExt _ (ModuleCat.of R R) n).symm
        ((Abelian.Ext.mk₀ q).comp x (zero_add n))) =
    (moduleExtLinearEquivAbelianExt _ (ModuleCat.of R R) n)
      (((_root_.Ext R (ModuleCat.{u} R) n).map q.op).app (ModuleCat.of R R)
        ((moduleExtLinearEquivAbelianExt _ (ModuleCat.of R R) n).symm x))
  rw [LinearEquiv.apply_symm_apply, moduleExtLinearEquivAbelianExt_naturality_first,
    LinearEquiv.apply_symm_apply]

/-- **IV.5.4, the representing module:** the original top quotient-Ext
colimit, with its canonical action, is the actual algebraic local-cohomology
module. The diagram comparison holds in every degree. -/
def regularLocalTopExtModuleIsoLocalCohomology (n : ℕ) :
    regularLocalTopExtModule (R := R) n ≅
      (_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R) :=
  HasColimit.isoOfNatIso (regularLocalTopExtDiagramIso n) ≪≫
    moduleExtPowerColimitIsoLocalCohomology (maximalIdeal R) (ModuleCat.of R R) n

/-- Each original quotient-Ext stage maps to local cohomology by its
original canonical colimit map under the comparison. -/
@[reassoc]
theorem regularLocalTopExtModuleIsoLocalCohomology_ι (n k : ℕ) :
    supportedFunctorColimitι (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) k ≫
      (regularLocalTopExtModuleIsoLocalCohomology (R := R) n).hom =
    (regularLocalTopExtStageIso (R := R) n k).hom ≫
      (colimit.ι (localCohomology.diagram
        (localCohomology.idealPowersDiagram (maximalIdeal R)) n) (op (op k))).app
          (ModuleCat.of R R) := by
  dsimp only [regularLocalTopExtModuleIsoLocalCohomology, Iso.trans_hom,
    supportedFunctorColimitι]
  erw [HasColimit.isoOfNatIso_ι_hom_assoc, moduleExtPowerColimitIsoLocalCohomology_ι]
  rfl

/-- **IV.5.4, original geometric interpretation:** the same actual
representing module has underlying group equal to the original supported
sheaf cohomology on the affine spectrum. -/
def regularLocalTopExtModuleIsoSupportedCohomology (n : ℕ) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj (regularLocalTopExtModule (R := R) n) ≅
      AddCommGrpCat.of (ExposeI.H_Z
        (ExposeII.affineSupportClosed (R := CommRingCat.of R) (maximalIdeal R))
        (ExposeII.affineTildeAbSheaf (R := CommRingCat.of R) (ModuleCat.of R R)) n) :=
  (forget₂ (ModuleCat R) AddCommGrpCat).mapIso (regularLocalTopExtModuleIsoLocalCohomology n) ≪≫
    ExposeII.affineLocalCohomologyIso (R := CommRingCat.of R)
      (maximalIdeal R) (ModuleCat.of R R) n

end SGA.SGA2.ExposeIV
