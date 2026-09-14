/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalExtDuality
import SGA.SGA2.ExposeIV.RegularLocalCohomologyComparison
import SGA.SGA2.ExposeIV.SupportedDualityTransport
import SGA.SGA2.ExposeIV.SupportedRestrictedHom

/-!
# IV.5.4: the actual top local cohomology module is dualizing

The original top Ext functor is represented by the actual local cohomology
module, using the proved comparison of the original quotient diagrams and
their colimits. Coefficient transport retains canonical Hom evaluation, so
the conclusion is genuine supported duality, not merely injectivity or an
unspecified representing coefficient.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- **IV.5.4.** The original algebraic local cohomology in the actual Krull
dimension is a supported dualizing module. -/
theorem regularLocal_localCohomology_dualizing (n : ℕ) (hdim : ringKrullDim R = n) :
    SupportedDualizingModule
      ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) :=
  SupportedDualizingModule.of_iso (regularLocalTopExtModuleIsoLocalCohomology n)
    (regularLocalTopExtModule_dualizing n hdim)

/-- In particular the actual top local cohomology is injective among all
`R`-modules, not only in the supported subcategory. -/
theorem regularLocal_localCohomology_injective (n : ℕ) (hdim : ringKrullDim R = n) :
    Injective ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) :=
  (supportedDualizingModule_iff_support_injective_residue _).mp
    (regularLocal_localCohomology_dualizing n hdim) |>.2.1

/-- The same original local cohomology module is locally Artinian. -/
theorem regularLocal_localCohomology_locallyArtinian (n : ℕ)
    (hdim : ringKrullDim R = n) :
    ModuleLocallyArtinian (R := R)
      ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) :=
  (regularLocal_localCohomology_dualizing n hdim).locallyArtinian

/-- Its actual maximal-ideal annihilator is the residue module. -/
theorem regularLocal_localCohomology_socle_iso (n : ℕ) (hdim : ringKrullDim R = n) :
    Nonempty (ModuleCat.of R (Submodule.torsionBySet R
      ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R))
      (maximalIdeal R : Set R)) ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) :=
  (regularLocal_localCohomology_dualizing n hdim).socle_iso

/-- **IV.5.4, the original representing functor.** Canonical evaluation
followed by the actual colimit comparison represents top Ext by the actual
local cohomology module, naturally on the original finite supported category. -/
def regularLocalTopExtLocalCohomologyRepresentationIso (n : ℕ)
    (hdim : ringKrullDim R = n) :
    regularLocalTopExtFunctor (R := R) n ≅
      supportedModuleHomFunctor (maximalIdeal R)
        ((_root_.localCohomology (maximalIdeal R) n).obj (ModuleCat.of R R)) ⋙
          forget₂ (ModuleCat R) AddCommGrpCat :=
  regularLocalTopExtRepresentationIso n hdim ≪≫
    (supportedModuleRepresentations (maximalIdeal R)).mapIso
      (regularLocalTopExtModuleIsoLocalCohomology n)

end SGA.SGA2.ExposeIV
