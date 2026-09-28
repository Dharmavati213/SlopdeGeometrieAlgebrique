/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.RegularLocalExtFunctor
import SGA.SGA2.ExposeIV.RegularLocalTopExt
import SGA.SGA2.ExposeIV.ModuleExtDerivedLinear
import SGA.SGA2.ExposeIV.LocalInjectiveEnvelopes

/-!
# IV.5.4: actual top Ext is a dualizing functor

The residue computation uses the actual regular Koszul resolution and the
proved scalar-compatible comparison of both Ext constructions. Thus it is
an isomorphism for the functor's canonical source-induced module action,
not merely an additive-group coincidence. Original top-Ext exactness and
IV.3.1 then prove duality and the dualizing property of the actual representing
quotient-Ext colimit. The local-cohomology identification is separate.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

local instance regularExtDualityResidueField : Field (R ⧸ maximalIdeal R) :=
  Ideal.Quotient.field _

/-- The top residue value with the original functor's actual canonical
module action. The isomorphism uses the chosen ordered regular parameters. -/
def regularLocalTopExtResidueIso (n : ℕ) (hdim : ringKrullDim R = n) :
    supportedFunctorValue (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n)
        (supportedResidueField (maximalIdeal R) (maximalIdeal R) le_rfl) ≅
      ModuleCat.of R (R ⧸ maximalIdeal R) :=
  regularLocalTopExtValueIso n _ ≪≫
    (moduleExtLinearIsoAbelianExt (ModuleCat.of R (ResidueField R)) (ModuleCat.of R R) n).symm ≪≫
    regularLocal_topResidueModuleExtIso n hdim

/-- All original residue tests follow from the actual local residue value. -/
theorem regularLocalTopExtFunctor_residueTests (n : ℕ) (hdim : ringKrullDim R = n) :
    SupportedFunctorResidueTests (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) := by
  intro m hm hle
  obtain rfl := IsLocalRing.eq_maximalIdeal hm
  exact ⟨regularLocalTopExtResidueIso n hdim⟩

/-- **SGA 2, IV.5.4, functor assertion.** The original abelian-group-valued
top Ext functor is dualizing. Its finite values, length preservation, and
canonical twice-iterated evaluation are conclusions, not hypotheses. -/
theorem regularLocalTopExtFunctor_duality (n : ℕ) (hdim : ringKrullDim R = n) :
    SupportedFunctorDuality (maximalIdeal R) (regularLocalTopExtFunctor (R := R) n) :=
  supportedFunctor_duality_of_exact_residue _ _
    (regularLocalTopExtFunctor_exact n hdim) (regularLocalTopExtFunctor_residueTests n hdim)

/-- **IV.5.4, actual representing module.** The original quotient-Ext
colimit with its canonical scalar action is supported dualizing. -/
theorem regularLocalTopExtModule_dualizing (n : ℕ) (hdim : ringKrullDim R = n) :
    SupportedDualizingModule (regularLocalTopExtModule (R := R) n) := by
  have h := regularLocalTopExtFunctor_duality n hdim
  have := h.1
  exact ⟨regularLocalTopExtModule_supported n,
    (supportedFunctor_reflexive_iff_homBidual _ _).mp h.2⟩

/-- The actual top quotient-Ext colimit is locally Artinian as a consequence
of its proved dualizing property. -/
theorem regularLocalTopExtModule_locallyArtinian (n : ℕ) (hdim : ringKrullDim R = n) :
    ModuleLocallyArtinian (R := R) (regularLocalTopExtModule (R := R) n) :=
  (regularLocalTopExtModule_dualizing n hdim).locallyArtinian

/-- Its actual annihilator of the maximal ideal is the residue module. -/
theorem regularLocalTopExtModule_socle_iso (n : ℕ) (hdim : ringKrullDim R = n) :
    Nonempty (ModuleCat.of R (Submodule.torsionBySet R (regularLocalTopExtModule (R := R) n)
      (maximalIdeal R : Set R)) ≅ ModuleCat.of R (R ⧸ maximalIdeal R)) :=
  (regularLocalTopExtModule_dualizing n hdim).socle_iso

end SGA.SGA2.ExposeIV
