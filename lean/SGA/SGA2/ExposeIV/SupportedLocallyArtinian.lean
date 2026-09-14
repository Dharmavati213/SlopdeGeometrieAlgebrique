/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorAnnihilatorStages

/-!
# Locally Artinian supported modules

Here locally Artinian has its literal module-theoretic meaning: every
finitely generated submodule is Artinian. For the actual canonical module
representing a dualizing functor, we prove this property and the stronger
description as the union of its finite-length ideal-power annihilators.
The support condition is explicit; no conclusion about invisible off-support
summands of an arbitrary coefficient module is asserted.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- Every finitely generated submodule is Artinian. -/
def ModuleLocallyArtinian (H : Type u) [AddCommGroup H] [Module R H] : Prop :=
  ∀ N : Submodule R H, N.FG → IsArtinian R N

variable [IsNoetherianRing R]

/-- Over a noetherian ring, the literal local Artinian property is equivalent
to finite length of every finitely generated submodule. -/
theorem moduleLocallyArtinian_iff_finiteLength (H : Type u) [AddCommGroup H] [Module R H] :
    ModuleLocallyArtinian (R := R) H ↔
      ∀ N : Submodule R H, N.FG → IsFiniteLength R N := by
  constructor
  · intro h N hN
    have : Module.Finite R N := Module.Finite.of_fg hN
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, h N hN⟩
  · intro h N hN
    exact (isFiniteLength_iff_isNoetherian_isArtinian.mp (h N hN)).2

variable (J : Ideal R) [IsArtinianRing (R ⧸ J)]

/-- Every actual finite submodule of a supported module has finite length;
the whole supported module need not be finite. -/
theorem supportedSubmodule_isFiniteLength (H : ModuleCat.{u} R)
    (hH : supportedModuleProperty J H) (N : Submodule R H) [Module.Finite R N] :
    IsFiniteLength R N :=
  isFiniteLength_of_finite_of_support J (ModuleCat.of R N)
    ((Module.support_subset_of_injective N.subtype N.subtype_injective).trans hH)

/-- Modules supported on an Artinian closed subset are locally Artinian. -/
theorem moduleLocallyArtinian_of_support (H : ModuleCat.{u} R)
    (hH : supportedModuleProperty J H) : ModuleLocallyArtinian (R := R) H := by
  apply (moduleLocallyArtinian_iff_finiteLength H).mpr
  intro N hN
  have : Module.Finite R N := Module.Finite.of_fg hN
  exact supportedSubmodule_isFiniteLength J H hH N

variable (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

/-- The original representing colimit is locally Artinian. Its actual support
is proved by the construction, not imposed as a new hypothesis. -/
theorem supportedFunctorColimit_locallyArtinian :
    ModuleLocallyArtinian (R := R) (supportedFunctorColimit J T) :=
  moduleLocallyArtinian_of_support J _ (supportedFunctorColimit_support J T)

/-- The stronger finite-annihilator filtration for a dualizing functor's
actual canonical representing module, used in IV.4.9 and the completion arguments. -/
theorem supportedFunctorColimit_finiteLength_annihilator_exhaustion
    (h : SupportedFunctorDuality J T) :
    (∀ n : ℕ, IsFiniteLength R
      (Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R))) ∧
    (⨆ n : ℕ, Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R)) =
      ⊤ :=
  ⟨supportedFunctorColimit_annihilator_isFiniteLength J T h,
    supportedFunctorColimit_iSup_annihilator J T⟩

/-- **IV.4.9 for the original canonical representing module.** The maximal
ideal quotient is a field, so no Artinian-ring hypothesis is added. -/
theorem localDualizingFunctorColimit_locallyArtinian [IsLocalRing R]
    (T : (SupportedFGModuleCat (IsLocalRing.maximalIdeal R))ᵒᵖ ⥤ AddCommGrpCat.{u})
    [T.Additive] :
    ModuleLocallyArtinian (R := R)
      (supportedFunctorColimit (IsLocalRing.maximalIdeal R) T) := by
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
  exact supportedFunctorColimit_locallyArtinian (IsLocalRing.maximalIdeal R) T

end SGA.SGA2.ExposeIV
