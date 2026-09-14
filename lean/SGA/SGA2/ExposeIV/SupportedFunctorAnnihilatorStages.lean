/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedFunctorDuality

/-!
# The actual annihilator stages of the representing module

The original map `T(R/Jⁿ) → colim T(R/Jⁿ)` identifies its domain with the
annihilator of `Jⁿ`, not merely an abstract isomorphic submodule. If `T`
is dualizing and `R/J` is Artinian, these actual annihilator stages have
finite length and exhaust the original representing module.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- Evaluation at one, for the actual categorical quotient Hom module. -/
def quotientHomAnnihilatorIso (I : Ideal R) (H : ModuleCat.{u} R) :
    (moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ I))) ≅
      ModuleCat.of R (Submodule.torsionBySet R H (I : Set R)) :=
  (ModuleCat.homLinearEquiv.trans (quotientHomEquivTorsionBySet I H)).toModuleIso

@[simp]
theorem quotientHomAnnihilatorIso_apply (I : Ideal R) (H : ModuleCat.{u} R)
    (f : ModuleCat.of R (R ⧸ I) ⟶ H) :
    ((quotientHomAnnihilatorIso I H).hom f : H) = f.hom 1 := rfl

variable [IsNoetherianRing R]
variable (J : Ideal R) (T : (SupportedFGModuleCat J)ᵒᵖ ⥤ AddCommGrpCat.{u}) [T.Additive]

private theorem supportedQuotientPoint_one (n : ℕ)
    (hn : J ^ n ≤ Module.annihilator R (supportedRingQuotient J n).obj) :
    supportedQuotientPoint J (supportedRingQuotient J n) n hn (1 : R ⧸ J ^ n) =
      𝟙 (supportedRingQuotient J n) := by
  apply ObjectProperty.hom_ext
  apply FGModuleCat.hom_ext
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  change r • (1 : R ⧸ J ^ n) = Ideal.Quotient.mk (J ^ n) r
  simp [Algebra.smul_def]

/-- The original canonical representation evaluates at one to the original
colimit structural map. This fixes the actual inclusion, not just its image. -/
theorem supportedFunctorEvaluation_quotient_one (n : ℕ)
    (t : supportedFunctorStage J T n) :
    supportedFunctorEvaluation J T (supportedRingQuotient J n) t (1 : R ⧸ J ^ n) =
      supportedFunctorColimitι J T n t := by
  have hn : J ^ n ≤ Module.annihilator R (supportedRingQuotient J n).obj := by
    change J ^ n ≤ Module.annihilator R (R ⧸ J ^ n)
    rw [Ideal.annihilator_quotient]
  rw [supportedFunctorEvaluation_eq_stage J T _ n hn,
    supportedColimitStageEvaluation_apply, supportedStageEvaluation_apply,
    supportedQuotientPoint_one, op_id, T.map_id]
  rfl

section LeftExact

variable [PreservesFiniteLimits T]

/-- Each original functor stage is precisely the annihilator of its ideal
power in the original colimit, via canonical evaluation. -/
def supportedFunctorStageAnnihilatorIso (n : ℕ) :
    supportedFunctorStage J T n ≅ ModuleCat.of R
      (Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R)) :=
  (supportedFunctorRepresentationIso J T).app (op (supportedRingQuotient J n)) ≪≫
    quotientHomAnnihilatorIso (J ^ n) (supportedFunctorColimit J T)

@[simp]
theorem supportedFunctorStageAnnihilatorIso_apply (n : ℕ)
    (t : supportedFunctorStage J T n) :
    ((supportedFunctorStageAnnihilatorIso J T n).hom t : supportedFunctorColimit J T) =
      supportedFunctorColimitι J T n t :=
  supportedFunctorEvaluation_quotient_one J T n t

/-- The actual image of the structural map is the actual annihilator. -/
theorem supportedFunctorColimit_range_eq_annihilator (n : ℕ) :
    LinearMap.range (supportedFunctorColimitι J T n).hom =
      Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R) := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    rw [← supportedFunctorStageAnnihilatorIso_apply J T n t]
    exact ((supportedFunctorStageAnnihilatorIso J T n).hom t).property
  · intro hx
    let y : Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R) :=
      ⟨x, hx⟩
    let e := (supportedFunctorStageAnnihilatorIso J T n).toLinearEquiv
    refine ⟨e.symm y, ?_⟩
    rw [← supportedFunctorStageAnnihilatorIso_apply]
    exact congrArg Subtype.val (e.apply_symm_apply y)

end LeftExact

/-- The actual annihilator filtration exhausts the original colimit. -/
theorem supportedFunctorColimit_iSup_annihilator :
    (⨆ n : ℕ, Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R)) =
      ⊤ :=
  supportedFunctorColimit_powerTorsion J T

variable [IsArtinianRing (R ⧸ J)]

/-- Under original functor duality, the actual annihilator stages are finite
length modules. Neither finiteness of the colimit nor of its stages is assumed. -/
theorem supportedFunctorColimit_annihilator_isFiniteLength
    (h : SupportedFunctorDuality J T) (n : ℕ) :
    IsFiniteLength R
      (Submodule.torsionBySet R (supportedFunctorColimit J T) (J ^ n : Ideal R)) := by
  let := h.1
  have hfin : Module.Finite R (supportedFunctorStage J T n) := h.2.1 (supportedRingQuotient J n)
  have hSupp : supportedModuleProperty J (supportedFunctorStage J T n) :=
    (support_subset_zeroLocus_iff_exists_pow_le_annihilator J _).mpr
      ⟨n, supportedFunctorStage_annihilator J T n⟩
  exact (isFiniteLength_of_finite_of_support J (supportedFunctorStage J T n) hSupp).of_surjective
    (supportedFunctorStageAnnihilatorIso J T n).toLinearEquiv.surjective

end SGA.SGA2.ExposeIV
