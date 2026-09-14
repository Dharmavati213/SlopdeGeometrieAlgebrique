/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.FiniteCoinductionDuality
import SGA.SGA2.ExposeIV.FiniteCoinductionSupport
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# IV.4.4: the actual ideal-annihilator dualizing module

Evaluation at `1` identifies genuine quotient coinduction with the actual
submodule of elements annihilated by the ideal, equipped with its ordinary
quotient-ring action. The duality assertions concern this submodule itself.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite ModuleCat IsLocalRing

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {A : Type u} [CommRing A] (J : Ideal A) (I : ModuleCat.{u} A)

/-- The actual ideal annihilator, with its standard quotient-ring action. -/
abbrev quotientAnnihilatorModule : ModuleCat.{u} (A ⧸ J) :=
  ModuleCat.of (A ⧸ J) (Submodule.torsionBySet A I J)

/-- Evaluation at `1` takes quotient coinduction to the actual annihilator. -/
def quotientCoinductionToAnnihilator :
    (coextendScalars (Ideal.Quotient.mk J)).obj I ⟶ quotientAnnihilatorModule J I :=
  ModuleCat.ofHom
    { toFun g := ⟨g (1 : A ⧸ J), by
        apply (Submodule.mem_torsionBySet_iff _ _).mpr
        intro a
        have h := g.map_smul (a : A) (1 : A ⧸ J)
        change g (Ideal.Quotient.mk J a * 1) = a.val • g (1 : A ⧸ J) at h
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr a.property, zero_mul, map_zero] at h
        exact h.symm⟩
      map_add' _ _ := rfl
      map_smul' b g := by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
        apply Subtype.ext
        change g (1 * Ideal.Quotient.mk J a) = a • g (1 : A ⧸ J)
        have h := g.map_smul a (1 : A ⧸ J)
        change g (Ideal.Quotient.mk J a * 1) = a • g (1 : A ⧸ J) at h
        simpa only [one_mul, mul_one] using h }

/-- The evaluation map is bijective: an annihilated element `x` gives the
actual quotient-linear map `a mod J ↦ a x`. -/
theorem quotientCoinductionToAnnihilator_bijective :
    Function.Bijective (quotientCoinductionToAnnihilator J I) := by
  constructor
  · intro g h he
    apply LinearMap.ext
    intro b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    have he' : g (1 : A ⧸ J) = h (1 : A ⧸ J) := congrArg Subtype.val he
    have hg := g.map_smul a (1 : A ⧸ J)
    have hh := h.map_smul a (1 : A ⧸ J)
    change g (Ideal.Quotient.mk J a * 1) = a • g (1 : A ⧸ J) at hg
    change h (Ideal.Quotient.mk J a * 1) = a • h (1 : A ⧸ J) at hh
    rw [he'] at hg
    simpa [CoextendScalars.equiv] using hg.trans hh.symm
  · intro x
    let l : A →ₗ[A] I := LinearMap.toSpanSingleton A I x.val
    have hl : J ≤ l.ker := by
      intro a ha
      exact (Submodule.mem_torsionBySet_iff _ _).mp x.property ⟨a, ha⟩
    let g : (coextendScalars (Ideal.Quotient.mk J)).obj I :=
      { toFun := J.liftQ l hl
        map_add' := (J.liftQ l hl).map_add
        map_smul' a b := by
          change J.liftQ l hl (Ideal.Quotient.mk J a * (show A ⧸ J from b)) =
            a • J.liftQ l hl b
          simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
            using (J.liftQ l hl).map_smul a b }
    refine ⟨g, ?_⟩
    apply Subtype.ext
    change J.liftQ l hl (Ideal.Quotient.mk J 1) = x.val
    change (1 : A) • x.val = x.val
    exact one_smul _ _

/-- The original quotient coinduction is canonically the actual ideal annihilator. -/
def quotientCoinductionAnnihilatorIso :
    (coextendScalars (Ideal.Quotient.mk J)).obj I ≅ quotientAnnihilatorModule J I := by
  have : Mono (quotientCoinductionToAnnihilator J I) :=
    (ModuleCat.mono_iff_injective _).mpr (quotientCoinductionToAnnihilator_bijective J I).1
  have : Epi (quotientCoinductionToAnnihilator J I) :=
    (ModuleCat.epi_iff_surjective _).mpr (quotientCoinductionToAnnihilator_bijective J I).2
  have := isIso_of_mono_of_epi (quotientCoinductionToAnnihilator J I)
  exact asIso (quotientCoinductionToAnnihilator J I)

/-- The actual ideal-annihilator inclusion is evaluation at `1`. -/
@[simp]
theorem quotientCoinductionAnnihilatorIso_hom_val
    (g : (coextendScalars (Ideal.Quotient.mk J)).obj I) :
    ((quotientCoinductionAnnihilatorIso J I).hom g).val = g (1 : A ⧸ J) := rfl

/-- The annihilator is genuinely injective as a quotient module. -/
theorem quotientAnnihilator_injective [Injective I] :
    Injective (quotientAnnihilatorModule J I) := by
  have := coinduced_injective (Ideal.Quotient.mk J) I
  exact Injective.of_iso (quotientCoinductionAnnihilatorIso J I) inferInstance

variable [IsNoetherianRing A] [IsLocalRing A] [IsLocalRing (A ⧸ J)]

/-- The actual annihilator satisfies the original residue-field test. -/
theorem quotientAnnihilator_residueTests [Injective I]
    (hbid : SupportedModuleBiduality (maximalIdeal A) I) :
    moduleHomDualResidueTests (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) := by
  have h := finite_local_coinduction_residueTests (B := A ⧸ J) I hbid
  intro m hm hle
  obtain ⟨e⟩ := h m hm hle
  exact ⟨(((linearYoneda (A ⧸ J) (ModuleCat (A ⧸ J))).mapIso
    (quotientCoinductionAnnihilatorIso J I)).app
      (op (ModuleCat.of (A ⧸ J) ((A ⧸ J) ⧸ m)))).symm ≪≫ e⟩

/-- **IV.4.4:** the actual annihilator has finite Hom values and canonical
biduality over the quotient local ring. -/
theorem quotientAnnihilator_duality [Injective I]
    (hbid : SupportedModuleBiduality (maximalIdeal A) I) :
    FiniteSupportedHomValues (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) ∧
      SupportedModuleBiduality (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) := by
  have := quotientAnnihilator_injective J I
  let : Field ((A ⧸ J) ⧸ maximalIdeal (A ⧸ J)) := Ideal.Quotient.field _
  have hres := quotientAnnihilator_residueTests J I hbid
  constructor
  · intro M hM hSupp
    exact moduleHomDual_finite_of_artinian_support _ _ hres M hSupp
  · intro M hM hSupp
    exact moduleBidualEvaluation_isIso_of_artinian_support _ _ hres M hSupp

/-- The actual quotient annihilator remains supported at the closed point. -/
theorem quotientAnnihilator_supported
    (hI : supportedModuleProperty (maximalIdeal A) I) :
    supportedModuleProperty (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) := by
  let e := quotientCoinductionAnnihilatorIso J I
  exact (Module.support_subset_of_surjective e.hom.hom
    ((ModuleCat.epi_iff_surjective e.hom).mp inferInstance)).trans
      (finite_local_coinduction_supported (B := A ⧸ J) I hI)

/-- **IV.4.4**, in all three original supported-dualizing conditions.
Injectivity is deduced from the original hypotheses, not additionally assumed. -/
theorem quotientAnnihilator_supported_duality
    (hI : supportedModuleProperty (maximalIdeal A) I)
    (hfin : FiniteSupportedHomValues (maximalIdeal A) I)
    (hbid : SupportedModuleBiduality (maximalIdeal A) I) :
    supportedModuleProperty (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) ∧
      FiniteSupportedHomValues (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) ∧
      SupportedModuleBiduality (maximalIdeal (A ⧸ J)) (quotientAnnihilatorModule J I) := by
  have := injective_of_supported_bidually_reflexive (maximalIdeal A) I hI hfin hbid
  exact ⟨quotientAnnihilator_supported J I hI, quotientAnnihilator_duality J I hbid⟩

end SGA.SGA2.ExposeIV
