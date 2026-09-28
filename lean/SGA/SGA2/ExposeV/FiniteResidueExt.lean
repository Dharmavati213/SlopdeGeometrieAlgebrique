/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ModuleExtFinite
import SGA.SGA2.ExposeIV.EssentialSocles
import SGA.SGA2.ExposeII.ExtCoefficientSequence

/-!
# Finite residue Ext through actual injective envelopes

Finiteness of all original `Extⁱ(k,M)` is preserved by passing to an actual
injective envelope and its actual categorical cokernel. Degree zero is the
original socle, which an essential embedding preserves; higher Ext vanishes
on the injective envelope. The quotient assertion uses the genuine original
coefficient exact sequence.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite IsLocalRing
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- All original residue-field Ext modules are finitely generated. -/
def FiniteResidueExt (M : ModuleCat.{u} R) : Prop :=
  ∀ i : ℕ, Module.Finite R (moduleExtValue (ModuleCat.of R (R ⧸ maximalIdeal R)) M i)

/-- Original degree-zero residue Ext is the actual maximal-ideal socle. -/
def residueExtZeroIsoSocle (M : ModuleCat.{u} R) :
    moduleExtValue (ModuleCat.of R (R ⧸ maximalIdeal R)) M 0 ≅
      ModuleCat.of R (localSocle (R := R) M) :=
  (extZeroIsoHom M).app (op (ModuleCat.of R (R ⧸ maximalIdeal R))) ≪≫
    quotientHomAnnihilatorIso (maximalIdeal R) M

/-- Finite residue Ext implies finite actual socle. -/
theorem FiniteResidueExt.socle_finite {M : ModuleCat.{u} R} (hM : FiniteResidueExt M) :
    Module.Finite R (localSocle (R := R) M) := by
  have := hM 0
  exact Module.Finite.equiv (residueExtZeroIsoSocle M).toLinearEquiv

/-- The genuine injective envelope preserves finiteness of all residue Ext,
without finite generation of the original module. -/
theorem FiniteResidueExt.injectiveEnvelope {M : ModuleCat.{u} R}
    (hM : FiniteResidueExt M) (E : ModuleInjectiveEnvelope M) : FiniteResidueExt E.obj := by
  have := hM.socle_finite
  have := E.essential.localSocle_finite
  intro i
  cases i with
  | zero => exact Module.Finite.equiv (residueExtZeroIsoSocle E.obj).symm.toLinearEquiv
  | succ i =>
    have := ModuleCat.subsingleton_of_isZero
      (isZero_Ext_succ_of_injective (ModuleCat.of R (R ⧸ maximalIdeal R)) E.obj i)
    infer_instance

variable [IsNoetherianRing R]

/-- Finite original residue Ext is inherited by the last term of an actual
short exact sequence when it holds for the first two terms. -/
theorem finiteResidueExt_of_shortExact (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (h₁ : FiniteResidueExt S.X₁) (h₂ : FiniteResidueExt S.X₂) :
    FiniteResidueExt S.X₃ := by
  intro i
  have := h₂ i
  have := h₁ (i + 1)
  let k := ModuleCat.of R (R ⧸ maximalIdeal R)
  have : IsNoetherian R (moduleExtValue k S.X₃ i) :=
    isNoetherian_of_range_eq_ker
      (((_root_.Ext R (ModuleCat.{u} R) i).obj (op k)).map S.g).hom
      (extCoefficientδ k S hS i).hom
      (extCoefficient_exact₃ k S hS i).moduleCat_range_eq_ker
  infer_instance

/-- The actual cokernel of an injective-envelope embedding retains all
residue Ext finiteness needed for successive dimension shifting. -/
theorem FiniteResidueExt.cokernel_injectiveEnvelope {M : ModuleCat.{u} R}
    (hM : FiniteResidueExt M) (E : ModuleInjectiveEnvelope M) :
    FiniteResidueExt (cokernel E.ι) := by
  have : Mono E.ι := E.essential.mono
  exact finiteResidueExt_of_shortExact (ShortComplex.mk _ _ (cokernel.condition E.ι))
    { exact := ShortComplex.exact_cokernel E.ι } hM (hM.injectiveEnvelope E)

/-- Finite modules have finite original residue Ext in every degree. -/
theorem finiteResidueExt_of_finite (M : ModuleCat.{u} R) [Module.Finite R M] :
    FiniteResidueExt M := fun _ => inferInstance

end SGA.SGA2.ExposeV
