/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleBidual
import SGA.SGA2.ExposeIV.SupportedFiniteModules

/-!
# Finite-length induction for genuine Hom duality

Canonical reflexivity and finiteness of the actual Hom values extend from
simple modules to finite-length modules, using actual short exact sequences.
The supported versions require simple tests only in the original closed set.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The actual submodule and quotient sequence used in finite-length induction. -/
private def submoduleSequence (M : Type u) [AddCommGroup M] [Module R M] (N : Submodule R M) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext x; simp)

private theorem submoduleSequence_shortExact (M : Type u) [AddCommGroup M] [Module R M]
    (N : Submodule R M) : (submoduleSequence M N).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    (N.range_subtype.trans N.ker_mkQ.symm)
  mono_f := (ModuleCat.mono_iff_injective _).mpr N.injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective

/-- Finite-length induction stated on original bundled modules, with genuine
short exact extensions rather than assumed presentations or decompositions. -/
theorem moduleFiniteLength_induction (P : ObjectProperty (ModuleCat.{u} R))
    (hzero : ∀ M : ModuleCat.{u} R, IsZero M → P M)
    (hsimple : ∀ M : ModuleCat.{u} R, IsSimpleModule R M → P M)
    (hext : ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → P S.X₁ → P S.X₃ → P S.X₂)
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) : P M := by
  suffices h : ∀ (N : Type u) [AddCommGroup N] [Module R N],
      IsFiniteLength R N → P (ModuleCat.of R N) from h M hM
  intro N _ _ hN
  induction hN with
  | of_subsingleton => exact hzero _ (ModuleCat.isZero_of_subsingleton _)
  | @of_simple_quotient N _ _ L _ _ ih =>
    exact hext (submoduleSequence N L) (submoduleSequence_shortExact N L) ih
      (hsimple (ModuleCat.of R (N ⧸ L)) inferInstance)

/-- The same induction restricted to a Serre property such as actual support
in `V(J)`. Only simple modules satisfying that property need be tested. -/
theorem moduleFiniteLength_induction_of_serre
    (P Q : ObjectProperty (ModuleCat.{u} R)) [P.IsSerreClass]
    (hzero : ∀ M : ModuleCat.{u} R, IsZero M → Q M)
    (hsimple : ∀ M : ModuleCat.{u} R, IsSimpleModule R M → P M → Q M)
    (hext : ∀ S : ShortComplex (ModuleCat.{u} R), S.ShortExact → Q S.X₁ → Q S.X₃ → Q S.X₂)
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) (hP : P M) : Q M := by
  apply moduleFiniteLength_induction (fun N ↦ P N → Q N)
    (fun N hN _ ↦ hzero N hN) hsimple ?_ M hM hP
  intro S hS h₁ h₃ h₂
  have := hS.mono_f
  have := hS.epi_g
  exact hext S hS (h₁ (P.prop_of_mono S.f h₂)) (h₃ (P.prop_of_epi S.g h₂))

/-- Canonical bidual evaluation is an isomorphism for every finite-length
module if it is so on simple modules and `H` is injective. -/
theorem moduleBidualEvaluation_isIso_of_finiteLength (H : ModuleCat.{u} R) [Injective H]
    (hsimple : ∀ S : ModuleCat.{u} R, IsSimpleModule R S → IsIso (moduleBidualEvaluation H S))
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) : IsIso (moduleBidualEvaluation H M) := by
  apply moduleFiniteLength_induction (fun N ↦ IsIso (moduleBidualEvaluation H N))
    (fun N hN ↦ hN.isIso ((moduleHomBidual H).map_isZero hN) _) hsimple ?_ M hM
  intro S hS h₁ h₃
  have := h₁
  have := h₃
  exact moduleBidualEvaluation_isIso_of_shortExact H hS

/-- The supported finite-length form needed in IV.3.1: no simple-module
tests outside the original support are imposed. -/
theorem moduleBidualEvaluation_isIso_of_finiteLength_of_support
    (J : Ideal R) (H : ModuleCat.{u} R) [Injective H]
    (hsimple : ∀ S : ModuleCat.{u} R, IsSimpleModule R S →
      supportedModuleProperty J S → IsIso (moduleBidualEvaluation H S))
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) (hSupp : supportedModuleProperty J M) :
    IsIso (moduleBidualEvaluation H M) := by
  apply moduleFiniteLength_induction_of_serre (supportedModuleProperty J)
    (fun N ↦ IsIso (moduleBidualEvaluation H N))
    (fun N hN ↦ hN.isIso ((moduleHomBidual H).map_isZero hN) _) hsimple ?_ M hM hSupp
  intro S hS h₁ h₃
  have := h₁
  have := h₃
  exact moduleBidualEvaluation_isIso_of_shortExact H hS

/-- Finiteness of simple Hom tests implies finiteness of every finite-length
Hom value, without requiring `H` itself to be finite. -/
theorem moduleHomDual_finite_of_finiteLength (H : ModuleCat.{u} R) [Injective H]
    (hsimple : ∀ S : ModuleCat.{u} R, IsSimpleModule R S →
      Module.Finite R ((moduleHomDual H).obj (op S)))
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) :
    Module.Finite R ((moduleHomDual H).obj (op M)) := by
  apply moduleFiniteLength_induction (fun N ↦ Module.Finite R ((moduleHomDual H).obj (op N)))
    ?_ hsimple ?_ M hM
  · intro N hN
    have := ModuleCat.isZero_iff_subsingleton.mp ((moduleHomDual H).map_isZero hN.op)
    infer_instance
  · intro S hS h₁ h₃
    have := h₁
    have := h₃
    exact moduleHomDual_finite_of_shortExact H hS

/-- Finiteness propagates using only the simple tests supported on `V(J)`. -/
theorem moduleHomDual_finite_of_finiteLength_of_support (J : Ideal R)
    (H : ModuleCat.{u} R) [Injective H]
    (hsimple : ∀ S : ModuleCat.{u} R, IsSimpleModule R S → supportedModuleProperty J S →
      Module.Finite R ((moduleHomDual H).obj (op S)))
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) (hSupp : supportedModuleProperty J M) :
    Module.Finite R ((moduleHomDual H).obj (op M)) := by
  apply moduleFiniteLength_induction_of_serre (supportedModuleProperty J)
    (fun N ↦ Module.Finite R ((moduleHomDual H).obj (op N))) ?_ hsimple ?_ M hM hSupp
  · intro N hN
    have := ModuleCat.isZero_iff_subsingleton.mp ((moduleHomDual H).map_isZero hN.op)
    infer_instance
  · intro S hS h₁ h₃
    have := h₁
    have := h₃
    exact moduleHomDual_finite_of_shortExact H hS

end SGA.SGA2.ExposeIV
