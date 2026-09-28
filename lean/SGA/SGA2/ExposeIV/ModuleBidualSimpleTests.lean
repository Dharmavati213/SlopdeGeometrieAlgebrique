/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.ModuleBidualFiniteLength
import Mathlib.RingTheory.Length

/-!
# Residue-field tests for the actual Hom duality

If `Hom_R(S,H) ≅ S` for a simple module, the canonical bidual evaluation
is nonzero and hence an isomorphism by Schur's lemma. Simple supported
modules are actual residue-field modules at maximal ideals containing `J`.
These tests give canonical reflexivity, finite Hom values, and length
preservation on finite-length supported modules.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- A nonzero actual dual prevents canonical evaluation from being zero. -/
theorem moduleBidualEvaluation_ne_zero (H M : ModuleCat.{u} R)
    [Nontrivial ((moduleHomDual H).obj (op M))] : moduleBidualEvaluation H M ≠ 0 := by
  intro h
  obtain ⟨f, hf⟩ := exists_ne (0 : (moduleHomDual H).obj (op M))
  apply hf
  apply ModuleCat.hom_ext
  ext x
  have h' := ConcreteCategory.congr_hom h x
  exact congrArg (fun g : (moduleHomDual H).obj (op M) ⟶ H ↦ ModuleCat.Hom.hom g f) h'

/-- An abstract simple dual test forces the original canonical bidual
evaluation to be an isomorphism, not just the existence of some isomorphism. -/
theorem moduleBidualEvaluation_isIso_of_simple_dual_iso (H S : ModuleCat.{u} R)
    [IsSimpleModule R S] (e : (moduleHomDual H).obj (op S) ≅ S) :
    IsIso (moduleBidualEvaluation H S) := by
  have : IsSimpleModule R ((moduleHomDual H).obj (op S)) :=
    IsSimpleModule.congr e.toLinearEquiv
  have : Nontrivial ((moduleHomDual H).obj (op S)) := IsSimpleModule.nontrivial R _
  have : IsSimpleModule R ((moduleHomBidual H).obj S) :=
    IsSimpleModule.congr ((moduleHomDual H).mapIso e.op).symm.toLinearEquiv
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  apply LinearMap.bijective_of_ne_zero
  intro h
  exact moduleBidualEvaluation_ne_zero H S (ModuleCat.hom_ext h)

/-- Any supported simple module is identified with an actual residue
field at a maximal ideal containing the original support ideal. -/
theorem supportedSimple_exists_residue (J : Ideal R) (S : ModuleCat.{u} R)
    [IsSimpleModule R S] (hSupp : supportedModuleProperty J S) :
    ∃ m : Ideal R, m.IsMaximal ∧ J ≤ m ∧ Nonempty (S ≅ ModuleCat.of R (R ⧸ m)) := by
  obtain ⟨m, hm, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := S)).mp inferInstance
  have hJ : J ≤ m := by
    change Module.support R S ⊆ _ at hSupp
    rw [e.support_eq, Module.support_eq_zeroLocus, Ideal.annihilator_quotient,
      PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hSupp
    exact hSupp.trans hm.isPrime.isRadical
  exact ⟨m, hm, hJ, ⟨LinearEquiv.toModuleIso (X₁ := S) (X₂ := ModuleCat.of R (R ⧸ m)) e⟩⟩

/-- Transport the residue-field dual tests through the actual simple
module isomorphism and the original Hom functor. -/
def moduleHomDualSimpleIso_of_residueTests (J : Ideal R) (H : ModuleCat.{u} R)
    (hres : ∀ m : Ideal R, m.IsMaximal → J ≤ m →
      Nonempty ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m))) ≅
        ModuleCat.of R (R ⧸ m)))
    (S : ModuleCat.{u} R) [IsSimpleModule R S] (hSupp : supportedModuleProperty J S) :
    (moduleHomDual H).obj (op S) ≅ S := Classical.choice <| by
  obtain ⟨m, hm, hJ, ⟨e⟩⟩ := supportedSimple_exists_residue J S hSupp
  exact ⟨((moduleHomDual H).mapIso e.op).symm ≪≫ (hres m hm hJ).some ≪≫ e.symm⟩

/-- The residue-field tests imply canonical reflexivity on every simple
module inside the original support. -/
theorem moduleBidualEvaluation_isIso_simple_of_residueTests (J : Ideal R) (H : ModuleCat.{u} R)
    (hres : ∀ m : Ideal R, m.IsMaximal → J ≤ m →
      Nonempty ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m))) ≅
        ModuleCat.of R (R ⧸ m)))
    (S : ModuleCat.{u} R) [IsSimpleModule R S] (hSupp : supportedModuleProperty J S) :
    IsIso (moduleBidualEvaluation H S) :=
  moduleBidualEvaluation_isIso_of_simple_dual_iso H S
    (moduleHomDualSimpleIso_of_residueTests J H hres S hSupp)

/-- Exact duality preserves length through a short exact sequence once
it preserves length on the two ends. -/
theorem moduleHomDual_length_of_shortExact (H : ModuleCat.{u} R) [Injective H]
    {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (h₁ : Module.length R ((moduleHomDual H).obj (op S.X₁)) = Module.length R S.X₁)
    (h₃ : Module.length R ((moduleHomDual H).obj (op S.X₃)) = Module.length R S.X₃) :
    Module.length R ((moduleHomDual H).obj (op S.X₂)) = Module.length R S.X₂ := by
  have hD := moduleHomDual_shortExact H hS
  have hlen : Module.length R ((moduleHomDual H).obj (op S.X₂)) =
      Module.length R ((moduleHomDual H).obj (op S.X₃)) +
        Module.length R ((moduleHomDual H).obj (op S.X₁)) :=
    Module.length_eq_add_of_exact (S.op.map (moduleHomDual H)).f.hom
    (S.op.map (moduleHomDual H)).g.hom
    ((ModuleCat.mono_iff_injective _).mp hD.mono_f)
    ((ModuleCat.epi_iff_surjective _).mp hD.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hD.exact)
  rw [hlen, h₃, h₁]
  rw [Module.length_eq_add_of_exact S.f.hom S.g.hom
    ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
    ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact), add_comm]

variable (J : Ideal R) (H : ModuleCat.{u} R) [Injective H]
variable (hres : ∀ m : Ideal R, m.IsMaximal → J ≤ m →
  Nonempty ((moduleHomDual H).obj (op (ModuleCat.of R (R ⧸ m))) ≅ ModuleCat.of R (R ⧸ m)))

include hres

/-- The canonical finite-length supported bidual is invertible under the
actual residue-field tests of IV.3.1(iii). -/
theorem moduleBidualEvaluation_isIso_finiteLength_of_residueTests
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) (hSupp : supportedModuleProperty J M) :
    IsIso (moduleBidualEvaluation H M) := by
  apply moduleBidualEvaluation_isIso_of_finiteLength_of_support J H ?_ M hM hSupp
  intro S hS hSupp
  have := hS
  exact moduleBidualEvaluation_isIso_simple_of_residueTests J H hres S hSupp

/-- Hom values on finite-length supported modules are genuinely finite. -/
theorem moduleHomDual_finite_finiteLength_of_residueTests
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) (hSupp : supportedModuleProperty J M) :
    Module.Finite R ((moduleHomDual H).obj (op M)) := by
  apply moduleHomDual_finite_of_finiteLength_of_support J H ?_ M hM hSupp
  intro S hS hSupp
  have := hS
  exact Module.Finite.equiv
    (moduleHomDualSimpleIso_of_residueTests J H hres S hSupp).symm.toLinearEquiv

/-- Exact Hom duality preserves the original module length on supported
finite-length modules, by simple-module tests and extension induction. -/
theorem moduleHomDual_length_finiteLength_of_residueTests
    (M : ModuleCat.{u} R) (hM : IsFiniteLength R M) (hSupp : supportedModuleProperty J M) :
    Module.length R ((moduleHomDual H).obj (op M)) = Module.length R M := by
  apply moduleFiniteLength_induction_of_serre (supportedModuleProperty J)
    (fun N ↦ Module.length R ((moduleHomDual H).obj (op N)) = Module.length R N) ?_ ?_ ?_ M hM hSupp
  · intro N hN
    have := ModuleCat.isZero_iff_subsingleton.mp hN
    have := ModuleCat.isZero_iff_subsingleton.mp ((moduleHomDual H).map_isZero hN.op)
    simp [Module.length_eq_zero]
  · intro S hS hSupp
    have := hS
    exact (moduleHomDualSimpleIso_of_residueTests J H hres S hSupp).toLinearEquiv.length_eq
  · intro S hS h₁ h₃
    exact moduleHomDual_length_of_shortExact H hS h₁ h₃

end SGA.SGA2.ExposeIV
