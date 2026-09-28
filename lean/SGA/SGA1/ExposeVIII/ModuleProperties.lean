/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import SGA.SGA1.ExposeVIII.ModuleDescent

/-!
# SGA 1, Exposé VIII, VIII.1.10–1.12: descent of properties of modules (affine case)

Corollary VIII.1.11: for a faithfully flat `A`-algebra `B`, an `A`-module `M` is of finite type
(resp. of finite presentation, resp. locally free of finite type) if and only if
`B ⊗_A M` is so over `B`. Mathlib has the descent of finite type and of flatness; we add
finite presentation and deduce "locally free of finite type", which for modules means
finitely generated projective, i.e. finitely presented and flat. Remark VIII.1.12 then
follows: the descended module of VIII.1.6 inherits these properties, and the same holds
for "locally free of rank `n`" (constant rank `n` at all stalks).

Proposition VIII.1.10 is the global form over preschemes, reduced in SGA to VIII.1.11; it is
proved in `QuasiCoherentDescent` (`isFiniteType_pullback_iff_of_flat`,
`isFinitePresentation_pullback_iff_of_flat`,
`isLocallyFree_and_isFiniteType_pullback_iff_of_flat`).
-/

universe u v w

open TensorProduct

namespace SGA.SGA1.ExposeVIII

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type w} [AddCommGroup M] [Module A M]

variable (A B M) in
/-- VIII.1.11, finite type (mathlib's `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`
for the converse). -/
theorem moduleFinite_baseChange_iff [Module.FaithfullyFlat A B] :
    Module.Finite B (B ⊗[A] M) ↔ Module.Finite A M :=
  ⟨fun _ ↦ .of_finite_tensorProduct_of_faithfullyFlat B, fun _ ↦ inferInstance⟩

variable (A B M) in
/-- VIII.1.11, flatness (mathlib's `Module.Flat.iff_flat_tensorProduct`). -/
theorem moduleFlat_baseChange_iff [Module.FaithfullyFlat A B] :
    Module.Flat B (B ⊗[A] M) ↔ Module.Flat A M :=
  Module.Flat.iff_flat_tensorProduct A M B

/-- VIII.1.11, finite presentation, the implication "it is sufficient": if `B ⊗_A M` is of
finite presentation over the faithfully flat `A`-algebra `B`, so is `M`. -/
theorem moduleFinitePresentation_of_baseChange
    [Module.FaithfullyFlat A B] [Module.FinitePresentation B (B ⊗[A] M)] :
    Module.FinitePresentation A M := by
  have : Module.Finite A M := .of_finite_tensorProduct_of_faithfullyFlat B
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A M
  rw [← Module.FinitePresentation.fg_ker_iff π hπ, ← Module.Finite.iff_fg]
  have hπB : Function.Surjective (TensorProduct.AlgebraTensorModule.lTensor B B π) :=
    LinearMap.lTensor_surjective B hπ
  have : Module.Finite B (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor B B π)) :=
    .of_fg (Module.FinitePresentation.fg_ker _ hπB)
  have : Module.Finite B (B ⊗[A] LinearMap.ker π) :=
    .equiv (LinearMap.tensorKerEquiv B B π).symm
  exact .of_finite_tensorProduct_of_faithfullyFlat B

variable (A B M) in
/-- VIII.1.11, finite presentation. -/
theorem moduleFinitePresentation_baseChange_iff [Module.FaithfullyFlat A B] :
    Module.FinitePresentation B (B ⊗[A] M) ↔ Module.FinitePresentation A M :=
  ⟨fun _ ↦ moduleFinitePresentation_of_baseChange
    (B := B), fun _ ↦ inferInstance⟩

/-- A module is locally free of finite type (finitely generated projective) iff it is of finite
presentation and flat; SGA leaves the non-noetherian case of this to the reader. -/
theorem projective_and_finite_iff_finitePresentation_and_flat {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] :
    Module.Projective R P ∧ Module.Finite R P ↔
      Module.FinitePresentation R P ∧ Module.Flat R P := by
  constructor
  · rintro ⟨_, _⟩
    exact ⟨Module.finitePresentation_of_projective R P, inferInstance⟩
  · rintro ⟨_, _⟩
    exact ⟨Module.Flat.projective_of_finitePresentation, inferInstance⟩

variable (A B M) in
/-- VIII.1.11, locally free of finite type: `M` is finitely generated projective over `A`
iff `B ⊗_A M` is finitely generated projective over `B`. -/
theorem moduleProjective_and_finite_baseChange_iff [Module.FaithfullyFlat A B] :
    Module.Projective B (B ⊗[A] M) ∧ Module.Finite B (B ⊗[A] M) ↔
      Module.Projective A M ∧ Module.Finite A M := by
  rw [projective_and_finite_iff_finitePresentation_and_flat,
    projective_and_finite_iff_finitePresentation_and_flat, moduleFinitePresentation_baseChange_iff,
    moduleFlat_baseChange_iff]

variable (A B M) in
/-- VIII.1.12, constant rank: for faithfully flat `A → B` and `M` finite and flat, `M` has
rank `n` at every stalk iff `B ⊗_A M` does. Together with
`moduleProjective_and_finite_baseChange_iff` this is the descent of "locally free of rank `n`". -/
theorem rankAtStalk_baseChange_eq_iff [Module.FaithfullyFlat A B] [Module.Flat A M]
    [Module.Finite A M] (n : ℕ) :
    (∀ q : PrimeSpectrum B, Module.rankAtStalk (B ⊗[A] M) q = n) ↔
      ∀ p : PrimeSpectrum A, Module.rankAtStalk M p = n := by
  simp only [Module.rankAtStalk_baseChange]
  refine ⟨fun h p ↦ ?_, fun h q ↦ h _⟩
  obtain ⟨q, rfl⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := B) p
  exact h q

namespace ModuleDescentDatum

variable {N : Type w} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
  (D : ModuleDescentDatum A B N)

/-- VIII.1.12, finite type: the descended module of a descent datum on a finite `B`-module
is finite. -/
theorem finite_invariants [Module.FaithfullyFlat A B] [Module.Finite B N] :
    Module.Finite A D.invariants := by
  have : Module.Finite B (B ⊗[A] D.invariants) := .equiv D.descentEquiv.symm
  exact .of_finite_tensorProduct_of_faithfullyFlat B

/-- VIII.1.12, finite presentation. -/
theorem finitePresentation_invariants [Module.FaithfullyFlat A B]
    [Module.FinitePresentation B N] : Module.FinitePresentation A D.invariants := by
  have : Module.FinitePresentation B (B ⊗[A] D.invariants) := .of_equiv D.descentEquiv.symm
  exact moduleFinitePresentation_of_baseChange (B := B)

/-- VIII.1.12, locally free of finite type. -/
theorem projective_invariants [Module.FaithfullyFlat A B] [Module.Projective B N]
    [Module.Finite B N] : Module.Projective A D.invariants := by
  have : Module.Projective B (B ⊗[A] D.invariants) := .of_equiv D.descentEquiv.symm
  have : Module.Finite B (B ⊗[A] D.invariants) := .equiv D.descentEquiv.symm
  exact ((moduleProjective_and_finite_baseChange_iff A B D.invariants).mp ⟨‹_›, ‹_›⟩).1

/-- VIII.1.12, locally free of rank `n`: if `N` is finitely generated projective of rank `n` at
every point of `Spec B`, the descended module has rank `n` at every point of `Spec A`. -/
theorem rankAtStalk_invariants [Module.FaithfullyFlat A B] [Module.Projective B N]
    [Module.Finite B N] (n : ℕ) (hN : ∀ q : PrimeSpectrum B, Module.rankAtStalk N q = n)
    (p : PrimeSpectrum A) : Module.rankAtStalk D.invariants p = n := by
  have := D.finite_invariants
  have := D.projective_invariants
  refine (rankAtStalk_baseChange_eq_iff A B D.invariants n).mp (fun q ↦ ?_) p
  rw [Module.rankAtStalk_eq_of_equiv (D.descentEquiv.restrictScalars B), hN]

end ModuleDescentDatum

end SGA.SGA1.ExposeVIII
