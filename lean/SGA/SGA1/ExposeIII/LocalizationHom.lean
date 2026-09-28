/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Localization of modules of homomorphisms and of derivations

Auxiliary algebra for SGA 1 III.5: for a finitely presented module `M`, `Hom(M, -)` commutes
with localization (`isLocalizedModule_compRight`); hence for a finitely presented algebra `A`, so
does `Der(A, -)` (`isLocalizedModule_compDer`). This is what makes the sheaf
`ℋom(g₀^* Ω_{X/Y}, 𝒥)` of SGA 1 III.5.2 quasi-coherent.

We also record that an additive map on a localization `A_s` satisfying the Leibniz rule into a
square-zero ideal and vanishing on `A` is zero (`eq_zero_of_isLocalization_away`), which is the
uniqueness of the extension of derivations along a localization.
-/

open LinearMap

section Hom

variable {R M N N' : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [AddCommGroup N'] [Module R N'] (S : Submonoid R) (g : N →ₗ[R] N')
  [IsLocalizedModule S g]

/-- `Hom(M, -)` commutes with localization when `M` is finitely presented. -/
theorem isLocalizedModule_compRight [Module.FinitePresentation R M] :
    IsLocalizedModule S (LinearMap.compRight R g : (M →ₗ[R] N) →ₗ[R] M →ₗ[R] N') where
  map_units s := by
    rw [Module.End.isUnit_iff]
    have hs := (Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units (S := S) (f := g) s)
    constructor
    · exact fun _ _ e ↦ LinearMap.ext fun m ↦ hs.1 (LinearMap.congr_fun e m)
    · intro h
      refine ⟨((IsLocalizedModule.map_units (S := S) (f := g) s).unit⁻¹).1 ∘ₗ h, ?_⟩
      ext x
      exact Module.End.isUnit_apply_inv_apply_of_isUnit
        (IsLocalizedModule.map_units (S := S) (f := g) s) (h x)
  surj h := by
    obtain ⟨h', s, e⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule S g h
    exact ⟨⟨h', s⟩, e.symm⟩
  exists_of_eq {h₁ h₂} e :=
    Module.Finite.exists_smul_of_comp_eq_of_isLocalizedModule S g h₁ h₂ e

end Hom

section Derivation

variable {R A M M' : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M]
  [AddCommGroup M'] [Module A M'] [Module R M'] [IsScalarTower R A M']

/-- `Der_R(A, -)` commutes with localization when `A` is a finitely presented `R`-algebra. -/
theorem isLocalizedModule_compDer [Algebra.FinitePresentation R A] (S : Submonoid A)
    (l : M →ₗ[A] M') [IsLocalizedModule S l] :
    IsLocalizedModule S (l.compDer : Derivation R A M →ₗ[A] Derivation R A M') := by
  let K := KaehlerDifferential.linearMapEquivDerivation R A (M := M)
  let K' := KaehlerDifferential.linearMapEquivDerivation R A (M := M')
  have : IsLocalizedModule S
      (LinearMap.compRight A l : (Ω[A⁄R] →ₗ[A] M) →ₗ[A] Ω[A⁄R] →ₗ[A] M') :=
    isLocalizedModule_compRight S l
  have e : (l.compDer : Derivation R A M →ₗ[A] Derivation R A M') =
      (K'.toLinearMap ∘ₗ LinearMap.compRight A l) ∘ₗ K.symm.toLinearMap := by
    ext D a
    obtain ⟨φ, rfl⟩ := K.surjective D
    simp [K, K']
  rw [e]
  infer_instance

end Derivation

section Leibniz

variable {A A' B C : Type*} [CommRing A] [CommRing A'] [CommRing B] [CommRing C]

/-- Let `A → A'` be a localization away from `s`, `ρ : B → C` surjective with square-zero kernel,
and `γ : A' → C`. An additive map `d : A' → ker ρ` satisfying the Leibniz rule with respect to
lifts of `γ` and vanishing on the image of `A` is zero. -/
theorem eq_zero_of_isLocalization_away (φ : A →+* A') (s : A) (hs : IsUnit (φ s))
    (hloc : ∀ y : A', ∃ (a : A) (n : ℕ), y * φ s ^ n = φ a)
    (ρ : B →+* C) (hρ : Function.Surjective ρ) (γ : A' →+* C)
    (hsq : ∀ x y, ρ x = 0 → ρ y = 0 → x * y = 0)
    (d : A' → B) (hmem : ∀ y, ρ (d y) = 0)
    (hleib : ∀ a b a' b', ρ a' = γ a → ρ b' = γ b → d (a * b) = a' * d b + b' * d a)
    (hzero : ∀ a, d (φ a) = 0) (y : A') : d y = 0 := by
  obtain ⟨a, n, ha⟩ := hloc y
  obtain ⟨σ, hσ⟩ := hρ (γ (φ s ^ n))
  obtain ⟨τ, hτ⟩ := hρ (γ (hs.unit⁻¹ ^ n : A'ˣ).1)
  obtain ⟨y', hy'⟩ := hρ (γ y)
  have h₁ : σ * d y = 0 := by
    have := hleib (φ s ^ n) y σ y' hσ hy'
    rw [mul_comm, ha, hzero, ← map_pow, hzero, mul_zero, add_zero] at this
    exact this.symm
  have h₂ : ρ (τ * σ - 1) = 0 := by
    rw [map_sub, map_mul, hτ, hσ, map_one, ← map_mul, Units.val_pow_eq_pow_val, ← mul_pow,
      IsUnit.val_inv_mul, one_pow, map_one, sub_self]
  have h₃ := hsq _ _ h₂ (hmem y)
  rw [sub_mul, one_mul, mul_assoc, h₁, mul_zero, zero_sub, neg_eq_zero] at h₃
  exact h₃

end Leibniz

section Kernel

variable {R B B' C C' : Type*} [CommRing R] [CommRing B] [CommRing B'] [CommRing C] [CommRing C']
  [Algebra R B] [Algebra R B'] [Algebra B B'] [IsScalarTower R B B'] [Algebra C C']

/-- Kernels commute with localization: if `B → B'` and `C → C'` are the localizations away from
`r ∈ R` and `ρ(r)`, compatible with `ρ : B → C` and `ρ' : B' → C'`, then `ker ρ → ker ρ'` is the
localization of `R`-modules away from `r`. -/
theorem isLocalizedModule_ker (ρ : B →+* C) (ρ' : B' →+* C')
    (hcomm : ∀ x, ρ' (algebraMap B B' x) = algebraMap C C' (ρ x)) (r : R)
    [IsLocalization.Away (algebraMap R B r) B'] [IsLocalization.Away (ρ (algebraMap R B r)) C']
    (L : RingHom.ker ρ →ₗ[R] RingHom.ker ρ')
    (hL : ∀ m, (L m : B') = algebraMap B B' m) :
    IsLocalizedModule (Submonoid.powers r) L where
  map_units s := by
    obtain ⟨_, n, rfl⟩ := s
    have hu : IsUnit (algebraMap R B' (r ^ n)) := by
      rw [IsScalarTower.algebraMap_apply R B B', map_pow, map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit (S := B') (algebraMap R B r)).pow n
    rw [Module.End.isUnit_iff]
    refine ⟨fun m₁ m₂ e ↦ Subtype.ext ?_, fun m ↦ ?_⟩
    · have e' := congrArg Subtype.val e
      simp only [Module.algebraMap_end_apply, Submodule.coe_smul_of_tower, Algebra.smul_def] at e'
      exact hu.mul_left_cancel e'
    · refine ⟨⟨hu.unit⁻¹.1 * m, Ideal.mul_mem_left _ _ m.2⟩, Subtype.ext ?_⟩
      simp only [Module.algebraMap_end_apply, Submodule.coe_smul_of_tower, Algebra.smul_def]
      rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
  surj m := by
    obtain ⟨⟨y, _, k, rfl⟩, hy⟩ := IsLocalization.surj
      (Submonoid.powers (algebraMap R B r)) (m : B')
    have h₀ : algebraMap C C' (ρ y) = 0 := by
      rw [← hcomm, ← hy, map_mul, (RingHom.mem_ker.mp m.2), zero_mul]
    obtain ⟨⟨_, l, rfl⟩, hl⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (ρ (algebraMap R B r))) C' (ρ y)).mp h₀
    have hmem : algebraMap R B r ^ l * y ∈ RingHom.ker ρ := by
      rw [RingHom.mem_ker, map_mul, map_pow]
      exact hl
    refine ⟨⟨⟨_, hmem⟩, ⟨r ^ (k + l), k + l, rfl⟩⟩, Subtype.ext ?_⟩
    simp only [Submonoid.smul_def, Submodule.coe_smul_of_tower, Algebra.smul_def, hL]
    rw [IsScalarTower.algebraMap_apply R B B', map_pow, map_pow, map_mul, pow_add, map_pow,
      ← hy, map_pow]
    ring
  exists_of_eq {m₁ m₂} e := by
    have e' : algebraMap B B' m₁ = algebraMap B B' m₂ := by
      rw [← hL, ← hL, e]
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exists_of_eq
      (M := Submonoid.powers (algebraMap R B r)) e'
    refine ⟨⟨r ^ n, n, rfl⟩, Subtype.ext ?_⟩
    simp only [Submonoid.smul_def, Submodule.coe_smul_of_tower, Algebra.smul_def, map_pow]
    exact hn

end Kernel
