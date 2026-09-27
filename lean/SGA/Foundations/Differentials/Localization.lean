/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Derivations of a localization

Let `B` be a localization of an `R`-algebra `A` and `N` a `B`-module. Every `R`-derivation
`A → N` extends uniquely to an `R`-derivation `B → N` (the quotient rule). We deduce this from
`Ω[B⁄R] ≅ B ⊗_A Ω[A⁄R]` (`KaehlerDifferential.isBaseChange_of_formallyEtale`).

## Main results

* `Derivation.ext_of_isLocalization`: two derivations of `B` agreeing on `A` are equal.
* `Derivation.extendOfIsLocalization`: the extension of a derivation of `A` to `B`.
* `Derivation.equivOfIsLocalization`: `Der_R(B, N) ≃ Der_R(A, N)`.
-/

universe u

namespace Derivation

variable {R A B N : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra A B] [Algebra R B]
  [AddCommGroup N] [Module B N] [Module R N] (S : Submonoid A) [IsLocalization S B]

include S in
/-- A derivation of a localization `B` of `A` is determined by its restriction to `A`. -/
theorem ext_of_isLocalization {D₁ D₂ : Derivation R B N}
    (h : ∀ a : A, D₁ (algebraMap A B a) = D₂ (algebraMap A B a)) : D₁ = D₂ := by
  ext b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  have hs : IsUnit (algebraMap A B s) := IsLocalization.map_units B s
  have key (D : Derivation R B N) : algebraMap A B s • D (IsLocalization.mk' B a s) =
      D (algebraMap A B a) - IsLocalization.mk' B a s • D (algebraMap A B s) := by
    rw [eq_sub_iff_add_eq, ← Derivation.leibniz, mul_comm, IsLocalization.mk'_spec]
  have h₁ := key D₁
  rw [h, h, ← key D₂] at h₁
  exact (hs.smul_left_cancel).mp h₁

variable [Algebra R A] [IsScalarTower R A B] [Module A N] [IsScalarTower A B N]
  [IsScalarTower R B N] [IsScalarTower R A N]

/-- The extension of a derivation of `A` to its localization `B` (the quotient rule). -/
noncomputable def extendOfIsLocalization (D : Derivation R A N) : Derivation R B N :=
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  ((KaehlerDifferential.isBaseChange_of_formallyEtale R A B).lift
    D.liftKaehlerDifferential).compDer (KaehlerDifferential.D R B)

@[simp]
theorem extendOfIsLocalization_algebraMap (D : Derivation R A N) (a : A) :
    D.extendOfIsLocalization S (algebraMap A B a) = D a := by
  have : Algebra.FormallyEtale A B := Algebra.FormallyEtale.of_isLocalization S
  change (KaehlerDifferential.isBaseChange_of_formallyEtale R A B).lift
    D.liftKaehlerDifferential (KaehlerDifferential.D R B (algebraMap A B a)) = D a
  rw [← KaehlerDifferential.map_D R R A B a, IsBaseChange.lift_eq,
    Derivation.liftKaehlerDifferential_comp_D]

/-- `Der_R(B, N) ≃ Der_R(A, N)` for a localization `B` of `A`: derivations extend uniquely along
localizations. -/
@[simps apply]
noncomputable def equivOfIsLocalization : Derivation R B N ≃ Derivation R A N where
  toFun D := D.compAlgebraMap A
  invFun D := D.extendOfIsLocalization S
  left_inv D := ext_of_isLocalization S fun a ↦ by simp
  right_inv D := by ext a; simp

end Derivation

/-- A variant of `Derivation.ext_of_isLocalization` for additive maps satisfying the Leibniz rule
with respect to a ring homomorphism `ψ : B →+* C` into the ring `C` acting on `N`: two such maps
on a localization `B` of `A` which agree on `A` are equal. -/
theorem AddMonoidHom.eq_of_leibniz_of_isLocalization {A B C N : Type*} [CommRing A] [CommRing B]
    [CommRing C] [Algebra A B] (S : Submonoid A) [IsLocalization S B] [AddCommGroup N]
    [Module C N] (ψ : B →+* C) {d₁ d₂ : B →+ N}
    (h₁ : ∀ x y, d₁ (x * y) = ψ x • d₁ y + ψ y • d₁ x)
    (h₂ : ∀ x y, d₂ (x * y) = ψ x • d₂ y + ψ y • d₂ x)
    (h : ∀ a : A, d₁ (algebraMap A B a) = d₂ (algebraMap A B a)) : d₁ = d₂ := by
  ext b
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective S b
  have hs : IsUnit (ψ (algebraMap A B s)) := (IsLocalization.map_units B s).map ψ
  have key (d : B →+ N) (hd : ∀ x y, d (x * y) = ψ x • d y + ψ y • d x) :
      ψ (algebraMap A B s) • d (IsLocalization.mk' B a s) =
        d (algebraMap A B a) - ψ (IsLocalization.mk' B a s) • d (algebraMap A B s) := by
    rw [eq_sub_iff_add_eq, ← hd, mul_comm, IsLocalization.mk'_spec]
  have e := key d₁ h₁
  rw [h, h, ← key d₂ h₂] at e
  exact (hs.smul_left_cancel).mp e
