/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!
# SGA 1, Exposé I, §6: étale extensions of complete local rings

Theorem I.6.1 says that finite étale algebras over a complete local ring `A`
are equivalent to finite separable algebras over the residue field. The fully
faithful half (I.6.2) is the infinitesimal lifting property:

* when `A` is artinian local the maximal ideal is nilpotent, so
  `FormallySmooth.lift` / `FormallyUnramified.ext` apply directly;
* when the *target* is adically complete for `m_A C`, the same bijection
  follows from `FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` and
  `FormallyUnramified.ext_of_iInf` (inverse-limit assembly).

Existence of a finite étale *algebra* lifting an arbitrary finite separable
residue algebra (Hensel essential surjectivity on objects) still needs a
global Henselian construction beyond mathlib’s root-lifting `HenselianRing`.
-/

universe u

namespace SGA.SGA1.ExposeI

open Algebra IsLocalRing

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

lemma isNilpotent_map_maximalIdeal [IsLocalRing A] [IsArtinianRing A]
    {C : Type u} [CommRing C] [Algebra A C] :
    IsNilpotent ((maximalIdeal A).map (algebraMap A C)) := by
  have hnil : IsNilpotent (maximalIdeal A) := by
    rw [← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, by simpa [Ideal.map_pow] using congr_arg (Ideal.map (algebraMap A C)) hn⟩

/-- I.6.2, uniqueness, in the artinian local case: maps out of a formally unramified
algebra are determined by their reductions modulo the maximal ideal. -/
theorem hom_eq_of_residue [FormallyUnramified A B] [IsLocalRing A] [IsArtinianRing A]
    {C : Type u} [CommRing C] [Algebra A C] (f g : B →ₐ[A] C)
    (h : ∀ x, Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A C)) (f x) =
      Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A C)) (g x)) : f = g :=
  FormallyUnramified.ext (I := (maximalIdeal A).map (algebraMap A C))
    isNilpotent_map_maximalIdeal h

/-- I.6.2, existence, in the artinian local case: a map into the special fibre of
`C` lifts uniquely through the nilpotent maximal ideal when the source is
formally étale. -/
noncomputable def liftResidue [FormallyEtale A B] [IsLocalRing A] [IsArtinianRing A]
    {C : Type u} [CommRing C] [Algebra A C]
    (φ : B →ₐ[A] C ⧸ (maximalIdeal A).map (algebraMap A C)) : B →ₐ[A] C :=
  FormallySmooth.lift _ isNilpotent_map_maximalIdeal φ

theorem liftResidue_comp [FormallyEtale A B] [IsLocalRing A] [IsArtinianRing A]
    {C : Type u} [CommRing C] [Algebra A C]
    (φ : B →ₐ[A] C ⧸ (maximalIdeal A).map (algebraMap A C)) :
    (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp (liftResidue φ) = φ :=
  FormallySmooth.comp_lift _ _ φ

/-- I.6.2, artinian local case: maps out of a formally étale algebra correspond
bijectively to maps into the special fibre. -/
theorem hom_equiv_residue [FormallyEtale A B] [IsLocalRing A] [IsArtinianRing A]
    {C : Type u} [CommRing C] [Algebra A C] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp f :=
  ⟨fun f g h ↦ hom_eq_of_residue f g fun x ↦ congr($(h) x),
    fun φ ↦ ⟨liftResidue φ, liftResidue_comp φ⟩⟩

/-- I.6.1, over a separably closed field: finite étale algebras are equivalent
to finite sets. -/
noncomputable def finiteEtaleEquivOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (CommAlgCat.FiniteEtale.{u} Ω)ᵒᵖ ≌ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed Ω

/-- I.6.1, fully faithful packaged for the artinian local case. -/
theorem finiteEtale_hom_equiv_residue_artinian [FormallyEtale A B] [IsLocalRing A]
    [IsArtinianRing A] {C : Type u} [CommRing C] [Algebra A C] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp f :=
  hom_equiv_residue

/-- I.6.1, existence half in the artinian local case. -/
theorem exists_liftResidue [FormallyEtale A B] [IsLocalRing A] [IsArtinianRing A]
    {C : Type u} [CommRing C] [Algebra A C]
    (φ : B →ₐ[A] C ⧸ (maximalIdeal A).map (algebraMap A C)) :
    ∃ f : B →ₐ[A] C,
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp f = φ :=
  ⟨liftResidue φ, liftResidue_comp φ⟩

/-! ## Complete-local form of I.6.1 / I.6.2

When the target is `m_A`-adically complete, maps out of a formally étale algebra
are still determined by (and lift uniquely from) the special fibre, by assembling
the nilpotent thickenings `C / mⁿ C` via adic completeness.
-/

variable {C : Type u} [CommRing C] [Algebra A C]

/-- Ideal of definition on the target: the extension of the maximal ideal of `A`. -/
abbrev mapMaximalIdeal [IsLocalRing A] : Ideal C :=
  (maximalIdeal A).map (algebraMap A C)

lemma iInf_pow_mapMaximalIdeal_eq_bot [IsLocalRing A]
    [IsHausdorff (mapMaximalIdeal (A := A) (C := C)) C] :
    ⨅ i, (mapMaximalIdeal (A := A) (C := C)) ^ i = ⊥ := by
  simpa [smul_eq_mul, Ideal.mul_top] using
    (IsHausdorff.iInf_pow_smul
      (I := mapMaximalIdeal (A := A) (C := C)) (M := C) ‹_›)

/-- I.6.2, uniqueness for Hausdorff targets: maps out of a formally unramified algebra
are determined by their reductions modulo `m_A C`. -/
theorem hom_eq_of_residue_of_isHausdorff [FormallyUnramified A B] [IsLocalRing A]
    [IsHausdorff (mapMaximalIdeal (A := A) (C := C)) C] (f g : B →ₐ[A] C)
    (h : ∀ x, Ideal.Quotient.mk (mapMaximalIdeal (A := A) (C := C)) (f x) =
      Ideal.Quotient.mk (mapMaximalIdeal (A := A) (C := C)) (g x)) : f = g :=
  FormallyUnramified.ext_of_iInf (I := mapMaximalIdeal (A := A) (C := C))
    iInf_pow_mapMaximalIdeal_eq_bot h

/-- I.6.2, existence for adically complete targets. -/
theorem exists_liftResidue_of_isAdicComplete [FormallyEtale A B] [IsLocalRing A]
    [IsAdicComplete (mapMaximalIdeal (A := A) (C := C)) C]
    (φ : B →ₐ[A] C ⧸ mapMaximalIdeal (A := A) (C := C)) :
    ∃ f : B →ₐ[A] C,
      (Ideal.Quotient.mkₐ A (mapMaximalIdeal (A := A) (C := C))).comp f = φ :=
  FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete φ

/-- I.6.1 / I.6.2, complete-local form: when the target is `m_A`-adically complete,
maps out of a formally étale algebra correspond bijectively to maps into the special
fibre. -/
theorem hom_equiv_residue_of_isAdicComplete [FormallyEtale A B] [IsLocalRing A]
    [IsAdicComplete (mapMaximalIdeal (A := A) (C := C)) C] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A (mapMaximalIdeal (A := A) (C := C))).comp f :=
  ⟨fun f g hfg ↦
    hom_eq_of_residue_of_isHausdorff f g fun x ↦ congr($(hfg) x),
    fun φ ↦
      let ⟨f, hf⟩ := exists_liftResidue_of_isAdicComplete φ
      ⟨f, hf⟩⟩

/-- I.6.1 packaged for complete-local targets (alias of the adic-complete form). -/
theorem finiteEtale_hom_equiv_residue_complete [FormallyEtale A B] [IsLocalRing A]
    [IsAdicComplete (mapMaximalIdeal (A := A) (C := C)) C] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A (mapMaximalIdeal (A := A) (C := C))).comp f :=
  hom_equiv_residue_of_isAdicComplete

/-- Complete local rings are Henselian local (mathlib’s `IsAdicComplete.henselianRing`
specialised at the maximal ideal). Object-level essential surjectivity of finite
étale algebras over `A` still needs a Henselian assembly of standard-étale
presentations beyond root lifting. -/
instance henselianLocalRing_of_isAdicComplete_maximalIdeal [IsLocalRing A]
    [IsAdicComplete (maximalIdeal A) A] : HenselianLocalRing A where
  is_henselian f hf a₀ h₁ h₂ := by
    have : HenselianRing A (maximalIdeal A) := IsAdicComplete.henselianRing A _
    exact HenselianRing.is_henselian f hf a₀ h₁
      (h₂.map (Ideal.Quotient.mk (maximalIdeal A)))

end SGA.SGA1.ExposeI
