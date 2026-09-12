/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Unramified.Basic

/-!
# SGA 1, Exposé I, §6: étale extensions of complete local rings

Theorem I.6.1 says that finite étale algebras over a complete local ring `A`
are equivalent to finite separable algebras over the residue field. The fully
faithful half (I.6.2) is the infinitesimal lifting property, and is proved here
when `A` is artinian local (so the maximal ideal is nilpotent). The complete
case follows by passing to the inverse limit, which is recorded as remaining.
Existence of a lift of a separable residue algebra uses Hensel's lemma together
with the standard étale presentation of I.7; that direction is in
`StandardEtale.lean`.
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

end SGA.SGA1.ExposeI
