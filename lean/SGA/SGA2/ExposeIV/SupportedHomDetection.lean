/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.InjectivityCriterion
import SGA.SGA2.ExposeIII.AssociatedPrimes
import Mathlib.Algebra.Category.Grp.Zero

/-!
# SGA 2, Exposé IV, 1.4: detecting an arbitrary supported module by Hom

A finite module whose support contains the support of an arbitrary module
`H` detects whether `H` is zero. The target is not assumed finite. The proof
uses the genuine associated-prime formula for Hom and existence of associated
primes for nonzero modules over a noetherian ring. This supplies the supported
representable-functor vanishing step in IV.1.4, not the full induction for an
arbitrary exact delta functor.
-/

noncomputable section

universe u v w

open CategoryTheory Limits Opposite
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- Actual ideal-power torsion, with no finiteness hypothesis on its
underlying module, has support contained in the ideal's zero locus. -/
theorem support_subset_zeroLocus_of_powerTorsion_eq_top (J : Ideal R)
    (H : Type v) [AddCommGroup H] [Module R H] (hH : powerTorsion J H = ⊤) :
    Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R) := by
  intro p hp a ha
  by_contra hap
  obtain ⟨x, hx⟩ := Module.mem_support_iff'.mp hp
  have hxT : x ∈ powerTorsion J H := by rw [hH]; trivial
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J H x).mp hxT
  exact hx (a ^ n) (fun han ↦ hap (p.isPrime.mem_of_pow_mem n han))
    (hn _ (Ideal.pow_mem_pow ha n))

/-- The unchanged torsion submodule is itself an ideal-power-torsion module. -/
theorem powerTorsion_powerTorsion_eq_top (J : Ideal R)
    (H : Type v) [AddCommGroup H] [Module R H] :
    powerTorsion J (powerTorsion J H) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨n, hn⟩ := (mem_powerTorsion_iff J H x.val).mp x.property
  exact (mem_powerTorsion_iff J (powerTorsion J H) x).mpr
    ⟨n, fun a ha ↦ Subtype.ext (hn a ha)⟩

/-- The original torsion submodule, not merely a finite approximation, is
supported on the actual closed subset `V(J)`. -/
theorem support_powerTorsion_subset_zeroLocus (J : Ideal R)
    (H : Type v) [AddCommGroup H] [Module R H] :
    Module.support R (powerTorsion J H) ⊆ PrimeSpectrum.zeroLocus (J : Set R) :=
  support_subset_zeroLocus_of_powerTorsion_eq_top J _ (powerTorsion_powerTorsion_eq_top J H)

variable [IsNoetherianRing R]

/-- Every associated prime of an arbitrary module is in its actual support.
Only the ring, not the module, is assumed noetherian. -/
theorem associatedPrimeSpectrum_subset_support (H : Type v)
    [AddCommGroup H] [Module R H] :
    SGA.SGA2.ExposeIII.associatedPrimeSpectrum (R := R) H ⊆ Module.support R H := by
  intro p hp
  obtain ⟨_, x, _, hann⟩ := (SGA.SGA2.ExposeIII.mem_associatedPrimes_iff H).mp hp
  apply Module.mem_support_iff'.mpr
  refine ⟨x, ?_⟩
  intro a hap hax
  apply hap
  rw [hann, Submodule.mem_colon_singleton, Submodule.mem_bot]
  exact hax

/-- A finite module detects zero targets whose support it contains, even
when the target is not finitely generated. -/
theorem subsingleton_linearMap_iff_of_support_subset
    (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (H : Type v) [AddCommGroup H] [Module R H]
    (hSupp : Module.support R H ⊆ Module.support R M) :
    Subsingleton (M →ₗ[R] H) ↔ Subsingleton H := by
  constructor
  · intro hHom
    let := hHom
    apply (SGA.SGA2.ExposeIII.associatedPrimes_eq_empty_iff_subsingleton (R := R) H).mp
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro p hp
    let P : PrimeSpectrum R := ⟨p, hp.isPrime⟩
    have hPH : P ∈ Module.support R H := associatedPrimeSpectrum_subset_support H hp
    have hP := (SGA.SGA2.ExposeIII.mem_associatedPrimes_linearMap_iff H M P).mpr
      ⟨hSupp hPH, hp⟩
    rw [associatedPrimes.eq_empty_of_subsingleton] at hP
    exact hP
  · intro hH
    let := hH
    infer_instance

/-- **IV.1.4, the supported Hom detection step:** a finite module with
support exactly `V(J)` detects whether any module supported there is zero. -/
theorem subsingleton_linearMap_iff_of_support_eq_zeroLocus
    (J : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.support R M = PrimeSpectrum.zeroLocus (J : Set R))
    (H : Type v) [AddCommGroup H] [Module R H]
    (hH : Module.support R H ⊆ PrimeSpectrum.zeroLocus (J : Set R)) :
    Subsingleton (M →ₗ[R] H) ↔ Subsingleton H :=
  subsingleton_linearMap_iff_of_support_subset M H (by rwa [hM])

/-- The same detection statement applies to arbitrary ideal-power-torsion
targets, such as the colimit modules in IV.1.4. -/
theorem subsingleton_linearMap_iff_of_powerTorsion
    (J : Ideal R) (M : Type w) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hM : Module.support R M = PrimeSpectrum.zeroLocus (J : Set R))
    (H : Type v) [AddCommGroup H] [Module R H] (hH : powerTorsion J H = ⊤) :
    Subsingleton (M →ₗ[R] H) ↔ Subsingleton H :=
  subsingleton_linearMap_iff_of_support_eq_zeroLocus J M hM H
    (support_subset_zeroLocus_of_powerTorsion_eq_top J H hH)

/-- Categorical zero detection for actual module Hom groups. -/
theorem isZero_hom_iff_of_support_subset (M H : ModuleCat.{u} R)
    [Module.Finite R M] (hSupp : Module.support R H ⊆ Module.support R M) :
    IsZero ((preadditiveYoneda.obj H).obj (op M)) ↔ IsZero H := by
  rw [AddCommGrpCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact (ModuleCat.homEquiv.subsingleton_congr).trans
    (subsingleton_linearMap_iff_of_support_subset M H hSupp)

/-- A represented contravariant functor on any chosen category of modules
vanishes if and only if it vanishes on one finite module containing the
support of its representing module. This includes the finite-supported
subcategory without assuming the representing module itself finite. -/
theorem homFunctor_isZero_iff_at_of_support_subset {C : Type*} [Category C]
    (D : C ⥤ ModuleCat.{u} R) (c : C) (H : ModuleCat.{u} R)
    [Module.Finite R (D.obj c)]
    (hSupp : Module.support R H ⊆ Module.support R (D.obj c)) :
    IsZero (D.op ⋙ preadditiveYoneda.obj H) ↔
      IsZero ((D.op ⋙ preadditiveYoneda.obj H).obj (op c)) := by
  constructor
  · intro h
    exact h.obj (op c)
  · intro hc
    have hH := (isZero_hom_iff_of_support_subset (D.obj c) H hSupp).mp hc
    apply Functor.isZero
    intro d
    apply AddCommGrpCat.isZero_iff_subsingleton.mpr
    change Subsingleton (D.obj d.unop ⟶ H)
    exact ⟨fun f g ↦ hH.eq_of_tgt f g⟩

/-- The detection statement transfers along an actual given representation
isomorphism; no representation theorem is assumed for an arbitrary functor. -/
theorem representedFunctor_isZero_iff_at_of_support_subset {C : Type*} [Category C]
    (D : C ⥤ ModuleCat.{u} R) (c : C) (H : ModuleCat.{u} R)
    [Module.Finite R (D.obj c)]
    (hSupp : Module.support R H ⊆ Module.support R (D.obj c))
    (T : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (e : T ≅ D.op ⋙ preadditiveYoneda.obj H) :
    IsZero T ↔ IsZero (T.obj (op c)) :=
  e.isZero_iff.trans ((homFunctor_isZero_iff_at_of_support_subset D c H hSupp).trans
    (e.app (op c)).isZero_iff.symm)

/-- **IV.1.4, representable supported case:** one finite object of full
support detects vanishing of a functor represented by an arbitrary
ideal-power-torsion module. -/
theorem representedSupportedFunctor_isZero_iff_at {C : Type*} [Category C]
    (J : Ideal R) (D : C ⥤ ModuleCat.{u} R) (c : C) (H : ModuleCat.{u} R)
    [Module.Finite R (D.obj c)]
    (hc : Module.support R (D.obj c) = PrimeSpectrum.zeroLocus (J : Set R))
    (hH : powerTorsion J H = ⊤) (T : Cᵒᵖ ⥤ AddCommGrpCat.{u})
    (e : T ≅ D.op ⋙ preadditiveYoneda.obj H) :
    IsZero T ↔ IsZero (T.obj (op c)) :=
  representedFunctor_isZero_iff_at_of_support_subset D c H
    (by rw [hc]; exact support_subset_zeroLocus_of_powerTorsion_eq_top J H hH) T e

end SGA.SGA2.ExposeIV
