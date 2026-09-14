/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.IntegralClosure
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# SGA 1, Exposé I, §9: permanence properties

Étale morphisms preserve and reflect a number of local properties. The
exposé records that a local étale homomorphism preserves Krull dimension
and depth (from flat + quasi-finite), and then proves statements special
to the étale case: regularity (I.9.1), reducedness (I.9.2–I.9.3), and
normality (I.9.5). Mathlib supplies the residue-field and `m_A S = m_S`
characterisation used in I.9.1, reducedness of étale algebras over fields
(I.9.3 in the generic fibre), and the comparison of integral closures under
smooth (hence étale) base change (I.9.5 / I.10.5).
-/

universe u

namespace SGA.SGA1.ExposeI

open Algebra IsLocalRing
open scoped TensorProduct

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- I.9.1, the local criterion used in the exposé: a local formally unramified
essentially finite-type homomorphism identifies maximal ideals, so the
cotangent spaces differ only by the separable residue extension. -/
theorem map_maximalIdeal_of_formallyUnramified [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [EssFiniteType A B] [FormallyUnramified A B] :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
  FormallyUnramified.map_maximalIdeal

/-- I.9.1: regularity is equivalent to equality of cotangent finrank and Krull
dimension; together with `map_maximalIdeal_of_formallyUnramified` this is the
input for transferring regularity along local étale maps. -/
theorem isRegularLocalRing_iff_finrank_cotangent (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    IsRegularLocalRing R ↔
      ↑(Module.finrank (ResidueField R) (CotangentSpace R)) = ringKrullDim R :=
  IsRegularLocalRing.iff_finrank_cotangentSpace (R := R)

/-- I.9.1 for étale local homs: maximal ideals identify. -/
theorem map_maximalIdeal_of_etale [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [EssFiniteType A B] [Etale A B] :
    (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
  FormallyUnramified.map_maximalIdeal

/-- I.9.3, over a field: an étale algebra is reduced. -/
theorem isReduced_of_etale_over_field (K : Type u) [Field K] [Algebra K B] [Etale K B] :
    IsReduced B :=
  FormallyUnramified.isReduced_of_field K B

/-- I.9.3, over a field: an étale algebra is a finite product of fields. -/
theorem etale_over_field_is_product_of_fields {K : Type u} [Field K] [Algebra K B] [Etale K B] :
    ∃ (I : Type u) (_ : Finite I) (Ai : I → Type u) (_ : ∀ i, Field (Ai i))
      (_ : ∀ i, Algebra K (Ai i)) (_ : B ≃ₐ[K] ∀ i, Ai i),
      ∀ i, Module.Finite K (Ai i) ∧ Algebra.IsSeparable K (Ai i) :=
  (Algebra.Etale.iff_exists_algEquiv_prod (K := K) (A := B)).mp inferInstance

/-- I.9.5 / I.10.5: smooth (in particular étale) base change commutes with
integral closure. -/
theorem toIntegralClosure_bijective_of_etale [Etale A B] {C : Type u} [CommRing C] [Algebra A C] :
    Function.Bijective (TensorProduct.toIntegralClosure A B C) :=
  TensorProduct.toIntegralClosure_bijective_of_smooth

/-- I.9.5(ii): the hypothesis package “unramified + injective over a normal local
domain”. Full étaleness follows by Serre’s criterion after I.7.6. -/
def IsUnramifiedInjectiveNormalLocal [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] : Prop :=
  EssFiniteType A B ∧ FormallyUnramified A B ∧ Function.Injective (algebraMap A B) ∧
    IsDomain A ∧ IsIntegrallyClosed A

/-- I.9.5(ii) / I.9.11: base change of an unramified algebra to the fraction field
remains unramified. -/
instance formallyUnramified_fractionRing_tensor [FiniteType A B] [FormallyUnramified A B] :
    FormallyUnramified (FractionRing A) (FractionRing A ⊗[A] B) :=
  inferInstance

/-- I.9.11: over a field, essentially finite-type formally unramified implies formally
étale. -/
theorem formallyEtale_of_formallyUnramified_of_field (K : Type u) [Field K] [Algebra K B]
    [EssFiniteType K B] [FormallyUnramified K B] : FormallyEtale K B :=
  (Algebra.FormallyEtale.iff_formallyUnramified_of_field (K := K) (A := B)).mpr inferInstance

/-- I.9.1: if `m_A B = m_B`, then the maximal ideal of `B` needs at most as many
generators as that of `A` (images of a generating set of `m_A` generate `m_B`). -/
theorem spanFinrank_maximalIdeal_le_of_map_eq [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    (maximalIdeal B).spanFinrank ≤ (maximalIdeal A).spanFinrank := by
  rw [← h]
  exact Ideal.spanFinrank_map_le_of_fg (algebraMap A B) (IsNoetherian.noetherian _)

/-- I.9.1: same inequality for local étale homs (via `map_maximalIdeal`). -/
theorem spanFinrank_maximalIdeal_le_of_etale [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [EssFiniteType A B] [Etale A B] [IsNoetherianRing A] :
    (maximalIdeal B).spanFinrank ≤ (maximalIdeal A).spanFinrank :=
  spanFinrank_maximalIdeal_le_of_map_eq map_maximalIdeal_of_etale

/-- I.9.1, finite étale case: `A → B` is integral (from `Module.Finite`) and flat
(from étale), so going-up and going-down apply. Full equality of Krull dimensions
and of cotangent finranks (needed for unconditional `IsRegularLocalRing` transfer)
still requires assembling those chain-lifting lemmas with the cotangent base-change
isomorphism, which mathlib does not yet package for local étale maps. -/
theorem isIntegral_of_finite_etale [Etale A B] [Module.Finite A B] : Algebra.IsIntegral A B :=
  inferInstance

theorem hasGoingDown_of_etale [Etale A B] : Algebra.HasGoingDown A B :=
  inferInstance

theorem hasGoingUp_of_finite_etale [Etale A B] [Module.Finite A B] : Algebra.HasGoingUp A B :=
  inferInstance

/-- I.9.1 conditional regularity transfer: if cotangent finranks and Krull dimensions
agree, regularity transfers. The equalities are the remaining algebraic input. -/
theorem isRegularLocalRing_of_etale_of_finrank_eq_dim
    [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing B] [EssFiniteType A B] [Etale A B]
    [IsRegularLocalRing A]
    (hcot :
      Module.finrank (ResidueField B) (CotangentSpace B) =
        Module.finrank (ResidueField A) (CotangentSpace A))
    (hdim : ringKrullDim B = ringKrullDim A) : IsRegularLocalRing B := by
  have hA := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp ‹_›
  refine (IsRegularLocalRing.iff_finrank_cotangentSpace (R := B)).mpr ?_
  simp [hcot, hdim, hA]

end SGA.SGA1.ExposeI
