/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.IntegralClosure

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

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- I.9.1, the local criterion used in the exposé: a local formally unramified
essentially finite-type homomorphism identifies maximal ideals, so the
cotangent spaces differ only by the separable residue extension. -/
theorem map_maximalIdeal_of_formallyUnramified [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [EssFiniteType A B] [FormallyUnramified A B] :
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

end SGA.SGA1.ExposeI
