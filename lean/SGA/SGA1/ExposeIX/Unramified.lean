/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Unramified.Finite

/-!
# Fibres of unramified and étale morphisms

Prerequisites for Exposé IX that mathlib lacks:

* an unramified algebra (of finite type) has finite fibres, so an unramified morphism of schemes
  is locally quasi-finite and has discrete fibres (used in IX.3.4);
* a finite algebra whose fibres `κ(p) ⊗_R B` are unramified is unramified, via the base change
  of Kähler differentials and Nakayama's lemma (Stacks 00UV, finite case); hence a finite
  projective algebra with étale fibres is étale (IX.1.9).
-/

universe u

open TensorProduct

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

/-- An unramified algebra of finite type has finite fibres. -/
theorem quasiFinite_of_formallyUnramified (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FormallyUnramified R S] [Algebra.EssFiniteType R S] :
    Algebra.QuasiFinite R S where
  finite_fiber P _ := Algebra.FormallyUnramified.finite_of_free P.ResidueField (P.Fiber S)

/-- An unramified morphism is locally quasi-finite; in particular its fibres are discrete. -/
theorem locallyQuasiFinite_of_formallyUnramified {X Y : Scheme.{u}} (f : X ⟶ Y)
    [FormallyUnramified f] [LocallyOfFiniteType f] : LocallyQuasiFinite f := by
  have h₁ : affineLocally _ f :=
    HasRingHomProperty.eq_affineLocally @FormallyUnramified ▸ ‹FormallyUnramified f›
  have h₂ : affineLocally _ f :=
    HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType ▸ ‹LocallyOfFiniteType f›
  rw [HasRingHomProperty.eq_affineLocally @LocallyQuasiFinite]
  intro U V
  have a : (Scheme.Hom.appLE (f ∣_ ↑U) ⊤ ↑V (by simp)).hom.FormallyUnramified := h₁ U V
  have b : (Scheme.Hom.appLE (f ∣_ ↑U) ⊤ ↑V (by simp)).hom.FiniteType := h₂ U V
  algebraize [(Scheme.Hom.appLE (f ∣_ ↑U) ⊤ ↑V (by simp)).hom]
  exact quasiFinite_of_formallyUnramified _ _

/-- A finite algebra whose fibres are unramified is unramified: `κ(p) ⊗_R Ω_{B/R}` is the
module of differentials of the fibre at `p`, so it vanishes for all `p`, and `Ω_{B/R}` is a
finite `R`-module, hence zero by Nakayama. -/
theorem formallyUnramified_of_formallyUnramified_fiber {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Algebra.FiniteType R B]
    (h : ∀ (p : Ideal R) [p.IsPrime], Algebra.FormallyUnramified p.ResidueField (p.Fiber B)) :
    Algebra.FormallyUnramified R B := by
  rw [Algebra.formallyUnramified_iff]
  have : Module.Finite R Ω[B⁄R] := Module.Finite.trans B Ω[B⁄R]
  rw [← Module.support_eq_empty_iff (R := R), Set.eq_empty_iff_forall_notMem]
  intro p hp
  rw [Module.mem_support_iff_nontrivial_residueField_tensorProduct] at hp
  have := h p.asIdeal
  have : Subsingleton Ω[p.asIdeal.Fiber B⁄p.asIdeal.ResidueField] :=
    (Algebra.formallyUnramified_iff _ _).mp inferInstance
  let : Algebra B (p.asIdeal.Fiber B) := Algebra.TensorProduct.rightAlgebra
  have e := KaehlerDifferential.tensorKaehlerEquivBase R p.asIdeal.ResidueField B
    (p.asIdeal.Fiber B)
  exact not_subsingleton _ e.toEquiv.subsingleton

/-- A finite projective (i.e. locally free of finite type) algebra with étale fibres is
étale. -/
theorem etale_of_projective_of_etale_fiber {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Module.Projective R B]
    (h : ∀ (p : Ideal R) [p.IsPrime], Algebra.Etale p.ResidueField (p.Fiber B)) :
    Algebra.Etale R B := by
  have : Module.FinitePresentation R B := Module.finitePresentation_of_projective R B
  have : Algebra.FinitePresentation R B :=
    (Module.FinitePresentation.iff_finitePresentation_of_finite R B).mp inferInstance
  have : Algebra.FormallyUnramified R B :=
    formallyUnramified_of_formallyUnramified_fiber fun p _ ↦ inferInstance
  exact .of_formallyUnramified_of_flat

end SGA.SGA1.ExposeIX
