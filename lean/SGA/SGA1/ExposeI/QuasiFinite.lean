/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# SGA 1, Exposé I, §2: quasi-finite morphisms

SGA calls a local homomorphism `A → B` quasi-finite when the special fibre
`B/mB` is finite-dimensional over `k = A/m`. For morphisms of schemes, being
quasi-finite at a point means that the point is isolated in its fibre.
Mathlib's `Algebra.QuasiFinite` asks the same finite-dimensionality of every
fibre `κ(p) ⊗ S`; `Scheme.Hom.QuasiFiniteAt` is the pointwise condition.
After no. I.2 the exposé assumes locally noetherian schemes. Over an artinian
ring, quasi-finite is equivalent to module-finite (I.2.2). Theorem I.2.1(iii)
says the completion `B̂` is finite over `Â`; for module-finite algebras this is
`finite_adicCompletion_of_moduleFinite`, and over an artinian local base
module-finiteness is equivalent to quasi-finiteness, so I.2.1(i)↔(iii) holds.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry Algebra IsLocalRing AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- I.2.1(i): the special fibre `κ(m) ⊗ S` of a local homomorphism is
finite-dimensional. For a local ring this is SGA's `B/mB`. -/
def IsQuasiFiniteLocal [IsLocalRing R] : Prop :=
  Module.Finite (Ideal.ResidueField (maximalIdeal R)) ((maximalIdeal R).Fiber S)

/-- The `m`-adic completion of a local ring. -/
abbrev adicCompletion (A : Type u) [CommRing A] [IsLocalRing A] : Type u :=
  AdicCompletion (maximalIdeal A) A

/-- I.2.1: a globally quasi-finite algebra has finite-dimensional special fibre. -/
theorem isQuasiFiniteLocal_of_quasiFinite (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [QuasiFinite R S] :
    Module.Finite (Ideal.ResidueField (maximalIdeal R)) ((maximalIdeal R).Fiber S) :=
  QuasiFinite.finite_fiber (maximalIdeal R)

/-- I.2.1: for a finite-type algebra, quasi-finite means finite fibres of spectra. -/
theorem quasiFinite_iff_finite_fibers [FiniteType R S] :
    QuasiFinite R S ↔
      ∀ p : PrimeSpectrum R, (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}).Finite :=
  ⟨fun _ p ↦ QuasiFinite.finite_comap_preimage_singleton p,
    fun h ↦ (QuasiFinite.iff_finite_comap_preimage_singleton (R := R) (S := S)).mpr h⟩

/-- I.2.2: over an artinian ring, quasi-finite is equivalent to module-finite. -/
theorem quasiFinite_iff_finite [IsArtinianRing R] :
    QuasiFinite R S ↔ Module.Finite R S :=
  QuasiFinite.iff_of_isArtinianRing

/-- I.2.1(iii): if `S` is module-finite over a noetherian local ring `R`, then the
`m`-adic completion `Ŝ` is module-finite over `R̂`. -/
theorem finite_adicCompletion_of_moduleFinite [IsLocalRing R] [IsNoetherianRing R]
    [Module.Finite R S] :
    Module.Finite (adicCompletion R) (AdicCompletion (maximalIdeal R) S) :=
  Module.Finite.of_surjective (AdicCompletion.ofTensorProduct (maximalIdeal R) S)
    (AdicCompletion.ofTensorProduct_surjective_of_finite (maximalIdeal R) S)

/-- I.2.1(i)↔(iii) over an artinian local ring: quasi-finite iff module-finite
(I.2.2), and then the completion is finite over `Â`. -/
theorem isQuasiFiniteLocal_iff_finite_adicCompletion [IsLocalRing R] [IsArtinianRing R] :
    QuasiFinite R S ↔
      Module.Finite R S ∧
        Module.Finite (adicCompletion R) (AdicCompletion (maximalIdeal R) S) := by
  rw [quasiFinite_iff_finite]
  refine ⟨fun h ↦ ⟨h, ?_⟩, fun ⟨h, _⟩ ↦ h⟩
  have : IsNoetherianRing R := inferInstance
  exact finite_adicCompletion_of_moduleFinite

/-- I.2.1(iii) packaged with the special-fibre condition, for module-finite algebras. -/
theorem isQuasiFiniteLocal_and_finite_adicCompletion_of_moduleFinite
    [IsLocalRing R] [IsNoetherianRing R] [Module.Finite R S] :
    IsQuasiFiniteLocal (R := R) (S := S) ∧
      Module.Finite (adicCompletion R) (AdicCompletion (maximalIdeal R) S) :=
  ⟨isQuasiFiniteLocal_of_quasiFinite R S, finite_adicCompletion_of_moduleFinite⟩

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- I.2: quasi-finite at a point, in SGA's language. -/
abbrev QuasiFiniteAt (x : X) : Prop := f.QuasiFiniteAt x

/-- I.2: a morphism of finite type is quasi-finite at `x` iff `{x}` is open in its fibre. -/
theorem quasiFiniteAt_iff_isolated_in_fiber [LocallyOfFiniteType f] {x : X} :
    f.QuasiFiniteAt x ↔ IsOpen {f.asFiber x} :=
  f.quasiFiniteAt_iff_isOpen_singleton_asFiber

/-- I.2: a locally quasi-finite morphism is quasi-finite at every point. -/
theorem quasiFiniteAt_of_locallyQuasiFinite [LocallyQuasiFinite f] (x : X) :
    f.QuasiFiniteAt x :=
  f.quasiFiniteAt x

end SGA.SGA1.ExposeI
