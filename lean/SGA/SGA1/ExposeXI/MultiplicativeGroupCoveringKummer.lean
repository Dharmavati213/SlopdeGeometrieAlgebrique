/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import SGA.SGA1.ExposeXI.KummerSequence

/-!
# The Kummer coverings `z ↦ z^d` of `𝔾_m` (for XIII.2.12)

Over `𝔾_{m,k} = Spec k[T, T⁻¹]`, the Kummer covering of degree `d` is
`k[T, T⁻¹][z]/(z^d - T)` (`KummerAlgebra k[T;T⁻¹] d (T 1)`, XI.6.2). Its ring is `k[z, z⁻¹]`
(`SGA.SGA1.ExposeXI.laurentKummerEquiv`, XI.6.1), so it is a domain (the covering is connected,
`isDomain_kummer`); when `d` is prime to the characteristic it is étale (`etale_kummer`) with at
least `d` automorphisms over `k[T, T⁻¹]` (the action of `μ_d(k)`,
`card_le_card_algEquiv_kummer`), i.e. a connected Galois covering with group `μ_d ≅ ℤ/d`.

We also record that `k[T, T⁻¹]`, the localization of `k[T]` at `T`, is a noetherian principal
ideal domain (mathlib has no such instances).
-/

universe u

open Polynomial
open scoped LaurentPolynomial

namespace SGA.SGA1.ExposeXI

variable (k : Type u) [Field k] (d : ℕ)

/-! `k[T, T⁻¹]` is the localization of `k[T]` at `T`, hence a noetherian Dedekind domain. -/

instance isNoetherianRing_laurent : IsNoetherianRing k[T;T⁻¹] :=
  IsLocalization.isNoetherianRing (Submonoid.powers (X : k[X])) _ inferInstance

instance isPrincipalIdealRing_laurent : IsPrincipalIdealRing k[T;T⁻¹] where
  principal I := by
    obtain ⟨a, ha⟩ := IsPrincipalIdealRing.principal (I.under k[X])
    refine ⟨algebraMap k[X] k[T;T⁻¹] a, ?_⟩
    rw [← IsLocalization.map_under (Submonoid.powers (X : k[X])) k[T;T⁻¹] I, ha,
      Ideal.submodule_span_eq, Ideal.map_span, Set.image_singleton, Ideal.submodule_span_eq]

instance isDedekindDomain_laurent : IsDedekindDomain k[T;T⁻¹] := inferInstance

variable [NeZero d]

/-- The Kummer covering of `𝔾_m` is connected: its ring is a domain. -/
instance isDomain_kummer : IsDomain (KummerAlgebra k[T;T⁻¹] d (LaurentPolynomial.T 1)) :=
  (laurentKummerEquiv d).symm.toMulEquiv.isDomain_iff.mp inferInstance

variable {k d}

/-- The Kummer covering of degree `d` of `𝔾_m` is étale when `d` is prime to the
characteristic. -/
lemma etale_kummer (hd : (d : k) ≠ 0) :
    Algebra.Etale k[T;T⁻¹] (KummerAlgebra k[T;T⁻¹] d (LaurentPolynomial.T 1)) := by
  refine Kummer.etale ?_ (LaurentPolynomial.isUnit_T 1)
  rw [← map_natCast (LaurentPolynomial.C : k →+* k[T;T⁻¹])]
  exact (isUnit_iff_ne_zero.mpr hd).map _

/-- The Kummer covering of degree `d` of `𝔾_{m,k}`, `k` separably closed and `d` prime to the
characteristic, has at least `d` automorphisms (`z ↦ ζ z`, `ζ ∈ μ_d(k)`): it is Galois. -/
lemma card_le_card_algEquiv_kummer [IsSepClosed k] (hd : (d : k) ≠ 0) :
    d ≤ Nat.card (KummerAlgebra k[T;T⁻¹] d (LaurentPolynomial.T 1) ≃ₐ[k[T;T⁻¹]]
      KummerAlgebra k[T;T⁻¹] d (LaurentPolynomial.T 1)) := by
  have : NeZero (d : k) := ⟨hd⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k d
  have hCinj : Function.Injective (LaurentPolynomial.C : k →+* k[T;T⁻¹]) :=
    (LaurentPolynomial.C : k →+* k[T;T⁻¹]).injective
  have hζ' : IsPrimitiveRoot (LaurentPolynomial.C ζ : k[T;T⁻¹]) d :=
    hζ.map_of_injective hCinj
  have hcard : Nat.card (rootsOfUnity d k[T;T⁻¹]) = d := hζ'.card_rootsOfUnity
  have hinjA : Function.Injective
      (algebraMap k[T;T⁻¹] (KummerAlgebra k[T;T⁻¹] d (LaurentPolynomial.T 1))) :=
    FaithfulSMul.algebraMap_injective _ _
  have hinj : Function.Injective
      (Kummer.rootsAction (A := k[T;T⁻¹]) d (LaurentPolynomial.T 1)) := by
    intro u v huv
    have h := congrArg (fun e ↦ e (AdjoinRoot.root (X ^ d - C
      (LaurentPolynomial.T 1 : k[T;T⁻¹])))) huv
    simp only [Kummer.rootsAction_root] at h
    exact Subtype.ext (Units.ext (hinjA ((isUnit_root_laurent d).mul_left_injective h)))
  calc d = Nat.card (rootsOfUnity d k[T;T⁻¹]) := hcard.symm
    _ ≤ _ := Nat.card_le_card_of_injective _ hinj

end SGA.SGA1.ExposeXI
