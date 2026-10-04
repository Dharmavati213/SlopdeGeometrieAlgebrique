/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.RingTheory.IsGaloisGroup.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# The normalization of a curve in a Galois covering is Galois (algebra for XIII.2.12 over `ℂ`)

For the comparison of inertia groups with loops (registry row C32) the automorphism group `G` of a
Galois covering `E` of `U ⊆ X` must be a Galois group (`IsGaloisGroup`) of the normalization `S`
of an affine neighbourhood `Spec B` of the removed point in `E`. Here `S` is the integral closure
of `B` in the algebra `C` of `E` over `U ∩ Spec B`, on which `G` acts by `B`-algebra
automorphisms.

* `isGaloisGroup_of_finrank_le`: a finite group acting faithfully on a finite field extension
  `L/K` by `K`-automorphisms, with at least `[L : K]` elements, is a Galois group of `L/K`;
* `isGaloisGroup_integralClosure`: for `B` an integrally closed domain and `C` an integrally
  closed domain, algebraic over `B`, with a faithful action of a finite group `G` by `B`-algebra
  automorphisms such that `[Frac C : Frac B] ≤ |G|`, `G` is a Galois group of the integral closure
  of `B` in `C` over `B`. (Compare `IntegralClosure.isGaloisGroup` in
  `SGA.Foundations.Ramification.IntegralClosure`, for `Gal(M/K)` and the integral closure in the
  field `M`; here `G` is an abstract group acting on a ring.)

## References

* [J.-P. Serre, *Corps locaux*, I §7][serre1962]
-/

open Module

namespace SGA.SGA1.ExposeXIII.LoopAlgebra

/-- A finite group `G` acting faithfully on a finite extension `L/K` by `K`-algebra automorphisms
is a Galois group of `L/K` as soon as `[L : K] ≤ |G|` (then `G ≅ Gal(L/K)` and `L/K` is
Galois). -/
theorem isGaloisGroup_of_finrank_le {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (G : Type*) [Group G] [Finite G] [MulSemiringAction G L]
    [SMulCommClass G K L] [FaithfulSMul G L] (h : finrank K L ≤ Nat.card G) :
    IsGaloisGroup G K L := by
  have hinj : Function.Injective (MulSemiringAction.toAlgAut G K L) :=
    MulSemiringAction.toAlgEquiv_injective (G := G) K L
  have hle : Nat.card G ≤ Nat.card (L ≃ₐ[K] L) := Nat.card_le_card_of_injective _ hinj
  have hcard : Nat.card (L ≃ₐ[K] L) = finrank K L :=
    le_antisymm (by rw [Nat.card_eq_fintype_card]; exact AlgEquiv.card_le) (h.trans hle)
  have : IsGalois K L := IsGalois.of_card_aut_eq_finrank K L hcard
  have hbij : Function.Bijective (MulSemiringAction.toAlgAut G K L) :=
    hinj.bijective_of_nat_card_le (hcard.le.trans h)
  exact IsGaloisGroup.of_mulEquiv_algEquiv (MulEquiv.ofBijective _ hbij) fun _ _ ↦ rfl

/-- **The normalization in a Galois algebra is Galois.** Let `B` be an integrally closed domain
with fraction field `K`, `C` an integrally closed domain containing `B` (`FaithfulSMul B C`) with
fraction field `L` finite over `K`, and `G` a finite group acting faithfully on `C` by
`B`-algebra automorphisms with `[L : K] ≤ |G|`. Then `G` is a Galois group of the integral closure
`S` of `B` in `C` over `B` (`IsGaloisGroup G B S`), for the action of `G` on `S` restricted from
`C`. -/
theorem isGaloisGroup_integralClosure {B C : Type*} [CommRing B] [IsDomain B]
    [IsIntegrallyClosed B] [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra B C]
    [FaithfulSMul B C] (K L : Type*) [Field K] [Field L] [Algebra B K] [IsFractionRing B K]
    [Algebra C L] [IsFractionRing C L] [Algebra K L] [Algebra B L] [IsScalarTower B K L]
    [IsScalarTower B C L] [FiniteDimensional K L] (G : Type*) [Group G] [Finite G]
    [MulSemiringAction G C] [SMulCommClass G B C] [FaithfulSMul G C]
    (h : finrank K L ≤ Nat.card G) :
    IsGaloisGroup G B (integralClosure B C) := by
  let := IsFractionRing.mulSemiringAction G C L
  have : FaithfulSMul G L := IsFractionRing.faithfulSMul G C L
  have : SMulCommClass G K L := IsFractionRing.smulCommClass G B C K L
  have hGKL : IsGaloisGroup G K L := isGaloisGroup_of_finrank_le G h
  -- the integral closure `S` of `B` in `C` is the integral closure of `B` in `L`
  set S := integralClosure B C
  have : IsScalarTower B S L := IsScalarTower.of_algebraMap_eq (R := B) (S := S) (A := L)
    fun b ↦ IsScalarTower.algebraMap_apply B C L b
  have hint : IsIntegralClosure S B L := by
    refine ⟨fun x y hxy ↦ Subtype.ext (IsFractionRing.injective C L hxy), fun {x} ↦ ⟨fun hx ↦ ?_,
      ?_⟩⟩
    · -- integral over `B`, hence over `C`, hence in `C`
      have hxC : IsIntegral C x := hx.tower_top
      obtain ⟨c, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxC
      have hc : IsIntegral B c := by
        rwa [← isIntegral_algHom_iff (IsScalarTower.toAlgHom B C L)
          (IsFractionRing.injective C L)]
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro ⟨s, rfl⟩
      exact s.2.map (IsScalarTower.toAlgHom B C L)
  have : Algebra.IsAlgebraic B L := by
    have : Algebra.IsAlgebraic K L := inferInstance
    exact IsFractionRing.comap_isAlgebraic_iff.mpr this
  have : IsFractionRing S L :=
    IsIntegralClosure.isFractionRing_of_finite_extension B K L S
  have : SMulDistribClass G S L := ⟨fun g s l ↦ by
    rw [Algebra.smul_def, Algebra.smul_def, smul_mul']
    congr 1
    change g • algebraMap C L (s : C) = algebraMap C L ((g • s : S) : C)
    rw [integralClosure.coe_smul, ← algebraMap.coe_smul']⟩
  exact IsGaloisGroup.of_isFractionRing G B S K L

end SGA.SGA1.ExposeXIII.LoopAlgebra
