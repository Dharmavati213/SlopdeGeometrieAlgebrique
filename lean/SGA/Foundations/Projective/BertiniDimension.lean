/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.NormalizationFinite
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-!
# Integral morphisms do not raise the dimension

Let `f : X ⟶ Y` be an integral morphism of schemes. Two points of a fibre of `f` are not
specializations of each other unless they are equal (incomparability,
`AlgebraicGeometry.Scheme.Hom.eq_of_specializes_of_isIntegralHom`), so `f` maps chains of
specializations to chains of the same length and `dim X ≤ dim Y`
(`AlgebraicGeometry.Scheme.Hom.topologicalKrullDim_le_of_isIntegralHom`). This is used for the
base change of the generic hyperplane section to an algebraic closure of its field of definition
(SGA 1 X.2.10).

## References

* [Stacks Project, Tag 00GT](https://stacks.math.columbia.edu/tag/00GT) (incomparability)
* [Stacks Project, Tag 0ECG](https://stacks.math.columbia.edu/tag/0ECG)
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Incomparability for integral morphisms**: if `f` is integral, `a ⤳ b` and `f a = f b`, then
`a = b`. -/
theorem Scheme.Hom.eq_of_specializes_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] {a b : X} (h : a ⤳ b) (hf : f a = f b) : a = b := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hbV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f b)) isOpen_univ
  have hU : IsAffineOpen (f ⁻¹ᵁ V) := hV.preimage f
  have hb : b ∈ f ⁻¹ᵁ V := hbV
  have ha : a ∈ f ⁻¹ᵁ V := h.mem_open (f ⁻¹ᵁ V).isOpen hb
  have hle : hU.primeIdealOf ⟨a, ha⟩ ≤ hU.primeIdealOf ⟨b, hb⟩ := by
    rw [PrimeSpectrum.le_iff_specializes]
    have h' : (⟨a, ha⟩ : f ⁻¹ᵁ V) ⤳ ⟨b, hb⟩ := (subtype_specializes_iff _ _).mpr h
    exact h'.map hU.isoSpec.hom.continuous
  by_contra hne
  have hlt : hU.primeIdealOf ⟨a, ha⟩ < hU.primeIdealOf ⟨b, hb⟩ := by
    refine lt_of_le_of_ne hle fun e ↦ hne ?_
    have := congrArg hU.fromSpec e
    rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this
  let φ := f.appLE V (f ⁻¹ᵁ V) le_rfl
  let _ := φ.hom.toAlgebra
  have hint : φ.hom.IsIntegral := by
    have := f.isIntegral_app V hV
    rwa [Scheme.Hom.app_eq_appLE] at this
  have : Algebra.IsIntegral Γ(Y, V) Γ(X, f ⁻¹ᵁ V) := ⟨hint⟩
  have hlt' := Ideal.IsIntegral.comap_lt_comap (R := Γ(Y, V)) (A := Γ(X, f ⁻¹ᵁ V))
    (I := (hU.primeIdealOf ⟨a, ha⟩).asIdeal) (J := (hU.primeIdealOf ⟨b, hb⟩).asIdeal) hlt
  have hca := IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hU le_rfl ha
  have hcb := IsAffineOpen.comap_primeIdealOf_appLE V hV (f ⁻¹ᵁ V) hU le_rfl hb
  have e : (hU.primeIdealOf ⟨a, ha⟩).asIdeal.comap φ.hom =
      (hU.primeIdealOf ⟨b, hb⟩).asIdeal.comap φ.hom := by
    have h1 := congrArg PrimeSpectrum.asIdeal hca
    have h2 := congrArg PrimeSpectrum.asIdeal hcb
    simp only [PrimeSpectrum.comap_asIdeal] at h1 h2
    rw [h1, h2]
    congr 2
    exact Subtype.ext hf
  exact hlt'.ne e

/-- **An integral morphism does not raise the dimension**: by incomparability
(`Scheme.Hom.eq_of_specializes_of_isIntegralHom`) it maps chains of specializations to chains of
specializations of the same length. -/
theorem Scheme.Hom.topologicalKrullDim_le_of_isIntegralHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIntegralHom f] : topologicalKrullDim X ≤ topologicalKrullDim Y := by
  rw [topologicalKrullDim, topologicalKrullDim, Order.krullDim_eq_of_orderIso
    irreducibleSetEquivPoints, Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
  refine Order.krullDim_le_of_strictMono f fun a b hab ↦ ?_
  have hle : f a ≤ f b := (le_iff_specializes.mp hab.le).map f.continuous
  refine lt_of_le_not_ge hle fun hge ↦ hab.ne ?_
  have heq : f a = f b :=
    ((le_iff_specializes.mp hge).antisymm (le_iff_specializes.mp hle)).eq
  exact (f.eq_of_specializes_of_isIntegralHom (le_iff_specializes.mp hab.le) heq.symm).symm

end AlgebraicGeometry
