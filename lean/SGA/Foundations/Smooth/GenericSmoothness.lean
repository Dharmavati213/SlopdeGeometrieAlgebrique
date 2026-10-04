/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Smooth.Locus
import SGA.Foundations.Fields.Separable

/-!
# Generic smoothness over a perfect field

A finitely generated domain `A` over a perfect field `k` (for instance a field of characteristic
`0`) is smooth over `k` on a dense open subset of `Spec A`: there is `f ≠ 0` in `A` with `A_f`
smooth over `k` (`Algebra.exists_ne_zero_smooth_localization_away`). Indeed the fraction field
of `A` is separable over `k` (`Algebra.IsGeometricallyReduced.of_perfectField_of_field`), so `A`
is smooth at its generic point (`Algebra.isSmoothAt_bot_iff_isGeometricallyReduced`), and the
smooth locus is open.

* `Subalgebra.exists_le_fg_smooth`: the same statement for subalgebras of a field: every finitely
  generated `k`-subalgebra of a field extension of `k` is contained in a finitely generated one
  which is smooth over `k` (the image of `A_f`).

## References

* [EGA IV₄, 17.15.5], [EGA IV₂, 4.6.1]
* [Stacks Project, Tag 056V] (generic smoothness for varieties over perfect fields)
-/

namespace Algebra

/-- **Generic smoothness**: a finitely generated domain `A` over a perfect field `k` has a smooth
localization `A_f` with `f ≠ 0`. -/
theorem exists_ne_zero_smooth_localization_away (k A : Type*) [Field k] [PerfectField k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ f : A, f ≠ 0 ∧ Algebra.Smooth k (Localization.Away f) := by
  have : Algebra.FinitePresentation k A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : IsSmoothAt k (⊥ : Ideal A) :=
    (isSmoothAt_bot_iff_isGeometricallyReduced (F := FractionRing A)).mpr
      (IsGeometricallyReduced.of_perfectField_of_field k _)
  obtain ⟨f, hf, h⟩ := IsSmoothAt.exists_notMem_smooth k (⊥ : Ideal A)
  exact ⟨f, by simpa using hf, h⟩

end Algebra

namespace Subalgebra

/-- **Generic smoothness**, for subalgebras of a field: a finitely generated subalgebra `A` of a
field `K` over a perfect field `k` is contained in a finitely generated subalgebra `B` smooth
over `k` (the image of a smooth localization `A_f`, `f ≠ 0`). -/
theorem exists_le_fg_smooth {k K : Type*} [Field k] [PerfectField k] [Field K] [Algebra k K]
    (A : Subalgebra k K) (hA : A.FG) :
    ∃ B : Subalgebra k K, A ≤ B ∧ B.FG ∧ Algebra.Smooth k B := by
  have : Algebra.FiniteType k A := (Subalgebra.fg_iff_finiteType A).mp hA
  obtain ⟨f, hf, hsm⟩ := Algebra.exists_ne_zero_smooth_localization_away k A
  have hu : IsUnit (A.val f) := (map_ne_zero_iff _ Subtype.val_injective).mpr hf |>.isUnit
  let φ₀ : Localization.Away f →+* K := IsLocalization.Away.lift f hu
  have hφ₀ : ∀ a : A, φ₀ (algebraMap A _ a) = a := IsLocalization.Away.lift_eq f hu
  let φ : Localization.Away f →ₐ[k] K :=
    { φ₀ with
      commutes' := fun c ↦ by
        change φ₀ (algebraMap A _ (algebraMap k A c)) = _
        rw [hφ₀]
        rfl }
  have hinj : Function.Injective φ := by
    refine (IsLocalization.lift_injective_iff (M := Submonoid.powers f) _).mpr fun x y ↦ ?_
    have hle : Submonoid.powers f ≤ nonZeroDivisors A :=
      powers_le_nonZeroDivisors_of_noZeroDivisors hf
    rw [(IsLocalization.injective (Localization.Away f) hle).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have : Algebra.FiniteType A (Localization.Away f) :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) _
  have : Algebra.FiniteType k (Localization.Away f) := .trans (S := A) inferInstance inferInstance
  refine ⟨φ.range, fun a ha ↦ ⟨algebraMap A _ ⟨a, ha⟩, hφ₀ _⟩, ?_, ?_⟩
  · rw [← Algebra.map_top]
    exact (Algebra.FiniteType.out).map φ
  · exact Algebra.Smooth.of_equiv (AlgEquiv.ofInjective φ hinj)

end Subalgebra
