/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.LocalComponents
import SGA.SGA1.ExposeX.TameLiftingBaseChange
import SGA.SGA1.ExposeXIII.RootAdjunction

/-!
# SGA 1, Exposé X, 3.7–3.8: the Kummer extension `V'' = V'[T]/(Tⁿ - u')`

In the proof of X.3.8 SGA adjoins an `n`-th root of a uniformizer `u` of the complete discrete
valuation ring `R` (`n` prime to `p`): `R_n = R[T]/(Tⁿ - u)` is again a complete discrete valuation
ring, finite over `R`, with the same residue field. The discrete valuation ring part is in
`SGA.SGA1.ExposeXIII.RootAdjunction`; we add completeness and the residue field, in the form
needed to compare `X_{R_n}` with `X`: for `X` proper and smooth over `R` with geometrically
connected fibres, base change of étale coverings along `X_{R_n} ⟶ X` is an equivalence
(`isEquivalence_pullback_adjoinRoot`).
-/

universe u

open IsLocalRing Polynomial CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeX

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (π : R) [Fact (Irreducible π)] (n : ℕ) [NeZero n]

/-- `R[T]/(Tⁿ - π)` is local over `R`. -/
instance : IsLocalHom (algebraMap R (AdjoinRoot (X ^ n - C π))) :=
  ExposeIII.isLocalHom_of_finite

/-- `R[T]/(Tⁿ - π)` is complete when `R` is (a local ring finite over a complete noetherian local
ring is complete). -/
instance [IsAdicComplete (maximalIdeal R) R] :
    IsAdicComplete (maximalIdeal (AdjoinRoot (X ^ n - C π))) (AdjoinRoot (X ^ n - C π)) :=
  ExposeIII.isAdicComplete_maximalIdeal_of_finite (A := R)

/-- The residue field extension of `R[T]/(Tⁿ - π)` over `R` is trivial: the residue field form of
`SGA.SGA1.ExposeXIII.algebraMap_quotient_surjective`. -/
theorem bijective_algebraMap_residueField_adjoinRoot :
    Function.Bijective
      (algebraMap (ResidueField R) (ResidueField (AdjoinRoot (X ^ n - C π)))) := by
  refine ⟨RingHom.injective _, fun w ↦ ?_⟩
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective w
  obtain ⟨c, hc⟩ := ExposeXIII.algebraMap_quotient_surjective π n (maximalIdeal _)
    (Ideal.Quotient.mk _ x)
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
  refine ⟨residue R a, ?_⟩
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver] at hc
  rw [IsLocalRing.ResidueField.algebraMap_residue]
  exact hc

instance : Module.Finite (ResidueField R) (ResidueField (AdjoinRoot (X ^ n - C π))) :=
  Module.Finite.of_surjective (Algebra.linearMap _ _)
    (bijective_algebraMap_residueField_adjoinRoot π n).2

instance : IsPurelyInseparable (ResidueField R) (ResidueField (AdjoinRoot (X ^ n - C π))) :=
  isPurelyInseparable_iff.mpr fun x ↦
    have ⟨y, hy⟩ := (bijective_algebraMap_residueField_adjoinRoot π n).2 x
    ⟨hy ▸ isIntegral_algebraMap, fun _ ↦ ⟨y, hy⟩⟩

/-- A step of the proof of X.3.8 (the comparison of the paragraph before X.3.7 for `V_n`): for
`R` a complete discrete valuation ring with uniformizer `π` and `Y` proper and
smooth over `R` with geometrically connected fibres, base change along `Y_{R_n} ⟶ Y`,
`R_n = R[T]/(Tⁿ - π)`, is an equivalence of the categories of étale coverings. -/
theorem isEquivalence_pullback_adjoinRoot [IsAdicComplete (maximalIdeal R) R] {Y : Scheme.{u}}
    (f : Y ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f] :
    (FEt.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdjoinRoot (X ^ n - C π))))))).IsEquivalence :=
  isEquivalence_pullback_baseChange_of_smooth R (AdjoinRoot (X ^ n - C π)) f

end SGA.SGA1.ExposeX
