/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Desingularization
import SGA.SGA1.ExposeX.CurveFiniteSmooth
import SGA.SGA1.ExposeXIII.LocalAcyclicity

/-!
# Desingularization of curves over a perfect field

EGA IV 7.9.1 in dimension `≤ 1` (`SGA.SGA1.ExposeXIII.desingularizableUpTo_one`): over a perfect
field `k`, every integral scheme `Z` of finite type over `k` of dimension `≤ 1` is desingularizable,
by its normalization `ν : Z' ⟶ Z` (the normalization of `Z` in its function field,
`SGA.Foundations.NormalizationFinite`):

* `ν` is finite (E. Noether,
  `AlgebraicGeometry.isFinite_fromNormalization_fromSpecStalk_genericPoint`), hence proper;
* `Z'` is integral, with integrally closed noetherian local rings of dimension `≤ dim Z ≤ 1`,
  i.e. fields or discrete valuation rings, hence regular (`isRegularScheme_normalization`, from
  `SGA.SGA1.ExposeX.isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one`);
* `ν` is an isomorphism over a nonempty open (`AlgebraicGeometry.isIso_fromNormalization_restrict`
  and `AlgebraicGeometry.exists_isAffineOpen_isIntegrallyClosed`, in
  `SGA.Foundations.Desingularization`).

Over a non-perfect field the normalization is not known to be finite here (E. Noether's theorem
`Algebra.FiniteType.finite_integralClosure` is only proved for perfect fields); XIII 3.3 and 3.4 use
the hypothesis over an algebraic closure, which is perfect. The strong form (SGA 5 I 3.1.5,
`StronglyDesingularizableUpTo`) for curves is `SGA.SGA1.ExposeXIII.stronglyDesingularizableUpTo_one`
(`SGA.SGA1.ExposeXIII.DesingularizationCurvesStrong`).

## References

* [EGA IV, 7.9.1][EGA4]; [EGA II, 6.3][EGA2]
-/

universe u

open CategoryTheory Limits AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

section Scheme

variable {Z : Scheme.{u}} [IsIntegral Z]

/-- `Spec K(Z) ⟶ Z`, the generic point of the integral scheme `Z`. -/
local notation "η" => Z.fromSpecStalk (genericPoint Z)

variable {k : Type u} [Field k] [PerfectField k] (p : Z ⟶ Spec (.of k)) [LocallyOfFiniteType p]

include p in
/-- The normalization of an integral scheme of dimension `≤ 1` of finite type over a perfect field
is regular: its local rings are noetherian, integrally closed, of dimension `≤ 1`, hence principal
ideal rings
(`SGA.SGA1.ExposeX.isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one`). -/
theorem isRegularScheme_normalization (hZ : topologicalKrullDim Z ≤ 1) :
    ExposeX.IsRegularScheme (η).normalization := by
  have : IsFinite (η).fromNormalization := isFinite_fromNormalization_fromSpecStalk_genericPoint p
  have : IsLocallyNoetherian (η).normalization :=
    LocallyOfFiniteType.isLocallyNoetherian ((η).fromNormalization ≫ p)
  have hdim : topologicalKrullDim (η).normalization ≤ 1 :=
    ((η).fromNormalization.topologicalKrullDim_le_of_locallyQuasiFinite).trans hZ
  intro z
  have : IsIntegrallyClosed ((η).normalization.presheaf.stalk z) :=
    isIntegrallyClosed_stalk_normalization_fromSpecStalk_genericPoint z
  have := ExposeX.isPrincipalIdealRing_of_isIntegrallyClosed_of_ringKrullDim_le_one
    ((ExposeX.ringKrullDim_stalk_le_topologicalKrullDim z).trans hdim)
  infer_instance

include p in
/-- **EGA IV 7.9.1 in dimension `≤ 1`**: an integral scheme of finite type over a perfect field of
dimension `≤ 1` is desingularizable, by its normalization. -/
theorem isDesingularizable_of_topologicalKrullDim_le_one (hZ : topologicalKrullDim Z ≤ 1) :
    IsDesingularizable Z := by
  obtain ⟨V, hV, hne, hic⟩ := exists_isAffineOpen_isIntegrallyClosed p
  have : Nonempty V := hne.to_subtype
  have : IsFinite (η).fromNormalization := isFinite_fromNormalization_fromSpecStalk_genericPoint p
  exact ⟨(η).normalization, (η).fromNormalization, inferInstance, inferInstance,
    isRegularScheme_normalization p hZ, V, hne, isIso_fromNormalization_restrict hV⟩

end Scheme

/-- **EGA IV 7.9.1 in dimension `≤ 1`** (the hypothesis of XIII.3.3 and 3.4 for relative curves):
over a perfect field `k`, the integral schemes of finite type of dimension `≤ 1` are
desingularizable. -/
theorem desingularizableUpTo_one (k : Type u) [Field k] [PerfectField k] :
    DesingularizableUpTo k 1 :=
  fun _ p _ _ _ hZ ↦ isDesingularizable_of_topologicalKrullDim_le_one p hZ

/-- XIII.3.4 a) for `dim X ≤ 1` without its desingularization hypothesis, given XIII.3.4
(`FieldLocalAsphericityStatement`): over any field `k`, a coherent morphism `f : X ⟶ Spec k` of
finite type with `dim X ≤ 1` is universally locally `1`-aspherical for the primes different from
the characteristic (the hypothesis holds by `desingularizableUpTo_one` over an algebraic closure of
`k`). -/
theorem isUniversallyLocallyOneAspherical_of_fieldLocalAsphericityStatement_of_dim_le_one
    (h : FieldLocalAsphericityStatement.{u}) (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f] [LocallyOfFiniteType f]
    (hX : topologicalKrullDim X ≤ 1) :
    IsUniversallyLocallyOneAspherical (primesInvertibleOn (Spec (.of k))) f :=
  h k f (Or.inl ⟨inferInstance, (desingularizableUpTo_one (AlgebraicClosure k)).mono hX⟩)

/-- XIII.3.3 for relative curves without its desingularization hypothesis, given XIII.3.3
(`GenericLocalAsphericityStatement`): for `S` irreducible and `f : X ⟶ S` of finite presentation
whose generic fibre has dimension `≤ 1`, `f` is universally locally `1`-aspherical, for the primes
invertible on `S`, over a nonempty open of `S`. -/
theorem exists_isUniversallyLocallyOneAspherical_of_genericLocalAsphericityStatement_of_dim_le_one
    (h : GenericLocalAsphericityStatement.{u}) {X S : Scheme.{u}} [IrreducibleSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (hX : topologicalKrullDim
      ↥(pullback f (S.fromSpecResidueField (genericPoint S)) : Scheme.{u}) ≤ 1) :
    ∃ S₁ : S.Opens, (S₁ : Set S).Nonempty ∧
      IsUniversallyLocallyOneAspherical (primesInvertibleOn S) (pullback.snd f S₁.ι) :=
  h f ((desingularizableUpTo_one _).mono hX)

end SGA.SGA1.ExposeXIII
