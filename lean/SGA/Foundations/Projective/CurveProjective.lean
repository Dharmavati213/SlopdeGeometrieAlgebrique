/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Formal.AmpleLiftProj
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Smooth proper curves over a field are finite and flat over `ℙ¹`

A smooth proper curve `X` over a field `k` has a finite flat `k`-morphism `X ⟶ ℙ¹_k`
(`SmoothProperCurveFiniteFlatStatement`). Classically: on each connected component (which is
integral, `X` being normal) choose a rational function `τ` transcendental over `k`; it extends to a
morphism to `ℙ¹_k` because the local rings of `X` are discrete valuation rings and `ℙ¹_k` is
proper (valuative criterion); the morphism is quasi-finite since no component is contracted, hence
finite by Zariski's main theorem (`IsFinite.of_isProper_of_locallyQuasiFinite`), and flat because
its local rings are torsion free over the discrete valuation rings of `ℙ¹_k`. In particular `X` is
projective and the union of the two affine opens `g⁻¹ D₊(x₀)`, `g⁻¹ D₊(x₁)`, with affine
intersection `g⁻¹ D₊(x₀ x₁)`.

This is the input of SGA 1 III.7.4 (lifting a smooth proper curve,
`SGA.SGA1.ExposeIII.SmoothProperCurveLiftStatement`) about the curve itself: SGA 1 III.7 uses that
such a curve is projective (and that `H²` of coherent sheaves on it vanishes).

## Main definitions

* `AlgebraicGeometry.SmoothProperCurveFiniteFlatStatement` (interface, wave 2 of the out-of-scope
  campaign, registry row A43). It is proved as
  `AlgebraicGeometry.smoothProperCurveFiniteFlatStatement` in `SGA.SGA1.ExposeIII.CurveLiftCurve`,
  since the proof uses facts proved in the SGA 1 files: smooth schemes are regular (SGA 1 II),
  rational maps from normal curves extend (SGA 1 X), and the points of a curve other than its
  generic point are closed (SGA 1 XIII).

## References

* [EGA II, 7.4][EGA2] (curves), [EGA III, 4.4.2] (Zariski's main theorem);
  [Hartshorne, II.6.7, II.6.8, III.9.7].
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open AmpleLift ProjectiveSpace

/-- **A smooth proper curve over a field is finite and flat over `ℙ¹`** (Hartshorne II.6.8 and
III.9.7, EGA II 7.4): for every field `k` and every smooth proper `f : X ⟶ Spec k` of relative
dimension `1`, there is a finite flat morphism `g : X ⟶ ℙ¹_k = Proj k[x₀, x₁]` over `Spec k`.
The curve `X` need not be connected. Proved as
`AlgebraicGeometry.smoothProperCurveFiniteFlatStatement` (`SGA.SGA1.ExposeIII.CurveLiftCurve`). -/
def SmoothProperCurveFiniteFlatStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f],
    ∃ g : X ⟶ Proj (grading Two.{u} k), IsFinite g ∧ Flat g ∧ g ≫ projToSpec Two.{u} k = f

end AlgebraicGeometry
