/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Resolution of two-dimensional schemes and regular models of curves (statements)

Interface statements of registry row A50 (work stream `semistable`), the first steps of the proof
of the semistable reduction theorem for curves after Artin–Winters, in the form written in the
Stacks Project (chapters 54 and 55):

* `AlgebraicGeometry.SurfaceResolutionStatement`: Lipman's theorem (Stacks, Tag 0BGP), for
  integral schemes of finite type and of dimension `≤ 2` over a complete noetherian local ring
  (such rings are excellent, so condition (4) of Tag 0BGP holds);
* `AlgebraicGeometry.RegularModelStatement`: a smooth proper geometrically connected curve over
  the fraction field of a complete discrete valuation ring has a regular proper flat model
  (Stacks, Tags 0C2U, 0C2W).

"Regular" is spelled out as "every local ring is a regular local ring" (mathlib's
`IsRegularLocalRing`); this is `SGA.SGA1.ExposeX.IsRegularScheme`, which Foundations cannot import.

The proofs are the work of row A50: blow-ups (`SGA.Foundations.Blowup.AffineAlgebra`, row A49),
normalized blow-ups, rational singularities and the boundedness argument of Stacks chapter 54,
and the excellence of schemes of finite type over a complete noetherian local ring.

## References

* [J. Lipman, *Desingularization of two-dimensional schemes*, Ann. of Math. 107 (1978)]
* [Stacks Project, Chapter 54 (Resolution of Surfaces), Tag 0BGP](https://stacks.math.columbia.edu/tag/0BGP)
* [Stacks Project, Chapter 55 (Semistable Reduction), Tags 0C2U, 0C2W](https://stacks.math.columbia.edu/tag/0C2W)
* [Q. Liu, *Algebraic Geometry and Arithmetic Curves*, 8.3.4 and 10.1]
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Lipman's resolution of singularities of two-dimensional schemes (Stacks, Tag 0BGP), for
schemes of finite type over a complete noetherian local ring `R` (for instance a field or a
complete discrete valuation ring). Let `Y` be an integral scheme of finite type over `Spec R`
whose local rings have Krull dimension `≤ 2`. There is a proper morphism `π : X ⟶ Y` from an
integral scheme `X` whose local rings are regular, such that `π` is an isomorphism over some
nonempty open subset of `Y` (so `π` is birational) and over every open subset of `Y` all of whose
points are regular.

Deviation from Tag 0BGP: Lipman's theorem is stated there for any two-dimensional integral
noetherian scheme satisfying condition (4) (finite normalization, finitely many singular points,
normal completions at them); here the scheme is of finite type over a complete noetherian local
ring, which implies (4) by excellence, and dimension `≤ 1` is allowed (normalization suffices
there). "Isomorphism over the regular locus" holds because a resolution by normalized blow-ups
only modifies the normalization at singular points (Stacks, Tag 0BGL). -/
def SurfaceResolutionStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (Y : Scheme.{u}) (h : Y ⟶ Spec (.of R))
    [LocallyOfFiniteType h] [QuasiCompact h] [IsIntegral Y],
    (∀ y : Y, ringKrullDim (Y.presheaf.stalk y) ≤ 2) →
    ∃ (X : Scheme.{u}) (π : X ⟶ Y), IsProper π ∧ IsIntegral X ∧
      (∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) ∧
      (∃ U : Y.Opens, (U : Set Y).Nonempty ∧ IsIso (π ∣_ U)) ∧
      ∀ U : Y.Opens, (∀ y ∈ U, IsRegularLocalRing (Y.presheaf.stalk y)) → IsIso (π ∣_ U)

/-- Regular models of curves (Stacks, Tags 0C2U and 0C2W; Liu, Prop. 10.1.8): let `R` be a complete
discrete valuation ring with fraction field `K`, and `X` a smooth proper geometrically connected
curve over `K`. There is a proper flat `R`-scheme `𝒳` whose local rings are all regular and whose
generic fibre `𝒳 ×_R K` is isomorphic to `X` over `K`.

Deviation from Stacks: Tag 0C2W is stated for any discrete valuation ring and gives a *minimal*
model; here `R` is complete (the case of `SemistableReductionStatement`) and only a regular
model is asserted. Minimality is a later step (Stacks, Tag 0CD9). -/
def RegularModelStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (K : Type u) [Field K] [Algebra R K]
    [IsFractionRing R K] (X : Scheme.{u}) (f : X ⟶ Spec (.of K)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [GeometricallyConnected f],
    ∃ (𝒳 : Scheme.{u}) (g : 𝒳 ⟶ Spec (.of R)), IsProper g ∧ Flat g ∧
      (∀ x : 𝒳, IsRegularLocalRing (𝒳.presheaf.stalk x)) ∧
      ∃ e : pullback g (Spec.map (CommRingCat.ofHom (algebraMap R K))) ≅ X,
        e.hom ≫ f = pullback.snd _ _

end AlgebraicGeometry
