/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.Topology.Constructible
import SGA.Foundations.Limits.PropertiesLimit

/-!
# Constructibility of properties of geometric fibres: statements

The interface statements of EGA IV 9.7.7 (registry row A40 of
`notes/topics/out-of-scope-plan.md`).

* `AlgebraicGeometry.Scheme.GeometricFibresConstructibleStatement` (EGA IV 9.7.7): for `f` of
  finite presentation, the sets of points of the base over which the fibre is geometrically
  connected, geometrically reduced, geometrically irreducible are locally constructible.
* `AlgebraicGeometry.Scheme.GeometricallyConnectedLimitStatement`: EGA IV 8.10.5 for the property
  "geometrically connected fibres" (`GeometricallyConnected`), the form SGA uses to reduce IX.6.8
  and IX.6.11 to a noetherian base (those are now proved without it,
  `SGA.SGA1.ExposeIX.ProperDescentGeneral`); it follows from 9.7.7 and the limit lemmas on
  constructible sets (EGA IV 8.3.4):
  `Scheme.geometricallyConnectedLimitStatement_of_geometricFibresConstructible`, in
  `SGA.Foundations.Limits.FibrePropertiesLimit`, conditional on 9.7.7.

Neither statement is proved.

mathlib's `GeometricallyConnected f` asks that every fibre `X ×_S Spec K` be connected, in
particular nonempty: it implies that `f` is surjective. This differs from the convention that the
empty space is connected only over points outside the image of `f`, a constructible set when `f`
is of finite presentation (Chevalley, `Scheme.Hom.isLocallyConstructible_image`), so the
constructibility statements are unaffected.

## References

* [EGA IV₃, 9.7.7][EGA4]; [EGA IV₃, 8.3.4, 8.10.5][EGA4]
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-- EGA IV 9.7.7, statement: let `f : X ⟶ S` be of finite presentation (locally of finite
presentation, quasi-compact and quasi-separated). The sets of points `s ∈ S` such that the fibre
`X_s` is geometrically connected, resp. geometrically reduced, resp. geometrically irreducible over
`κ(s)` are locally constructible in `S`. (EGA 9.7.7 also treats geometrically integral fibres and
the number of geometric connected or irreducible components; they are not stated.) -/
def Scheme.GeometricFibresConstructibleStatement : Prop :=
  ∀ ⦃X S : Scheme.{u}⦄ (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f]
    [QuasiSeparated f],
    IsLocallyConstructible {s : S | GeometricallyConnected (f.fiberToSpecResidueField s)} ∧
      IsLocallyConstructible {s : S | GeometricallyReduced (f.fiberToSpecResidueField s)} ∧
      IsLocallyConstructible {s : S | GeometricallyIrreducible (f.fiberToSpecResidueField s)}

/-- EGA IV 8.10.5 and 9.7.7 for geometrically connected fibres, statement: over the limit of a
cofiltered diagram of quasi-compact and quasi-separated schemes with affine transition maps, a
morphism of finite presentation `X_j ⟶ E j` whose base change to the limit has geometrically
connected fibres (mathlib's `GeometricallyConnected`, which includes nonempty fibres) has a base
change to some `E k` with geometrically connected fibres. -/
def Scheme.GeometricallyConnectedLimitStatement : Prop :=
  Scheme.LimitDescendsStatement.{u} @GeometricallyConnected

end AlgebraicGeometry
