/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import SGA.SGA1.ExposeII.Permanence

/-!
# Smooth morphisms are geometrically reduced

A smooth morphism `f : X ⟶ S` is geometrically reduced: for every field `K` and every
`Spec K ⟶ S`, the base change `X ×_S Spec K` is smooth over `Spec K`, hence reduced
(EGA IV 17.5.7, Stacks 056T and 033B).

The reducedness of a scheme smooth over a reduced locally noetherian scheme is
`SGA.SGA1.ExposeII.isReduced_of_smooth_of_isReduced`, which only depends on mathlib; we import
it rather than reprove it.

## Main results

* `AlgebraicGeometry.Smooth.geometricallyReduced`: `Smooth f → GeometricallyReduced f`
  (an instance).
-/

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A smooth morphism is geometrically reduced (EGA IV 17.5.7, Stacks 056T): every base change to
the spectrum of a field is smooth over that field, hence reduced. -/
instance (priority := 100) Smooth.geometricallyReduced {X S : Scheme.{u}} (f : X ⟶ S)
    [Smooth f] : GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd hpb ↦ ?_⟩
  have : Smooth snd := MorphismProperty.of_isPullback hpb ‹Smooth f›
  exact SGA.SGA1.ExposeII.isReduced_of_smooth_of_isReduced snd

end AlgebraicGeometry
