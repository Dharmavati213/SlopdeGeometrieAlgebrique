/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.BaseChange
import SGA.Foundations.Etale.Points

/-!
# SGA 1, Exposé XIII, §1.0: direct and inverse images of étale sheaves, base change

Exposé XIII works with the direct image `f_*` and the inverse image `f^*` of sheaves on small
étale sites, and with the base change morphism `g^* f_* F ⟶ f'_* h^* F` attached to a square
```
X' --h--> X
|f'       |f
Y' --g--> Y
```
(XIII 1.0.1, 1.2.1). These are constructed for sheaves of sets in
`SGA.Foundations.Etale.Functoriality` (`Scheme.etalePushforward`, `Scheme.etalePullback`,
`Scheme.etaleAdjunction`), `SGA.Foundations.Etale.BaseChange` (`Scheme.etaleBaseChangeMap` and
the pasting formulas `Scheme.etaleBaseChangeMap_comp_app`, used in the proof of XIII 1.6, and
`Scheme.etaleBaseChangeMap_comp_horiz_app`) and `SGA.Foundations.Etale.Points` (left exactness
of `f^*`, and conservativity of the inverse images along an étale covering).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace SGA.SGA1.ExposeXIII

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {h : X' ⟶ X} {f' : X' ⟶ Y'}

/-- XIII (1.2.1): the base change morphism `g^* f_* F ⟶ f'_* h^* F` of a commutative square
`h ≫ f = f' ≫ g` is `Scheme.etaleBaseChangeMap`, the mate of the canonical morphism
`h_* ⋙ f_* ⟶ f'_* ⋙ g_*` for the adjunctions `h^* ⊣ h_*` and `g^* ⊣ g_*`. -/
theorem etaleBaseChangeMap_eq (w : h ≫ f = f' ≫ g) :
    Scheme.etaleBaseChangeMap w = (mateEquiv (Scheme.etaleAdjunction h)
      (Scheme.etaleAdjunction g)).symm (Scheme.etalePushforwardComparison w) :=
  rfl

end SGA.SGA1.ExposeXIII
