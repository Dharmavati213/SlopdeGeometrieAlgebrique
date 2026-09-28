/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.RingTheory.Depth.Rees

/-!
# SGA 2, Exposé I → III: algebraic local cohomology (mathlib bridge)

Exposé I defines the topological functors `H_Z^*(X, F)` as derived functors of
`Γ_Z` (I.2.1). On an affine scheme `Spec R` with `Z = V(J)` and `F = M̃`, these
recover the algebraic local cohomology modules `H_J^i(M)`.

Mathlib already defines that algebraic avatar as a colimit of `Ext`-modules:

* `localCohomology J i` — colim_t Ext^i(R/J^t, -)
* `localCohomology.ofSelfLERadical J i` — same over all ideals with radical ≥ J
* `localCohomology.isoSelfLERadical`, `isoOfSameRadical` — comparison isomorphisms

Depth (Exposé III) is linked via the Rees theorem
`ModuleCat.exists_isRegular_tfae` in mathlib.

This file does **not** re-prove the comparison with sheaf-theoretic `H_Z^*`
(that is Exposé II); it imports the mathlib language under SGA numbering.
-/

universe u

open CategoryTheory

namespace SGA.SGA2.ExposeI

variable {R : Type u} [CommRing R]

/-- **I.2.1 (algebraic avatar):** the `i`-th local cohomology functor with support
in the closed set `V(J) ⊆ Spec R`. -/
noncomputable abbrev localCohomology (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  _root_.localCohomology J i

/-- **I.2.1:** local cohomology computed over all ideals with radical containing `J`. -/
noncomputable abbrev localCohomology_ofSelfLERadical (J : Ideal R) (i : ℕ) :
    ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  _root_.localCohomology.ofSelfLERadical J i

/-- Comparison of the two algebraic models (Noetherian case). -/
noncomputable abbrev localCohomology_isoSelfLERadical (J : Ideal R) [IsNoetherianRing R]
    (i : ℕ) :
    localCohomology_ofSelfLERadical J i ≅ localCohomology J i :=
  _root_.localCohomology.isoSelfLERadical J i

/-- Local cohomology depends only on the radical of the ideal (Noetherian case). -/
noncomputable abbrev localCohomology_isoOfSameRadical {J K : Ideal R} [IsNoetherianRing R]
    (h : J.radical = K.radical) (i : ℕ) :
    localCohomology J i ≅ localCohomology K i :=
  _root_.localCohomology.isoOfSameRadical h i

/-- **III (Rees / depth):** mathlib's Rees theorem relating Ext-vanishing to regular
sequences. Used from Exposé III onward; recorded here as the algebraic depth bridge
promised by the local-cohomology formalism of I.2. -/
abbrev exists_isRegular_tfae := @ModuleCat.exists_isRegular_tfae

end SGA.SGA2.ExposeI
