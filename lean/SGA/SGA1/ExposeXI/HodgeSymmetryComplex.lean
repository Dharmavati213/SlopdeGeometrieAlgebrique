/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.SerreUnirational
import SGA.SGA1.ExposeXI.UnirationalFormsZero
import SGA.Foundations.Ample
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# SGA 1 XI.1.4: Hodge symmetry `h^{0,q} = h^{q,0}` over `ℂ` (statement)

SGA 1 XI.1.4 quotes Serre's theorem: a smooth projective unirational variety over an algebraically
closed field of characteristic `0` is simply connected. Its only transcendental input is the
`(0, q)` case of Hodge symmetry, `HodgeSymmetryZeroStatement` (`SerreUnirational.lean`).

This file records the case that analytic Hodge theory proves, over `ℂ` and for projective `X`:

* `HodgeSymmetryZeroComplexStatement`: for a smooth projective integral `ℂ`-scheme `X`,
  `dim_ℂ Hᵍ(X, 𝒪_X) = dim_ℂ H⁰(X, Ω^q_{X/ℂ})`, with `H⁰(X, Ω^q)` written as `regularForms f q`.
  "Projective" is `IsProper f` together with `IsQuasiProjective f` (a relatively ample line
  bundle).

Its intended proof (registry row C19, stream `hodge`): GAGA (`Hᵍ(X, 𝒪_X) ≅ Hᵍ(X^an, 𝒪)` and
`H⁰(X, Ωᵍ) ≅ H⁰(X^an, Ωᵍ)`, row A48), the Dolbeault isomorphism (row C23), and Hodge theory on the
compact Kähler manifold `X(ℂ)` (Fubini–Study metric; rows C22, C24, C25):
`H^{0,q}_∂̄ ≅ conj H⁰(Ωᵍ)`. The analytic half is stated as
`Hodge.CompactKahlerHodgeSymmetryStatement` (`Foundations/Hodge/Statements.lean`).

Proved here:

* `hodgeSymmetryZeroComplexStatement_of_hodgeSymmetryZero`: the statement is the case `k = ℂ`
  (universe `0`), `X` projective, of `HodgeSymmetryZeroStatement` (the trivial direction; it is
  not progress on XI.1.4);
* `hodgeSymmetryZeroComplex_zero`: its case `q = 0`, which holds for every proper integral
  `X / ℂ` (neither smoothness nor projectivity is needed), from
  `finrankH_unit_zero_eq_finrank_regularForms_zero` (`UnirationalFormsZero.lean`).

Deviation from `HodgeSymmetryZeroStatement`: that statement quantifies over *proper* `X`. Hodge
theory on compact Kähler manifolds gives only projective `X`. For proper non-projective `X` one
needs in addition Chow's lemma and resolution of singularities (to reach a smooth projective
modification) or Deligne's purity (Hodge II); none of these is planned. SGA 1 XI.1.4 itself is
stated for projective `X`.
-/

open AlgebraicGeometry CategoryTheory

namespace SGA.SGA1.ExposeXI

/-- XI.1.4, transcendental input over `ℂ` (statement only): **Hodge symmetry** `h^{0,q} = h^{q,0}`
for a smooth projective integral scheme `X` over `ℂ`, i.e. `dim_ℂ Hᵍ(X, 𝒪_X) = dim_ℂ H⁰(X, Ωᵍ)`.
Here `Hᵍ(X, 𝒪_X)` carries the `ℂ`-structure of `Scheme.Modules.finrankH`, `H⁰(X, Ωᵍ)` is
`regularForms f q` (the forms of `Ωᵍ_{ℂ(X)/ℂ}` regular at every point), and "projective" means
`IsProper f` and `IsQuasiProjective f`. This is the special case `k = ℂ`, `X` projective, of
`HodgeSymmetryZeroStatement` (`hodgeSymmetryZeroComplexStatement_of_hodgeSymmetryZero`); it is the
case analytic Hodge theory proves (GAGA, Dolbeault, harmonic forms for the Fubini–Study metric). -/
def HodgeSymmetryZeroComplexStatement : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [IsProper f] [IsQuasiProjective f]
    [Smooth f] (q : ℕ),
    letI := (functionFieldMap f).toAlgebra
    Scheme.Modules.finrankH f (CohomologyAux.unitModule X) q =
      Module.finrank ℂ (regularForms f q)

/-- `HodgeSymmetryZeroComplexStatement` is the case `k = ℂ`, `X` projective, of
`HodgeSymmetryZeroStatement` (in universe `0`). -/
theorem hodgeSymmetryZeroComplexStatement_of_hodgeSymmetryZero
    (h : HodgeSymmetryZeroStatement.{0}) : HodgeSymmetryZeroComplexStatement := by
  intro X _ f _ _ _ q
  exact h ℂ X f q

/-- The case `q = 0` of `HodgeSymmetryZeroComplexStatement`, unconditionally: for a proper
integral scheme `X` over `ℂ`, `dim_ℂ H⁰(X, 𝒪_X) = dim_ℂ H⁰(X, Ω⁰) (= 1)`. Neither smoothness nor
projectivity is needed. -/
theorem hodgeSymmetryZeroComplex_zero (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℂ))
    [IsProper f] :
    letI := (functionFieldMap f).toAlgebra
    Scheme.Modules.finrankH f (CohomologyAux.unitModule X) 0 =
      Module.finrank ℂ (regularForms f 0) :=
  finrankH_unit_zero_eq_finrank_regularForms_zero f

end SGA.SGA1.ExposeXI
