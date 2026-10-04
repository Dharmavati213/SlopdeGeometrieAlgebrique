/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.SerreUnirational
import SGA.SGA1.ExposeXI.HodgeSymmetryComplex
import SGA.Foundations.Projective.LineBundle

/-!
# Serre's theorem XI.1.4 for projective varieties, over `ℂ`

SGA 1 XI.1.4 (Serre) is stated for a smooth **projective** unirational variety `X` over an
algebraically closed field of characteristic `0`. The repository's
`SerreUnirationalSimplyConnectedStatement` (`Geometry.lean`) is the stronger form for proper `X`;
its only open input is Hodge symmetry for proper `X`, which analytic Hodge theory does not give
(for proper non-projective `X` one needs Chow's lemma plus resolution of singularities, or
Deligne's Hodge II). This file records SGA's form, and proves it over `ℂ` from the case of Hodge
symmetry that Hodge theory on compact Kähler manifolds proves.

* `SerreUnirationalProjectiveStatement`: XI.1.4 as stated in SGA. "Projective" over the field `k`
  is rendered as `IsProper f` together with `IsQuasiProjective f` (a relatively ample line
  bundle), which is EGA II 5.5.3's characterization of projective morphisms over an affine base;
  H-projective morphisms (closed subschemes of `ℙⁿ_k`, `IsHProjective`) satisfy both
  (`IsHProjective.isProper`, `IsHProjective.isQuasiProjective`).
* `serreUnirationalProjectiveStatement_of_serreUnirationalSimplyConnectedStatement`: the proper
  form implies SGA's form.
* `isSimplyConnected_of_hodgeSymmetryZeroComplex`: **XI.1.4 over `ℂ`** (universe `0`), given
  `HodgeSymmetryZeroComplexStatement` (Hodge symmetry `h^{0,q} = h^{q,0}` for smooth projective
  integral `ℂ`-schemes; stated in `HodgeSymmetryComplex.lean`, to be proved by stream `hodge`).
  Serre's argument (`isSimplyConnected_of_forall_subsingleton_H`) applies Hodge symmetry to `X`
  and to its integral finite étale coverings `Y ⟶ X`; these are again projective
  (`IsQuasiProjective.comp_of_isAffineHom`: the inverse image of an ample line bundle under a
  finite morphism is ample) and unirational (`isUnirational_of_isFinite_of_etale`).

The passage from `ℂ` to an arbitrary algebraically closed field of characteristic `0` (the
Lefschetz principle) is in `HodgeLefschetz.lean`.
-/

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeXI

/-- **XI.1.4** (Serre), as stated in SGA (statement only): a smooth projective integral scheme `X`
over an algebraically closed field `k` of characteristic `0` whose function field is unirational
over `k` is simply connected. "Projective" is rendered as `IsProper f` and `IsQuasiProjective f`
(proper with a relatively ample line bundle, EGA II 5.5.3); closed subschemes of `ℙⁿ_k`
(`IsHProjective f`) are covered. The form for proper `X` is
`SerreUnirationalSimplyConnectedStatement`, which implies this one
(`serreUnirationalProjectiveStatement_of_serreUnirationalSimplyConnectedStatement`). -/
def SerreUnirationalProjectiveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (X : Scheme.{u}) [IsIntegral X]
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsQuasiProjective f] [Smooth f],
    (letI := (functionFieldMap f).toAlgebra; IsUnirational k X.functionField) →
    IsSimplyConnected X

/-- The proper form of XI.1.4 (`SerreUnirationalSimplyConnectedStatement`) implies SGA's
projective form. -/
theorem serreUnirationalProjectiveStatement_of_serreUnirationalSimplyConnectedStatement
    (h : SerreUnirationalSimplyConnectedStatement.{u}) :
    SerreUnirationalProjectiveStatement.{u} :=
  fun k _ _ _ X _ f _ _ _ hX ↦ h k X f hX

/-- **XI.1.4 over `ℂ`**, conditional on Hodge symmetry over `ℂ`
(`HodgeSymmetryZeroComplexStatement`, not proved yet): a smooth projective (proper and
quasi-projective) integral `ℂ`-scheme `X` (in universe `0`) with unirational function field is
simply connected. Hodge symmetry and the vanishing of regular forms
(`subsingleton_H_of_finrankH_eq`) give `H^q(𝒪) = 0` for `q > 0` on `X` and on each integral
finite étale covering `Y ⟶ X`, which is again smooth, projective and unirational; then Serre's
Euler characteristic argument applies (`isSimplyConnected_of_forall_subsingleton_H`). -/
theorem isSimplyConnected_of_hodgeSymmetryZeroComplex (hC : HodgeSymmetryZeroComplexStatement)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℂ)) [IsProper f] [IsQuasiProjective f]
    [Smooth f] (h : letI := (functionFieldMap f).toAlgebra; IsUnirational ℂ X.functionField) :
    IsSimplyConnected X := by
  refine isSimplyConnected_of_forall_subsingleton_H f fun Y π _ _ _ q ↦ ?_
  have : IsQuasiProjective (π ≫ f) := IsQuasiProjective.comp_of_isAffineHom π f
  exact subsingleton_H_of_finrankH_eq (π ≫ f) (isUnirational_of_isFinite_of_etale f π h) q
    (hC Y (π ≫ f) (q + 1))

end SGA.SGA1.ExposeXI
