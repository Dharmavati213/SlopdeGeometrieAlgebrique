/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.EulerCharacteristic
import SGA.Foundations.Limits.GeometricFiberCard
import SGA.Foundations.Cohomology.QuasiCoherentLocal

/-!
# The Euler characteristic of `𝒪` in finite étale coverings

Let `X` be proper over a field `k` and `π : Y ⟶ X` finite étale of constant degree `d` (every
geometric fibre has `d` points, `Scheme.Hom.geometricFiberCard`). Then
`χ(Y, 𝒪_Y) = d · χ(X, 𝒪_X)` (`EulerCharFiniteEtaleStatement`), in every characteristic.

This file only states it. The statement is proved in
`SGA.Foundations.Cohomology.EulerCharacteristicFiniteEtaleProof`
(`AlgebraicGeometry.eulerCharFiniteEtaleStatement`, with the strong form
`Scheme.Modules.eulerChar_pullback_eq_mul` for every coherent `F`), by an elementary dévissage
(Stacks Tag 01YF) instead of Riemann–Roch: `Δ(F) = χ(Y, π^*F) - d χ(X, F)` is additive, vanishes
on modules supported in lower dimension by induction, so equals `rk(F) Δ(𝒪_X)` on an integral
`X`; and `Δ(π_* 𝒪_Y) = 0` by induction on `d`, since `Y ×_X Y = Δ(Y) ⊔ Y'` with `Y' ⟶ Y` finite
étale of degree `d - 1` (`Scheme.Hom.diagonalComplFst`).
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- **Multiplicativity of `χ(𝒪)` in finite étale coverings**: for `X` proper over a field `k` and
`π : Y ⟶ X` finite étale whose geometric fibres all have `d` points,
`χ(Y, 𝒪_Y) = d · χ(X, 𝒪_X)`, in every characteristic. Proved by dévissage (Stacks Tag 01YF) as
`AlgebraicGeometry.eulerCharFiniteEtaleStatement` (`EulerCharacteristicFiniteEtaleProof`). -/
def EulerCharFiniteEtaleStatement : Prop :=
  ∀ (k : Type u) [Field k] (X Y : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    (π : Y ⟶ X) [IsFinite π] [Etale π] (d : ℕ), (∀ x : X, π.geometricFiberCard x = d) →
    Scheme.Modules.eulerChar (π ≫ f) (CohomologyAux.unitModule Y) =
      d * Scheme.Modules.eulerChar f (CohomologyAux.unitModule X)

end AlgebraicGeometry
