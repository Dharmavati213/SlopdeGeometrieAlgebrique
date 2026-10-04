/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.Cohomology.EulerCharacteristic
import SGA.Foundations.Etale.Picard

/-!
# Torsion in the Picard group of a curve (statement)

Interface statement of registry row A51 (work stream `semistable`): for a smooth proper connected
curve `X` of genus `g` over an algebraically closed field `k` and `n` invertible in `k`,
`Pic(X)[n] ≅ (ℤ/n)^{2g}` (Stacks, Tag 0C1Z (1)). It is one of the two inequalities behind the
semistable reduction theorem in genus `≥ 2` (Stacks, Tag 0CEI), used both for the generic fibre
and, through the normalization, for the components of the special fibre (Stacks, Tag 0C20).

The genus is `Scheme.Hom.genus f = h¹(X, 𝒪_X)` and `Pic X = H¹(X_Zar, 𝒪_X^×)`
(`AlgebraicGeometry.Scheme.Pic`).

Stacks proves Tag 0C1Z with the Picard scheme: `Pic⁰` is an abelian variety of dimension `g`. In
this repository the intended route is Kummer theory (`ExposeXI.kummer_exact_pic`: `Pic(X)[n]` is
`H¹(X, μ_n)` for `X` proper and connected over `k = k̄`) together with `π₁` of curves (XIII.2.12,
registry rows of `xiii212`): `H¹(X, μ_n) = Hom(π₁(X), ℤ/n) = (ℤ/n)^{2g}`.

## References

* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
* [D. Mumford, *Abelian varieties*, §4, §6]
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Stacks, Tag 0C1Z (1) (statement): let `k` be an algebraically closed field, `X` a smooth proper
connected curve over `k`, of genus `g = h¹(X, 𝒪_X)` (`Scheme.Hom.genus`), and `n` an integer
invertible in `k`. The `n`-torsion subgroup of `Pic X` is isomorphic to `(ℤ/n)^{2g}`. -/
def PicTorsionCurveStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [IsProper f]
    [SmoothOfRelativeDimension 1 f] [ConnectedSpace X] (n : ℕ), (n : k) ≠ 0 →
    Nonempty ((powMonoidHom n : X.Pic →* X.Pic).ker ≃*
      Multiplicative (Fin (2 * f.genus) → ZMod n))

end AlgebraicGeometry
