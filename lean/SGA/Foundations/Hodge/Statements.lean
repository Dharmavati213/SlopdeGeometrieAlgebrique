/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Hodge.Kahler

/-!
# Statements: Hodge symmetry `h^{0,q} = h^{q,0}` on compact Kähler manifolds

The analytic half of the transcendental input of SGA 1 XI.1.4 (registry row C19), recorded as a
`Prop` (the target of the Hodge theory in `Foundations/Hodge`):

* `Hodge.CompactKahlerHodgeSymmetryStatement`: on a compact (Hausdorff) complex manifold `M`
  admitting a Kähler form, for every `q` the space of holomorphic `q`-forms `H⁰(M, Ωᵍ)`
  (`Hodge.holomorphicForms`) and the Dolbeault cohomology `H^{0,q}_∂̄(M)`
  (`Hodge.dolbeaultCohomology`) are finite-dimensional, of the same dimension.

Classically (Hodge, Kodaira; Huybrechts, *Complex geometry*, Cor. 3.2.12; Voisin, *Hodge theory
and complex algebraic geometry I*, Thm. 6.11 and Cor. 6.12): every holomorphic form on a compact
Kähler manifold is `d`-closed and `η ↦ [η̄]` is a conjugate-linear isomorphism
`H⁰(M, Ωᵍ) ≅ H^{0,q}_∂̄(M)`. One inequality, `h^{q,0} ≤ h^{0,q}`, follows from Stokes' theorem and
the positivity of `i^{q²} η ∧ η̄ ∧ ωⁿ⁻ᵍ`; the other needs the Hodge theorem for the
`∂̄`-Laplacian (elliptic regularity) and the Kähler identities.

Together with the Dolbeault isomorphism `Hᵍ(M, 𝒪) ≅ H^{0,q}_∂̄(M)` (registry row C23), GAGA (row
A48), the complex manifold structure of `X(ℂ)` and the Fubini–Study form (row C25), it gives
`SGA.SGA1.ExposeXI.HodgeSymmetryZeroComplexStatement` (`SGA1/ExposeXI/HodgeSymmetryComplex.lean`).
-/

open scoped Manifold ContDiff

universe u v

namespace Hodge

/-- **Hodge symmetry `h^{0,q} = h^{q,0}` for compact Kähler manifolds** (statement only): for a
compact Hausdorff complex manifold `M` modelled on a finite-dimensional complex normed space `E`
(`ChartedSpace E M`, `IsManifold 𝓘(ℂ, E) ω M`) which admits a Kähler form, and every `q`, the
holomorphic `q`-forms and the Dolbeault cohomology `H^{0,q}_∂̄(M)` are finite-dimensional complex
vector spaces of the same dimension. -/
def CompactKahlerHodgeSymmetryStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (M : Type v) [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [CompactSpace M] [T2Space M], IsKahlerManifold E M → ∀ q : ℕ,
      FiniteDimensional ℂ (holomorphicForms E M q) ∧
        FiniteDimensional ℂ (dolbeaultCohomology E M 0 q) ∧
        Module.finrank ℂ (holomorphicForms E M q) =
          Module.finrank ℂ (dolbeaultCohomology E M 0 q)

end Hodge
