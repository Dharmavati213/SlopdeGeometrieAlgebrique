/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.FiniteCovering
import Mathlib.Topology.Homotopy.Lifting

/-!
# Transitivity of monodromy on a path-connected finite covering

If the total space of a finite covering `E → X` is path-connected, then `π₁(X, x)` acts
transitively on the fibre over `x` by monodromy: lift a path between two points of the fibre and
push it down to a loop at `x`.
-/

universe u

open CategoryTheory

namespace TopCat.FiniteCovering

variable {X : TopCat.{u}}

/-- On a finite covering with path-connected total space, the monodromy action of `π₁(X, x)` on
the fibre at `x` is transitive. -/
theorem exists_monodromy_eq (x : X) (E : FiniteCovering X) [PathConnectedSpace E.obj.left]
    (e₁ e₂ : E.obj.hom ⁻¹' {x}) :
    ∃ γ : FundamentalGroup X x, E.isCoveringMap.monodromy γ e₁ = e₂ := by
  let δ : Path e₁.1 e₂.1 := PathConnectedSpace.somePath _ _
  let γ : Path.Homotopic.Quotient (E.obj.hom e₁.1) (E.obj.hom e₂.1) :=
    (Path.Homotopic.Quotient.mk δ).map E.obj.hom.hom
  have h₁ : E.obj.hom e₁.1 = x := e₁.2
  have h₂ : E.obj.hom e₂.1 = x := e₂.2
  refine ⟨γ.cast h₁.symm h₂.symm, ?_⟩
  refine E.isCoveringMap.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk δ) ?_
  change _ = (γ.cast h₁.symm h₂.symm).cast h₁ h₂
  rw [Path.Homotopic.Quotient.cast_cast]
  exact (Path.Homotopic.Quotient.cast_rfl_rfl _).symm

end TopCat.FiniteCovering
