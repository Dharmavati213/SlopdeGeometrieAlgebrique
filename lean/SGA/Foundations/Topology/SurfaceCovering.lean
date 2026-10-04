/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

/-!
# The fundamental group of a covering space

For a covering map `p : E → X` and `e ∈ E`, the induced map `π₁(E, e) → π₁(X, p e)` is injective
(mathlib's `IsCoveringMap.injective_path_homotopic_map`) and its image is the stabilizer of `e`
for the monodromy action of `π₁(X, p e)` on the fibre (`IsCoveringMap.range_map_eq_stabilizer`).
If `E` is path-connected, the monodromy action on the fibre is transitive
(`IsCoveringMap.exists_smul_eq`).

## References

* [A. Hatcher, *Algebraic Topology*, Proposition 1.31 and §1.3][hatcher02]
-/

open Topology

namespace IsCoveringMap

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}
  (cov : IsCoveringMap p)

/-- The map induced by a covering map on fundamental groups is injective. -/
theorem map_fundamentalGroup_injective (e : E) :
    Function.Injective (FundamentalGroup.map ⟨p, cov.continuous⟩ e) :=
  cov.injective_path_homotopic_map e e

/-- **The image of `π₁(E, e)` is the stabilizer of `e`** for the monodromy action of
`π₁(X, p e)` on the fibre over `p e`. -/
theorem range_map_eq_stabilizer (e : E) :
    (FundamentalGroup.map ⟨p, cov.continuous⟩ e).range =
      @MulAction.stabilizer _ _ _ (cov.fundamentalGroupMulAction (p e)) ⟨e, rfl⟩ := by
  let := cov.fundamentalGroupMulAction (p e)
  ext γ
  constructor
  · rintro ⟨γ', rfl⟩
    exact cov.monodromy_map γ'
  · intro h
    have h' : (cov.monodromy γ ⟨e, rfl⟩ : E) = e := congrArg Subtype.val h
    refine ⟨(cov.liftPathQuotient γ ⟨e, rfl⟩).cast rfl h'.symm, ?_⟩
    change ((cov.liftPathQuotient γ ⟨e, rfl⟩).cast rfl h'.symm).map ⟨p, cov.continuous⟩ = γ
    rw [Path.Homotopic.Quotient.map_cast, cov.map_liftPathQuotient]
    exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq _ _).trans
      (Path.Homotopic.Quotient.cast_heq _ _))

/-- An element `γ` of `π₁(X, p e)` lies in the image of `π₁(E, e)` if and only if its monodromy
fixes `e`. -/
theorem mem_range_map_iff (e : E) (γ : FundamentalGroup X (p e)) :
    γ ∈ (FundamentalGroup.map ⟨p, cov.continuous⟩ e).range ↔
      cov.monodromy γ ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
  rw [cov.range_map_eq_stabilizer]
  rfl

/-- **Transitivity of the monodromy action** on the fibre of a path-connected covering space. -/
theorem exists_smul_eq [PathConnectedSpace E] {x : X} (e e' : p ⁻¹' {x}) :
    ∃ γ : FundamentalGroup X x, cov.monodromy γ e = e' := by
  let δ := PathConnectedSpace.somePath (e : E) e'
  refine ⟨((Path.Homotopic.Quotient.mk δ).map ⟨p, cov.continuous⟩).cast e.2.symm e'.2.symm, ?_⟩
  exact cov.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk δ) rfl

end IsCoveringMap
