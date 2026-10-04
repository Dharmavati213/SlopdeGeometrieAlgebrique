/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.PuncturedDisc
import SGA.Foundations.Topology.FiniteCoveringMonodromy
import SGA.Foundations.Topology.PathConnectedHelpers

/-!
# Connected finite coverings of a punctured disc are Kummer coverings

`Complex.exists_homeomorph_powRestrict` classifies the finite coverings of `B ⊆ ℂ ∖ {0}` (with
`exp⁻¹(B)` simply connected, e.g. a punctured disc) on which the monodromy is transitive. Here
is the form with a connectedness hypothesis on the total space instead:
`Complex.exists_homeomorph_powRestrict_of_connectedSpace`. A covering space of the locally
path-connected space `B` is locally path-connected, so a connected one is path-connected, and
then the monodromy is transitive (`TopCat.FiniteCovering.exists_monodromy_eq`).

## References

* [O. Forster, *Lectures on Riemann Surfaces*, Theorem 5.10][forster1981]
-/

open Set Topology CategoryTheory

namespace Complex

variable {B : Set ℂ}

/-- **Connected finite coverings of a punctured disc are Kummer coverings.** Let `B ⊆ ℂ ∖ {0}` be
open with `exp⁻¹(B)` simply connected (e.g. a punctured disc, `ℂ ∖ {0}`, an annulus), and let
`p : E → B` be a covering map with finite fibres and connected total space `E`. Then for some
`n ≠ 0` there is a homeomorphism `φ : E ≃ₜ {w | wⁿ ∈ B}` with `p = φⁿ`. -/
theorem exists_homeomorph_powRestrict_of_connectedSpace (hBo : IsOpen B) (hB0 : (0 : ℂ) ∉ B)
    (hS : IsSimplyConnected (exp ⁻¹' B)) {E : Type} [TopologicalSpace E] [ConnectedSpace E]
    {p : E → B} (hp : IsCoveringMap p) (hfin : ∀ b, (p ⁻¹' {b}).Finite) :
    ∃ (n : ℕ) (_ : n ≠ 0) (φ : E ≃ₜ {w : ℂ // w ^ n ∈ B}),
      ∀ x, powRestrict B n (φ x) = p x := by
  have : LocallyPathConnectedSpace B := hBo.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace E := hp.isLocalHomeomorph.locallyPathConnectedSpace
  have hE : PathConnectedSpace E := .of_locallyPathConnectedSpace
  refine exists_homeomorph_powRestrict hBo hB0 hS hp hfin fun b e₁ e₂ ↦ ?_
  let EC : TopCat.FiniteCovering (TopCat.of B) :=
    ⟨Over.mk (TopCat.ofHom ⟨p, hp.continuous⟩), hp, hfin⟩
  have : PathConnectedSpace EC.obj.left := hE
  exact TopCat.FiniteCovering.exists_monodromy_eq (X := TopCat.of B) b EC e₁ e₂

end Complex
