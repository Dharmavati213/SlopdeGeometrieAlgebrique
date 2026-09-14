/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeI.NestedSupportLocallyClosed

/-!
# Nested support indexed by the literal locally closed subspace

The support space inside an open witness is canonically homeomorphic to
the literal subset of the ambient space. Thus I.1.10 and I.2.8 accept any
closed subset of that literal subspace, with no extra presentation data.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat

namespace SGA.SGA2.ExposeI

variable {X : TopCat.{u}}

/-- Flattening the two actual subtype inclusions is a homeomorphism onto
the original locally closed subset of the ambient space. -/
def LocallyClosedIn.supportSpaceHomeomorph (W : LocallyClosedIn X) :
    (W.ZV : Set W.V) ≃ₜ W.asSet :=
  Topology.IsEmbedding.subtypeVal.homeomorphImage (W.ZV : Set W.V)

@[simp]
theorem LocallyClosedIn.supportSpaceHomeomorph_apply_val (W : LocallyClosedIn X)
    (x : (W.ZV : Set W.V)) : (W.supportSpaceHomeomorph x).val = x.val.val := rfl

/-- An arbitrary closed subset of the literal support, in witness coordinates. -/
def nestedClosedSubspace (W : LocallyClosedIn X) (T : Closeds W.asSet) :
    Closeds (W.ZV : Set W.V) :=
  ⟨W.supportSpaceHomeomorph ⁻¹' (T : Set W.asSet),
    T.isClosed.preimage W.supportSpaceHomeomorph.continuous⟩

/-- The resulting smaller support is literally the original chosen closed
subset, included into the ambient space. -/
theorem nestedClosedSubspace_support_asSet (W : LocallyClosedIn X)
    (T : Closeds W.asSet) :
    (nestedClosedSupportWitness W (nestedClosedSubspace W T)).asSet =
      Subtype.val '' (T : Set W.asSet) := by
  rw [nestedClosedSupportWitness_asSet]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨W.supportSpaceHomeomorph y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨W.supportSpaceHomeomorph.symm y, ?_, ?_⟩
    · change W.supportSpaceHomeomorph (W.supportSpaceHomeomorph.symm y) ∈ (T : Set W.asSet)
      simpa only [Homeomorph.apply_symm_apply] using hy
    · exact congrArg Subtype.val (W.supportSpaceHomeomorph.apply_symm_apply y)

/-- The difference is literally the complement of the chosen closed
subset inside the original locally closed subset. -/
theorem nestedClosedSubspace_difference_asSet (W : LocallyClosedIn X)
    (T : Closeds W.asSet) :
    (nestedDifferenceSupportWitness W (nestedClosedSubspace W T)).asSet =
      W.asSet \ Subtype.val '' (T : Set W.asSet) := by
  rw [nestedDifferenceSupportWitness_asSet, nestedClosedSubspace_support_asSet]

/-- **I.1.10**, with a closed subset of the literal ambient support space. -/
theorem nestedClosedSubspaceObjectSequence_shortExact (W : LocallyClosedIn X)
    (T : Closeds W.asSet) :
    (locallyClosedNestedObjectSequence W (nestedClosedSubspace W T)).ShortExact :=
  locallyClosedNestedObjectSequence_shortExact W (nestedClosedSubspace W T)

/-- **I.2.8**, with a closed subset of the literal ambient support space. -/
theorem nestedClosedSubspaceCohomologySequence_exact (W : LocallyClosedIn X)
    (T : Closeds W.asSet) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (locallyClosedNestedCohomologySequence W (nestedClosedSubspace W T) F n).Exact :=
  locallyClosedNestedCohomologySequence_exact W (nestedClosedSubspace W T) F n

end SGA.SGA2.ExposeI
