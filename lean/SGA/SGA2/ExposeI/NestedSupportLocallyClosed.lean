/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeI.NestedSupportCohomology

/-!
# Nested support for an arbitrary locally closed subset

Starting with the original witness `W` and any actual closed subset of its
support space, the canonical closed hulls put the pair in the open/closed
presentation used by the proved section sequence. Genuine witness-independence
isomorphisms then transport its short exact sequence to the original support
object of `W`. The resulting Ext sequence is I.2.8 in its full locally closed
generality, without an ambient closedness assumption.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace TopCat Abelian

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {X : TopCat.{u}}

/-- A closed subset of the actual support space is closed in the open
neighbourhood, because the support is itself closed there. -/
def nestedClosedPart (W : LocallyClosedIn X) (T : Closeds (W.ZV : Set W.V)) :
    Closeds W.V :=
  ⟨Subtype.val '' (T : Set (W.ZV : Set W.V)),
    W.ZV.isClosed.isClosedMap_subtype_val _ T.isClosed⟩

theorem nestedClosedPart_le (W : LocallyClosedIn X) (T : Closeds (W.ZV : Set W.V)) :
    nestedClosedPart W T ≤ W.ZV := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- The genuine locally closed witness of the chosen closed subset. -/
def nestedClosedSupportWitness (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) : LocallyClosedIn X :=
  ⟨W.V, nestedClosedPart W T⟩

/-- Its underlying subset is precisely the image of the chosen closed set
under the original support-space inclusion. -/
theorem nestedClosedSupportWitness_asSet (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedClosedSupportWitness W T).asSet =
      (fun x : (W.ZV : Set W.V) => x.val.val) '' (T : Set (W.ZV : Set W.V)) := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z, hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.val, ⟨z, hz, rfl⟩, rfl⟩

theorem nestedClosedSupportWitness_subset (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedClosedSupportWitness W T).asSet ⊆ W.asSet := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, nestedClosedPart_le W T hy, rfl⟩

theorem nestedSupportClosedHulls_le (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedClosedSupportWitness W T).closedHull ≤ W.closedHull :=
  closure_mono (nestedClosedSupportWitness_subset W T)

/-- The actual difference support, closed in the open neighbourhood with
the smaller support removed. -/
def nestedDifferenceSupportWitness (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) : LocallyClosedIn X :=
  LocallyClosedIn.ofOpenClosed
    (W.V ⊓ (nestedClosedSupportWitness W T).closedHull.compl) W.closedHull

/-- The difference witness represents literally `Z \ Z'`. -/
theorem nestedDifferenceSupportWitness_asSet (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (nestedDifferenceSupportWitness W T).asSet =
      W.asSet \ (nestedClosedSupportWitness W T).asSet := by
  rw [nestedDifferenceSupportWitness, LocallyClosedIn.ofOpenClosed_asSet,
    ← W.inter_closedHull, ← (nestedClosedSupportWitness W T).inter_closedHull]
  ext x
  change ((x ∈ W.V ∧ x ∉ (nestedClosedSupportWitness W T).closedHull) ∧
      x ∈ W.closedHull) ↔
    ((x ∈ W.V ∧ x ∈ W.closedHull) ∧
      ¬(x ∈ W.V ∧ x ∈ (nestedClosedSupportWitness W T).closedHull))
  tauto

/-- The support object of any original witness agrees with its canonical
ambient closed-hull presentation, by the proved same-set comparison. -/
def locallyClosedSupportClosedHullIso (W : LocallyClosedIn X) :
    zZX_locallyClosed (LocallyClosedIn.ofOpenClosed W.V W.closedHull) ≅
      zZX_locallyClosed W :=
  locallyClosedSupportIsoOfSameSet
    ((LocallyClosedIn.ofOpenClosed_asSet W.V W.closedHull).trans W.inter_closedHull)

/-- Inclusion of the original difference-support object into the original
middle-support object. -/
def locallyClosedNestedObjectInclusion (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    zZX_locallyClosed (nestedDifferenceSupportWitness W T) ⟶ zZX_locallyClosed W :=
  nestedSupportObjectInclusion (nestedClosedSupportWitness W T).closedHull W.closedHull W.V ≫
    (locallyClosedSupportClosedHullIso W).hom

/-- Restriction of the original middle-support object to its chosen closed part. -/
def locallyClosedNestedObjectRestriction (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    zZX_locallyClosed W ⟶ zZX_locallyClosed (nestedClosedSupportWitness W T) :=
  (locallyClosedSupportClosedHullIso W).inv ≫
    nestedSupportObjectRestriction (nestedSupportClosedHulls_le W T) W.V ≫
      (locallyClosedSupportClosedHullIso (nestedClosedSupportWitness W T)).hom

theorem locallyClosedNestedObject_comp (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    locallyClosedNestedObjectInclusion W T ≫ locallyClosedNestedObjectRestriction W T = 0 := by
  simp only [locallyClosedNestedObjectInclusion, locallyClosedNestedObjectRestriction,
    Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, nestedSupportObject_comp, zero_comp]

/-- The actual constant-support short complex for an arbitrary locally
closed set and a closed subset of its support space. -/
def locallyClosedNestedObjectSequence (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) : ShortComplex (Sheaf AddCommGrpCat.{u} X) :=
  ShortComplex.mk (locallyClosedNestedObjectInclusion W T)
    (locallyClosedNestedObjectRestriction W T) (locallyClosedNestedObject_comp W T)

/-- The previously proved actual sequence is transported by genuine
same-support sheaf isomorphisms, retaining its actual maps. -/
def locallyClosedNestedObjectSequenceIso (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    nestedSupportObjectSequence (nestedSupportClosedHulls_le W T) W.V ≅
      locallyClosedNestedObjectSequence W T :=
  ShortComplex.isoMk (Iso.refl _) (locallyClosedSupportClosedHullIso W)
    (locallyClosedSupportClosedHullIso (nestedClosedSupportWitness W T))
    (by simp [nestedSupportObjectSequence, locallyClosedNestedObjectSequence,
      locallyClosedNestedObjectInclusion])
    (by simp [nestedSupportObjectSequence, locallyClosedNestedObjectSequence,
      locallyClosedNestedObjectRestriction])

/-- **I.1.10:** the genuine integer-support sequence is short exact for
every locally closed support and every closed subset of it. -/
theorem locallyClosedNestedObjectSequence_shortExact (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) :
    (locallyClosedNestedObjectSequence W T).ShortExact :=
  ShortComplex.shortExact_of_iso (locallyClosedNestedObjectSequenceIso W T)
    (nestedSupportObjectSequence_shortExact (nestedSupportClosedHulls_le W T) W.V)

/-- The support-increasing map on the original ambient support cohomology. -/
def locallyClosedNestedCohomologyMap (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed (nestedClosedSupportWitness W T) F n →+ H_locallyClosed W F n :=
  (Ext.mk₀ (locallyClosedNestedObjectRestriction W T)).precomp F (zero_add n)

/-- Restriction to the original locally closed difference on actual Ext. -/
def locallyClosedNestedCohomologyRestriction (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed W F n →+ H_locallyClosed (nestedDifferenceSupportWitness W T) F n :=
  (Ext.mk₀ (locallyClosedNestedObjectInclusion W T)).precomp F (zero_add n)

/-- The actual connecting map for the original ambient support Ext groups. -/
def locallyClosedNestedCohomologyBoundary (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    H_locallyClosed (nestedDifferenceSupportWitness W T) F n →+
      H_locallyClosed (nestedClosedSupportWitness W T) F (n + 1) :=
  (locallyClosedNestedObjectSequence_shortExact W T).extClass.precomp F (Nat.add_comm 1 n)

/-- **I.2.8:** six consecutive original ambient support cohomology groups. -/
def locallyClosedNestedCohomologySequence (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{u} 5 :=
  Ext.contravariantSequence (locallyClosedNestedObjectSequence_shortExact W T)
    F n (n + 1) (Nat.add_comm 1 n)

/-- The general locally closed sequence is genuinely exact in every degree. -/
theorem locallyClosedNestedCohomologySequence_exact (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    (locallyClosedNestedCohomologySequence W T F n).Exact :=
  Ext.contravariantSequence_exact (locallyClosedNestedObjectSequence_shortExact W T)
    F n (n + 1) (Nat.add_comm 1 n)

/-- The sequence begins with an injection in ordinary degree zero. -/
theorem locallyClosedNestedCohomologyMap_zero_injective (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) (F : Sheaf AddCommGrpCat.{u} X) :
    Function.Injective (locallyClosedNestedCohomologyMap W T F 0) := by
  have : Epi (locallyClosedNestedObjectRestriction W T) :=
    (locallyClosedNestedObjectSequence_shortExact W T).epi_g
  exact Ext.precomp_mk₀_injective_of_epi F (locallyClosedNestedObjectRestriction W T)

/-- The first map is natural in the coefficient sheaf. -/
theorem locallyClosedNestedCohomologyMap_naturality (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : H_locallyClosed (nestedClosedSupportWitness W T) F n) :
    locallyClosedNestedCohomologyMap W T G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (locallyClosedNestedCohomologyMap W T F n x).comp (Ext.mk₀ f) (add_zero n) := by
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

/-- The second map is natural in the coefficient sheaf. -/
theorem locallyClosedNestedCohomologyRestriction_naturality (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : H_locallyClosed W F n) :
    locallyClosedNestedCohomologyRestriction W T G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (locallyClosedNestedCohomologyRestriction W T F n x).comp (Ext.mk₀ f) (add_zero n) := by
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (zero_add n)).symm

/-- The genuine connecting maps are natural in the coefficient sheaf. -/
theorem locallyClosedNestedCohomologyBoundary_naturality (W : LocallyClosedIn X)
    (T : Closeds (W.ZV : Set W.V)) {F G : Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ)
    (x : H_locallyClosed (nestedDifferenceSupportWitness W T) F n) :
    locallyClosedNestedCohomologyBoundary W T G n (x.comp (Ext.mk₀ f) (add_zero n)) =
      (locallyClosedNestedCohomologyBoundary W T F n x).comp
        (Ext.mk₀ f) (add_zero (n + 1)) := by
  exact (Ext.comp_assoc_of_third_deg_zero _ _ _ (Nat.add_comm 1 n)).symm

end SGA.SGA2.ExposeI
