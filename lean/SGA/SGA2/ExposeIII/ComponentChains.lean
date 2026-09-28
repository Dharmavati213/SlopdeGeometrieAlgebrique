/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AntifilterEquivalence
import SGA.SGA2.ExposeIII.ConnectednessInCodimension

/-!
# SGA 2, III.3.7: component chains in bounded codimension

Under the depth/dimension hypothesis, any two irreducible components of a
connected locally noetherian scheme can be joined by a finite chain whose
successive intersections contain points of local dimension less than `d`.
This is the source's definition of connectedness in codimension `d - 1`.
-/

noncomputable section

universe u

open Set TopologicalSpace AlgebraicGeometry Relation List

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- Closed sets whose points all satisfy a given condition form an antifilter. -/
def ClosedAntifilter.ofPointwise {X : Type u} [TopologicalSpace X]
    (P : X → Prop) : ClosedAntifilter X where
  mem Y := IsClosed Y ∧ ∀ x ∈ Y, P x
  isClosed_of_mem h := h.1
  mem_empty := ⟨isClosed_empty, by simp⟩
  mem_of_subset h hcl hsub := ⟨hcl, fun x hx => h.2 x (hsub hx)⟩
  mem_union h h' := ⟨h.1.union h'.1, fun x hx => hx.elim (h.2 x) (h'.2 x)⟩

/-- Pointwise membership satisfies the locality assumption of III.3.8. -/
theorem ClosedAntifilter.ofPointwise_isLocal {X : Type u} [TopologicalSpace X]
    (P : X → Prop) : (ClosedAntifilter.ofPointwise P).IsLocal := by
  intro Y hY hlocal
  refine ⟨hY, ?_⟩
  intro x hxY
  obtain ⟨U, _, hxU, Y', hY', htrace⟩ := hlocal x
  have hx : x ∈ U ∩ Y' := htrace ▸ ⟨hxU, hxY⟩
  exact hY'.2 x hx.2

/-- The topological space of a locally noetherian scheme is locally noetherian. -/
instance locallyNoetherianSpace_scheme (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyNoetherianSpace X where
  exists_open_noetherian x := by
    obtain ⟨U, hU, hxU, _⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
    let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    exact ⟨U, U.isOpen, hxU, noetherianSpace_of_isAffineOpen U hU⟩

/-- Injectivity on connected components into a preconnected space makes the
source preconnected. -/
theorem preconnectedSpace_of_injective_connectedComponentsMap
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    {f : Y → X} (hf : Continuous f)
    (hinj : Function.Injective hf.connectedComponentsMap) : PreconnectedSpace Y := by
  apply preconnectedSpace_iff_connectedComponent.mpr
  intro y
  apply eq_univ_of_forall
  intro z
  exact ConnectedComponents.coe_eq_coe'.mp (hinj (Subsingleton.elim _ _))

/-- The antifilter of closed sets of codimension at least `d`, using the
source's definition by dimensions of the structure stalks. -/
def codimensionAntifilter (X : Scheme.{u}) (d : ℕ) : ClosedAntifilter X :=
  ClosedAntifilter.ofPointwise fun x => (d : WithBot ℕ∞) ≤ structureStalkDim X x

/-- Codimension in the convention of III.3.7: the infimum of local ring
dimensions over all points of the subset. The empty subset has codimension `⊤`. -/
def schemeSubsetCodimension (X : Scheme.{u}) (Z : Set X) : WithBot ℕ∞ :=
  ⨅ x : Z, structureStalkDim X x.1

/-- The pointwise antifilter agrees with the source's numerical codimension. -/
theorem codimensionAntifilter_mem_iff (X : Scheme.{u}) (d : ℕ) (Z : Set X) :
    (codimensionAntifilter X d).mem Z ↔
      IsClosed Z ∧ (d : WithBot ℕ∞) ≤ schemeSubsetCodimension X Z := by
  simp only [codimensionAntifilter, ClosedAntifilter.ofPointwise, schemeSubsetCodimension,
    le_iInf_iff, Subtype.forall]

/-- Consecutive components meet at a point whose local dimension is below `d`. -/
def ComponentsMeetInCodimensionLt (X : Scheme.{u}) (d : ℕ) (C D : Set X) : Prop :=
  ComponentsAdjacent C D ∧ ∃ x ∈ C ∩ D, structureStalkDim X x < (d : WithBot ℕ∞)

/-- **III.3.7:** the depth/dimension condition gives chains of irreducible
components whose consecutive intersections have codimension below `d`.
There is no global noetherian or quasi-compactness hypothesis. -/
theorem III_3_7 {X : Scheme.{u}} [IsLocallyNoetherian X] [PreconnectedSpace X]
    (d : ℕ)
    (hdepth : ∀ x : X, (d : WithBot ℕ∞) ≤ structureStalkDim X x →
      (2 : ℕ∞) ≤ structureStalkDepth X x)
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ReflTransGen (ComponentsMeetInCodimensionLt X d) C D := by
  have hi : ∀ Y : Set X, (codimensionAntifilter X d).mem Y →
      IsPreconnected (Yᶜ : Set X) := by
    intro Y hY
    let Z : Closeds X := ⟨Y, hY.1⟩
    have hbij := III_3_7_complement Z d hdepth hY.2
    have : PreconnectedSpace (Scheme.Opens.toScheme Z.compl) :=
      preconnectedSpace_of_injective_connectedComponentsMap
        (Scheme.Opens.ι Z.compl).continuous hbij.1
    exact isPreconnected_iff_preconnectedSpace.mpr this
  have hchain := III_3_8_i_implies_ii (codimensionAntifilter X d)
    (ClosedAntifilter.ofPointwise_isLocal _) hi hC hD
  refine ReflTransGen.mono ?_ C D hchain
  intro E G hEG
  refine ⟨hEG.1, ?_⟩
  by_contra hno
  apply hEG.2
  refine ⟨(isClosed_of_mem_irreducibleComponents _ hEG.1.1).inter
    (isClosed_of_mem_irreducibleComponents _ hEG.1.2.1), ?_⟩
  intro x hx
  exact not_lt.mp (fun hlt => hno ⟨x, hx, hlt⟩)

/-- The actual finite sequence of components in III.3.7. -/
theorem III_3_7_list {X : Scheme.{u}} [IsLocallyNoetherian X] [PreconnectedSpace X]
    (d : ℕ)
    (hdepth : ∀ x : X, (d : WithBot ℕ∞) ≤ structureStalkDim X x →
      (2 : ℕ∞) ≤ structureStalkDepth X x)
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ∃ l : List (Set X), l.head? = some C ∧ l.getLast? = some D ∧
      (∀ E ∈ l, E ∈ irreducibleComponents X) ∧
      l.IsChain (fun E G => ∃ x ∈ E ∩ G, structureStalkDim X x < (d : WithBot ℕ∞)) := by
  obtain ⟨l, hchain, hlast⟩ :=
    List.exists_isChain_cons_of_relationReflTransGen (III_3_7 d hdepth hC hD)
  refine ⟨C :: l, by simp, ?_, ?_, hchain.imp fun _ _ h => h.2⟩
  · rw [List.getLast?_eq_getLast_of_ne_nil (List.cons_ne_nil _ _), hlast]
  · exact isChain_componentsAdjacent_mem (hchain.imp fun _ _ h => h.1) (by simp) hC

/-- The numerical codimension formulation of III.3.7, with the depth
threshold written as `d + 1`: every successive intersection has
codimension at most `d`. -/
theorem III_3_7_codimension_list {X : Scheme.{u}} [IsLocallyNoetherian X]
    [PreconnectedSpace X] (d : ℕ)
    (hdepth : ∀ x : X, ((d + 1 : ℕ) : WithBot ℕ∞) ≤ structureStalkDim X x →
      (2 : ℕ∞) ≤ structureStalkDepth X x)
    {C D : Set X} (hC : C ∈ irreducibleComponents X)
    (hD : D ∈ irreducibleComponents X) :
    ∃ l : List (Set X), l.head? = some C ∧ l.getLast? = some D ∧
      (∀ E ∈ l, E ∈ irreducibleComponents X) ∧
      l.IsChain (fun E G => schemeSubsetCodimension X (E ∩ G) ≤ (d : WithBot ℕ∞)) := by
  obtain ⟨l, hhead, hlast, hmem, hchain⟩ := III_3_7_list (d + 1) hdepth hC hD
  refine ⟨l, hhead, hlast, hmem, hchain.imp ?_⟩
  rintro E G ⟨x, hx, hdim⟩
  exact (iInf_le (fun y : (E ∩ G : Set X) => structureStalkDim X y.1) ⟨x, hx⟩).trans
    (ENat.WithBot.lt_add_one_iff.mp
      (by simpa only [Nat.cast_add, Nat.cast_one] using hdim))

end SGA.SGA2.ExposeIII
