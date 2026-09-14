/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.SchemeClopens
import SGA.SGA2.ExposeIII.SchemeHartogs
import SGA.SGA2.ExposeIII.AffineConnectedComponents
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Hartshorne connectedness for locally noetherian schemes

The actual inclusion of the open complement induces a bijection on
connected components when the actual local structure rings have depth
at least two along the closed complement (SGA 2, III.3.6). No global
quasi-compactness assumption is imposed. Clopen extension follows from
the actual structure-sheaf Hartogs isomorphism and genuine global
structure idempotents.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

/-- A locally noetherian scheme is locally connected: clopen components
of a noetherian affine neighborhood give connected open neighborhoods. -/
theorem locallyConnectedSpace_of_isLocallyNoetherian (X : Scheme.{u})
    [IsLocallyNoetherian X] : LocallyConnectedSpace X := by
  apply locallyConnectedSpace_iff_subsets_isOpen_isConnected.mpr
  intro x S hS
  obtain ⟨O, hOS, hO, hxO⟩ := mem_nhds_iff.mp hS
  obtain ⟨V, hV, hxV, hVO⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⟨O, hO⟩) hxO
  let : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  let : NoetherianSpace (V : Set X) := noetherianSpace_of_isAffineOpen V hV
  let y : V := ⟨x, hxV⟩
  refine ⟨Subtype.val '' connectedComponent y, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, _, rfl⟩
    exact hOS (hVO z.2)
  · exact V.isOpenEmbedding.isOpenMap _ (isClopen_connectedComponent_of_noetherian y).isOpen
  · exact ⟨y, mem_connectedComponent, rfl⟩
  · exact isConnected_connectedComponent.image _ continuous_subtype_val.continuousOn

variable {X Y : Scheme.{u}}

/-- The actual map on connected components induced by a scheme morphism. -/
def schemeConnectedComponentsMap (f : Y ⟶ X) :
    ConnectedComponents Y → ConnectedComponents X :=
  f.continuous.connectedComponentsMap

@[simp] theorem schemeConnectedComponentsMap_mk (f : Y ⟶ X) (y : Y) :
    schemeConnectedComponentsMap f (ConnectedComponents.mk y) = ConnectedComponents.mk (f y) :=
  rfl

/-- Injective global structure pullback cannot miss a clopen connected
component of the target. -/
theorem schemeConnectedComponentsMap_surjective (f : Y ⟶ X)
    [LocallyConnectedSpace X] (h : Function.Injective f.appTop) :
    Function.Surjective (schemeConnectedComponentsMap f) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hn : (f ⁻¹' connectedComponent x).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    have hc0 := (scheme_clopen_preimage_eq_empty_iff f h _ isClopen_connectedComponent).mp he
    exact Set.nonempty_iff_ne_empty.mp ⟨x, mem_connectedComponent⟩ hc0
  obtain ⟨y, hy⟩ := hn
  exact ⟨ConnectedComponents.mk y, ConnectedComponents.coe_eq_coe'.mpr hy⟩

/-- Bijective global structure pullback prevents distinct clopen connected
components of the source from mapping into one target component. -/
theorem schemeConnectedComponentsMap_injective (f : Y ⟶ X)
    [LocallyConnectedSpace Y] (h : Function.Bijective f.appTop) :
    Function.Injective (schemeConnectedComponentsMap f) := by
  intro c d hcd
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  obtain ⟨t, ht, he⟩ := exists_scheme_clopen_extension f h (connectedComponent y)
    isClopen_connectedComponent
  have hy : f y ∈ t := by
    change y ∈ f ⁻¹' t
    rw [he]
    exact mem_connectedComponent
  have hxy : f x ∈ connectedComponent (f y) := ConnectedComponents.coe_eq_coe'.mp hcd
  have hx := ht.connectedComponent_subset hy hxy
  apply ConnectedComponents.coe_eq_coe'.mpr
  change x ∈ f ⁻¹' t at hx
  rwa [he] at hx

/-- For locally connected schemes, a morphism bijective on global structure
sections induces a bijection on actual connected-components types. -/
theorem schemeConnectedComponentsMap_bijective (f : Y ⟶ X)
    [LocallyConnectedSpace X] [LocallyConnectedSpace Y]
    (h : Function.Bijective f.appTop) :
    Function.Bijective (schemeConnectedComponentsMap f) :=
  ⟨schemeConnectedComponentsMap_injective f h,
    schemeConnectedComponentsMap_surjective f h.1⟩

/-- The component morphism on global sections of an open inclusion is
bijective whenever the actual structure-sheaf restriction is bijective. -/
theorem openInclusion_appTop_bijective_of_restriction (W : X.Opens)
    (h : Function.Bijective (X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op)) :
    Function.Bijective W.ι.appTop := by
  have : IsIso (X.presheaf.map (homOfLE le_top : W ⟶ ⊤).op) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr h
  have := isIso_presheaf_map_of_eq X.presheaf
    (homOfLE le_top : W.ι ''ᵁ ⊤ ⟶ ⊤) (homOfLE le_top : W ⟶ ⊤)
    W.ι_image_top rfl
  rw [W.ι_appTop]
  exact ConcreteCategory.bijective_of_isIso _

/-- **III.3.6 (Hartshorne):** for a locally noetherian scheme, depth at least
two of every actual structure stalk along a closed subset implies that
the actual open-complement inclusion induces a bijection on connected
components. -/
theorem schemeConnectedComponents_bijective_of_stalkDepth
    [IsLocallyNoetherian X] (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x) :
    Function.Bijective (schemeConnectedComponentsMap (Scheme.Opens.ι Z.compl)) := by
  let := locallyConnectedSpace_of_isLocallyNoetherian X
  let : LocallyConnectedSpace (Scheme.Opens.toScheme Z.compl) :=
    Z.compl.isOpen.locallyConnectedSpace
  apply schemeConnectedComponentsMap_bijective
  exact openInclusion_appTop_bijective_of_restriction Z.compl
    (structureGlobalRestriction_bijective_of_stalkDepth Z h)

/-- The equivalence has the actual open inclusion as its forward map on
connected components. -/
def schemeConnectedComponentsEquiv [IsLocallyNoetherian X] (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x) :
    ConnectedComponents (Scheme.Opens.toScheme Z.compl) ≃ ConnectedComponents X :=
  Equiv.ofBijective (schemeConnectedComponentsMap (Scheme.Opens.ι Z.compl))
    (schemeConnectedComponents_bijective_of_stalkDepth Z h)

@[simp] theorem schemeConnectedComponentsEquiv_apply_mk
    [IsLocallyNoetherian X] (Z : Closeds X)
    (h : ∀ x : X, x ∈ Z → (2 : ℕ∞) ≤ structureStalkDepth X x)
    (x : Scheme.Opens.toScheme Z.compl) :
    schemeConnectedComponentsEquiv Z h (ConnectedComponents.mk x) =
      ConnectedComponents.mk x.1 :=
  rfl

end SGA.SGA2.ExposeIII
