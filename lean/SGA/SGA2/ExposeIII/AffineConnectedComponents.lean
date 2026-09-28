/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.AffineHartogs
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.Topology.Separation.Connected

/-!
# Affine invariance of connected components across depth-two supports

The map is the actual connected-components map induced by the open
inclusion. The proof extends clopen characteristic sections through the
Hartogs ring isomorphism and uses finiteness of connected components of a
noetherian space.
-/

noncomputable section

universe u v

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

/-- A noetherian space has finitely many connected components: a finite
irreducible closed cover maps to a finite cover by singleton components. -/
theorem finite_connectedComponents_of_noetherian (X : Type u)
    [TopologicalSpace X] [NoetherianSpace X] : Finite (ConnectedComponents X) := by
  obtain ⟨S, hS, _, hI, hcov⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible
      (isClosed_univ : IsClosed (Set.univ : Set X))
  have hf : (⋃ t ∈ S, ConnectedComponents.mk '' t).Finite := hS.biUnion fun t ht =>
    ((hI t ht).isConnected.isPreconnected.image _
      ConnectedComponents.continuous_coe.continuousOn).subsingleton.finite
  apply Finite.of_finite_univ
  refine hf.subset ?_
  intro c _
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hx : x ∈ ⋃₀ S := hcov ▸ Set.mem_univ x
  obtain ⟨t, ht, hxt⟩ := hx
  exact Set.mem_iUnion₂.mpr ⟨t, ht, x, hxt, rfl⟩

/-- Every connected component of a noetherian space is genuinely clopen. -/
theorem isClopen_connectedComponent_of_noetherian {X : Type u}
    [TopologicalSpace X] [NoetherianSpace X] (x : X) : IsClopen (connectedComponent x) := by
  have := finite_connectedComponents_of_noetherian X
  simpa only [connectedComponents_preimage_singleton] using
    (isClopen_discrete ({ConnectedComponents.mk x} : Set (ConnectedComponents X))).preimage
      ConnectedComponents.continuous_coe

variable {R : CommRingCat.{u}}

/-- A clopen subset of an affine open extends to an ambient clopen whenever
the actual global structure-sheaf restriction is bijective. -/
theorem exists_affine_clopen_extension (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Bijective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op))
    (s : Set U) (hs : IsClopen s) :
    ∃ t : Set (PrimeSpectrum R), IsClopen t ∧ Subtype.val ⁻¹' t = s := by
  let e : R ≃+* (Spec.structureSheaf R).presheaf.obj (op U) :=
    (StructureSheaf.globalSectionsIso R).commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective ((Spec.structureSheaf R).presheaf.map
        (homOfLE le_top : U ⟶ ⊤).op).hom h)
  let a : R := e.symm (affineClopenSection U s hs)
  have ha : IsIdempotentElem a := (affineClopenSection_idempotent U s hs).map e.symm
  refine ⟨PrimeSpectrum.basicOpen a, PrimeSpectrum.isClopen_iff.mpr ⟨a, ha, rfl⟩, ?_⟩
  ext x
  have he := congrArg (fun t => t.1 x) (e.apply_symm_apply (affineClopenSection U s hs))
  change algebraMap R (StructureSheaf.Localizations R x.1) a =
    (affineClopenSection U s hs).1 x at he
  change a ∈ x.1.asIdeal.primeCompl ↔ x ∈ s
  rw [← IsLocalization.AtPrime.isUnit_to_map_iff (StructureSheaf.Localizations R x.1)
    x.1.asIdeal a, he, affineClopenSection_apply]
  let := IsLocalization.AtPrime.nontrivial (StructureSheaf.Localizations R x.1) x.1.asIdeal
  classical
  by_cases hx : x ∈ s <;> simp [hx]

/-- Injectivity of actual global restriction detects the empty ambient
clopen. In particular, it cannot miss an entire connected component. -/
theorem affine_clopen_preimage_eq_empty_iff (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Injective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op))
    (s : Set (PrimeSpectrum R)) (hs : IsClopen s) :
    (Subtype.val ⁻¹' s : Set U) = ∅ ↔ s = ∅ := by
  constructor
  · intro h0
    let t : Set (⊤ : Opens (PrimeSpectrum.Top R)) := Subtype.val ⁻¹' s
    have ht : IsClopen t := hs.preimage continuous_subtype_val
    have hc : affineClopenSection ⊤ t ht = 0 := by
      apply h
      rw [affineClopenSection_restrict, map_zero]
      apply (affineClopenSection_eq_zero_iff _ _ _).mpr
      exact h0
    have ht0 := (affineClopenSection_eq_zero_iff ⊤ t ht).mp hc
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have : (⟨x, trivial⟩ : (⊤ : Opens (PrimeSpectrum.Top R))) ∈ t := hx
    simp [ht0] at this
  · rintro rfl
    rfl

/-- The actual map on connected components induced by affine open inclusion. -/
def affineOpenConnectedComponentsMap (U : Opens (PrimeSpectrum.Top R)) :
    ConnectedComponents U → ConnectedComponents (PrimeSpectrum R) :=
  (continuous_subtype_val : Continuous (Subtype.val : U → PrimeSpectrum R)).connectedComponentsMap

@[simp] theorem affineOpenConnectedComponentsMap_mk (U : Opens (PrimeSpectrum.Top R)) (x : U) :
    affineOpenConnectedComponentsMap U (ConnectedComponents.mk x) = ConnectedComponents.mk x.1 :=
  rfl

/-- Surjectivity on connected components follows already from injectivity
of global sections when the ambient components are clopen. -/
theorem affineOpenConnectedComponentsMap_surjective
    [IsNoetherianRing R] (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Injective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) :
    Function.Surjective (affineOpenConnectedComponentsMap U) := by
  intro c
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have hc := isClopen_connectedComponent_of_noetherian x
  have hn : (Subtype.val ⁻¹' connectedComponent x : Set U).Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro he
    have hc0 := (affine_clopen_preimage_eq_empty_iff U h _ hc).mp he
    exact Set.nonempty_iff_ne_empty.mp ⟨x, mem_connectedComponent⟩ hc0
  obtain ⟨y, hy⟩ := hn
  exact ⟨ConnectedComponents.mk y, ConnectedComponents.coe_eq_coe'.mpr hy⟩

/-- Unique extension of actual global sections prevents two connected
components of the complement from lying in one ambient component. -/
theorem affineOpenConnectedComponentsMap_injective
    [IsNoetherianRing R] (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Bijective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) :
    Function.Injective (affineOpenConnectedComponentsMap U) := by
  have : NoetherianSpace (PrimeSpectrum.Top R) :=
    inferInstanceAs (NoetherianSpace (PrimeSpectrum R))
  have : NoetherianSpace U :=
    Topology.IsInducing.noetherianSpace U.isOpenEmbedding.isInducing
  intro c d hcd
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨y, rfl⟩ := ConnectedComponents.surjective_coe d
  obtain ⟨t, ht, he⟩ := exists_affine_clopen_extension U h (connectedComponent y)
    (isClopen_connectedComponent_of_noetherian y)
  have hy : y.1 ∈ t := by
    change y ∈ (Subtype.val ⁻¹' t : Set U)
    rw [he]
    exact mem_connectedComponent
  have hxy : x.1 ∈ connectedComponent y.1 := ConnectedComponents.coe_eq_coe'.mp hcd
  have hx := ht.connectedComponent_subset hy hxy
  apply ConnectedComponents.coe_eq_coe'.mpr
  change x ∈ (Subtype.val ⁻¹' t : Set U) at hx
  rwa [he] at hx

/-- Bijective actual affine ring restriction induces a bijection on the
actual connected-components types of a noetherian affine scheme. -/
theorem affineOpenConnectedComponentsMap_bijective
    [IsNoetherianRing R] (U : Opens (PrimeSpectrum.Top R))
    (h : Function.Bijective ((Spec.structureSheaf R).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op)) :
    Function.Bijective (affineOpenConnectedComponentsMap U) :=
  ⟨affineOpenConnectedComponentsMap_injective U h,
    affineOpenConnectedComponentsMap_surjective U h.1⟩

/-- **III.3.6, noetherian affine case:** the actual inclusion of the open
complement induces a bijection on connected components under depth at least two. -/
theorem affineConnectedComponents_bijective_of_two_le_depth
    [IsNoetherianRing R] (I : Ideal R)
    (h : (2 : ℕ∞) ≤ depth I (ModuleCat.of R R)) :
    Function.Bijective (affineOpenConnectedComponentsMap (affineSupportComplement I)) :=
  affineOpenConnectedComponentsMap_bijective (affineSupportComplement I)
    (affineStructureRestriction_bijective I h)

/-- **III.3.6, noetherian affine case in local form:** local structure-module
depth at least two along `V(I)` gives the genuine connected-components bijection. -/
theorem affineConnectedComponents_bijective_of_localDepth
    [IsNoetherianRing R] (I : Ideal R)
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth (ModuleCat.of R R) p) :
    Function.Bijective (affineOpenConnectedComponentsMap (affineSupportComplement I)) :=
  affineConnectedComponents_bijective_of_two_le_depth I
    ((le_depth_iff_forall_localDepth I (ModuleCat.of R R) 2).mpr h)

/-- The equivalence has exactly the map induced by the inclusion as its
forward function. -/
def affineConnectedComponentsEquiv [IsNoetherianRing R] (I : Ideal R)
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth (ModuleCat.of R R) p) :
    ConnectedComponents (affineSupportComplement I) ≃ ConnectedComponents (Spec R) :=
  Equiv.ofBijective (affineOpenConnectedComponentsMap (affineSupportComplement I))
    (affineConnectedComponents_bijective_of_localDepth I h)

@[simp] theorem affineConnectedComponentsEquiv_apply_mk [IsNoetherianRing R] (I : Ideal R)
    (h : ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ localDepth (ModuleCat.of R R) p)
    (x : affineSupportComplement I) :
    affineConnectedComponentsEquiv I h (ConnectedComponents.mk x) = ConnectedComponents.mk x.1 :=
  rfl

end SGA.SGA2.ExposeIII
