/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIV.FlatLocus
import SGA.SGA1.ExposeIV.OpenMorphisms
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# SGA 1, Exposé IV, §6: scheme-theoretic forms

The statements of IV.6.5, IV.6.10 and IV.6.11 for a morphism `f : X → Y` locally of finite type
over a locally noetherian scheme, with `F = 𝒪_X` in IV.6.10 and IV.6.11 (the case of a coherent
sheaf `F` is in `CoherentModules`). Flatness of `f` at `x` means that the stalk map
`𝒪_{Y,f(x)} → 𝒪_{X,x}` is flat.

* IV.6.5: `image_mem_nhds_iff_forall_specializes_of_locallyOfFiniteType`;
* IV.6.10: `isOpen_setOf_flat_stalkMap`;
* IV.6.11: `exists_nonempty_forall_flat_stalkMap`.

As in SGA, all three reduce to the affine statements of `OpenMorphisms` and `FlatLocus`.
-/

universe u

open AlgebraicGeometry CategoryTheory

namespace SGA.SGA1.ExposeIV

variable {X Y : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-- Given affine opens `x ∈ V ⊆ f⁻¹(U)`, the stalk map of `f` at `x` is flat if and only if the
localization of `Γ(X, V)` at the prime of `x` is flat over `Γ(Y, U)`. -/
lemma flat_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U) (V : X.Opens)
    (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.Flat ↔
      Module.Flat Γ(Y, U) (Localization.AtPrime (hV.primeIdealOf ⟨x, hx⟩).asIdeal) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Module.Flat (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.flat_algebraMap_iff]
    exact RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _

/-- Flatness of `B_𝔮` over `A`, whether `B_𝔮` is written `LocalizedModule` or `Localization`. -/
lemma flat_localizedModule_iff_flat_localization {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (q : Ideal B) [q.IsPrime] :
    Module.Flat A (LocalizedModule q.primeCompl B) ↔ Module.Flat A (Localization.AtPrime q) := by
  let e : LocalizedModule q.primeCompl B ≃ₗ[B] Localization.AtPrime q :=
    IsLocalizedModule.linearEquiv q.primeCompl (LocalizedModule.mkLinearMap _ B)
      (Algebra.linearMap B (Localization.AtPrime q))
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv (e.restrictScalars A).symm,
    fun _ ↦ Module.Flat.of_linearEquiv (e.restrictScalars A)⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- IV.6.10 for `F = 𝒪_X`: let `f : X → Y` be locally of finite type, with `Y` locally noetherian.
The set of points `x` of `X` such that `𝒪_{X,x}` is flat over `𝒪_{Y,f(x)}` is open. -/
theorem isOpen_setOf_flat_stalkMap (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    IsOpen {x : X | (f.stalkMap x).hom.Flat} := by
  refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finiteType_appLE hU hV hVU
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  algebraize [(f.appLE U V hVU).hom]
  let O := {P : PrimeSpectrum Γ(X, V) |
    Module.Flat Γ(Y, U) (LocalizedModule P.asIdeal.primeCompl Γ(X, V))}
  have hO : IsOpen O := isOpen_flatLocus
  have key (y : X) (hy : y ∈ V) : (f.stalkMap y).hom.Flat ↔ hV.primeIdealOf ⟨y, hy⟩ ∈ O := by
    rw [flat_stalkMap_iff U hU V hV hVU hy]
    exact (flat_localizedModule_iff_flat_localization _).symm
  refine ⟨hV.fromSpec '' O, ?_, hV.fromSpec.isOpenEmbedding.isOpenMap _ hO,
    ⟨_, (key x hxV).1 hx, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩⟩
  rintro _ ⟨P, hP, rfl⟩
  have hPV : hV.fromSpec P ∈ V := by
    rw [← SetLike.mem_coe, ← hV.range_fromSpec]; exact ⟨P, rfl⟩
  refine (key _ hPV).2 ?_
  have : hV.primeIdealOf ⟨_, hPV⟩ = P :=
    hV.fromSpec.isOpenEmbedding.injective (hV.fromSpec_primeIdealOf ⟨_, hPV⟩)
  rw [this]
  exact hP

set_option backward.isDefEq.respectTransparency.types false in
/-- The affine form of IV.6.11 (generic flatness), transported to the stalks of a morphism: for
affine opens `V ⊆ f⁻¹ W` with `Γ(Y, W)` a noetherian domain, there is `g ≠ 0` in `Γ(Y, W)` such
that `f` is flat at every point of `V` above `D(g)`. -/
lemma exists_ne_zero_forall_flat_stalkMap (f : X ⟶ Y) [LocallyOfFiniteType f] {W : Y.Opens}
    (hW : IsAffineOpen W) [IsNoetherianRing Γ(Y, W)] [IsDomain Γ(Y, W)] {V : X.Opens}
    (hV : IsAffineOpen V) (hVW : V ≤ f ⁻¹ᵁ W) :
    ∃ g : Γ(Y, W), g ≠ 0 ∧ ∀ x ∈ V, f x ∈ Y.basicOpen g → (f.stalkMap x).hom.Flat := by
  have := f.finiteType_appLE hW hV hVW
  algebraize [(f.appLE W V hVW).hom]
  obtain ⟨g, hg0, hflat⟩ := exists_forall_flat_localizedModule (A := Γ(Y, W)) (B := Γ(X, V))
    (M := Γ(X, V))
  refine ⟨g, hg0, fun x hxV hx ↦ ?_⟩
  rw [flat_stalkMap_iff W hW V hV hVW hxV, ← flat_localizedModule_iff_flat_localization]
  refine hflat _ fun hmem ↦ ?_
  -- `x` lies in `X.basicOpen (f.appLE W V hVW g) = V ∩ f⁻¹ D(g)`
  have hxb : x ∈ X.basicOpen (f.appLE W V hVW g) := by
    rw [Scheme.basicOpen_appLE]
    exact ⟨hxV, hx⟩
  have : hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∈ X.basicOpen (f.appLE W V hVW g) := by
    rwa [hV.fromSpec_primeIdealOf]
  rw [← Scheme.Hom.mem_preimage, hV.fromSpec_preimage_basicOpen] at this
  exact this hmem

section Transfer

open Topology Set

variable {X' Y' S T : Type*} [TopologicalSpace X'] [TopologicalSpace Y'] [TopologicalSpace S]
  [TopologicalSpace T] {f : X' → Y'} {g : S → T} {i : S → X'} {j : T → Y'}

/-- The condition of IV.6.5 on neighbourhoods is local: it can be checked on open embeddings
`i : S → X`, `j : T → Y` with `f ∘ i = j ∘ g`. -/
lemma image_mem_nhds_iff_of_isOpenEmbedding (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
    (hfg : f ∘ i = j ∘ g) (s : S) :
    (∀ N ∈ 𝓝 (i s), f '' N ∈ 𝓝 (f (i s))) ↔ ∀ N ∈ 𝓝 s, g '' N ∈ 𝓝 (g s) := by
  have himg (N : Set S) : f '' (i '' N) = j '' (g '' N) := by
    rw [image_image, image_image]; exact congr_arg (· '' N) hfg
  have hs : f (i s) = j (g s) := congr_fun hfg s
  constructor
  · intro h N hN
    have := h (i '' N) (hi.image_mem_nhds.2 hN)
    rw [himg, hs] at this
    exact hj.image_mem_nhds.1 this
  · intro h N hN
    have hN' : i ⁻¹' N ∈ 𝓝 s := hi.continuous.continuousAt.preimage_mem_nhds hN
    have := hj.image_mem_nhds.2 (h _ hN')
    rw [← himg, ← hs] at this
    exact Filter.mem_of_superset this (image_mono (image_preimage_subset i N))

/-- The condition of IV.6.5 on generizations is local, in the same sense. -/
lemma forall_specializes_iff_of_isOpenEmbedding (hi : IsOpenEmbedding i) (hj : IsOpenEmbedding j)
    (hfg : f ∘ i = j ∘ g) (s : S) :
    (∀ y', y' ⤳ f (i s) → ∃ x', x' ⤳ i s ∧ f x' = y') ↔
      ∀ t', t' ⤳ g s → ∃ s', s' ⤳ s ∧ g s' = t' := by
  have hs : f (i s) = j (g s) := congr_fun hfg s
  constructor
  · intro h t' ht'
    obtain ⟨x', hx', hfx'⟩ := h (j t') (by rw [hs]; exact ht'.map hj.continuous)
    obtain ⟨s', rfl⟩ : x' ∈ range i := hx'.mem_open hi.isOpen_range ⟨s, rfl⟩
    refine ⟨s', hi.isInducing.specializes_iff.1 hx', hj.injective ?_⟩
    rw [← hfx']
    exact (congr_fun hfg s').symm
  · intro h y' hy'
    obtain ⟨t', rfl⟩ : y' ∈ range j := hy'.mem_open hj.isOpen_range ⟨g s, hs.symm⟩
    obtain ⟨s', hs', rfl⟩ := h t' (hj.isInducing.specializes_iff.1 (hs ▸ hy'))
    exact ⟨i s', hs'.map hi.continuous, congr_fun hfg s'⟩

end Transfer

set_option backward.isDefEq.respectTransparency.types false in
open Topology in
/-- IV.6.5: let `f : X → Y` be locally of finite type, with `Y` locally noetherian, and `x ∈ X`.
Then `f` maps every neighbourhood of `x` to a neighbourhood of `f x` if and only if every
generization of `f x` is the image of a generization of `x`. (SGA assumes `f` of finite type; the
statement is local.) As in SGA, one reduces to affine schemes. -/
theorem image_mem_nhds_iff_forall_specializes_of_locallyOfFiniteType (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] (x : X) :
    (∀ N ∈ 𝓝 x, f '' N ∈ 𝓝 (f x)) ↔ ∀ y', y' ⤳ f x → ∃ x', x' ⤳ x ∧ f x' = y' := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finiteType_appLE hU hV hVU
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  algebraize [(f.appLE U V hVU).hom]
  have hfg : (f : X → Y) ∘ hV.fromSpec = hU.fromSpec ∘ Spec.map (f.appLE U V hVU) := by
    ext p
    simp only [Function.comp_apply, ← Scheme.Hom.comp_apply,
      IsAffineOpen.SpecMap_appLE_fromSpec f hU hV hVU]
  have hi : Topology.IsOpenEmbedding hV.fromSpec := hV.fromSpec.isOpenEmbedding
  have hj : Topology.IsOpenEmbedding hU.fromSpec := hU.fromSpec.isOpenEmbedding
  obtain ⟨P, rfl⟩ : ∃ P, hV.fromSpec P = x := ⟨_, hV.fromSpec_primeIdealOf ⟨x, hxV⟩⟩
  rw [image_mem_nhds_iff_of_isOpenEmbedding hi hj hfg,
    forall_specializes_iff_of_isOpenEmbedding hi hj hfg]
  exact image_mem_nhds_iff_forall_specializes (A := Γ(Y, U)) (B := Γ(X, V)) _

/-- IV.6.11 for `F = 𝒪_X`: let `f : X → Y` be of finite type, with `Y` integral and locally
noetherian. There is a nonempty open `V ⊆ Y` such that `f` is flat at every point of `f⁻¹(V)`.
The proof uses generic freeness (IV.6.7) on a finite affine cover of `f⁻¹(W)`, `W` an affine
open of `Y`, as noted in SGA after IV.6.11. -/
theorem exists_nonempty_forall_flat_stalkMap (f : X ⟶ Y) [IsIntegral Y] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ V : Y.Opens, (V : Set Y).Nonempty ∧ ∀ x, f x ∈ V → (f.stalkMap x).hom.Flat := by
  classical
  -- a nonempty affine open `W` of `Y`, with noetherian domain of sections
  obtain ⟨y⟩ := (inferInstance : Nonempty Y)
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have : Nonempty W := ⟨⟨y, hyW⟩⟩
  have : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  -- `f⁻¹ W` is covered by finitely many affine opens
  let ι := {V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ W}
  obtain ⟨t, ht⟩ := (f.isCompact_preimage hW.isCompact).elim_finite_subcover
    (fun V : ι ↦ (V.1 : Set X)) (fun V ↦ V.1.1.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ W).2
      exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩)
  choose g hg0 hflat using fun V : ι ↦ exists_ne_zero_forall_flat_stalkMap f hW V.1.2 V.2
  refine ⟨Y.basicOpen (∏ V ∈ t, g V), ?_, fun x hx ↦ ?_⟩
  · have hne : Y.basicOpen (∏ V ∈ t, g V) ≠ ⊥ := by
      rw [ne_eq, basicOpen_eq_bot_iff]
      exact Finset.prod_ne_zero_iff.2 fun V _ ↦ hg0 V
    by_contra h
    exact hne ((TopologicalSpace.Opens.not_nonempty_iff_eq_bot _).1 h)
  · have hxW : x ∈ f ⁻¹ᵁ W := Y.basicOpen_le _ hx
    obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.1 (ht hxW)
    refine hflat V x hxV ?_
    rw [← Finset.mul_prod_erase t g hVt, Scheme.basicOpen_mul] at hx
    exact hx.1

end SGA.SGA1.ExposeIV
