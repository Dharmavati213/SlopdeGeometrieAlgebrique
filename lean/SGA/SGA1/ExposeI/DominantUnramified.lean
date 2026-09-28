/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeI.Etale
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeIV.Schemes

/-!
# SGA 1, Exposé I, I.9.11: unramified dominant morphisms to a normal scheme

Corollary I.9.11: a dominant unramified morphism `f : X ⟶ Y` of finite type from a connected
scheme to a locally noetherian normal scheme is étale; then `X` is normal and irreducible.

SGA's proof is followed. The set `U` of points where `f` is flat is open (IV.6.10, from
Exposé IV); it is closed, because a point `x` of its closure has a generization `ξ` in `U`, the
generizations of `f ξ` lift along the flat stalk map at `ξ`, so `x` has a generization over a
maximal point of `Y`: then `𝒪_{f x} → 𝒪_x` is injective and I.9.5(ii) applies. It is nonempty
because a quasi-compact dominant morphism hits the maximal points of `Y`. The skeleton
(`etale_of_dominant_of_flat_of_injective`) is also used for the geometrically unibranch variant
in I.11.

Quasi-compactness is part of SGA's standing "finite type" hypothesis and cannot be dropped: a
connected infinite grid of lines immersed in the plane is dominant and unramified, but not étale.
-/

universe u

open AlgebraicGeometry CategoryTheory Topology

namespace SGA.SGA1.ExposeI

section Topology

/-- In a quasi-sober space every point has a maximal generization (the generic point of an
irreducible component through it). -/
theorem exists_specializes_forall_specializes {α : Type*} [TopologicalSpace α] [QuasiSober α]
    (x : α) : ∃ η, η ⤳ x ∧ ∀ z, z ⤳ η → η ⤳ z := by
  have hZ := (isIrreducible_irreducibleComponent (x := x)).isGenericPoint_genericPoint
    isClosed_irreducibleComponent
  refine ⟨_, hZ.specializes mem_irreducibleComponent, fun z hz ↦ ?_⟩
  have hsub : irreducibleComponent x ⊆ closure {z} := by
    rw [← hZ.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hz))
      isClosed_closure
  have := eq_irreducibleComponent isIrreducible_singleton.closure.isPreirreducible hsub
  rw [specializes_iff_mem_closure, hZ.def, ← this]
  exact subset_closure rfl

/-- In a locally noetherian scheme, a point in the closure of an open set `U` has a
generization in `U` (the closure of `U` near a point is a finite union of irreducible closed
sets meeting `U`). -/
theorem exists_mem_specializes_of_mem_closure {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ closure U) : ∃ ξ ∈ U, ξ ⤳ x := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hWn : TopologicalSpace.NoetherianSpace W := noetherianSpace_of_isAffineOpen W hW
  set T : Set X := U ∩ W
  have : TopologicalSpace.NoetherianSpace T := by
    have hW' := (TopologicalSpace.noetherianSpace_set_iff (W : Set X)).mp hWn
    exact (TopologicalSpace.noetherianSpace_set_iff T).mpr
      fun t ht ↦ hW' t (ht.trans Set.inter_subset_right)
  have hxT : x ∈ closure T := by
    have := W.2.inter_closure ⟨hxW, hx⟩
    rwa [Set.inter_comm] at this
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := T)
  have hT : T = ⋃ C ∈ irreducibleComponents T, ((↑) '' C : Set X) := by
    rw [← Set.image_iUnion₂, ← Set.sUnion_eq_biUnion, sUnion_irreducibleComponents,
      Set.image_univ, Subtype.range_coe]
  rw [hT, hfin.closure_biUnion] at hxT
  simp only [Set.mem_iUnion] at hxT
  obtain ⟨C, hC, hxC⟩ := hxT
  have hCirr : IsIrreducible ((↑) '' C : Set X) := hC.1.image _ continuous_subtype_val.continuousOn
  have hξ := hCirr.isGenericPoint_genericPoint_closure
  refine ⟨_, ?_, hξ.specializes hxC⟩
  rw [hξ.mem_open_set_iff hU]
  obtain ⟨c, hc⟩ := hC.1.nonempty
  exact ⟨c, subset_closure ⟨c, hc, rfl⟩, c.2.1⟩

end Topology

variable {X Y : Scheme.{u}}

/-- A flat stalk map lifts generizations: if `f` is flat at `x` and `y ⤳ f x`, then `y = f x'`
for some generization `x'` of `x` (going down). -/
theorem exists_specializes_of_flat_stalkMap (f : X ⟶ Y) {x : X}
    (hx : (f.stalkMap x).hom.Flat) {y : Y} (hy : y ⤳ f x) : ∃ x', x' ⤳ x ∧ f x' = y := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range (Y.fromSpecStalk (f x)) := by
    rw [Scheme.range_fromSpecStalk]; exact hy
  have h : p ⤳ PrimeSpectrum.comap (f.stalkMap x).hom
      (IsLocalRing.closedPoint (X.presheaf.stalk x)) := by
    rw [IsLocalRing.comap_closedPoint]; exact IsLocalRing.specializes_closedPoint p
  obtain ⟨q, -, hq⟩ := hx.generalizingMap_comap h
  refine ⟨X.fromSpecStalk x q, ?_, ?_⟩
  · have := (IsLocalRing.specializes_closedPoint q).map (X.fromSpecStalk x).continuous
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  · change (X.fromSpecStalk x ≫ f) q = _
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact congrArg (Y.fromSpecStalk (f x)) hq

set_option backward.isDefEq.respectTransparency.types false in
/-- A quasi-compact dominant morphism hits every maximal point of its target, i.e. the generic
point of every irreducible component (Stacks 01RL). If `η` were not in the image, on each of
finitely many affine opens covering `f⁻¹ W` some function not vanishing at `η` would vanish, and
their product would define a neighbourhood of `η` missing the image. -/
theorem mem_range_of_forall_specializes (f : X ⟶ Y) [QuasiCompact f] [IsDominant f] {η : Y}
    (hη : ∀ z, z ⤳ η → η ⤳ z) : η ∈ Set.range f := by
  classical
  by_contra hne
  obtain ⟨_, ⟨W, hW, rfl⟩, hηW, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  set p := hW.primeIdealOf ⟨η, hηW⟩
  -- `f⁻¹ W` is covered by finitely many affine opens
  let ι := {V : X.affineOpens // (V : X.Opens) ≤ f ⁻¹ᵁ W}
  obtain ⟨t, ht⟩ := (f.isCompact_preimage hW.isCompact).elim_finite_subcover
    (fun V : ι ↦ (V.1 : Set X)) (fun V ↦ V.1.1.2) (by
      intro x hx
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hx (f ⁻¹ᵁ W).2
      exact Set.mem_iUnion.2 ⟨⟨⟨V, hV⟩, hVW⟩, hxV⟩)
  -- on each of them some `s ∉ p` vanishes, since no point of `V` lies over `η`
  have key (V : ι) : ∃ s ∉ p.asIdeal, f.appLE W V.1 V.2 s = 0 := by
    by_contra! H
    let M := p.asIdeal.primeCompl.map (f.appLE W V.1 V.2).hom
    have hM : Disjoint ((⊥ : Ideal Γ(X, V.1)) : Set Γ(X, V.1)) M := by
      rw [Set.disjoint_left]
      rintro _ h ⟨s, hs, rfl⟩
      exact H s hs h
    obtain ⟨Q, hQ, -, hQM⟩ := Ideal.exists_le_prime_disjoint _ M hM
    let x := V.1.2.fromSpec ⟨Q, hQ⟩
    have hxV : x ∈ V.1.1 := by
      rw [← SetLike.mem_coe, ← V.1.2.range_fromSpec]; exact ⟨_, rfl⟩
    have hQx : V.1.2.primeIdealOf ⟨x, hxV⟩ = ⟨Q, hQ⟩ :=
      V.1.2.fromSpec.isOpenEmbedding.injective (V.1.2.fromSpec_primeIdealOf ⟨x, hxV⟩)
    have hle : hW.primeIdealOf ⟨f x, V.2 hxV⟩ ≤ p := by
      rw [← IsAffineOpen.comap_primeIdealOf_appLE W hW V.1.1 V.1.2 V.2 hxV, hQx]
      intro a ha
      by_contra hap
      exact Set.disjoint_left.mp hQM ha ⟨a, hap, rfl⟩
    have hsp : f x ⤳ η := by
      have := ((PrimeSpectrum.le_iff_specializes _ _).mp hle).map hW.fromSpec.continuous
      rwa [hW.fromSpec_primeIdealOf, hW.fromSpec_primeIdealOf] at this
    exact hne ⟨x, (hsp.antisymm (hη _ hsp)).eq⟩
  choose s hsp hs0 using key
  -- the basic open `D(∏ s)` of `W` contains `η` but no point of the image
  set g := ∏ V ∈ t, s V
  have hg : g ∉ p.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    push Not
    exact fun V _ ↦ hsp V
  obtain ⟨x, P, hP, hPx⟩ := f.denseRange.exists_mem_open
    (hW.fromSpec.isOpenEmbedding.isOpenMap _ (PrimeSpectrum.basicOpen g).2)
    ⟨η, p, hg, hW.fromSpec_primeIdealOf _⟩
  have hxW : x ∈ f ⁻¹ᵁ W := by
    change f x ∈ W
    rw [← hPx, ← SetLike.mem_coe, ← hW.range_fromSpec]; exact ⟨_, rfl⟩
  obtain ⟨V, hVt, hxV⟩ := Set.mem_iUnion₂.1 (ht hxW)
  have hPf : hW.primeIdealOf ⟨f x, V.2 hxV⟩ = P :=
    hW.fromSpec.isOpenEmbedding.injective ((hW.fromSpec_primeIdealOf _).trans hPx.symm)
  have hg0 : f.appLE W V.1 V.2 g = 0 := by
    simp only [g]
    rw [← Finset.mul_prod_erase t s hVt, map_mul, hs0, zero_mul]
  have hV : IsAffineOpen V.1.1 := V.1.2
  have hmem : g ∈ P.asIdeal := by
    rw [← hPf, ← IsAffineOpen.comap_primeIdealOf_appLE W hW V.1.1 hV V.2 hxV,
      PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, hg0]
    exact zero_mem _
  exact hP hmem

/-- The key step of I.9.11: if `Y` is normal and `f` unramified, locally of finite type, then
`f` is flat at every point `x` having a generization `ξ` over a maximal point of `Y`. Indeed
`𝒪_{f x} → 𝒪_x` is then injective, and I.9.5(ii) applies. -/
theorem flat_stalkMap_of_specializes (f : X ⟶ Y) [LocallyOfFiniteType f] [FormallyUnramified f]
    (hY : IsNormalScheme Y) {x ξ : X} (hξ : ξ ⤳ x) (hmax : ∀ z, z ⤳ f ξ → f ξ ⤳ z) :
    (f.stalkMap x).hom.Flat := by
  obtain ⟨_, _⟩ := hY (f x)
  have hinj := injective_stalkMap_of_specializes f hξ hmax
  have h₂ := FormallyUnramified.stalkMap f x
  have h₃ := LocallyOfFiniteType.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  exact flat_of_injective_of_formallyUnramified hinj

/-- The skeleton of the proof of I.9.11: let `f : X ⟶ Y` be dominant, unramified and of finite
type, with `Y` locally noetherian with local rings domains and `X` connected, and suppose that `f`
is flat at every point where its stalk map is injective (I.9.5(ii) if `Y` is normal, I.11 if `Y`
is geometrically unibranch). Then `f` is étale. The flat locus `U` is open (IV.6.10); it is
closed, because a point `x` of its closure has a generization `ξ ∈ U`, the generizations of `f ξ`
lift along the flat stalk map at `ξ`, so `x` has a generization over a maximal point of `Y`, and
then `𝒪_{f x} → 𝒪_x` is injective; it is nonempty because `f` hits the maximal points of `Y`. -/
theorem etale_of_dominant_of_flat_of_injective (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] [FormallyUnramified f] [IsDominant f]
    [ConnectedSpace X] (hdom : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (H : ∀ x : X, Function.Injective (f.stalkMap x) → (f.stalkMap x).hom.Flat) : Etale f := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hflat {x ξ : X} (hξ : ξ ⤳ x) (hmax : ∀ z, z ⤳ f ξ → f ξ ⤳ z) :
      (f.stalkMap x).hom.Flat := by
    have := hdom (f x)
    exact H x (injective_stalkMap_of_specializes f hξ hmax)
  let U : Set X := {x | (f.stalkMap x).hom.Flat}
  have hUo : IsOpen U := ExposeIV.isOpen_setOf_flat_stalkMap f
  have hUc : IsClosed U := by
    refine isClosed_of_closure_subset fun x hx ↦ ?_
    obtain ⟨ξ, hξU, hξx⟩ := exists_mem_specializes_of_mem_closure hUo hx
    obtain ⟨η, hη, hηmax⟩ := exists_specializes_forall_specializes (f ξ)
    obtain ⟨ξ', hξ'ξ, rfl⟩ := exists_specializes_of_flat_stalkMap f hξU hη
    exact hflat (hξ'ξ.trans hξx) hηmax
  have hUne : U.Nonempty := by
    obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
    obtain ⟨η, -, hηmax⟩ := exists_specializes_forall_specializes (f x₀)
    obtain ⟨x, rfl⟩ := mem_range_of_forall_specializes f hηmax
    exact ⟨x, hflat specializes_rfl hηmax⟩
  have hU : U = Set.univ := (isClopen_iff.mp ⟨hUc, hUo⟩).resolve_left hUne.ne_empty
  have : Flat f := Flat.of_stalkMap f fun x ↦ (hU ▸ Set.mem_univ x : x ∈ U)
  exact etale_of_flat_unramified_locallyNoetherian f

/-- I.9.11: let `f : X ⟶ Y` be dominant, unramified and of finite type (the exposé's standing
hypothesis), with `Y` locally noetherian and normal (all local rings integrally closed domains)
and `X` connected. Then `f` is étale. -/
theorem etale_of_dominant_of_formallyUnramified (f : X ⟶ Y) [IsLocallyNoetherian Y]
    [LocallyOfFiniteType f] [QuasiCompact f] [FormallyUnramified f] [IsDominant f]
    [ConnectedSpace X] (hY : IsNormalScheme Y) : Etale f := by
  refine etale_of_dominant_of_flat_of_injective f (fun y ↦ (hY y).1) fun x hinj ↦ ?_
  obtain ⟨_, _⟩ := hY (f x)
  have h₂ := FormallyUnramified.stalkMap f x
  have h₃ := LocallyOfFiniteType.stalkMap f x
  algebraize [(f.stalkMap x).hom]
  exact flat_of_injective_of_formallyUnramified hinj

/-- If `𝒪_x` is a domain, every generization of `x` is a specialization of the generic point
of `Spec 𝒪_x` (the image of the prime `0`). -/
theorem specializes_of_isDomain_stalk {x η : X} [IsDomain (X.presheaf.stalk x)] (hη : η ⤳ x) :
    X.fromSpecStalk x ⟨⊥, Ideal.isPrime_bot⟩ ⤳ η := by
  obtain ⟨q, rfl⟩ : η ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hη
  exact ((PrimeSpectrum.le_iff_specializes _ q).mp bot_le).map (X.fromSpecStalk x).continuous

/-- A connected locally noetherian scheme whose local rings are domains (e.g. a connected
normal scheme) is irreducible. Near each point only the irreducible components through that
point matter, and they all have the generic point of `Spec 𝒪_x` as generic point; so the
closure of a maximal point is open. -/
theorem irreducibleSpace_of_isDomain_stalk [IsLocallyNoetherian X] [ConnectedSpace X]
    (h : ∀ x : X, IsDomain (X.presheaf.stalk x)) : IrreducibleSpace X := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  obtain ⟨η₀, -, hη₀⟩ := exists_specializes_forall_specializes x₀
  let Z : Set X := {x | η₀ ⤳ x}
  have hZcl : Z = closure {η₀} := Set.ext fun _ ↦ specializes_iff_mem_closure
  have hZo : IsOpen Z := by
    refine isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
    have : TopologicalSpace.NoetherianSpace W := noetherianSpace_of_isAffineOpen W hW
    -- the irreducible components of `W` avoiding `x`
    let S := {C ∈ irreducibleComponents W | (⟨x, hxW⟩ : W) ∉ C}
    have hS : S.Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset (Set.sep_subset _ _)
    have hN : IsOpen (⋃₀ S)ᶜ := by
      rw [Set.sUnion_eq_biUnion]
      exact (Set.Finite.isClosed_biUnion hS fun C hC ↦
        isClosed_of_mem_irreducibleComponents C hC.1).isOpen_compl
    refine ⟨Subtype.val '' (⋃₀ S)ᶜ, ?_, W.isOpenEmbedding'.isOpenMap _ hN,
      ⟨⟨x, hxW⟩, fun hx' ↦ ?_, rfl⟩⟩
    · rintro _ ⟨y, hyN, rfl⟩
      obtain ⟨C, hC, hyC⟩ : ∃ C ∈ irreducibleComponents W, y ∈ C := by
        have := Set.mem_univ y
        rwa [← sUnion_irreducibleComponents, Set.mem_sUnion] at this
      have hxC : (⟨x, hxW⟩ : W) ∈ C := by
        by_contra hxC
        exact hyN (Set.mem_sUnion_of_mem hyC ⟨hC, hxC⟩)
      have hCirr : IsIrreducible (Subtype.val '' C : Set X) :=
        hC.1.image _ continuous_subtype_val.continuousOn
      have hη := hCirr.isGenericPoint_genericPoint_closure
      have hηx : hCirr.genericPoint ⤳ x := hη.specializes (subset_closure ⟨_, hxC, rfl⟩)
      have hηy : hCirr.genericPoint ⤳ y.1 := hη.specializes (subset_closure ⟨_, hyC, rfl⟩)
      have := h x
      have h₁ := specializes_of_isDomain_stalk hx
      have h₂ := specializes_of_isDomain_stalk hηx
      exact ((hη₀ _ h₁).trans h₂).trans hηy
    · obtain ⟨C, ⟨-, hxC⟩, hC'⟩ := Set.mem_sUnion.mp hx'
      exact hxC hC'
  have hZ : Z = Set.univ := (isClopen_iff.mp ⟨hZcl ▸ isClosed_closure, hZo⟩).resolve_left
    (Set.nonempty_iff_ne_empty.mp ⟨η₀, specializes_rfl⟩)
  rw [irreducibleSpace_def, Set.top_eq_univ, ← hZ, hZcl]
  exact isIrreducible_singleton.closure

/-- I.9.11, conclusion: under the hypotheses of `etale_of_dominant_of_formallyUnramified`, `X`
is normal (I.9.10) and hence, being connected, irreducible. -/
theorem isNormalScheme_and_irreducibleSpace_of_dominant_of_formallyUnramified (f : X ⟶ Y)
    [IsLocallyNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] [FormallyUnramified f]
    [IsDominant f] [ConnectedSpace X] (hY : IsNormalScheme Y) :
    IsNormalScheme X ∧ IrreducibleSpace X := by
  have := etale_of_dominant_of_formallyUnramified f hY
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hX := isNormalScheme_of_etale f hY
  exact ⟨hX, irreducibleSpace_of_isDomain_stalk fun x ↦ (hX x).1⟩

end SGA.SGA1.ExposeI
