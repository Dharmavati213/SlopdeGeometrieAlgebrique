/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannExtensionTopology
import SGA.Foundations.Analytic.RiemannSurfacePunctures
import SGA.Foundations.Topology.SurfaceLoopAround

/-!
# Ends of a covering over a punctured neighbourhood (topology for XIII.2.12 over `ℂ`)

Let `q : Y → Z` be a closed continuous map with finite fibres, `Y` Hausdorff and locally connected,
and `a ∈ Z` a point over which every point of `Y` has connected punctured neighbourhoods (e.g.
`Y = Ē(ℂ)` for the normalization `Ē` of a curve `X` in a finite étale covering `E` of `X - {a}`,
and `Z = X(ℂ)`). Over a small punctured neighbourhood `S` of `a` on which `q` is a covering, the
connected components of `q⁻¹(S)` (the "ends" of `E(ℂ)` at `a`) correspond to the points of the
fibre `q⁻¹(a)`: each component `K` has exactly one point of `q⁻¹(a)` in its closure, and contains
a whole punctured neighbourhood of it. Consequently, for a group `G` acting on `Y` by
homeomorphisms over `Z` (the automorphisms of a Galois covering), the stabilizer of the component
through `e` is the stabilizer of the corresponding point of `q⁻¹(a)`
(`exists_forall_smul_mem_connectedComponentIn_iff`). With the comparison of components with the
orbits of a small loop around `a`, this identifies the local monodromy at `a` with the stabilizer
of a point of `Ē(ℂ)` over `a`.

* `image_connectedComponentIn_eq`: a connected component of `q⁻¹(S)`, `S` preconnected, maps onto
  `S` when `q` restricts to a covering with finite fibres over `S`;
* `exists_mem_nhds_forall_connectedComponentIn`: the structure of the components of `q⁻¹(S)`;
* `exists_forall_smul_mem_connectedComponentIn_iff`: the stabilizers.

## References

* [O. Forster, *Lectures on Riemann Surfaces*, §8][forster1981] (local structure of proper
  holomorphic maps, here only its topological part)
-/

open Topology Set Filter

namespace SGA.SGA1.ExposeXIII.LoopTopology

open ExposeXII ExposeXII.RiemannExtension

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- A connected component of `q⁻¹(S)` maps onto `S` if `S` is preconnected, `q⁻¹(S)` is locally
connected and `q` restricts over `S` to a covering map with finite fibres. -/
theorem image_connectedComponentIn_eq [LocallyConnectedSpace Y] {q : Y → Z} {S : Set Z}
    (hS : IsPreconnected S) (hcov : IsCoveringMap (S.restrictPreimage q))
    (hfin : ∀ z, (q ⁻¹' {z}).Finite) {e : Y} (he : q e ∈ S) (hSo : IsOpen (q ⁻¹' S)) :
    q '' connectedComponentIn (q ⁻¹' S) e = S := by
  set f := S.restrictPreimage q
  have : PreconnectedSpace S := Subtype.preconnectedSpace hS
  have : LocallyConnectedSpace (q ⁻¹' S) := hSo.locallyConnectedSpace
  have hffin : ∀ z, (f ⁻¹' {z}).Finite := fun z ↦ by
    refine ((hfin z).preimage Subtype.val_injective.injOn).subset fun y hy ↦ ?_
    simp only [mem_preimage, mem_singleton_iff] at hy ⊢
    exact congrArg Subtype.val hy
  set K := connectedComponent (⟨e, he⟩ : q ⁻¹' S)
  have hKo : IsOpen (f '' K) := hcov.isOpenMap _ isOpen_connectedComponent
  have hKc : IsClosed (f '' K) := hcov.isClosedMap_of_finite hffin _ isClosed_connectedComponent
  have hne : (f '' K).Nonempty := ⟨_, mem_image_of_mem _ mem_connectedComponent⟩
  have huniv : f '' K = univ :=
    IsClopen.eq_univ ⟨hKc, hKo⟩ hne
  rw [connectedComponentIn_eq_image (F := q ⁻¹' S) (x := e) he, image_image]
  ext z
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · intro hz
    obtain ⟨y, hyK, hy⟩ := huniv.symm ▸ (mem_univ (⟨z, hz⟩ : S) : (⟨z, hz⟩ : S) ∈ univ)
    exact ⟨y, hyK, congrArg Subtype.val hy⟩

variable [T2Space Y] [LocallyConnectedSpace Y] {q : Y → Z}

/-- **The ends at a point.** Let `q : Y → Z` be continuous and closed with finite fibres, `Y`
Hausdorff and locally connected, and `a ∈ Z` such that every point of `q⁻¹(a)` has connected
punctured neighbourhoods. There is a neighbourhood `M` of `a` such that for every open punctured
neighbourhood `S ⊆ M` of `a` (`a ∉ S`, `S ∪ {a} ∈ 𝓝 a`), preconnected, over which `q` is a
covering, every connected component `K` of `q⁻¹(S)` has exactly one point `y₀` of `q⁻¹(a)` in its
closure, and contains `N ∖ {y₀}` for some open neighbourhood `N` of `y₀` (with `N ∖ {y₀}`
nonempty). -/
theorem exists_mem_nhds_forall_connectedComponentIn (hqc : Continuous q) (hq : IsClosedMap q)
    (hfin : ∀ z, (q ⁻¹' {z}).Finite) {a : Z}
    (hP : ∀ y ∈ q ⁻¹' {a}, HasConnectedPuncturedNhds y) :
    ∃ M ∈ 𝓝 a, ∀ S : Set Z, S ⊆ M → a ∉ S → insert a S ∈ 𝓝 a → IsOpen S → IsPreconnected S →
      IsCoveringMap (S.restrictPreimage q) → ∀ e : Y, q e ∈ S →
      ∃ y₀, q y₀ = a ∧ y₀ ∈ closure (connectedComponentIn (q ⁻¹' S) e) ∧
        (∀ y, q y = a → y ∈ closure (connectedComponentIn (q ⁻¹' S) e) → y = y₀) ∧
        ∃ N, IsOpen N ∧ y₀ ∈ N ∧ (N \ {y₀}).Nonempty ∧
          N \ {y₀} ⊆ connectedComponentIn (q ⁻¹' S) e := by
  classical
  set P := q ⁻¹' {a}
  obtain ⟨U, hU, hUd⟩ := (hfin a).t2_separation
  have hUo (y : Y) : IsOpen (U y) := (hU y).2
  set M := (q '' (⋃ y ∈ P, U y)ᶜ)ᶜ
  have hMo : IsOpen M := (hq _ (isOpen_biUnion fun y _ ↦ hUo y).isClosed_compl).isOpen_compl
  have haM : a ∈ M := by
    rintro ⟨y, hy, hya⟩
    exact hy (mem_iUnion₂.mpr ⟨y, hya, (hU y).1⟩)
  have hqM : q ⁻¹' M ⊆ ⋃ y ∈ P, U y := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  -- the only point of `P` in `U y₀` is `y₀`
  have hPU {y y' : Y} (hy : y ∈ P) (hy' : y' ∈ P) (h : y' ∈ U y) : y' = y := by
    by_contra hne
    exact Set.disjoint_left.mp (hUd hy' hy hne) (hU y').1 h
  refine ⟨M, hMo.mem_nhds haM, fun S hSM haS hSa hSo hSc hcov e he ↦ ?_⟩
  set K := connectedComponentIn (q ⁻¹' S) e
  have hSo' : IsOpen (q ⁻¹' S) := hSo.preimage hqc
  have hKS : K ⊆ q ⁻¹' S := connectedComponentIn_subset _ _
  have heK : e ∈ K := mem_connectedComponentIn he
  have hKimg : q '' K = S := image_connectedComponentIn_eq hSc hcov hfin he hSo'
  -- `K` lies in one `U y₀`
  obtain ⟨y₀, hy₀P, heU⟩ := mem_iUnion₂.mp (hqM (hSM he))
  have hKU : K ⊆ U y₀ :=
    subset_of_isPreconnected_of_pairwiseDisjoint isPreconnected_connectedComponentIn
      hUo hUd (fun y hy ↦ hqM (hSM (hKS hy))) hy₀P ⟨e, heK, heU⟩
  -- a connected punctured neighbourhood of `y₀` over `S ∪ {a}`, inside `U y₀`
  have hW : U y₀ ∩ q ⁻¹' insert a S ∈ 𝓝 y₀ :=
    inter_mem ((hUo y₀).mem_nhds (hU y₀).1) (hqc.continuousAt.preimage_mem_nhds (hy₀P ▸ hSa))
  obtain ⟨N, hNW, hNo, hy₀N, hNc, hNne⟩ := hP y₀ hy₀P _ hW
  have hNS : N \ {y₀} ⊆ q ⁻¹' S := by
    rintro z ⟨hzN, hzy₀⟩
    rcases (hNW hzN).2 with h | h
    · exact absurd (hPU hy₀P h (hNW hzN).1) hzy₀
    · exact h
  -- `K` meets `N ∖ {y₀}`: points of `K` over points of `S` near `a` lie in `N`
  set F := (N ∪ ⋃ y ∈ P \ {y₀}, U y)ᶜ
  have hFc : IsClosed F := (hNo.union (isOpen_biUnion fun y _ ↦ hUo y)).isClosed_compl
  have haF : a ∉ q '' F := by
    rintro ⟨y, hyF, hya⟩
    refine hyF ?_
    by_cases hy : y = y₀
    · exact Or.inl (hy ▸ hy₀N)
    · exact Or.inr (mem_iUnion₂.mpr ⟨y, ⟨hya, hy⟩, (hU y).1⟩)
  have hM₁ : (q '' F)ᶜ ∈ 𝓝 a := (hq _ hFc).isOpen_compl.mem_nhds haF
  -- a point of `S` in `(q '' F)ᶜ`: the image of a point of a small punctured neighbourhood
  obtain ⟨N₂, hN₂, -, hy₀N₂, -, z₂, hz₂N₂, hz₂y₀⟩ := hP y₀ hy₀P _ (inter_mem hW
    (hqc.continuousAt.preimage_mem_nhds (hy₀P ▸ hM₁)))
  have hz₂S : q z₂ ∈ S := by
    rcases ((hN₂ hz₂N₂).1).2 with h | h
    · exact absurd (hPU hy₀P h ((hN₂ hz₂N₂).1).1) hz₂y₀
    · exact h
  obtain ⟨k, hkK, hk⟩ := hKimg.symm ▸ hz₂S
  have hkN : k ∈ N := by
    have hkF : k ∉ F := fun h ↦ (hN₂ hz₂N₂).2 ⟨k, h, hk⟩
    simp only [F, mem_compl_iff, not_not, mem_union, mem_iUnion₂] at hkF
    rcases hkF with h | ⟨y, ⟨hyP, hyy₀⟩, hyk⟩
    · exact h
    · exact absurd (hKU hkK) (Set.disjoint_left.mp (hUd hyP hy₀P hyy₀) hyk)
  have hky₀ : k ≠ y₀ := by
    rintro rfl
    have h1 : q k = a := hy₀P
    exact haS (by rw [← h1, hk]; exact hz₂S)
  have hNK : N \ {y₀} ⊆ K := by
    have hk' : k ∈ N \ {y₀} := ⟨hkN, hky₀⟩
    change N \ {y₀} ⊆ connectedComponentIn (q ⁻¹' S) e
    rw [connectedComponentIn_eq hkK]
    exact hNc.subset_connectedComponentIn hk' hNS
  -- `y₀` is in the closure of `K`, and is the only point of `P` there
  have hy₀cl : y₀ ∈ closure K := by
    rw [mem_closure_iff_nhds]
    intro O hO
    obtain ⟨N₃, hN₃, -, -, -, z₃, hz₃, hz₃y₀⟩ := hP y₀ hy₀P _ (inter_mem hO (hNo.mem_nhds hy₀N))
    exact ⟨z₃, (hN₃ hz₃).1, hNK ⟨(hN₃ hz₃).2, hz₃y₀⟩⟩
  refine ⟨y₀, hy₀P, hy₀cl, fun y hy hycl ↦ ?_, N, hNo, hy₀N, hNne, hNK⟩
  by_contra hyy₀
  have := mem_closure_iff_nhds.mp hycl (U y) ((hUo y).mem_nhds (hU y).1)
  obtain ⟨z, hzU, hzK⟩ := this
  exact Set.disjoint_left.mp (hUd hy hy₀P hyy₀) hzU (hKU hzK)

/-- **Stabilizers of ends.** With the hypotheses of `exists_mem_nhds_forall_connectedComponentIn`,
let a group `G` act on `Y` by homeomorphisms over `Z` (`q (g • y) = q y`). For `S` a small
punctured neighbourhood of `a` as there and `e ∈ q⁻¹(S)`, there is a point `y₀ ∈ q⁻¹(a)` whose
stabilizer is the stabilizer of the connected component of `q⁻¹(S)` through `e`:
`g • e` lies in that component iff `g • y₀ = y₀`. -/
theorem exists_forall_smul_mem_connectedComponentIn_iff (hqc : Continuous q)
    (hq : IsClosedMap q) (hfin : ∀ z, (q ⁻¹' {z}).Finite) {a : Z}
    (hP : ∀ y ∈ q ⁻¹' {a}, HasConnectedPuncturedNhds y) {G : Type*} [Group G] [MulAction G Y]
    [ContinuousConstSMul G Y] (hGq : ∀ (g : G) (y : Y), q (g • y) = q y) :
    ∃ M ∈ 𝓝 a, ∀ S : Set Z, S ⊆ M → a ∉ S → insert a S ∈ 𝓝 a → IsOpen S → IsPreconnected S →
      IsCoveringMap (S.restrictPreimage q) → ∀ e : Y, q e ∈ S →
      ∃ y₀, q y₀ = a ∧ ∀ g : G, g • e ∈ connectedComponentIn (q ⁻¹' S) e ↔ g • y₀ = y₀ := by
  obtain ⟨M, hM, H⟩ := exists_mem_nhds_forall_connectedComponentIn hqc hq hfin hP
  refine ⟨M, hM, fun S hSM haS hSa hSo hSc hcov e he ↦ ?_⟩
  obtain ⟨y₀, hy₀a, hy₀cl, hy₀u, N, hNo, hy₀N, -, hNK⟩ := H S hSM haS hSa hSo hSc hcov e he
  refine ⟨y₀, hy₀a, fun g ↦ ?_⟩
  -- `g` maps the component through `e` to the component through `g • e`
  have hpre : (Homeomorph.smul g : Y ≃ₜ Y) '' (q ⁻¹' S) = q ⁻¹' S := by
    ext y
    constructor
    · rintro ⟨y', hy', rfl⟩
      change q (g • y') ∈ S
      rwa [hGq]
    · intro hy
      refine ⟨g⁻¹ • y, ?_, smul_inv_smul g y⟩
      change q (g⁻¹ • y) ∈ S
      rwa [hGq]
  have himg : (Homeomorph.smul g : Y ≃ₜ Y) '' connectedComponentIn (q ⁻¹' S) e =
      connectedComponentIn (q ⁻¹' S) (g • e) := by
    rw [Homeomorph.image_connectedComponentIn (s := q ⁻¹' S) (x := e) _ he, hpre]
    rfl
  have hge : q (g • e) ∈ S := by rwa [hGq]
  obtain ⟨y₀', hy₀'a, hy₀'cl, hy₀'u, N', hN'o, hy₀N', -, hN'K⟩ :=
    H S hSM haS hSa hSo hSc hcov _ hge
  -- the point of `q⁻¹(a)` attached to the component through `g • e` is `g • y₀`
  have hgy₀ : g • y₀ = y₀' := by
    refine hy₀'u _ (by rw [hGq, hy₀a]) ?_
    rw [← himg]
    have := (Homeomorph.smul g : Y ≃ₜ Y).image_closure (connectedComponentIn (q ⁻¹' S) e)
    rw [← this]
    exact mem_image_of_mem _ hy₀cl
  constructor
  · intro hgK
    have heq : connectedComponentIn (q ⁻¹' S) (g • e) = connectedComponentIn (q ⁻¹' S) e :=
      (connectedComponentIn_eq hgK).symm
    rw [hgy₀]
    exact hy₀u y₀' hy₀'a (heq ▸ hy₀'cl)
  · intro hg
    rw [hg] at hgy₀
    subst hgy₀
    -- both components contain a punctured neighbourhood of `y₀`, so they meet
    obtain ⟨N₃, hN₃, -, -, -, w, hw, hwy₀⟩ :=
      hP y₀ hy₀a _ (inter_mem (hNo.mem_nhds hy₀N) (hN'o.mem_nhds hy₀N'))
    have hw₁ : w ∈ connectedComponentIn (q ⁻¹' S) e := hNK ⟨(hN₃ hw).1, hwy₀⟩
    have hw₂ : w ∈ connectedComponentIn (q ⁻¹' S) (g • e) := hN'K ⟨(hN₃ hw).2, hwy₀⟩
    rw [connectedComponentIn_eq hw₁, ← connectedComponentIn_eq hw₂]
    exact mem_connectedComponentIn hge

section Orbits

variable {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]

omit [TopologicalSpace Z] in
/-- In a locally path-connected space, the connected component of a point in an open set is its
path component there. -/
theorem connectedComponentIn_eq_pathComponentIn [LocallyPathConnectedSpace E] {F : Set E}
    (hF : IsOpen F) {e : E} (he : e ∈ F) : connectedComponentIn F e = pathComponentIn F e := by
  refine le_antisymm ?_ ((isPathConnected_pathComponentIn he).isConnected.isPreconnected
    |>.subset_connectedComponentIn (mem_pathComponentIn_self he) pathComponentIn_subset)
  have hV : IsOpen (F \ pathComponentIn F e) := by
    have : F \ pathComponentIn F e = ⋃ y ∈ F \ pathComponentIn F e, pathComponentIn F y := by
      ext z
      simp only [Set.mem_sdiff, mem_iUnion, exists_prop]
      constructor
      · intro hz
        exact ⟨z, hz, mem_pathComponentIn_self hz.1⟩
      · rintro ⟨y, ⟨hyF, hye⟩, hz⟩
        refine ⟨pathComponentIn_subset hz, fun hze ↦ hye ?_⟩
        rw [← (pathComponentIn_congr hz).symm.trans (pathComponentIn_congr hze)]
        exact mem_pathComponentIn_self hyF
    rw [this]
    exact isOpen_biUnion fun y _ ↦ hF.pathComponentIn y
  exact isPreconnected_connectedComponentIn.subset_left_of_subset_union (hF.pathComponentIn e) hV
    disjoint_sdiff_right (fun z hz ↦ by
      by_cases h : z ∈ pathComponentIn F e
      · exact Or.inl h
      · exact Or.inr ⟨connectedComponentIn_subset _ _ hz, h⟩)
    ⟨e, mem_connectedComponentIn he, mem_pathComponentIn_self he⟩

omit [TopologicalSpace Z] in
/-- **Orbits of a generating loop and components.** Let `p : E → B` be a covering map, `E` locally
path-connected, `S ⊆ B` open, `b ∈ S`, and `c ∈ π₁(S, b)` generating `π₁(S, b)`. Two points
`e₁`, `e₂` of the fibre over `b` lie in the same connected component of `p⁻¹(S)` iff
`e₂ = cⁿ • e₁` for some `n ∈ ℤ`, the action being the monodromy of `p` along the image of `cⁿ`
in `π₁(B, b)`. -/
theorem mem_connectedComponentIn_iff_exists_zpow [LocallyPathConnectedSpace E] {p : E → B}
    (hp : IsCoveringMap p) {S : Set B} (hS : IsOpen S) {b : S}
    {c : _root_.FundamentalGroup S b} (hc : ∀ γ : _root_.FundamentalGroup S b,
      γ ∈ Subgroup.zpowers c) (e₁ e₂ : p ⁻¹' {(b : B)}) :
    (e₂ : E) ∈ connectedComponentIn (p ⁻¹' S) e₁ ↔
      ∃ n : ℤ, hp.monodromy (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ b
        (c ^ n)) e₁ = e₂ := by
  have he₁ : (e₁ : E) ∈ p ⁻¹' S := by
    have : p e₁ = b := e₁.2
    change p e₁ ∈ S
    rw [this]
    exact b.2
  rw [connectedComponentIn_eq_pathComponentIn (hS.preimage hp.continuous) he₁]
  constructor
  · intro h
    obtain ⟨Γ, hΓ⟩ := h
    -- the projection of `Γ`, a loop in `S`
    have h₁ : p e₁ = b := e₁.2
    have h₂ : p e₂ = b := e₂.2
    let γ : Path b b := ((Γ.map hp.continuous).cast h₁.symm h₂.symm).codRestrict
      (by rintro _ ⟨t, rfl⟩; exact hΓ t)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hc (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk γ)))
    refine ⟨n, hp.monodromy_eq_of_map_eq (Path.Homotopic.Quotient.mk Γ) ?_⟩
    rw [hn]
    rfl
  · rintro ⟨n, hn⟩
    rw [← hn]
    generalize c ^ n = γ
    induction γ using Path.Homotopic.Quotient.ind with | mk γ => ?_
    have h0 : (γ.map continuous_subtype_val : C(unitInterval, B)) 0 = p e₁ := by
      change ((γ 0 : S) : B) = p e₁
      rw [γ.source]
      exact e₁.2.symm
    refine ⟨⟨⟨hp.liftPath (γ.map continuous_subtype_val) e₁ h0, ?_⟩,
      hp.liftPath_zero (γ_0 := h0), rfl⟩,
      fun t ↦ ?_⟩
    · exact (hp.liftPath (γ.map continuous_subtype_val) e₁ h0).continuous
    · change p (hp.liftPath (γ.map continuous_subtype_val) e₁ h0 t) ∈ S
      rw [← Function.comp_apply (f := p), hp.liftPath_lifts]
      exact (γ t).2

end Orbits

section PuncturedDisc

/-- A loop around `s` generates `π₁(Y, y)` (for `j` an open embedding onto `C ∖ {s}`, `C` convex
and open, e.g. a punctured disc): every element is a power of it. -/
theorem mem_zpowers_of_isLoopAround {Y : Type} [TopologicalSpace Y] {j : Y → ℂ} {C : Set ℂ}
    {s : ℂ} (hCc : Convex ℝ C) (hCo : IsOpen C) (hs : s ∈ C) (hj : IsOpenEmbedding j)
    (hjr : range j = C \ {s}) {y : Y} {σ : _root_.FundamentalGroup Y y}
    (h : FundamentalGroup.IsLoopAround j s σ) (γ : _root_.FundamentalGroup Y y) :
    γ ∈ Subgroup.zpowers σ := by
  obtain ⟨b, hb⟩ := Complex.exists_freeGroupBasis_fundamentalGroup_of_isOpenEmbedding
    (S := {s}) hCc hCo (by simpa using hs) hj (by simpa using hjr) y
  set s₀ : ({s} : Finset ℂ) := ⟨s, Finset.mem_singleton_self s⟩
  have hσ : b s₀ = σ :=
    FundamentalGroup.IsLoopAround.eq hCc hCo hs hj.isEmbedding hjr (hb s₀) h
  have hrange : Set.range b = {σ} := by
    ext g
    constructor
    · rintro ⟨t, rfl⟩
      have ht : t = s₀ := Subtype.ext (Finset.mem_singleton.mp t.2)
      rw [ht, hσ]
      rfl
    · rintro rfl
      exact ⟨s₀, hσ⟩
  have htop : Subgroup.closure (Set.range b) = ⊤ := by
    have hb' (t : ({s} : Finset ℂ)) : b.repr.symm (FreeGroup.of t) = b t :=
      (MulEquiv.symm_apply_eq _).mpr (FreeGroupBasis.repr_apply_coe b t).symm
    have h1 : Set.range b = b.repr.symm '' Set.range (FreeGroup.of (α := ({s} : Finset ℂ))) := by
      ext g
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨FreeGroup.of t, ⟨t, rfl⟩, hb' t⟩
      · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
        exact ⟨t, (hb' t).symm⟩
    have e := MonoidHom.map_closure b.repr.symm.toMonoidHom
      (Set.range (FreeGroup.of (α := ({s} : Finset ℂ))))
    rw [FreeGroup.closure_range_of, Subgroup.map_top_of_surjective _ b.repr.symm.surjective] at e
    rw [h1]
    exact e.symm
  rw [hrange, ← Subgroup.zpowers_eq_closure] at htop
  rw [htop]
  trivial

end PuncturedDisc

end SGA.SGA1.ExposeXIII.LoopTopology
