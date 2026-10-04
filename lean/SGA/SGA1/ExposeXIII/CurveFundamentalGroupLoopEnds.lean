/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXIII.CurveFundamentalGroupLoopTopology
import SGA.Foundations.Topology.SurfaceFilling
import SGA.Foundations.Topology.CoveringOfFunctor

/-!
# The local monodromy around a point is the stabilizer of a point over it (topology)

This file assembles the topological half of the comparison of inertia groups with loops
(XIII.2.12 over `ℂ`, registry row C32). The setting, with `XC = X(ℂ)`:

* a covering map `p : E → U'` (`E = E(ℂ)` for an étale covering `E` of an open `U ⊆ X`,
  `U' = U(ℂ)`), with an open embedding `u : U' → XC`;
* a closed map `q : Y → Z` with finite fibres (`Y = Ē(ℂ)` for the normalization `Ē` of an affine
  neighbourhood `Z = V(ℂ)` of `a` in `E`), with an open embedding `c : Z → XC`, such that every
  point of `Y` over `a` has connected punctured neighbourhoods;
* a common open piece `P` (`P = C(ℂ)`, `C` the algebra of `E` over `U ∩ V`) embedded in `E` and in
  `Y`, compatibly with the maps to `XC`, covering the parts of `E` and `Y` over a chart
  `φ : W ≃ₜ D(0, r)` of `XC` at `a` (minus `a`);
* a group `G` acting on `E`, `P` and `Y` compatibly (the automorphism group of a Galois covering).

Then for a loop `σ` around `a` in the chart, at a base point `x ∈ U'`, and a point `e` of the fibre
of `p` over `x`, there is a point `y₀ ∈ Y` over `a` such that `g ∈ G` maps `e` into its orbit under
the monodromy of `σ` iff `g` fixes `y₀`
(`LoopTopology.exists_forall_exists_monodromy_zpow_eq_smul_iff`).

The proof: shrink the circle of `σ` into a punctured disc `S` small enough for the ends of `Y` at
`a` (`exists_forall_smul_mem_connectedComponentIn_iff`); conjugate by the path of `σ` (deck
transformations commute with monodromy); the orbits of the circle on the fibre are the connected
components of `p⁻¹(S)` (`mem_connectedComponentIn_iff_exists_zpow`, the circle generating
`π₁(S)` by `mem_zpowers_of_isLoopAround`); move them to `Y` through `P`
(`image_connectedComponentIn_preimage`).
-/

open Topology Set Filter Metric

namespace SGA.SGA1.ExposeXIII.LoopTopology

open ExposeXII ExposeXII.RiemannExtension

section Embedding

variable {P T : Type*} [TopologicalSpace P] [TopologicalSpace T]

/-- An embedding `f : P → T` maps the connected component of `x` in `f⁻¹(F)` onto the connected
component of `f x` in `F`, when `F` lies in the range of `f`. -/
theorem image_connectedComponentIn_preimage {f : P → T} (hf : IsEmbedding f) {F : Set T}
    (hF : F ⊆ range f) {x : P} (hx : f x ∈ F) :
    f '' connectedComponentIn (f ⁻¹' F) x = connectedComponentIn F (f x) := by
  refine (hf.continuous.continuousOn.image_connectedComponentIn_subset hx).trans
    (connectedComponentIn_mono _ (image_preimage_subset f F)) |>.antisymm ?_
  -- the preimage of the component of `f x` is preconnected
  set K := connectedComponentIn F (f x)
  have hKF : K ⊆ F := connectedComponentIn_subset F (f x)
  have hK : f '' (f ⁻¹' K) = K := image_preimage_eq_of_subset (hKF.trans hF)
  have hpre : IsPreconnected (f ⁻¹' K) := by
    rw [← hf.isInducing.isPreconnected_image, hK]
    exact isPreconnected_connectedComponentIn
  have hsub : f ⁻¹' K ⊆ connectedComponentIn (f ⁻¹' F) x :=
    hpre.subset_connectedComponentIn (mem_connectedComponentIn hx) (preimage_mono hKF)
  calc K = f '' (f ⁻¹' K) := hK.symm
    _ ⊆ f '' connectedComponentIn (f ⁻¹' F) x := image_mono hsub

/-- For an injective embedding `f : P → T`, `F ⊆ range f` and `f x ∈ F`, `f x'` lies in the
component of `f x` in `F` iff `x'` lies in the component of `x` in `f⁻¹(F)`. -/
theorem mem_connectedComponentIn_iff_of_isEmbedding {f : P → T} (hf : IsEmbedding f) {F : Set T}
    (hF : F ⊆ range f) {x x' : P} (hx : f x ∈ F) :
    f x' ∈ connectedComponentIn F (f x) ↔ x' ∈ connectedComponentIn (f ⁻¹' F) x := by
  rw [← image_connectedComponentIn_preimage hf hF hx, hf.injective.mem_set_image]

end Embedding

section Ends

variable {XC : Type*} {U' : Type} {E P Y Z : Type*} [TopologicalSpace XC] [TopologicalSpace U']
  [TopologicalSpace E] [TopologicalSpace P] [TopologicalSpace Y] [TopologicalSpace Z]

omit [TopologicalSpace E] in
/-- The class of `δ · γ · δ⁻¹` is the image of `γ` under the change of base point along `δ⁻¹`. -/
lemma fundamentalGroupMulEquivOfPath_symm_apply {x b : U'} (δ : Path x b)
    (γ : _root_.FundamentalGroup U' b) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath δ.symm γ =
      (Path.Homotopic.Quotient.mk δ).trans (γ.trans (Path.Homotopic.Quotient.mk δ.symm)) := by
  simp only [FundamentalGroup.fundamentalGroupMulEquivOfPath]
  rw [CategoryTheory.Iso.conj_apply]
  simp only [Path.Homotopic.Quotient.mk''_eq_mk, Path.Homotopic.Quotient.mk_symm,
    CategoryTheory.Groupoid.isoEquivHom_symm_apply_inv,
    CategoryTheory.Groupoid.isoEquivHom_symm_apply_hom]
  rw [← CategoryTheory.Groupoid.inv_eq_inv]
  have h : CategoryTheory.Groupoid.inv (Path.Homotopic.Quotient.mk δ).symm =
      FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk δ) := by
    change ((Path.Homotopic.Quotient.mk δ).symm).symm = _
    rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_symm, Path.symm_symm]
  rw [h]
  rfl

/-- The monodromy of a loop conjugated by a path: if `σ = δ · c · δ⁻¹`, then `σⁿ` acts on the fibre
over the base point of `δ` as `δ⁻¹ ∘ cⁿ ∘ δ`. -/
theorem monodromy_zpow_conj {p : E → U'} (hp : IsCoveringMap p) {x b : U'} (δ : Path x b)
    (c : _root_.FundamentalGroup U' b) (n : ℤ) (e : p ⁻¹' {x}) :
    hp.monodromy ((FundamentalGroup.fundamentalGroupMulEquivOfPath δ.symm c) ^ n) e =
      hp.monodromy (Path.Homotopic.Quotient.mk δ.symm)
        (hp.monodromy (c ^ n) (hp.monodromy (Path.Homotopic.Quotient.mk δ) e)) := by
  rw [← map_zpow, fundamentalGroupMulEquivOfPath_symm_apply]
  rw [IsCoveringMap.monodromy_trans_apply, IsCoveringMap.monodromy_trans_apply]

/-- **The local monodromy is the stabilizer of a point over `a`.** Let `p : E → U'` be a covering
map (`E` locally path-connected) and `u : U' → X̂` an open embedding; let `q : Y → Z` be a
continuous closed map with finite fibres (`Y` Hausdorff and locally connected) and `c : Z → X̂` an
open embedding. Let `φ : W ≃ₜ D(0, r)` be a chart of `X̂` at `c a` (`W ⊆ c(Z)` open, `φ (c a) = 0`)
with `W ∩ u(U') = W ∖ {c a}`, such that `q` is a covering over `c⁻¹(W) ∖ {a}` and every point of `Y`
over `a` has connected punctured neighbourhoods. Let `P` be a space with embeddings `ιE : P → E`
and `ιY : P → Y` over `X̂` (`u ∘ p ∘ ιE = c ∘ q ∘ ιY`) whose ranges contain the parts of `E` and of
`Y` over `W ∖ {c a}`, and let a group `G` act on `E`, `P`, `Y`, continuously on `E` and `Y`, over
`U'` and `Z`, compatibly with `ιE` and `ιY`. Then for a loop `σ` around `a` in the coordinate
`Complex.chartCoord φ ∘ u` at `x ∈ U'` and a point `e` of the fibre of `p` over `x`, there is
`y₀ ∈ q⁻¹(a)` such that `g ∈ G` maps `e` into its orbit under the monodromy of `σ` iff
`g • y₀ = y₀`. -/
theorem exists_forall_exists_monodromy_zpow_eq_smul_iff [LocallyPathConnectedSpace E] [T2Space Y]
    [LocallyConnectedSpace Y] {p : E → U'} (hp : IsCoveringMap p) {q : Y → Z} (hqc : Continuous q)
    (hq : IsClosedMap q) (hfin : ∀ z, (q ⁻¹' {z}).Finite) {u : U' → XC} (hu : IsOpenEmbedding u)
    {c : Z → XC} (hc : IsOpenEmbedding c) {W : Set XC} (hW : IsOpen W) (hWc : W ⊆ range c)
    {r : ℝ} (φ : W ≃ₜ ball (0 : ℂ) r) {a : Z} (haW : c a ∈ W) (hφa : (φ ⟨c a, haW⟩ : ℂ) = 0)
    (hWu : ∀ w ∈ W, w ∈ range u ↔ w ≠ c a) (hqcov : IsCoveringMapOn q (c ⁻¹' W \ {a}))
    (hP : ∀ y ∈ q ⁻¹' {a}, HasConnectedPuncturedNhds y) {ιE : P → E} (hιE : IsEmbedding ιE)
    {ιY : P → Y} (hιY : IsEmbedding ιY) (hι : ∀ π, u (p (ιE π)) = c (q (ιY π)))
    (hιErange : p ⁻¹' (u ⁻¹' W) ⊆ range ιE) (hιYrange : q ⁻¹' (c ⁻¹' W \ {a}) ⊆ range ιY)
    {G : Type*} [Group G] [MulAction G E] [ContinuousConstSMul G E] [MulAction G P]
    [MulAction G Y] [ContinuousConstSMul G Y] (hGp : ∀ (g : G) e, p (g • e) = p e)
    (hGq : ∀ (g : G) y, q (g • y) = q y) (hGιE : ∀ (g : G) π, ιE (g • π) = g • ιE π)
    (hGιY : ∀ (g : G) π, ιY (g • π) = g • ιY π) {x : U'} {σ : _root_.FundamentalGroup U' x}
    (hσ : FundamentalGroup.IsLoopAround (fun y ↦ Complex.chartCoord φ (u y)) 0 σ)
    (e : p ⁻¹' {x}) :
    ∃ y₀ : Y, q y₀ = a ∧ ∀ g : G,
      (∃ n : ℤ, (hp.monodromy (σ ^ n) e : E) = g • (e : E)) ↔ g • y₀ = y₀ := by
  classical
  -- the ends of `Y` at `a`
  obtain ⟨M, hM, hends⟩ := exists_forall_smul_mem_connectedComponentIn_iff hqc hq hfin hP hGq
  -- a radius `ρ` such that the points of `W` with coordinate in `D(0, ρ)` lie in `c '' M`
  have h0r : (0 : ℂ) ∈ ball (0 : ℂ) r := by
    have := (φ ⟨c a, haW⟩).2
    rwa [hφa] at this
  have hr : 0 < r := by simpa using h0r
  set z₀ : ball (0 : ℂ) r := ⟨0, h0r⟩
  have hφz₀ : φ.symm z₀ = ⟨c a, haW⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext hφa.symm
  have hpre : (fun z : ball (0 : ℂ) r ↦ ((φ.symm z : W) : XC)) ⁻¹' (c '' M) ∈ 𝓝 z₀ := by
    refine (continuous_subtype_val.comp φ.symm.continuous).continuousAt.preimage_mem_nhds ?_
    simp only [Function.comp_apply, hφz₀]
    exact hc.isOpenMap.image_mem_nhds hM
  obtain ⟨ε, hε, hεM⟩ := Metric.mem_nhds_iff.mp hpre
  set ρ := min ε r
  have hρ : 0 < ρ := lt_min hε hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hWM : ∀ w (hw : w ∈ W), (φ ⟨w, hw⟩ : ℂ) ∈ ball (0 : ℂ) ρ → w ∈ c '' M := by
    intro w hw hwρ
    have hmem : φ ⟨w, hw⟩ ∈ Metric.ball z₀ ε := by
      rw [mem_ball, Subtype.dist_eq]
      exact (mem_ball.mp hwρ).trans_le (min_le_left _ _)
    simpa using hεM hmem
  -- the punctured disc of radius `ρ` in the chart, and its parts in `U'` and in `Z`
  set D : Set ℂ := ball (0 : ℂ) ρ \ {0} with hD
  set SW : Set XC := {w | ∃ hw : w ∈ W, (φ ⟨w, hw⟩ : ℂ) ∈ D} with hSW
  have hSW' : SW = (fun z : ball (0 : ℂ) r ↦ ((φ.symm z : W) : XC)) ''
      {z : ball (0 : ℂ) r | (z : ℂ) ∈ D} := by
    ext w
    constructor
    · rintro ⟨hw, hwD⟩
      exact ⟨φ ⟨w, hw⟩, hwD, by simp⟩
    · rintro ⟨z, hzD, rfl⟩
      exact ⟨(φ.symm z).2, by simpa using hzD⟩
  have hSWo : IsOpen SW := by
    have : SW = Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' D)) := by
      ext w
      constructor
      · rintro ⟨hw, hwD⟩
        exact ⟨⟨w, hw⟩, hwD, rfl⟩
      · rintro ⟨⟨w, hw⟩, hwD, rfl⟩
        exact ⟨hw, hwD⟩
    rw [this]
    exact hW.isOpenMap_subtype_val _ (((isOpen_ball.sdiff isClosed_singleton).preimage
      continuous_subtype_val).preimage φ.continuous)
  have hSWW : SW ⊆ W := fun w hw ↦ hw.1
  have hSWa : ∀ w ∈ SW, w ≠ c a := by
    rintro w ⟨hw, hwD⟩ rfl
    exact hwD.2 hφa
  have hSWc : IsPreconnected SW := by
    rw [hSW']
    refine IsPreconnected.image ?_ _ (continuous_subtype_val.comp φ.symm.continuous).continuousOn
    rw [← Topology.IsInducing.subtypeVal.isPreconnected_image]
    have : Subtype.val '' {z : ball (0 : ℂ) r | (z : ℂ) ∈ D} = D := by
      ext z
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hz
        exact ⟨⟨z, ball_subset_ball hρr hz.1⟩, hz, rfl⟩
    rw [this]
    exact isPreconnected_ball_diff_zero_complex ρ
  have hopen : ∀ D' : Set ℂ, IsOpen D' → IsOpen {w | ∃ hw : w ∈ W, (φ ⟨w, hw⟩ : ℂ) ∈ D'} := by
    intro D' hD'
    have : {w | ∃ hw : w ∈ W, (φ ⟨w, hw⟩ : ℂ) ∈ D'} =
        Subtype.val '' (φ ⁻¹' (Subtype.val ⁻¹' D')) := by
      ext w
      constructor
      · rintro ⟨hw, hwD⟩
        exact ⟨⟨w, hw⟩, hwD, rfl⟩
      · rintro ⟨⟨w, hw⟩, hwD, rfl⟩
        exact ⟨hw, hwD⟩
    rw [this]
    exact hW.isOpenMap_subtype_val _ ((hD'.preimage continuous_subtype_val).preimage φ.continuous)
  set SU : Set U' := u ⁻¹' SW with hSU
  set SZ : Set Z := c ⁻¹' SW with hSZ
  have hSUo : IsOpen SU := hSWo.preimage hu.continuous
  have hSZo : IsOpen SZ := hSWo.preimage hc.continuous
  -- the coordinate is an open embedding of `SU` onto `D`
  let h₁ : SU → W := fun y ↦ ⟨u y, y.2.1⟩
  have hh₁ : IsOpenEmbedding h₁ := by
    rw [← IsOpenEmbedding.of_comp_iff _ hW.isOpenEmbedding_subtypeVal]
    exact hu.comp hSUo.isOpenEmbedding_subtypeVal
  let jS : SU → ℂ := fun y ↦ (φ (h₁ y) : ℂ)
  have hjS : IsOpenEmbedding jS :=
    (isOpen_ball.isOpenEmbedding_subtypeVal.comp φ.isOpenEmbedding).comp hh₁
  have hjSr : range jS = D := by
    ext z
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2.2
    · intro hz
      set w : W := φ.symm ⟨z, ball_subset_ball hρr hz.1⟩
      have hwa : (w : XC) ≠ c a := by
        intro hw
        have h1 : φ w = ⟨z, ball_subset_ball hρr hz.1⟩ := by simp [w]
        have h2 : w = ⟨c a, haW⟩ := Subtype.ext hw
        rw [h2] at h1
        exact hz.2 (by rw [mem_singleton_iff, ← hφa]; exact (congrArg Subtype.val h1).symm)
      obtain ⟨y, hy⟩ := (hWu w w.2).mpr hwa
      have hyS : y ∈ SU := by
        change u y ∈ SW
        refine ⟨by rw [hy]; exact w.2, ?_⟩
        have : (⟨u y, by rw [hy]; exact w.2⟩ : W) = w := Subtype.ext hy
        rw [this]
        simpa [w] using hz
      refine ⟨⟨y, hyS⟩, ?_⟩
      change (φ ⟨u y, _⟩ : ℂ) = z
      have : (⟨u y, hyS.1⟩ : W) = w := Subtype.ext hy
      rw [this]
      simp [w]
  have hjS_eq (y : SU) : Complex.chartCoord φ (u y) = jS y :=
    Complex.chartCoord_of_mem φ y.2.1
  -- shrink the circle of `σ` into `D`
  obtain ⟨r₁, hr₁, hr₁ρ, κ, hκ, δ, rfl⟩ := hσ.exists_radius_lt hρ
  have hκS (z : ↥(closedBall (0 : ℂ) r₁ \ {0})) : κ z ∈ SU := by
    have hz0 : (z : ℂ) ≠ 0 := z.2.2
    have hjz : Complex.chartCoord φ (u (κ z)) = z := hκ z
    have hw : u (κ z) ∈ W := Complex.mem_of_chartCoord_ne_zero φ (by rw [hjz]; exact hz0)
    refine ⟨hw, ?_⟩
    rw [← Complex.chartCoord_of_mem φ hw, hjz]
    exact ⟨mem_ball.mpr ((mem_closedBall.mp z.2.1).trans_lt hr₁ρ), hz0⟩
  let κ' : C(↥(closedBall (0 : ℂ) r₁ \ {0}), SU) :=
    ⟨fun z ↦ ⟨κ z, hκS z⟩, κ.continuous.subtype_mk _⟩
  let z₁ : ↥(closedBall (0 : ℂ) r₁ \ {0}) := ⟨0 + r₁, Complex.add_ofReal_mem_closedBall_diff hr₁⟩
  set circ := (Complex.circlePath (0 : ℂ) r₁).codRestrict (Complex.range_circlePath_subset hr₁)
  set c₀ : _root_.FundamentalGroup SU (κ' z₁) := Path.Homotopic.Quotient.mk (circ.map κ'.continuous)
  have hc₀ : FundamentalGroup.IsLoopAround jS 0 c₀ := by
    refine ⟨r₁, hr₁, κ', fun z ↦ ?_, Path.refl _, ?_⟩
    · rw [← hjS_eq]
      exact hκ z
    · rw [Path.refl_symm, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.refl_trans,
        Path.Homotopic.Quotient.trans_refl]
  have hgen : ∀ γ : _root_.FundamentalGroup SU (κ' z₁), γ ∈ Subgroup.zpowers c₀ :=
    mem_zpowers_of_isLoopAround (convex_ball 0 ρ) isOpen_ball (mem_ball_self hρ) hjS hjSr hc₀
  -- the circle in `U'`, and `σ = δ c δ⁻¹`
  set cU : _root_.FundamentalGroup U' (κ z₁) := Path.Homotopic.Quotient.mk (circ.map κ.continuous)
  have hmap : FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ (κ' z₁) c₀ = cU := by
    change Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk _) _ = _
    rw [← Path.Homotopic.Quotient.mk_map]
    rfl
  have hσc : Path.Homotopic.Quotient.mk ((δ.trans (circ.map κ.continuous)).trans δ.symm) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath δ.symm cU := by
    rw [fundamentalGroupMulEquivOfPath_symm_apply, Path.Homotopic.Quotient.mk_trans,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc]
  -- deck transformations commute with monodromy
  have hdeck (g : G) {x₁ x₂ : U'} (γ : Path.Homotopic.Quotient x₁ x₂) (e₁ : p ⁻¹' {x₁}) :
      g • (hp.monodromy γ e₁ : E) = hp.monodromy γ ⟨g • (e₁ : E), (hGp g _).trans e₁.2⟩ :=
    hp.apply_monodromy hp ⟨(g • ·), continuous_const_smul g⟩ (hGp g) γ e₁
  -- move to the base point `b` along `δ`
  set Δ : Path.Homotopic.Quotient x (κ z₁) := Path.Homotopic.Quotient.mk δ
  set ε : p ⁻¹' {κ z₁} := hp.monodromy Δ e
  have hΔΔ (e₁ : p ⁻¹' {κ z₁}) : hp.monodromy Δ (hp.monodromy Δ.symm e₁) = e₁ := by
    rw [← IsCoveringMap.monodromy_trans_apply, Path.Homotopic.Quotient.symm_trans,
      IsCoveringMap.monodromy_refl]
    rfl
  have hΔΔ' (e₁ : p ⁻¹' {x}) : hp.monodromy Δ.symm (hp.monodromy Δ e₁) = e₁ := by
    rw [← IsCoveringMap.monodromy_trans_apply, Path.Homotopic.Quotient.trans_symm,
      IsCoveringMap.monodromy_refl]
    rfl
  have hstep1 (g : G) : (∃ n : ℤ, (hp.monodromy (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk ((δ.trans (circ.map κ.continuous)).trans δ.symm)) ^ n) e :
        E) = g • (e : E)) ↔
      ∃ n : ℤ, (hp.monodromy (cU ^ n) ε : E) = g • (ε : E) := by
    refine exists_congr fun n ↦ ?_
    rw [hσc, monodromy_zpow_conj hp δ cU n e]
    have hgε : g • (ε : E) = hp.monodromy Δ ⟨g • (e : E), (hGp g _).trans e.2⟩ := hdeck g Δ e
    rw [hgε, Path.Homotopic.Quotient.mk_symm]
    constructor
    · intro h
      have h' : hp.monodromy Δ.symm (hp.monodromy (cU ^ n) ε) =
          ⟨g • (e : E), (hGp g _).trans e.2⟩ := Subtype.ext h
      rw [← h', hΔΔ]
    · intro h
      have h' : hp.monodromy (cU ^ n) ε = hp.monodromy Δ ⟨g • (e : E), (hGp g _).trans e.2⟩ :=
        Subtype.ext h
      rw [h', hΔΔ']
  -- the orbits of the circle on the fibre over `b` are the components of `p⁻¹(SU)`
  have hbS : κ z₁ ∈ SU := hκS z₁
  have hstep2 (g : G) : (∃ n : ℤ, (hp.monodromy (cU ^ n) ε : E) = g • (ε : E)) ↔
      g • (ε : E) ∈ connectedComponentIn (p ⁻¹' SU) ε := by
    rw [mem_connectedComponentIn_iff_exists_zpow hp hSUo (b := κ' z₁) hgen ε
      ⟨g • (ε : E), (hGp g _).trans ε.2⟩]
    refine exists_congr fun n ↦ ?_
    rw [map_zpow, hmap]
    exact ⟨fun h ↦ Subtype.ext h, fun h ↦ congrArg Subtype.val h⟩
  -- move the components to `Y` through `P`
  have hSUE : p ⁻¹' SU ⊆ range ιE := fun e₁ he₁ ↦ hιErange (hSWW he₁)
  have hSZY : q ⁻¹' SZ ⊆ range ιY := fun y hy ↦
    hιYrange ⟨hSWW hy, fun hya ↦ hSWa _ hy (by rw [mem_singleton_iff.mp hya])⟩
  have hpreP : ιE ⁻¹' (p ⁻¹' SU) = ιY ⁻¹' (q ⁻¹' SZ) := by
    ext π
    change u (p (ιE π)) ∈ SW ↔ c (q (ιY π)) ∈ SW
    rw [hι]
  have hεS : (ε : E) ∈ p ⁻¹' SU := by
    change p ε ∈ SU
    rw [show p ε = κ z₁ from ε.2]
    exact hbS
  obtain ⟨π, hπ⟩ := hSUE hεS
  have hπS : ιE π ∈ p ⁻¹' SU := hπ ▸ hεS
  have hqπ : q (ιY π) ∈ SZ := by
    change c (q (ιY π)) ∈ SW
    rw [← hι]
    exact hπS
  have hstep3 (g : G) : g • (ε : E) ∈ connectedComponentIn (p ⁻¹' SU) ε ↔
      g • ιY π ∈ connectedComponentIn (q ⁻¹' SZ) (ιY π) := by
    rw [← hπ, ← hGιE, ← hGιY, mem_connectedComponentIn_iff_of_isEmbedding hιE hSUE hπS,
      mem_connectedComponentIn_iff_of_isEmbedding hιY hSZY hqπ, hpreP]
  -- the ends of `Y` over the punctured disc `SZ`
  have hSZM : SZ ⊆ M := by
    rintro z ⟨hw, hD⟩
    obtain ⟨m, hm, hmz⟩ := hWM (c z) hw hD.1
    rwa [← hc.injective hmz]
  have haSZ : a ∉ SZ := fun h ↦ hSWa _ h rfl
  have hins : insert a SZ ∈ 𝓝 a := by
    have hcaT : c a ∈ {w | ∃ hw : w ∈ W, (φ ⟨w, hw⟩ : ℂ) ∈ ball (0 : ℂ) ρ} :=
      ⟨haW, by rw [hφa]; exact mem_ball_self hρ⟩
    refine Filter.mem_of_superset (((hopen _ isOpen_ball).preimage hc.continuous).mem_nhds hcaT) ?_
    rintro z ⟨hw, hzρ⟩
    by_cases hza : z = a
    · exact Or.inl hza
    · refine Or.inr ⟨hw, hzρ, fun h0 ↦ hza (hc.injective ?_)⟩
      have h1 : φ ⟨c z, hw⟩ = φ ⟨c a, haW⟩ :=
        Subtype.ext ((mem_singleton_iff.mp h0).trans hφa.symm)
      exact congrArg Subtype.val (φ.injective h1)
  have hSZc : IsPreconnected SZ := by
    rw [← hc.isInducing.isPreconnected_image,
      image_preimage_eq_of_subset (hSWW.trans hWc)]
    exact hSWc
  have hcovZ : IsCoveringMap (SZ.restrictPreimage q) :=
    IsCoveringMapOn.isCoveringMap_restrictPreimage (s := SZ) (hf := fun z hz ↦
      hqcov z ⟨hSWW hz, fun hza ↦ haSZ (by rwa [mem_singleton_iff.mp hza] at hz)⟩)
  obtain ⟨y₀, hy₀a, hy₀⟩ := hends SZ hSZM haSZ hins hSZo hSZc hcovZ (ιY π) hqπ
  exact ⟨y₀, hy₀a, fun g ↦ (hstep1 g).trans ((hstep2 g).trans ((hstep3 g).trans (hy₀ g)))⟩

end Ends

end SGA.SGA1.ExposeXIII.LoopTopology
