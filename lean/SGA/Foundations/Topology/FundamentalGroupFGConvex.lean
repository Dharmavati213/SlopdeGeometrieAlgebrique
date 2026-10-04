/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import SGA.Foundations.Topology.FundamentalGroupFG
import SGA.Foundations.Topology.PathConnectedHelpersBasic

/-!
# Spaces covered by finitely many convex sets have finitely generated `π₁`

Let `X` be a path-connected subset of a real topological vector space, covered by finitely many
open convex sets `W i ⊆ X`. Then `π₁(X, x)` is finitely generated
(`FundamentalGroup.fg_of_finite_convex_cover`): if `W i` and `W j` meet, `W i ∪ W j` is star-convex
about a common point, hence contractible, so `FundamentalGroup.fg_of_finite_cover` applies.

The complement of a finite set `S` in `ℂ` has such a cover (half-planes far away, half-discs around
the points of `S`, and finitely many discs in between), so `π₁(ℂ ∖ S)` is finitely generated
(`Complex.fg_fundamentalGroup_compl`). This is an input of this formalization's planned
elementary-fibration route to Riemann existence in higher dimension (SGA 1 XII.5.1; that route is
not formalized yet, and SGA's own proof differs: it uses resolution of singularities). The
fibration argument only needs finite generation of `π₁` of the fibre, a plane minus finitely many
points.

## References

* [A. Hatcher, *Algebraic Topology*, §1.2][hatcher02]
-/

open Set Topology Metric

namespace FundamentalGroup

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [ContinuousAdd E]
  [ContinuousSMul ℝ E]

/-- In a subset `X` of a real topological vector space, a nonempty star-convex set `T ⊆ X` is
relatively simply connected (any two paths in `T` with the same endpoints are homotopic in `X`). -/
theorem isRelSimplyConnected_preimage_of_starConvex {X T : Set E} {p : E}
    (hT : StarConvex ℝ p T) (hne : T.Nonempty) (hTX : T ⊆ X) :
    IsRelSimplyConnected (((↑) : X → E) ⁻¹' T) := by
  have : ContractibleSpace T := hT.contractibleSpace hne
  intro a b γ γ' hγ hγ'
  have h₁ : range (γ.map continuous_subtype_val) ⊆ T := by
    rintro _ ⟨t, rfl⟩
    exact hγ ⟨t, rfl⟩
  have h₂ : range (γ'.map continuous_subtype_val) ⊆ T := by
    rintro _ ⟨t, rfl⟩
    exact hγ' ⟨t, rfl⟩
  exact (SimplyConnectedSpace.paths_homotopic ((γ.map _).codRestrict h₁)
    ((γ'.map _).codRestrict h₂)).map ⟨inclusion hTX, continuous_inclusion hTX⟩

/-- **Finite generation of `π₁` from a finite convex cover.** Let `X` be a path-connected subset of
a real topological vector space, covered by finitely many open convex sets `W i ⊆ X`. Then
`π₁(X, x)` is finitely generated. -/
theorem fg_of_finite_convex_cover {X : Set E} (hX : IsPathConnected X) {ι : Type*} [Finite ι]
    (W : ι → Set E) (hWo : ∀ i, IsOpen (W i)) (hWc : ∀ i, Convex ℝ (W i)) (hWX : ∀ i, W i ⊆ X)
    (hcov : X ⊆ ⋃ i, W i) (x : X) : Group.FG (FundamentalGroup X x) := by
  have : PathConnectedSpace X := isPathConnected_iff_pathConnectedSpace.mp hX
  refine fg_of_finite_cover (ι := {i // (W i).Nonempty}) (fun i ↦ ((↑) : X → E) ⁻¹' W i.1)
    (fun i ↦ (hWo i.1).preimage continuous_subtype_val) (fun i ↦ ?_) (fun y ↦ ?_)
    (fun i j hij ↦ ?_) x
  · rw [IsInducing.subtypeVal.isPathConnected_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr (hWX i.1)]
    exact (hWc i.1).isPathConnected i.2
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov y.2)
    exact ⟨⟨i, ⟨y, hi⟩⟩, hi⟩
  · obtain ⟨y, hyi, hyj⟩ := hij
    rw [← preimage_union]
    exact isRelSimplyConnected_preimage_of_starConvex
      (((hWc i.1).starConvex hyi).union ((hWc j.1).starConvex hyj)) ⟨y, Or.inl hyi⟩
      (union_subset (hWX i.1) (hWX j.1))

end FundamentalGroup

namespace Complex

/-- The complement of a finite set `S ⊆ ℂ` is covered by finitely many open convex sets
contained in it. -/
theorem exists_finite_convex_cover_compl {S : Set ℂ} (hS : S.Finite) :
    ∃ 𝒲 : Set (Set ℂ), 𝒲.Finite ∧ (∀ W ∈ 𝒲, IsOpen W ∧ Convex ℝ W ∧ W ⊆ Sᶜ) ∧ Sᶜ ⊆ ⋃₀ 𝒲 := by
  -- a box `|re|, |im| < R` containing `S`
  obtain ⟨R₀, hR₀⟩ := hS.isBounded.subset_closedBall 0
  set R := R₀ + 1
  have hSR : ∀ s ∈ S, |s.re| < R ∧ |s.im| < R := fun s hs ↦ by
    have h := mem_closedBall_zero_iff.mp (hR₀ hs)
    exact ⟨(abs_re_le_norm s).trans_lt (by linarith), (abs_im_le_norm s).trans_lt (by linarith)⟩
  -- radii isolating the points of `S`
  have hiso : ∀ s ∈ S, ∃ ρ > 0, ∀ s' ∈ S, s' ∈ ball s ρ → s' = s := by
    intro s hs
    have hU : IsOpen (S \ {s})ᶜ := (hS.subset sdiff_subset).isClosed.isOpen_compl
    obtain ⟨ρ, hρ, hball⟩ := isOpen_iff.mp hU s (fun h ↦ h.2 rfl)
    refine ⟨ρ, hρ, fun s' hs' hs'b ↦ ?_⟩
    by_contra hne
    exact hball hs'b ⟨hs', hne⟩
  choose! ρ hρpos hρ using hiso
  -- the sets of the cover
  let far : Set (Set ℂ) := {{z | R < z.re}, {z | z.re < -R}, {z | R < z.im}, {z | z.im < -R}}
  let disc : ℂ → Set (Set ℂ) := fun s ↦
    {ball s (ρ s) ∩ {z | s.re < z.re}, ball s (ρ s) ∩ {z | z.re < s.re},
      ball s (ρ s) ∩ {z | s.im < z.im}, ball s (ρ s) ∩ {z | z.im < s.im}}
  let K : Set ℂ := ({z | |z.re| ≤ R} ∩ {z | |z.im| ≤ R}) ∩ ⋂ s ∈ S, (ball s (ρ s))ᶜ
  have hKS : K ⊆ Sᶜ := fun z hz hzS ↦ by
    have := mem_iInter₂.mp hz.2 z hzS
    exact this (mem_ball_self (hρpos z hzS))
  have hK : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine IsClosed.inter ?_ (isClosed_biInter fun s _ ↦ isOpen_ball.isClosed_compl)
      exact (isClosed_le (continuous_abs.comp continuous_re) continuous_const).inter
        (isClosed_le (continuous_abs.comp continuous_im) continuous_const)
    · refine (isBounded_closedBall (x := (0 : ℂ)) (r := 2 * R)).subset fun z hz ↦ ?_
      rw [mem_closedBall_zero_iff]
      have h₁ : |z.re| ≤ R := hz.1.1
      have h₂ : |z.im| ≤ R := hz.1.2
      calc ‖z‖ ≤ |z.re| + |z.im| := norm_le_abs_re_add_abs_im z
        _ ≤ 2 * R := by linarith
  have hr : ∀ z ∈ Sᶜ, ∃ r > 0, ball z r ⊆ Sᶜ := isOpen_iff.mp hS.isClosed.isOpen_compl
  choose! r hrpos hr using hr
  obtain ⟨t, htK, hKt⟩ := hK.elim_nhds_subcover (fun z ↦ ball z (r z))
    (fun z hz ↦ ball_mem_nhds z (hrpos z (hKS hz)))
  refine ⟨far ∪ (⋃ s ∈ S, disc s) ∪ ((fun z ↦ ball z (r z)) '' t), ?_, ?_, ?_⟩
  · refine ((toFinite far).union (hS.biUnion fun s _ ↦ toFinite (disc s))).union
      (t.finite_toSet.image _)
  · have hre : ∀ a : ℝ, IsOpen {z : ℂ | a < z.re} ∧ Convex ℝ {z : ℂ | a < z.re} := fun a ↦
      ⟨isOpen_lt continuous_const continuous_re, convex_halfSpace_gt reLm.isLinear a⟩
    have hre' : ∀ a : ℝ, IsOpen {z : ℂ | z.re < a} ∧ Convex ℝ {z : ℂ | z.re < a} := fun a ↦
      ⟨isOpen_lt continuous_re continuous_const, convex_halfSpace_lt reLm.isLinear a⟩
    have him : ∀ a : ℝ, IsOpen {z : ℂ | a < z.im} ∧ Convex ℝ {z : ℂ | a < z.im} := fun a ↦
      ⟨isOpen_lt continuous_const continuous_im, convex_halfSpace_gt imLm.isLinear a⟩
    have him' : ∀ a : ℝ, IsOpen {z : ℂ | z.im < a} ∧ Convex ℝ {z : ℂ | z.im < a} := fun a ↦
      ⟨isOpen_lt continuous_im continuous_const, convex_halfSpace_lt imLm.isLinear a⟩
    have hball : ∀ (c : ℂ) (ε : ℝ), IsOpen (ball c ε) ∧ Convex ℝ (ball c ε) := fun c ε ↦
      ⟨isOpen_ball, convex_ball c ε⟩
    rintro W ((hW | hW) | hW)
    · simp only [far, mem_insert_iff, mem_singleton_iff] at hW
      rcases hW with rfl | rfl | rfl | rfl
      · exact ⟨(hre R).1, (hre R).2, fun z hz hzS ↦ by
          have := (abs_lt.mp (hSR z hzS).1).2; exact absurd hz (not_lt.mpr this.le)⟩
      · exact ⟨(hre' _).1, (hre' _).2, fun z hz hzS ↦ by
          have := (abs_lt.mp (hSR z hzS).1).1; exact absurd hz (not_lt.mpr this.le)⟩
      · exact ⟨(him R).1, (him R).2, fun z hz hzS ↦ by
          have := (abs_lt.mp (hSR z hzS).2).2; exact absurd hz (not_lt.mpr this.le)⟩
      · exact ⟨(him' _).1, (him' _).2, fun z hz hzS ↦ by
          have := (abs_lt.mp (hSR z hzS).2).1; exact absurd hz (not_lt.mpr this.le)⟩
    · obtain ⟨s, hs, hW⟩ := mem_iUnion₂.mp hW
      simp only [disc, mem_insert_iff, mem_singleton_iff] at hW
      have hsub : ∀ P : ℂ → Prop, ¬ P s → ball s (ρ s) ∩ {z | P z} ⊆ Sᶜ := fun P hP z hz hzS ↦ by
        obtain rfl := hρ s hs z hzS hz.1
        exact hP hz.2
      rcases hW with rfl | rfl | rfl | rfl
      · exact ⟨(hball _ _).1.inter (hre _).1, (hball _ _).2.inter (hre _).2,
          hsub _ (lt_irrefl _)⟩
      · exact ⟨(hball _ _).1.inter (hre' _).1, (hball _ _).2.inter (hre' _).2,
          hsub _ (lt_irrefl _)⟩
      · exact ⟨(hball _ _).1.inter (him _).1, (hball _ _).2.inter (him _).2,
          hsub _ (lt_irrefl _)⟩
      · exact ⟨(hball _ _).1.inter (him' _).1, (hball _ _).2.inter (him' _).2,
          hsub _ (lt_irrefl _)⟩
    · obtain ⟨z, hz, rfl⟩ := hW
      exact ⟨(hball _ _).1, (hball _ _).2, hr z (hKS (htK z hz))⟩
  · intro z hz
    by_cases hbox : |z.re| ≤ R ∧ |z.im| ≤ R
    · by_cases hnear : ∃ s ∈ S, z ∈ ball s (ρ s)
      · obtain ⟨s, hs, hzs⟩ := hnear
        have hne : z ≠ s := fun h ↦ hz (h ▸ hs)
        have hcases : s.re < z.re ∨ z.re < s.re ∨ s.im < z.im ∨ z.im < s.im := by
          by_contra! h
          exact hne (Complex.ext (le_antisymm h.1 h.2.1) (le_antisymm h.2.2.1 h.2.2.2))
        have hmem : ∀ W ∈ disc s, z ∈ W → z ∈ ⋃₀ (far ∪ (⋃ s ∈ S, disc s) ∪
            ((fun z ↦ ball z (r z)) '' t)) := fun W hW hzW ↦
          mem_sUnion.mpr ⟨W, Or.inl (Or.inr (mem_iUnion₂.mpr ⟨s, hs, hW⟩)), hzW⟩
        rcases hcases with h | h | h | h
        · exact hmem (ball s (ρ s) ∩ {z | s.re < z.re}) (by simp [disc]) ⟨hzs, h⟩
        · exact hmem (ball s (ρ s) ∩ {z | z.re < s.re}) (by simp [disc]) ⟨hzs, h⟩
        · exact hmem (ball s (ρ s) ∩ {z | s.im < z.im}) (by simp [disc]) ⟨hzs, h⟩
        · exact hmem (ball s (ρ s) ∩ {z | z.im < s.im}) (by simp [disc]) ⟨hzs, h⟩
      · push Not at hnear
        have hzK : z ∈ K := ⟨hbox, mem_iInter₂.mpr fun s hs ↦ hnear s hs⟩
        obtain ⟨w, hw, hzw⟩ := mem_iUnion₂.mp (hKt hzK)
        exact mem_sUnion.mpr ⟨_, Or.inr ⟨w, hw, rfl⟩, hzw⟩
    · have hmem : ∀ W ∈ far, z ∈ W → z ∈ ⋃₀ (far ∪ (⋃ s ∈ S, disc s) ∪
          ((fun z ↦ ball z (r z)) '' t)) := fun W hW hzW ↦
        mem_sUnion.mpr ⟨W, Or.inl (Or.inl hW), hzW⟩
      rw [not_and_or, not_le, not_le, lt_abs, lt_abs] at hbox
      rcases hbox with (h | h) | (h | h)
      · exact hmem {z | R < z.re} (by simp [far]) h
      · exact hmem {z | z.re < -R} (by simp [far]) (show z.re < -R by linarith)
      · exact hmem {z | R < z.im} (by simp [far]) h
      · exact hmem {z | z.im < -R} (by simp [far]) (show z.im < -R by linarith)

/-- **`π₁` of the plane minus finitely many points is finitely generated.** -/
theorem fg_fundamentalGroup_compl {S : Set ℂ} (hS : S.Finite) (x : (Sᶜ : Set ℂ)) :
    Group.FG (FundamentalGroup (Sᶜ : Set ℂ) x) := by
  obtain ⟨𝒲, hfin, h𝒲, hcov⟩ := exists_finite_convex_cover_compl hS
  have : Finite 𝒲 := hfin.to_subtype
  refine FundamentalGroup.fg_of_finite_convex_cover
    (hS.countable.isPathConnected_compl_of_one_lt_rank (by simp [rank_real_complex]))
    (Subtype.val : 𝒲 → Set ℂ) (fun W ↦ (h𝒲 W.1 W.2).1) (fun W ↦ (h𝒲 W.1 W.2).2.1)
    (fun W ↦ (h𝒲 W.1 W.2).2.2) (fun z hz ↦ ?_) x
  obtain ⟨W, hW, hzW⟩ := mem_sUnion.mp (hcov hz)
  exact mem_iUnion.mpr ⟨⟨W, hW⟩, hzW⟩

end Complex
