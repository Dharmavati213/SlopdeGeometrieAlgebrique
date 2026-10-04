/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultDisc
import SGA.Foundations.Analytic.RiemannSurfaceRefinement
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The first Cousin problem on a disc

**Cousin I on a disc** (`AnalyticGeometry.exists_differentiableOn_sub_eq_of_cocycle`): let
`B = B(c, R)` be an open disc and `(Uᵢ)` an arbitrary family of open sets covering `B`. Every
holomorphic additive cocycle `fᵢⱼ` on the `Uᵢ ∩ Uⱼ ∩ B` (`fᵢⱼ + fⱼₖ = fᵢₖ` on triple
intersections) is a coboundary: `fᵢⱼ = gⱼ - gᵢ` with `gᵢ` holomorphic on `Uᵢ ∩ B`. In other
words the Čech cohomology `Ȟ¹(𝔘, 𝒪)` of every open cover `𝔘` of a disc vanishes.

The proof is the classical one (Hörmander, *An introduction to complex analysis in several
variables*, 1.4.5; Forster, *Lectures on Riemann surfaces*, 13.4 and 26.1). With a smooth
partition of unity `χₖ` on `B` subordinate to the cover (mathlib's `SmoothPartitionOfUnity` on the
open submanifold `B`), the smooth functions `hᵢ = ∑ₖ χₖ fₖᵢ` satisfy `fᵢⱼ = hⱼ - hᵢ`
(`partition_sum_sub`). Their `∂/∂z̄` agree, giving a smooth `w` on `B`. Dolbeault's lemma on the
disc (`exists_contDiffOn_dbar_eq_ball`) gives `u` with `∂u/∂z̄ = w`, and `gᵢ = hᵢ - u` is
holomorphic.

This is the one-variable, first-degree case of Theorem B for `𝒪` on a disc
(`AnalyticGeometry.PolydiscProductVanishingStatement`). For the derived-functor statement one
still needs a Cartan criterion for infinite covers: the repo's
`TopCat.Sheaf.H'_subsingleton_of_cech` asks for finite refining families, which an open disc does
not have.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold ContDiff

namespace AnalyticGeometry

variable {ι : Type*} {c : ℂ} {R : ℝ}

/-- A smooth partition of unity on the disc `B(c, R)` subordinate to an open cover, as functions
on `ℂ`: smooth on the disc, vanishing near the points of the disc outside `Uᵢ`, locally finite on
the disc, and summing to `1` there. -/
theorem exists_partitionOfUnity_ball (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hcov : ball c R ⊆ ⋃ i, U i) :
    ∃ χ : ι → ℂ → ℝ, (∀ i, ∀ z ∈ ball c R, ContDiffAt ℝ ∞ (χ i) z) ∧
      (∀ i, ∀ z ∈ ball c R, z ∉ U i → χ i =ᶠ[𝓝 z] 0) ∧
      (∀ z ∈ ball c R, ∃ N ∈ 𝓝 z, {i | ∃ y ∈ N, χ i y ≠ 0}.Finite) ∧
      (∀ z ∈ ball c R, ∑ᶠ i, χ i z = 1) := by
  classical
  let B : TopologicalSpace.Opens ℂ := ⟨ball c R, isOpen_ball⟩
  have hBo : IsOpen (B : Set ℂ) := isOpen_ball
  have : LocallyCompactSpace B := hBo.locallyCompactSpace
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, ℂ)) (M := B)
    isClosed_univ (fun i => Subtype.val ⁻¹' U i) (fun i => (hU i).preimage continuous_subtype_val)
    (fun x _ => by simpa using hcov x.2)
  let χ : ι → ℂ → ℝ := fun i z => if h : z ∈ ball c R then ρ i ⟨z, h⟩ else 0
  have hχB : ∀ i (x : B), χ i x = ρ i x := fun i x => by
    have hx : dist (x : ℂ) c < R := x.2
    simp [χ, hx]
  -- the partition near a point of the disc, through the open embedding `B → ℂ`
  have hnhds : ∀ (z : ℂ) (h : z ∈ ball c R) {P : ℂ → Prop},
      (∀ᶠ x : B in 𝓝 ⟨z, h⟩, P x) → ∀ᶠ y in 𝓝 z, P y := by
    intro z h P hP
    have := hBo.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨z, h⟩
    rw [← show ((⟨z, h⟩ : B) : ℂ) = z from rfl, ← this]
    exact hP
  refine ⟨χ, fun i z hz => ?_, fun i z hz hzU => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun x : B => χ i x) ⟨z, hz⟩ := by
      have := (ρ i).contMDiff.contMDiffAt (x := ⟨z, hz⟩)
      exact this.congr_of_eventuallyEq (Eventually.of_forall fun x => hχB i x)
    rw [contMDiffAt_subtype_iff, contMDiffAt_iff_contDiffAt] at h1
    exact h1
  · have hnot : (⟨z, hz⟩ : B) ∉ tsupport (ρ i) := fun h => hzU (hρ i h)
    have h0 : ∀ᶠ x : B in 𝓝 ⟨z, hz⟩, ρ i x = 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    have h0' : ∀ᶠ x : B in 𝓝 ⟨z, hz⟩, χ i x = 0 := h0.mono fun x hx => by rw [hχB, hx]
    exact hnhds z hz h0'
  · obtain ⟨N, hN, hfin⟩ := ρ.locallyFinite ⟨z, hz⟩
    refine ⟨Subtype.val '' N, hBo.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hN,
      hfin.subset fun i hi => ?_⟩
    obtain ⟨_, ⟨x, hxN, rfl⟩, hx⟩ := hi
    exact ⟨x, Function.mem_support.mpr (by rwa [← hχB]), hxN⟩
  · have := ρ.sum_eq_one (x := ⟨z, hz⟩) (mem_univ _)
    simp only [show ∀ i, χ i z = ρ i ⟨z, hz⟩ from fun i => hχB i ⟨z, hz⟩]
    exact this

/-- **Cousin I on a disc**: let `(Uᵢ)` be open sets covering the disc `B = B(c, R)` and `fᵢⱼ`
holomorphic on `Uᵢ ∩ Uⱼ ∩ B` with `fᵢⱼ + fⱼₖ = fᵢₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ ∩ B`. Then there are `gᵢ`
holomorphic on `Uᵢ ∩ B` with `fᵢⱼ = gⱼ - gᵢ` on `Uᵢ ∩ Uⱼ ∩ B`. The index family is arbitrary (no
finiteness or local finiteness). -/
theorem exists_differentiableOn_sub_eq_of_cocycle (U : ι → Set ℂ) (hU : ∀ i, IsOpen (U i))
    (hcov : ball c R ⊆ ⋃ i, U i) (f : ι → ι → ℂ → ℂ)
    (hf : ∀ i j, DifferentiableOn ℂ (f i j) (U i ∩ U j ∩ ball c R))
    (hcoc : ∀ i j k, ∀ z ∈ U i ∩ U j ∩ U k ∩ ball c R, f i j z + f j k z = f i k z) :
    ∃ g : ι → ℂ → ℂ, (∀ i, DifferentiableOn ℂ (g i) (U i ∩ ball c R)) ∧
      ∀ i j, ∀ z ∈ U i ∩ U j ∩ ball c R, f i j z = g j z - g i z := by
  classical
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨fun _ => 0, fun i => differentiableOn_const 0, fun i j z hz => ?_⟩
    exact absurd hz.2 (by rw [ball_eq_empty.mpr hR]; exact notMem_empty z)
  obtain ⟨χ, hχs, hχ0, hχf, hχ1⟩ := exists_partitionOfUnity_ball U hU hcov
  have hUUB : ∀ i j, IsOpen (U i ∩ U j ∩ ball c R) := fun i j =>
    ((hU i).inter (hU j)).inter isOpen_ball
  have hfs : ∀ i j, ∀ z ∈ U i ∩ U j ∩ ball c R, ContDiffAt ℝ ∞ (f i j) z := fun i j z hz =>
    (((hf i j).contDiffOn (n := ∞) (hUUB i j)).restrict_scalars ℝ).contDiffAt
      ((hUUB i j).mem_nhds hz)
  have hfd : ∀ i j, ∀ z ∈ U i ∩ U j ∩ ball c R, DifferentiableAt ℂ (f i j) z := fun i j z hz =>
    (hf i j).differentiableAt ((hUUB i j).mem_nhds hz)
  -- the glued functions `hᵢ = ∑ₖ χₖ fₖᵢ`
  set h : ι → ℂ → ℂ := fun i z => ∑ᶠ k, (χ k z : ℂ) * f k i z with hhdef
  -- locally, the sums are finite
  have hloc : ∀ z ∈ ball c R, ∃ N ∈ 𝓝 z, ∃ F : Finset ι, ∀ y ∈ N, ∀ k ∉ F, χ k y = 0 := by
    intro z hz
    obtain ⟨N, hN, hfin⟩ := hχf z hz
    refine ⟨N, hN, hfin.toFinset, fun y hy k hk => ?_⟩
    by_contra hne
    exact hk (hfin.mem_toFinset.mpr ⟨y, hy, hne⟩)
  have hsum : ∀ (i : ι) (F : Finset ι) (y : ℂ), (∀ k ∉ F, χ k y = 0) →
      h i y = ∑ k ∈ F, (χ k y : ℂ) * f k i y := by
    intro i F y hF
    refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
    by_contra hkF
    exact hk (by simp [hF k hkF])
  have hsum1 : ∀ (F : Finset ι) (y : ℂ), y ∈ ball c R → (∀ k ∉ F, χ k y = 0) →
      ∑ k ∈ F, (χ k y : ℂ) = 1 := by
    intro F y hy hF
    have h1 := hχ1 y hy
    rw [finsum_eq_sum_of_support_subset _ (s := F) fun k hk => by
      by_contra hkF; exact hk (hF k hkF)] at h1
    rw [← Complex.ofReal_sum, h1, Complex.ofReal_one]
  -- `χₖ` vanishes at the points of the disc outside `Uₖ`
  have hχz : ∀ k, ∀ z ∈ ball c R, z ∉ U k → χ k z = 0 := fun k z hz hzk =>
    (hχ0 k z hz hzk).eq_of_nhds
  -- smoothness of the `hᵢ`
  have hhs : ∀ i, ∀ z ∈ U i ∩ ball c R, ContDiffAt ℝ ∞ (h i) z := by
    intro i z hz
    obtain ⟨N, hN, F, hF⟩ := hloc z hz.2
    have hev : h i =ᶠ[𝓝 z] fun y => ∑ k ∈ F, (χ k y : ℂ) * f k i y := by
      filter_upwards [hN] with y hy using hsum i F y (hF y hy)
    refine ContDiffAt.congr_of_eventuallyEq ?_ hev
    refine ContDiffAt.sum fun k _ => ?_
    by_cases hzk : z ∈ U k
    · exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp z (hχs k z hz.2)).mul
        (hfs k i z ⟨⟨hzk, hz.1⟩, hz.2⟩)
    · refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hχ0 k z hz.2 hzk] with y hy
      simp [hy]
  -- `fᵢⱼ = hⱼ - hᵢ`
  have hdiff : ∀ i j, ∀ z ∈ U i ∩ U j ∩ ball c R, h j z - h i z = f i j z := by
    intro i j z hz
    obtain ⟨N, hN, F, hF⟩ := hloc z hz.2
    rw [hsum j F z (hF z (mem_of_mem_nhds hN)), hsum i F z (hF z (mem_of_mem_nhds hN)),
      ← Finset.sum_sub_distrib]
    have hterm : ∀ k ∈ F, (χ k z : ℂ) * f k j z - (χ k z : ℂ) * f k i z =
        (χ k z : ℂ) * f i j z := by
      intro k _
      by_cases hzk : z ∈ U k
      · have := hcoc k i j z ⟨⟨⟨hzk, hz.1.1⟩, hz.1.2⟩, hz.2⟩
        rw [← mul_sub, ← this]
        ring
      · simp [hχz k z hz.2 hzk]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      hsum1 F z hz.2 (hF z (mem_of_mem_nhds hN)), one_mul]
  -- the `∂/∂z̄` of the `hᵢ` agree
  have hdbar : ∀ i j, ∀ z ∈ U i ∩ U j ∩ ball c R, dbar (h j) z = dbar (h i) z := by
    intro i j z hz
    have hj := (hhs j z ⟨hz.1.2, hz.2⟩).differentiableAt (by simp)
    have hi := (hhs i z ⟨hz.1.1, hz.2⟩).differentiableAt (by simp)
    have hev : h j - h i =ᶠ[𝓝 z] f i j := by
      filter_upwards [(hUUB i j).mem_nhds hz] with y hy using hdiff i j y hy
    have h0 : dbar (f i j) z = 0 :=
      (dbar_eq_zero_iff ((hfd i j z hz).restrictScalars ℝ)).mpr (hfd i j z hz)
    have := dbar_sub hj hi
    rw [dbar_congr hev, h0] at this
    exact (sub_eq_zero.mp this.symm)
  -- the smooth function `w = ∂hᵢ/∂z̄` on the disc
  have hidx : ∀ z ∈ ball c R, ∃ i, z ∈ U i := fun z hz => mem_iUnion.mp (hcov hz)
  have : Nonempty ι := ⟨(mem_iUnion.mp (hcov (mem_ball_self hR))).choose⟩
  choose! idx hidx using hidx
  set w : ℂ → ℂ := fun z => dbar (h (idx z)) z with hwdef
  have hw : ∀ i, ∀ z ∈ U i ∩ ball c R, w z = dbar (h i) z := fun i z hz =>
    hdbar i (idx z) z ⟨⟨hz.1, hidx z hz.2⟩, hz.2⟩
  have hwsmooth : ContDiffOn ℝ ∞ w (ball c R) := by
    intro z hz
    have hU' : U (idx z) ∩ ball c R ∈ 𝓝 z :=
      ((hU (idx z)).inter isOpen_ball).mem_nhds ⟨hidx z hz, hz⟩
    have hev : w =ᶠ[𝓝 z] dbar (h (idx z)) := by
      filter_upwards [hU'] with y hy using hw (idx z) y hy
    exact ((contDiffAt_dbar (hhs (idx z) z ⟨hidx z hz, hz⟩)).congr_of_eventuallyEq hev)
      |>.contDiffWithinAt
  obtain ⟨u, hu, hdu⟩ := exists_contDiffOn_dbar_eq_ball hR hwsmooth
  refine ⟨fun i => h i - u, fun i z hz => ?_, fun i j z hz => ?_⟩
  · have hi := (hhs i z hz).differentiableAt (by simp)
    have hud : DifferentiableAt ℝ u z :=
      (hu.contDiffAt (isOpen_ball.mem_nhds hz.2)).differentiableAt (by simp)
    exact (differentiableAt_sub_of_dbar_eq hi hud (by rw [hdu z hz.2, hw i z hz]))
      |>.differentiableWithinAt
  · simp only [Pi.sub_apply]
    rw [← hdiff i j z hz]
    ring

end AnalyticGeometry
