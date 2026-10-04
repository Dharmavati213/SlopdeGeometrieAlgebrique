/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherIsotopy
import SGA.SGA1.ExposeXII.RiemannHigherTransport
import SGA.SGA1.ExposeXII.SimpleRoot
import Mathlib.FieldTheory.Separable
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# Families of punctured planes cut out by separable polynomials

Let `B` be a topological space and `G : B → ℂ[X]` a family of monic separable polynomials of fixed
degree `r` with continuous coefficients, and `P = {(b, x) | G_b(x) ≠ 0}` (`PolyComplement G`).

* `exists_continuousOn_roots`: near every `b₀` the roots of `G_b` are `r` continuous, pairwise
  distinct functions of `b` (from the implicit function theorem, `exists_continuousOn_simpleRoot`);
* `exists_trivialization_polyComplement`: if `B` is locally path-connected, `P → B` is trivial over
  path-connected neighbourhoods of every point (with the isotopies of
  `SGA.SGA1.ExposeXII.RiemannHigherIsotopy`);
* `isClopen_setOf_fibreIso_polyComplement`: hence for two coverings of `P`, the set of `b` over
  which they are isomorphic is clopen (`isClopen_setOf_fibreIso`).

These families are the fibrations by punctured lines of the induction step of XII.5.1 in higher
dimension, and the parameter families of the algebraic covers of their fibres
(`SGA.SGA1.ExposeXII.RiemannHigher`).
-/
noncomputable section

open Polynomial Topology Set Metric Filter

namespace SGA.SGA1.ExposeXII.RiemannHigher

section PolyFamily

variable {B : Type*} [TopologicalSpace B] {r : ℕ} {G : B → ℂ[X]}

variable (G) in
/-- The family of `ℂ` minus the roots of `G b`, over `B`. -/
abbrev PolyComplement : Type _ := {x : B × ℂ // (G x.1).eval x.2 ≠ 0}

/-- Local root functions: near `b₀`, the roots of a continuous family of monic separable
polynomials of degree `r` are `r` continuous functions, pairwise distinct. This generalizes
`RootLocus.exists_local_roots` (`SGA.SGA1.ExposeXII.RootLocus`) from polynomial to continuous
coefficient functions on any space `B`. -/
theorem exists_continuousOn_roots (hmonic : ∀ b, (G b).Monic) (hdeg : ∀ b, (G b).natDegree = r)
    (hcont : ∀ i, Continuous fun b ↦ (G b).coeff i) (hsep : ∀ b, (G b).Separable) (b₀ : B) :
    ∃ (W : Set B) (s : B → Fin r → ℂ) (ρ : ℝ), W ∈ 𝓝 b₀ ∧ ContinuousOn s W ∧ 0 < ρ ∧
      (∀ i j, i ≠ j → ρ ≤ ‖s b₀ i - s b₀ j‖) ∧
      ∀ b ∈ W, ∀ x, (G b).eval x ≠ 0 ↔ ∀ i, x ≠ s b i := by
  classical
  set R₀ := (G b₀).roots.toFinset
  have hcard : R₀.card = r := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots (hsep b₀)),
      ← (IsAlgClosed.splits (G b₀)).natDegree_eq_card_roots, hdeg]
  let e : R₀ ≃ Fin r := Fintype.equivFinOfCardEq (by simpa using hcard)
  let a₀ : Fin r → ℂ := fun i ↦ (e.symm i).1
  have ha₀_root (i : Fin r) : (G b₀).IsRoot (a₀ i) := by
    have := (e.symm i).2
    rw [Multiset.mem_toFinset, mem_roots (hmonic b₀).ne_zero] at this
    exact this
  have ha₀_inj : Function.Injective a₀ := fun i j h ↦ e.symm.injective (Subtype.ext h)
  have hsimple (i : Fin r) : (G b₀).derivative.eval (a₀ i) ≠ 0 := by
    have := (hsep b₀).aeval_derivative_ne_zero (x := a₀ i) (by
      rw [coe_aeval_eq_eval]; exact ha₀_root i)
    rwa [coe_aeval_eq_eval] at this
  have key (i : Fin r) := exists_continuousOn_simpleRoot G hmonic hdeg hcont (ha₀_root i)
    (hsimple i)
  choose U V hUo hVo hb₀U ha₀V s' hs'c hs'maps hs'uniq using key
  have hs'b₀ (i : Fin r) : s' i b₀ = a₀ i :=
    (hs'uniq i b₀ (hb₀U i) (a₀ i) (ha₀V i)).mp (ha₀_root i)
  -- a separation radius `ρ` and a smaller radius `ε`
  obtain ⟨ρ, hρsep, hρ⟩ : ∃ ρ : ℝ, (∀ i j, i ≠ j → ρ ≤ ‖a₀ i - a₀ j‖) ∧ 0 < ρ := by
    have : ∀ᶠ ρ in 𝓝[>] (0 : ℝ), ∀ ij : Fin r × Fin r, ij.1 ≠ ij.2 →
        ρ ≤ ‖a₀ ij.1 - a₀ ij.2‖ := by
      refine eventually_all.mpr fun ij ↦ ?_
      by_cases h : ij.1 = ij.2
      · exact Eventually.of_forall fun _ h' ↦ (h' h).elim
      · have hpos : 0 < ‖a₀ ij.1 - a₀ ij.2‖ :=
          norm_pos_iff.mpr (sub_ne_zero.mpr (ha₀_inj.ne h))
        filter_upwards [Ioo_mem_nhdsGT hpos] with ρ hρ _ using hρ.2.le
    obtain ⟨ρ, hρ, hρ0⟩ := (this.and self_mem_nhdsWithin).exists
    exact ⟨ρ, fun i j hij ↦ hρ (i, j) hij, hρ0⟩
  obtain ⟨ε, ⟨hεV, hερ⟩, hε⟩ : ∃ ε : ℝ, ((∀ i, ball (a₀ i) ε ⊆ V i) ∧ ε ≤ ρ / 3) ∧ 0 < ε := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, ball (a₀ i) ε ⊆ V i := by
      refine eventually_all.mpr fun i ↦ ?_
      obtain ⟨δ, hδ, hδV⟩ := Metric.isOpen_iff.mp (hVo i) (a₀ i) (ha₀V i)
      filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε using (ball_subset_ball hε.2.le).trans hδV
    have h2 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ≤ ρ / 3 := by
      filter_upwards [Ioo_mem_nhdsGT (by positivity : (0 : ℝ) < ρ / 3)] with ε hε using hε.2.le
    exact ((h1.and h2).and self_mem_nhdsWithin).exists
  -- the neighbourhood `W` and the root functions `s`
  let W : Set B := {b | ∀ i, b ∈ U i ∧ s' i b ∈ ball (a₀ i) ε}
  have hW : W ∈ 𝓝 b₀ := by
    refine eventually_all.mpr fun i ↦ ?_
    have hca : ContinuousAt (s' i) b₀ := (hs'c i).continuousAt ((hUo i).mem_nhds (hb₀U i))
    filter_upwards [(hUo i).mem_nhds (hb₀U i), hca.eventually (isOpen_ball.mem_nhds
      (by rw [hs'b₀]; exact mem_ball_self hε))] with b h1 h2 using ⟨h1, h2⟩
  refine ⟨W, fun b i ↦ s' i b, ρ, hW, continuousOn_pi.mpr fun i ↦ (hs'c i).mono
    fun b hb ↦ (hb i).1, hρ, fun i j hij ↦ by simpa only [hs'b₀] using hρsep i j hij,
    fun b hb x ↦ ?_⟩
  have hroot_i (i : Fin r) : (G b).IsRoot (s' i b) :=
    (hs'uniq i b (hb i).1 (s' i b) (hs'maps i (hb i).1)).mpr rfl
  constructor
  · intro hx i hxi
    exact hx (hxi ▸ hroot_i i)
  · intro hx hev
    have hdist : Function.Injective fun i ↦ s' i b := fun i j h ↦ by
      by_contra hij
      have h1 : dist (s' i b) (a₀ i) < ε := (hb i).2
      have h2 : dist (s' j b) (a₀ j) < ε := (hb j).2
      have h3 := hρsep i j hij
      simp only at h
      rw [h] at h1
      have : ‖a₀ i - a₀ j‖ < 2 * ε := by
        calc ‖a₀ i - a₀ j‖ = dist (a₀ i) (a₀ j) := (dist_eq_norm _ _).symm
          _ ≤ dist (a₀ i) (s' j b) + dist (s' j b) (a₀ j) := dist_triangle _ _ _
          _ < ε + ε := by rw [dist_comm]; exact add_lt_add h1 h2
          _ = 2 * ε := by ring
      linarith
    have himg : (Finset.univ.image fun i ↦ s' i b) ⊆ (G b).roots.toFinset := by
      intro y hy
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
      rw [Multiset.mem_toFinset, mem_roots (hmonic b).ne_zero]
      exact hroot_i i
    have hcardb : (G b).roots.toFinset.card ≤ r :=
      (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hdeg b).le)
    have heq := Finset.eq_of_subset_of_card_le himg (by
      rw [Finset.card_image_of_injective _ hdist, Finset.card_univ, Fintype.card_fin]
      exact hcardb)
    have hxmem : x ∈ (G b).roots.toFinset := by
      rw [Multiset.mem_toFinset, mem_roots (hmonic b).ne_zero]
      exact hev
    rw [← heq] at hxmem
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hxmem
    exact hx i hi.symm

/-- Local triviality of `ℂ` minus the roots of a continuous family of monic separable polynomials
of fixed degree, over path-connected neighbourhoods (`B` locally path-connected): the input of
`isClopen_setOf_fibreIso` for such families. -/
theorem exists_trivialization_polyComplement [LocallyPathConnectedSpace B]
    (hmonic : ∀ b, (G b).Monic) (hdeg : ∀ b, (G b).natDegree = r)
    (hcont : ∀ i, Continuous fun b ↦ (G b).coeff i) (hsep : ∀ b, (G b).Separable) (b₀ : B) :
    ∃ N ∈ 𝓝 b₀, IsPathConnected N ∧ ∃ (F : Type) (_ : TopologicalSpace F)
      (Θ : {x : PolyComplement G // x.1.1 ∈ N} ≃ₜ N × F), ∀ x, ((Θ x).1 : B) = x.1.1.1 := by
  obtain ⟨W, s, ρ, hW, hs, hρ, hsep', hiff⟩ := exists_continuousOn_roots hmonic hdeg hcont hsep b₀
  have hiso : isotopyNhd s b₀ ρ ∈ 𝓝 b₀ := by
    have hsc : ContinuousAt s b₀ := hs.continuousAt hW
    have : ContinuousAt (fun b ↦ ∑ i, ‖s b i - s b₀ i‖) b₀ := by
      have hi (i : Fin r) : ContinuousAt (fun b ↦ s b i) b₀ :=
        (continuous_apply i).continuousAt.comp hsc
      fun_prop
    have h0 : (fun b ↦ ∑ i, ‖s b i - s b₀ i‖) b₀ < ρ / 2 := by simp [hρ]
    exact this.eventually (gt_mem_nhds h0)
  have hW' : W ∩ isotopyNhd s b₀ ρ ∈ 𝓝 b₀ := inter_mem hW hiso
  let N := pathComponentIn (W ∩ isotopyNhd s b₀ ρ) b₀
  have hNW' : N ⊆ W ∩ isotopyNhd s b₀ ρ := pathComponentIn_subset
  let e : {x : PolyComplement G // x.1.1 ∈ N} ≃ₜ PuncturedTotal s N :=
    { toFun x := ⟨x.1.1, x.2, (hiff x.1.1.1 (hNW' x.2).1 x.1.1.2).mp x.1.2⟩
      invFun p := ⟨⟨p.1, (hiff p.1.1 (hNW' p.2.1).1 p.1.2).mpr p.2.2⟩, p.2.1⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨N, pathComponentIn_mem_nhds hW', isPathConnected_pathComponentIn (mem_of_mem_nhds hW'),
    PuncturedFibre s b₀, inferInstance, e.trans (isotopyTrivOn (fun b hb ↦ (hNW' hb).2)
      (hs.mono fun b hb ↦ (hNW' hb).1) hρ hsep'), fun _ ↦ rfl⟩

/-- For two coverings of `ℂ` minus the roots of a continuous family of monic separable polynomials
over a locally path-connected `B`, the set of parameters over which they are isomorphic is
clopen. -/
theorem isClopen_setOf_fibreIso_polyComplement [LocallyPathConnectedSpace B]
    (hmonic : ∀ b, (G b).Monic) (hdeg : ∀ b, (G b).natDegree = r)
    (hcont : ∀ i, Continuous fun b ↦ (G b).coeff i) (hsep : ∀ b, (G b).Separable)
    {C₁ C₂ : Type*} [TopologicalSpace C₁] [TopologicalSpace C₂] {p₁ : C₁ → PolyComplement G}
    {p₂ : C₂ → PolyComplement G} (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) :
    IsClopen {b | FibreIso p₁ p₂ (fun x : PolyComplement G ↦ x.1.1) b} :=
  isClopen_setOf_fibreIso p₁ p₂ _ (fun b₀ ↦ by
    obtain ⟨N, hN, hpc, F, _, Θ, hΘ⟩ :=
      exists_trivialization_polyComplement hmonic hdeg hcont hsep b₀
    exact ⟨N, hN, hpc, F, inferInstance, Θ, hΘ⟩) hp₁ hp₂

end PolyFamily

end SGA.SGA1.ExposeXII.RiemannHigher
