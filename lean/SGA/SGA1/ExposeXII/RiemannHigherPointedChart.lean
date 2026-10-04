/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigherPolyFamily
import SGA.SGA1.ExposeXII.RiemannHigherFrames
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.LocallyContractible
import Mathlib.Topology.Homotopy.Contractible

/-!
# Pointed charts of families of punctured lines

Let `G : B → ℂ[X]` be a continuous family of monic separable polynomials of fixed degree and
`t₀ : B → ℂ` a continuous function with `G_b(t₀ b) ≠ 0`, a section of
`PolyComplement G = {(b, x) | G_b(x) ≠ 0} → B`. If `B` is strongly locally contractible, the
family has pointed charts at every point (`RiemannHigher.nonempty_pointedChart_polyComplement`):
over a contractible neighbourhood `N` of `b₀`, the isotopies of `ℂ` moving the roots of `G_{b₀}`
*and* the point `t₀ b₀` to those of `G_b` and `t₀ b` (`isotopyTrivAlong`) trivialize the family,
sending the section to a constant.

Consequently (`RiemannHigher.exists_frame_iso_polyComplement`), two coverings of `PolyComplement G`
with finite fibres which are isomorphic over every fibre become isomorphic over a finite covering
of `B` (`exists_frame_iso`). This is the topological core of the induction step of XII.5.1 in
higher dimension (`SGA.SGA1.ExposeXII.RiemannHigher`).
-/
noncomputable section

open Polynomial Topology Set Metric Filter

namespace SGA.SGA1.ExposeXII.RiemannHigher

variable {B : Type*} [TopologicalSpace B] {r : ℕ} {G : B → ℂ[X]}

/-- The complement in `ℂ` of finitely many points is path-connected. -/
lemma pathConnectedSpace_compl_range {m : ℕ} (a : Fin m → ℂ) :
    PathConnectedSpace {x : ℂ // ∀ k, x ≠ a k} := by
  have h : (range a)ᶜ = {x : ℂ | ∀ k, x ≠ a k} := by
    ext x
    simp [eq_comm]
  have hpc : IsPathConnected (range a)ᶜ :=
    (finite_range a).countable.isPathConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]
      exact Cardinal.one_lt_two)
  rw [h] at hpc
  exact isPathConnected_iff_pathConnectedSpace.mp hpc

/-- A contraction of a contractible space: a homotopy from a constant map to the identity. -/
lemma exists_contraction (N : Type*) [TopologicalSpace N] [ContractibleSpace N] :
    ∃ (c : N) (h : C(unitInterval × N, N)), (∀ n, h (0, n) = c) ∧ ∀ n, h (1, n) = n := by
  obtain ⟨c, ⟨H⟩⟩ := (contractible_iff_id_nullhomotopic N).mp inferInstance
  exact ⟨c, H.symm.toContinuousMap, fun n ↦ H.symm.apply_zero n, fun n ↦ H.symm.apply_one n⟩

/-- **Pointed charts of families of punctured lines.** Over a strongly locally contractible `B`,
the family `PolyComplement G → B` of `ℂ` minus the roots of `G_b` (monic, separable, of degree `r`,
with continuous coefficients), with the section `b ↦ (b, t₀ b)`, has a pointed chart at every
point. -/
theorem nonempty_pointedChart_polyComplement [StronglyLocallyContractibleSpace B]
    (hmonic : ∀ b, (G b).Monic) (hdeg : ∀ b, (G b).natDegree = r)
    (hcont : ∀ i, Continuous fun b ↦ (G b).coeff i) (hsep : ∀ b, (G b).Separable)
    {t₀ : B → ℂ} (ht₀ : Continuous t₀) (hG : ∀ b, (G b).eval (t₀ b) ≠ 0) (b₀ : B) :
    Nonempty (PointedChart (fun x : PolyComplement G ↦ x.1.1) (fun b ↦ ⟨(b, t₀ b), hG b⟩)
      (fun _ ↦ rfl) b₀) := by
  obtain ⟨W, s, ρ, hW, hs, hρ, hsep', hiff⟩ := exists_continuousOn_roots hmonic hdeg hcont hsep b₀
  -- the moving points: the roots and the section
  let t : B → Fin (r + 1) → ℂ := fun b ↦ Fin.snoc (α := fun _ ↦ ℂ) (s b) (t₀ b)
  have ht_cs (b : B) (k : Fin r) : t b k.castSucc = s b k := Fin.snoc_castSucc ..
  have ht_last (b : B) : t b (Fin.last r) = t₀ b := Fin.snoc_last ..
  have htc : ContinuousOn t W := by
    refine continuousOn_pi.mpr fun i ↦ ?_
    induction i using Fin.lastCases with
    | last => simpa only [ht_last] using ht₀.continuousOn
    | cast k =>
      simp only [ht_cs]
      exact (continuous_apply k).comp_continuousOn hs
  have ht₀s (k : Fin r) : t₀ b₀ ≠ s b₀ k :=
    (hiff b₀ (mem_of_mem_nhds hW) (t₀ b₀)).mp (hG b₀) k
  -- a separation radius for all the moving points at `b₀`
  obtain ⟨ε, hε, hεs⟩ : ∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ ‖t₀ b₀ - s b₀ k‖ := by
    rcases isEmpty_or_nonempty (Fin r) with h | h
    · exact ⟨1, one_pos, fun k ↦ (IsEmpty.false k).elim⟩
    · let f : Fin r → ℝ := fun k ↦ ‖t₀ b₀ - s b₀ k‖
      obtain ⟨k₀, -, hk₀⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
      exact ⟨f k₀, norm_pos_iff.mpr (sub_ne_zero.mpr (ht₀s k₀)), fun k ↦ hk₀ k (Finset.mem_univ _)⟩
  set ρ' := min ρ ε with hρ'
  have hρ'0 : 0 < ρ' := lt_min hρ hε
  have htsep : ∀ i j, i ≠ j → ρ' ≤ ‖t b₀ i - t b₀ j‖ := by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact (hij rfl).elim
      | cast l => rw [ht_last, ht_cs]; exact (min_le_right _ _).trans (hεs l)
    | cast k =>
      induction j using Fin.lastCases with
      | last =>
        rw [ht_last, ht_cs, norm_sub_rev]
        exact (min_le_right _ _).trans (hεs k)
      | cast l =>
        rw [ht_cs, ht_cs]
        exact (min_le_left _ _).trans (hsep' k l fun h ↦ hij (by rw [h]))
  have hiso : isotopyNhd t b₀ ρ' ∈ 𝓝 b₀ := by
    have hsc : ContinuousAt t b₀ := htc.continuousAt hW
    have : ContinuousAt (fun b ↦ ∑ i, ‖t b i - t b₀ i‖) b₀ := by
      have hi (i : Fin (r + 1)) : ContinuousAt (fun b ↦ t b i) b₀ :=
        (continuous_apply i).continuousAt.comp hsc
      fun_prop
    have h0 : (fun b ↦ ∑ i, ‖t b i - t b₀ i‖) b₀ < ρ' / 2 := by simp [hρ'0]
    exact this.eventually (gt_mem_nhds h0)
  -- a contractible neighbourhood inside `W ∩ isotopyNhd`
  obtain ⟨N, ⟨hN, hNc⟩, hNsub⟩ :=
    (StronglyLocallyContractibleSpace.contractible_basis b₀).mem_iff.mp (inter_mem hW hiso)
  have hNW : ∀ b ∈ N, b ∈ W := fun b hb ↦ (hNsub hb).1
  have hNiso : N ⊆ isotopyNhd t b₀ ρ' := fun b hb ↦ (hNsub hb).2
  obtain ⟨c, h, h0, h1⟩ := exists_contraction N
  -- the trivialization
  let e : {x : PolyComplement G // x.1.1 ∈ N} ≃ₜ PuncturedTotalAlong t Fin.castSucc N :=
    { toFun x := ⟨x.1.1, x.2, fun k ↦ by
        rw [ht_cs]; exact (hiff x.1.1.1 (hNW _ x.2) x.1.1.2).mp x.1.2 k⟩
      invFun p := ⟨⟨p.1, (hiff p.1.1 (hNW _ p.2.1) p.1.2).mpr fun k ↦ by
        rw [← ht_cs]; exact p.2.2 k⟩, p.2.1⟩
      left_inv _ := rfl
      right_inv _ := rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let Θ := e.trans (isotopyTrivAlong Fin.castSucc hNiso (htc.mono hNW) hρ'0 htsep)
  have : PathConnectedSpace (PuncturedFibreAlong t Fin.castSucc b₀) :=
    pathConnectedSpace_compl_range _
  refine ⟨⟨N, hN, c, h, h0, h1, PuncturedFibreAlong t Fin.castSucc b₀,
    ⟨t₀ b₀, fun k hk ↦ ht₀s k (hk.trans (ht_cs b₀ k))⟩, Θ, fun _ ↦ rfl, fun n ↦ ?_⟩⟩
  refine Prod.ext rfl (Subtype.ext ?_)
  change famIsotopyInv t b₀ ρ' n.1 (t₀ n.1) = t₀ b₀
  have hfam : famIsotopy t b₀ ρ' n.1 (t₀ b₀) = t₀ n.1 := by
    rw [← ht_last, ← ht_last n.1]
    exact famIsotopy_apply hρ'0 htsep n.1 (Fin.last r)
  rw [← hfam]
  exact famIsotopyInv_famIsotopy hρ'0 (hNiso n.2) _

/-- **Fibrewise isomorphic coverings of a family of punctured lines become isomorphic over a finite
covering of the base.** Let `B` be strongly locally contractible, `G : B → ℂ[X]` a continuous family
of monic separable polynomials of degree `r`, `t₀ : B → ℂ` continuous with `G_b(t₀ b) ≠ 0`, and
`p₁`, `p₂` coverings of `PolyComplement G` with finite fibres which are isomorphic over every
fibre `ℂ ∖ G_b⁻¹(0)`, the fibres of `p₁` over `(b, t₀ b)` having `n` points. Then there are a
covering `M → B` with finite fibres, surjective, and a continuous bijection
`M ×_B E₁ → M ×_B E₂` over `M ×_B PolyComplement G` (`exists_frame_iso`). -/
theorem exists_frame_iso_polyComplement.{u, w₁, w₂} {B : Type u} [TopologicalSpace B]
    [StronglyLocallyContractibleSpace B] {G : B → ℂ[X]} (hmonic : ∀ b, (G b).Monic)
    (hdeg : ∀ b, (G b).natDegree = r) (hcont : ∀ i, Continuous fun b ↦ (G b).coeff i)
    (hsep : ∀ b, (G b).Separable) {t₀ : B → ℂ} (ht₀ : Continuous t₀)
    (hG : ∀ b, (G b).eval (t₀ b) ≠ 0) {E₁ : Type w₁} {E₂ : Type w₂} [TopologicalSpace E₁]
    [TopologicalSpace E₂] {p₁ : E₁ → PolyComplement G} {p₂ : E₂ → PolyComplement G}
    (hp₁ : IsCoveringMap p₁) (hp₂ : IsCoveringMap p₂) (hfin₁ : ∀ x, (p₁ ⁻¹' {x}).Finite)
    (hfin₂ : ∀ x, (p₂ ⁻¹' {x}).Finite)
    (hiso : ∀ b, FibreIso p₁ p₂ (fun x : PolyComplement G ↦ x.1.1) b) (n : ℕ)
    (hcard : ∀ b, Nat.card (p₁ ⁻¹' {⟨(b, t₀ b), hG b⟩}) = n) :
    ∃ (M : Type (max u w₁ w₂)) (_ : TopologicalSpace M) (pM : M → B), IsCoveringMap pM ∧
      (∀ b, (pM ⁻¹' {b}).Finite) ∧ Function.Surjective pM ∧
      ∃ Φ : {q : M × E₁ // pM q.1 = (p₁ q.2).1.1} → {q : M × E₂ // pM q.1 = (p₂ q.2).1.1},
        Continuous Φ ∧ Function.Bijective Φ ∧ ∀ q, (Φ q).1.1 = q.1.1 ∧ p₂ (Φ q).1.2 = p₁ q.1.2 :=
  exists_frame_iso (π := fun x : PolyComplement G ↦ x.1.1)
    (sec := fun b ↦ ⟨(b, t₀ b), hG b⟩) (hsec := fun _ ↦ rfl) (p₁ := p₁) (p₂ := p₂) (n := n)
    (nonempty_pointedChart_polyComplement hmonic hdeg hcont hsep ht₀ hG) hp₁ hp₂ hfin₁ hfin₂
    hiso hcard

end SGA.SGA1.ExposeXII.RiemannHigher
