/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.OneVariable

/-!
# Semialgebraic choice for families with compact fibres

Let `S ⊆ ℝ × ℝⁿ` be semialgebraic, with compact fibres `S_s = {x | (s, x) ∈ S}`. Then there is a
map `γ : ℝ → ℝⁿ` whose coordinates are semialgebraic functions, with `γ s ∈ S_s` whenever `S_s`
is nonempty (`IsSemialgebraic.exists_section_of_isCompact`). We take for `γ s` the
lexicographically least point of `S_s`: its first coordinate is the least first coordinate of a
point of `S_s`, a semialgebraic function of `s` by Tarski–Seidenberg, and we recurse on the
remaining coordinates.

Here `ℝ × ℝⁿ` is `ℝ^(Option (Fin n))`, the parameter being the coordinate `none`.

## References

* [L. van den Dries, *Tame topology and o-minimal structures*, Chapter 6, (1.2)][vdD]
-/

open Set hiding ofPred_and ofPred_or ofPred_exists ofPred_forall
open MvPolynomial

namespace IsSemialgebraic

/-- **Semialgebraic choice** for families with compact fibres: if `S ⊆ ℝ × ℝⁿ` is semialgebraic
and its fibres `{x | (s, x) ∈ S}` are compact, there is `γ : ℝ → ℝⁿ` with semialgebraic
coordinates such that `(s, γ s) ∈ S` whenever the fibre over `s` is nonempty. -/
theorem exists_section_of_isCompact {n : ℕ} {S : Set (Option (Fin n) → ℝ)}
    (hS : IsSemialgebraic S)
    (hK : ∀ s, IsCompact {x : Fin n → ℝ | (fun o ↦ Option.elim o s x) ∈ S}) :
    ∃ γ : ℝ → Fin n → ℝ, (∀ s x, (fun o ↦ Option.elim o s x) ∈ S →
      (fun o ↦ Option.elim o s (γ s)) ∈ S) ∧ ∀ i, Real.IsSemialgebraicFun fun s ↦ γ s i := by
  induction n with
  | zero =>
    refine ⟨fun _ ↦ Fin.elim0, fun s x hx ↦ ?_, fun i ↦ i.elim0⟩
    convert hx using 3
  | succ n ih =>
    -- `m s`: the least first coordinate of a point of the fibre over `s`
    set K : ℝ → Set (Fin (n + 1) → ℝ) := fun s ↦ {x | (fun o ↦ Option.elim o s x) ∈ S}
      with hK_def
    set m : ℝ → ℝ := fun s ↦ sInf ((fun x ↦ x 0) '' K s) with hm_def
    have hKc (s : ℝ) : IsCompact ((fun x : Fin (n + 1) → ℝ ↦ x 0) '' K s) :=
      (hK s).image (continuous_apply 0)
    have hm_mem (s : ℝ) (hs : (K s).Nonempty) : m s ∈ (fun x ↦ x 0) '' K s :=
      (hKc s).sInf_mem (hs.image _)
    have hm_le (s : ℝ) (x : Fin (n + 1) → ℝ) (hx : x ∈ K s) : m s ≤ x 0 :=
      csInf_le (hKc s).bddBelow ⟨x, hx, rfl⟩
    have hm : Real.IsSemialgebraicFun m := by
      have key : {v : Fin 2 → ℝ | m (v 0) = v 1} = {v | ((∃ x : Fin (n + 1) → ℝ,
          (fun o ↦ Option.elim o (v 0) x) ∈ S ∧ x 0 = v 1) ∧
          ∀ x : Fin (n + 1) → ℝ, (fun o ↦ Option.elim o (v 0) x) ∈ S → v 1 ≤ x 0) ∨
          ((∀ x : Fin (n + 1) → ℝ, (fun o ↦ Option.elim o (v 0) x) ∉ S) ∧ v 1 = 0)} := by
        ext v
        simp only [mem_ofPred_eq]
        by_cases hne : (K (v 0)).Nonempty
        · obtain ⟨x₀, hx₀, hx₀'⟩ := hm_mem _ hne
          constructor
          · intro h
            exact Or.inl ⟨⟨x₀, hx₀, hx₀'.trans h⟩, fun x hx ↦ h ▸ hm_le _ x hx⟩
          · rintro (⟨⟨x, hx, hx'⟩, hle⟩ | ⟨hno, -⟩)
            · exact le_antisymm (hx' ▸ hm_le _ x hx) (hx₀' ▸ hle x₀ hx₀)
            · obtain ⟨x, hx⟩ := hne
              exact (hno x hx).elim
        · have he : K (v 0) = ∅ := not_nonempty_iff_eq_empty.mp hne
          have hm0 : m (v 0) = 0 := by
            simp only [hm_def, he, image_empty, Real.sInf_empty]
          rw [hm0]
          constructor
          · intro h
            exact Or.inr ⟨fun x hx ↦ hne ⟨x, hx⟩, h.symm⟩
          · rintro (⟨⟨x, hx, -⟩, -⟩ | ⟨-, h⟩)
            · exact absurd ⟨x, hx⟩ hne
            · exact h.symm
      unfold Real.IsSemialgebraicFun
      rw [key]
      have hmem : IsSemialgebraic {w : Fin 2 ⊕ Fin (n + 1) → ℝ |
          (fun o ↦ Option.elim o (w (.inl 0)) fun k ↦ w (.inr k)) ∈ S} := by
        refine hS.ofPred_mem fun o ↦ ?_
        rcases o with _ | k
        · simp only [Option.elim_none]
          fun_prop
        · simp only [Option.elim_some]
          fun_prop
      exact ofPred_or (ofPred_and (ofPred_exists_pi (ofPred_and hmem
        (ofPred_eq (by fun_prop) (by fun_prop)))) (ofPred_forall_pi (ofPred_imp hmem
        (ofPred_le (by fun_prop) (by fun_prop))))) (ofPred_and (ofPred_forall_pi
        (ofPred_not hmem)) (ofPred_eq (by fun_prop) (by fun_prop)))
    -- the family of the remaining coordinates
    set S' : Set (Option (Fin n) → ℝ) :=
      {w | (fun o ↦ Option.elim o (w none) (Fin.cons (m (w none)) fun i ↦ w (some i))) ∈ S}
    have hS' : IsSemialgebraic S' := by
      have : S' = {w | ∃ t, m (w none) = t ∧
          (fun o ↦ Option.elim o (w none) (Fin.cons t fun i ↦ w (some i))) ∈ S} := by
        ext w
        simp [S']
      rw [this]
      refine ofPred_exists (ofPred_and (hm.graph _ _) (hS.ofPred_mem fun o ↦ ?_))
      rcases o with _ | j
      · simp only [Option.elim_none]
        fun_prop
      · refine Fin.cases ?_ (fun i ↦ ?_) j
        · simp only [Option.elim_some, Fin.cons_zero]
          fun_prop
        · simp only [Option.elim_some, Fin.cons_succ]
          fun_prop
    have hK' (s : ℝ) : IsCompact {y : Fin n → ℝ | (fun o ↦ Option.elim o s y) ∈ S'} := by
      have hcl : IsClosed {y : Fin n → ℝ | (fun o ↦ Option.elim o s y) ∈ S'} := by
        change IsClosed ((fun y : Fin n → ℝ ↦ (Fin.cons (m s) y : Fin (n + 1) → ℝ)) ⁻¹' K s)
        exact (hK s).isClosed.preimage (continuous_const.finCons continuous_id)
      refine ((hK s).image (continuous_pi fun i ↦ continuous_apply _ :
        Continuous (Fin.tail : (Fin (n + 1) → ℝ) → Fin n → ℝ))).of_isClosed_subset hcl
        fun y hy ↦ ⟨Fin.cons (m s) y, hy, Fin.tail_cons _ _⟩
    obtain ⟨γ', hγ'S, hγ'⟩ := ih hS' hK'
    refine ⟨fun s ↦ Fin.cons (m s) (γ' s), fun s x hx ↦ ?_, fun i ↦ ?_⟩
    · obtain ⟨x₀, hx₀, hx₀'⟩ := hm_mem s ⟨x, hx⟩
      have h : (fun o ↦ Option.elim o s (Fin.tail x₀)) ∈ S' := by
        change (fun o ↦ Option.elim o s (Fin.cons (m s) (Fin.tail x₀))) ∈ S
        rw [← hx₀', Fin.cons_self_tail]
        exact hx₀
      exact hγ'S s _ h
    · refine Fin.cases ?_ (fun i ↦ ?_) i
      · simpa using hm
      · simpa using hγ' i

end IsSemialgebraic
