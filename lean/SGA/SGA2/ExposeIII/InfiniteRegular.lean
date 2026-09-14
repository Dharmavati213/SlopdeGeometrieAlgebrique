/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIII.MaximalRegular
import Mathlib.Data.List.OfFn

/-!
# SGA 2, Exposé III, 2.6: infinite regular sequences

At infinite depth, a given finite regular sequence extends to an actual
infinite sequence: every finite prefix of the extension is regular. This
complements the finite maximal-sequence theorem and makes the infinite
case an existence statement about one compatible family of elements.
-/

noncomputable section

universe u

open CategoryTheory RingTheory.Sequence

namespace SGA.SGA2.ExposeIII

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- At infinite depth, any finite regular sequence extends to a single
infinite regular sequence of elements of `I`. -/
theorem exists_infinite_regular_extension (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (hdepth : depth I M = ⊤) (rs : List R)
    (hmem : ∀ r ∈ rs, r ∈ I) (hreg : IsWeaklyRegular M rs) :
    ∃ f : ℕ → R, (∀ n, f n ∈ I) ∧
      ∀ n, IsWeaklyRegular M (rs ++ List.ofFn (fun i : Fin n ↦ f i.val)) := by
  classical
  let P := {s : List R // (∀ r ∈ s, r ∈ I) ∧ IsWeaklyRegular M s}
  have hex (s : P) : ∃ r ∈ I, IsWeaklyRegular M (s.val ++ [r]) :=
    exists_regular_extension_of_depth_top I M hdepth s.val s.property.1 s.property.2
  choose next hnext using hex
  let step : P → P := fun s ↦
    ⟨s.val ++ [next s], (fun r hr ↦ (List.mem_append.mp hr).elim (s.property.1 r)
      (fun hr ↦ List.mem_singleton.mp hr ▸ (hnext s).1)), (hnext s).2⟩
  let stages : ℕ → P := Nat.rec ⟨rs, hmem, hreg⟩ (fun _ s ↦ step s)
  let f : ℕ → R := fun n ↦ next (stages n)
  have hstage (n : ℕ) :
      (stages n).val = rs ++ List.ofFn (fun i : Fin n ↦ f i.val) := by
    induction n with
    | zero => simp [stages]
    | succ n ih =>
      change (stages n).val ++ [f n] = _
      rw [ih, List.ofFn_succ']
      simp only [Fin.val_castSucc, Fin.val_last, List.concat_eq_append, List.append_assoc]
  refine ⟨f, fun n ↦ (hnext (stages n)).1, fun n ↦ ?_⟩
  rw [← hstage n]
  exact (stages n).property.2

/-- Infinite depth produces an infinite regular sequence starting from the empty prefix. -/
theorem exists_infinite_regular_sequence (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] (hdepth : depth I M = ⊤) :
    ∃ f : ℕ → R, (∀ n, f n ∈ I) ∧
      ∀ n, IsWeaklyRegular M (List.ofFn (fun i : Fin n ↦ f i.val)) := by
  simpa using exists_infinite_regular_extension I M hdepth [] (by simp)
    (IsWeaklyRegular.nil R M)

end SGA.SGA2.ExposeIII
