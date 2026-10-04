/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Topology.SurfaceSchreier

/-!
# Face words of the Schreier ribbon graph

For a transversal `t : Φ → F` (in the applications, `t ψ • φ₀ = ψ`), the edge `(ψ, i)` of the
Schreier graph is labelled `t ψ⁻¹ σᵢ t (σᵢ⁻¹ • ψ)` (`Ribbon.Schreier.edgeLabel`). The word of the
face through `out i ψ` is `t ψ⁻¹ σᵢ ^ e t ψ` with `e` the length of the orbit of `ψ` under `σᵢ`
(`Ribbon.Schreier.word_cyc_true`), and the word of the face through `in n ψ` is
`t ψ⁻¹ (τ⁻¹) ^ e t ψ` with `τ = σ₀ ⋯ σₙ` and `e` the length of the orbit of `ψ` under `τ`
(`Ribbon.Schreier.word_cyc_inn`).

## References

* [W. Magnus, A. Karrass, D. Solitar, *Combinatorial Group Theory*, §2.3][magnus1966]
-/

open Function

namespace Ribbon.Schreier

variable {F : Type*} [Group F] {Φ : Type*} [MulAction F Φ] {n : ℕ} (σ : Fin (n + 1) → F)

/-- The **Schreier label** of the edge `(ψ, i)` for a transversal `t`:
`t ψ⁻¹ σᵢ t (σᵢ⁻¹ • ψ)`. -/
def edgeLabel (t : Φ → F) (e : Φ × Fin (n + 1)) : F := (t e.1)⁻¹ * σ e.2 * t ((σ e.2)⁻¹ • e.1)

/-- The generator read along a dart: `σᵢ` along `out`, `σᵢ⁻¹` along `in`. -/
def gen (d : Dart Φ n) : F := if d.2 then σ d.1.2 else (σ d.1.2)⁻¹

lemma label_edgeLabel (t : Φ → F) (d : Dart Φ n) :
    label (edgeLabel σ t) d = (t (vtx σ d))⁻¹ * gen σ d * t (vtx σ (facePerm (rot σ) d)) := by
  obtain ⟨⟨ψ, i⟩, _ | _⟩ := d <;> simp [label, edgeLabel, gen, mul_assoc, flip]

/-- The product of the generators read along `L` steps of a face. -/
def genProd (d : Dart Φ n) (L : ℕ) : F := ((List.iterate (facePerm (rot σ)) d L).map (gen σ)).prod

lemma word_iterate (t : Φ → F) (d : Dart Φ n) (L : ℕ) :
    word (edgeLabel σ t) (List.iterate (facePerm (rot σ)) d L) =
      (t (vtx σ d))⁻¹ * genProd σ d L * t (vtx σ ((facePerm (rot σ))^[L] d)) := by
  induction L generalizing d with
  | zero => simp [genProd]
  | succ L ih =>
    have h1 : List.iterate (facePerm (rot σ)) d (L + 1) =
        d :: List.iterate (facePerm (rot σ)) (facePerm (rot σ) d) L := rfl
    have h2 : genProd σ d (L + 1) = gen σ d * genProd σ (facePerm (rot σ) d) L := by
      rw [genProd, h1, List.map_cons, List.prod_cons, genProd]
    rw [h1, word_cons, ih, label_edgeLabel, h2, iterate_succ_apply]
    group

lemma genProd_add (d : Dart Φ n) (a b : ℕ) :
    genProd σ d (a + b) = genProd σ d a * genProd σ ((facePerm (rot σ))^[a] d) b := by
  rw [genProd, List.iterate_add, List.map_append, List.prod_append, genProd, genProd]

lemma genProd_true (ψ : Φ) (i : Fin (n + 1)) (L : ℕ) :
    genProd σ ((ψ, i), true) L = σ i ^ L := by
  induction L generalizing ψ with
  | zero => simp [genProd]
  | succ L ih =>
    have h1 : List.iterate (facePerm (rot σ)) ((ψ, i), true) (L + 1) =
        ((ψ, i), true) :: List.iterate (facePerm (rot σ)) (facePerm (rot σ) ((ψ, i), true)) L :=
      rfl
    rw [genProd, h1, List.map_cons, List.prod_cons, ← genProd, facePerm_true, ih, pow_succ']
    simp [gen]

lemma genProd_inn (i : ℕ) (hi : i < n + 1) (v : Φ) :
    genProd σ (inn σ ⟨i, hi⟩ v) (i + 1) = (prefixProd σ i)⁻¹ := by
  induction i generalizing v with
  | zero =>
    simp [genProd, gen, inn, prefixProd_zero]
  | succ i ih =>
    have h1 : List.iterate (facePerm (rot σ)) (inn σ ⟨i + 1, hi⟩ v) (i + 1 + 1) =
        inn σ ⟨i + 1, hi⟩ v ::
          List.iterate (facePerm (rot σ)) (facePerm (rot σ) (inn σ ⟨i + 1, hi⟩ v)) (i + 1) :=
      rfl
    rw [genProd, h1, List.map_cons, List.prod_cons, ← genProd, facePerm_inn,
      fin_mk_succ_sub_one i hi, ih (by omega), prefixProd_succ σ i hi, mul_inv_rev]
    simp [gen, inn]

lemma genProd_inn_last (v : Φ) : genProd σ (inn σ (Fin.last n) v) (n + 1) = (tau σ)⁻¹ := by
  rw [← prefixProd_last]
  exact genProd_inn σ n (Nat.lt_succ_self n) v

lemma genProd_inn_mul (v : Φ) (q : ℕ) :
    genProd σ (inn σ (Fin.last n) v) ((n + 1) * q) = (tau σ)⁻¹ ^ q := by
  induction q generalizing v with
  | zero => simp [genProd]
  | succ q ih =>
    rw [mul_add, mul_one, add_comm, genProd_add, genProd_inn_last, facePerm_iterate_inn_last, ih,
      pow_succ']

lemma minimalPeriod_true (ψ : Φ) (i : Fin (n + 1)) :
    minimalPeriod (facePerm (rot σ)) ((ψ, i), true) = MulAction.period (σ i) ψ := by
  rw [← MulAction.period_inv, MulAction.period_eq_minimalPeriod,
    minimalPeriod_eq_minimalPeriod_iff]
  intro k
  simp only [IsPeriodicPt, IsFixedPt, facePerm_iterate_true, smul_iterate_apply, Prod.mk.injEq,
    and_true]

lemma minimalPeriod_inn (ψ : Φ) :
    minimalPeriod (facePerm (rot σ)) (inn σ (Fin.last n) ψ) =
      (n + 1) * MulAction.period (tau σ) ψ := by
  set d := inn σ (Fin.last n) ψ
  apply Nat.dvd_antisymm
  · apply IsPeriodicPt.minimalPeriod_dvd
    change (facePerm (rot σ))^[_] d = d
    rw [facePerm_iterate_inn_mul, MulAction.pow_period_smul]
  · have h := iterate_minimalPeriod (f := facePerm (rot σ)) (x := d)
    have hcol := (facePerm_iterate_false_snd σ d rfl (minimalPeriod (facePerm (rot σ)) d)).2
    rw [h] at hcol
    obtain ⟨q, hq⟩ := (Fin.natCast_eq_zero).mp (sub_eq_self.mp hcol.symm)
    rw [hq] at h ⊢
    rw [facePerm_iterate_inn_mul] at h
    have h' := inn_injective σ _ h
    exact Nat.mul_dvd_mul_left _ (MulAction.pow_smul_eq_iff_period_dvd.mp h')

/-- **The word of the face through `out i ψ`**: `t ψ⁻¹ σᵢ ^ e t ψ`, `e` the length of the orbit
of `ψ` under `σᵢ`. -/
theorem word_cyc_true (t : Φ → F) (ψ : Φ) (i : Fin (n + 1)) :
    word (edgeLabel σ t) (cyc (facePerm (rot σ)) ((ψ, i), true)) =
      (t ψ)⁻¹ * σ i ^ MulAction.period (σ i) ψ * t ψ := by
  rw [cyc, word_iterate, iterate_minimalPeriod, genProd_true, minimalPeriod_true]
  rfl

/-- **The word of the face through `in n ψ`**: `t ψ⁻¹ (τ⁻¹) ^ e t ψ`, `τ = σ₀ ⋯ σₙ`, `e` the
length of the orbit of `ψ` under `τ`. -/
theorem word_cyc_inn (t : Φ → F) (ψ : Φ) :
    word (edgeLabel σ t) (cyc (facePerm (rot σ)) (inn σ (Fin.last n) ψ)) =
      (t ψ)⁻¹ * (tau σ)⁻¹ ^ MulAction.period (tau σ) ψ * t ψ := by
  rw [cyc, word_iterate, iterate_minimalPeriod, minimalPeriod_inn, genProd_inn_mul, vtx_inn]

end Ribbon.Schreier
