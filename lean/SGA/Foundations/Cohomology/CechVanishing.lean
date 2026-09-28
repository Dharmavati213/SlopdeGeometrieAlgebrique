/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.Cech

/-!
# Vanishing of Čech cohomology above the number of opens

For a presheaf of abelian groups `P` and `n` opens `U₀, …, U_{n-1}`, the Čech complex of `P` is
exact in degrees `≥ n` (Stacks Project, Tag 01FM together with Lemma 20.23.6: the ordered Čech
complex is homotopy equivalent to the alternating one, which vanishes in degrees `≥ n`).

We prove this directly for the full ordered Čech complex `TopCat.Presheaf.cechComplex`, by
induction on `n`: a cocycle is first corrected, using the opens `U₀, …, U_{n-2}`, to a cocycle
supported on the tuples containing `n - 1`; on these tuples the intersections lie in `U_{n-1}`,
and the cone construction on `U_{n-1}`, corrected once more using the family `Uᵢ ∩ U_{n-1}`
(`i < n - 1`), provides a primitive.

## Main results

* `TopCat.Presheaf.cechComplex_exactAt_of_card_le`: the Čech complex of `n` opens is exact in
  degrees `≥ n`.
-/

universe v u

open CategoryTheory TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} (P : TopCat.Presheaf AddCommGrpCat.{v} X)

section Lemmas

variable {ι : Type*}

/-- The cone construction on an open containing all the others is an explicit primitive of a
cocycle. -/
lemma cechD_cone (U : ι → Opens X) (k : ι) (hk : ∀ i, U i ≤ U k) {n : ℕ}
    (c : CechCochain U P (n + 1)) (hc : cechD U P (n + 1) c = 0) :
    cechD U P n (fun y ↦ P.map (homOfLE (le_cechOpen_cons U hk y)).op (c (Fin.cons k y))) = c := by
  funext x
  have h := congrArg (P.map (homOfLE (le_cechOpen_cons U hk x)).op)
    ((cechD_cons U P k c x).symm.trans (congrFun hc (Fin.cons k x)))
  rw [map_sub, map_sum, Pi.zero_apply, map_zero, map_map_apply,
    map_apply_eq_of_eq U P rfl, sub_eq_zero] at h
  rw [h, cechD_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_map_apply, map_map_apply]

/-- Restriction to a family of smaller opens commutes with the Čech differential. -/
lemma cechD_res {U W : ι → Opens X}
    (hWU : ∀ {m : ℕ} (x : Fin (m + 1) → ι), cechOpen W x ≤ cechOpen U x) {n : ℕ}
    (c : CechCochain U P n) :
    cechD W P n (fun x ↦ P.map (homOfLE (hWU x)).op (c x)) =
      fun x ↦ P.map (homOfLE (hWU x)).op (cechD U P n c x) := by
  funext x
  rw [cechD_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, map_map_apply, map_map_apply]

end Lemmas

section Extension

variable {n : ℕ} (U : Fin (n + 1) → Opens X)

omit P in
lemma cechOpen_castPred {m : ℕ} (y : Fin (m + 1) → Fin (n + 1)) (h : ∀ j, y j ≠ Fin.last n) :
    cechOpen U y = cechOpen (U ∘ Fin.castSucc) (fun j ↦ (y j).castPred (h j)) := by
  change cechOpen U y = cechOpen U (Fin.castSucc ∘ fun j ↦ (y j).castPred (h j))
  exact congrArg _ (funext fun j ↦ (Fin.castSucc_castPred _ _).symm)

/-- Extension by zero of a cochain for the opens `U₀, …, U_{n-1}` to the tuples of
`U₀, …, Uₙ`. -/
noncomputable def extendByZero {m : ℕ} (f : CechCochain (U ∘ Fin.castSucc) P m) :
    CechCochain U P m := fun y ↦
  haveI := Classical.dec
  if h : ∀ j, y j ≠ Fin.last n then
    P.map (homOfLE (cechOpen_castPred U y h).le).op (f (fun j ↦ (y j).castPred (h j)))
  else 0

lemma extendByZero_of_forall {m : ℕ} (f : CechCochain (U ∘ Fin.castSucc) P m)
    (y : Fin (m + 1) → Fin (n + 1)) (h : ∀ j, y j ≠ Fin.last n) :
    extendByZero P U f y =
      P.map (homOfLE (cechOpen_castPred U y h).le).op (f (fun j ↦ (y j).castPred (h j))) :=
  dite_eq_left h

lemma extendByZero_of_exists {m : ℕ} (f : CechCochain (U ∘ Fin.castSucc) P m)
    (y : Fin (m + 1) → Fin (n + 1)) (h : ¬ ∀ j, y j ≠ Fin.last n) :
    extendByZero P U f y = 0 :=
  dite_eq_right h

/-- On tuples avoiding `n`, the differential of an extension by zero is the extension of the
differential. -/
lemma cechD_extendByZero {m : ℕ} (f : CechCochain (U ∘ Fin.castSucc) P m)
    (x : Fin (m + 2) → Fin (n + 1)) (h : ∀ j, x j ≠ Fin.last n) :
    cechD U P m (extendByZero P U f) x = P.map (homOfLE (cechOpen_castPred U x h).le).op
      (cechD (U ∘ Fin.castSucc) P m f (fun j ↦ (x j).castPred (h j))) := by
  rw [cechD_apply, cechD_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [extendByZero_of_forall P U f (x ∘ Fin.succAbove i) (fun j ↦ h _), map_zsmul,
    map_map_apply, map_map_apply]
  rfl

end Extension

/-- **Vanishing of Čech cohomology above the number of opens** (Stacks Project, Tag 01FM and
Lemma 20.23.6), elementwise form: for `n` opens and `p + 1 ≥ n`, every Čech cocycle of degree
`p + 1` of a presheaf of abelian groups is a coboundary. -/
theorem exists_cechD_eq_of_card_le : ∀ (n : ℕ) (U : Fin n → Opens X) (p : ℕ), n ≤ p + 1 →
    ∀ c : CechCochain U P (p + 1), cechD U P (p + 1) c = 0 →
      ∃ b : CechCochain U P p, cechD U P p b = c := by
  intro n
  induction n with
  | zero =>
    intro U p _ c _
    exact ⟨fun y ↦ isEmptyElim (y 0), funext fun x ↦ isEmptyElim (x 0)⟩
  | succ n ih =>
    intro U p hp c hc
    classical
    set k := Fin.last n with hk
    -- Step 1: correct `c` on the tuples avoiding `k`, using `U₀, …, U_{n-1}`.
    have hc' : cechD (U ∘ Fin.castSucc) P (p + 1)
        (fun x' ↦ c (Fin.castSucc ∘ x') : CechCochain (U ∘ Fin.castSucc) P (p + 1)) = 0 := by
      funext x'
      refine (cechD_apply _ _ _ _).trans ?_
      exact (cechD_apply U P c (Fin.castSucc ∘ x')).symm.trans (congrFun hc _)
    obtain ⟨b', hb'⟩ := ih (U ∘ Fin.castSucc) p (by omega) _ hc'
    set c₁ := c - cechD U P p (extendByZero P U b') with hc₁
    have hc₁_avoid (x : Fin (p + 2) → Fin (n + 1)) (hx : ∀ j, x j ≠ k) : c₁ x = 0 := by
      rw [hc₁, Pi.sub_apply, cechD_extendByZero P U b' x hx, hb', sub_eq_zero]
      exact (map_apply_eq_of_eq U P (funext fun j ↦ by simp) _ c).symm
    have hdc₁ : cechD U P (p + 1) c₁ = 0 := by
      rw [hc₁, map_sub, hc, cechD_cechD, sub_zero]
    -- Step 2: the cone construction on `U_k`, for the opens `Wᵢ = Uᵢ ∩ U_k`.
    set W : Fin (n + 1) → Opens X := fun i ↦ U i ⊓ U k with hW
    have hWU {m : ℕ} (x : Fin (m + 1) → Fin (n + 1)) : cechOpen W x ≤ cechOpen U x :=
      le_iInf fun a ↦ (iInf_le _ a).trans inf_le_left
    have hUW {m : ℕ} (x : Fin (m + 1) → Fin (n + 1)) (hx : k ∈ Set.range x) :
        cechOpen U x ≤ cechOpen W x := by
      obtain ⟨a, ha⟩ := hx
      exact le_iInf fun b ↦ le_inf (iInf_le _ b) ((iInf_le _ a).trans (by rw [ha]))
    set c₁W : CechCochain W P (p + 1) := fun x ↦ P.map (homOfLE (hWU x)).op (c₁ x) with hc₁W
    have hdc₁W : cechD W P (p + 1) c₁W = 0 := by
      rw [hc₁W, cechD_res P hWU, hdc₁]
      funext x
      simp
    have hkW : ∀ i, W i ≤ W k := fun i ↦ le_inf inf_le_right inf_le_right
    set b₁ : CechCochain W P p :=
      fun y ↦ P.map (homOfLE (le_cechOpen_cons W hkW y)).op (c₁W (Fin.cons k y)) with hb₁
    have hdb₁ : cechD W P p b₁ = c₁W := cechD_cone P W k hkW c₁W hdc₁W
    -- `b₁` restricted to the tuples avoiding `k` is a cocycle for `W₀, …, W_{n-1}`.
    have hdbbar : cechD (W ∘ Fin.castSucc) P p
        (fun y' ↦ b₁ (Fin.castSucc ∘ y') : CechCochain (W ∘ Fin.castSucc) P p) = 0 := by
      funext x'
      refine (cechD_apply _ _ _ _).trans ?_
      refine ((cechD_apply W P b₁ (Fin.castSucc ∘ x')).symm.trans (congrFun hdb₁ _)).trans ?_
      change P.map (homOfLE (hWU _)).op (c₁ (Fin.castSucc ∘ x')) = 0
      rw [hc₁_avoid (Fin.castSucc ∘ x') fun j ↦ Fin.castSucc_ne_last _, map_zero]
    -- a primitive of `b₁` on the tuples avoiding `k`
    obtain ⟨b₂, hb₂_avoid, hdb₂⟩ : ∃ b₂ : CechCochain W P p,
        (∀ y, (∀ j, y j ≠ k) → b₂ y = 0) ∧ cechD W P p b₂ = c₁W := by
      cases p with
      | zero =>
        refine ⟨b₁, fun y hy ↦ absurd ?_ (hy 0), hdb₁⟩
        have : n = 0 := by omega
        subst this
        exact Fin.ext (by have := (y 0).isLt; simp only [hk, Fin.val_last]; omega)
      | succ p' =>
        obtain ⟨e', he'⟩ := ih (W ∘ Fin.castSucc) p' (by omega) _ hdbbar
        refine ⟨b₁ - cechD W P p' (extendByZero P W e'), fun y hy ↦ ?_, ?_⟩
        · rw [Pi.sub_apply, cechD_extendByZero P W e' y hy, he', sub_eq_zero]
          exact (map_apply_eq_of_eq W P (funext fun j ↦ by simp) _ b₁).symm
        · rw [map_sub, hdb₁, cechD_cechD, sub_zero]
    -- transport `b₂` back to the tuples of `U` (containing `k`)
    set b : CechCochain U P p := fun y ↦
      if h : k ∈ Set.range y then P.map (homOfLE (hUW y h)).op (b₂ y) else 0 with hbdef
    refine ⟨b + extendByZero P U b', ?_⟩
    rw [map_add]
    suffices hdb : cechD U P p b = c₁ by
      rw [hdb, hc₁, sub_add_cancel]
    funext x
    by_cases hx : k ∈ Set.range x
    · have h := congrArg (P.map (homOfLE (hUW x hx)).op) (congrFun hdb₂ x)
      rw [hc₁W] at h
      dsimp only at h
      rw [map_map_apply, map_apply_eq_of_eq U P rfl] at h
      rw [← h, cechD_apply, cechD_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_zsmul, map_map_apply]
      by_cases hi : k ∈ Set.range (x ∘ Fin.succAbove i)
      · rw [hbdef]
        dsimp only
        rw [dite_eq_left hi, map_map_apply]
      · rw [hbdef]
        dsimp only
        rw [dite_eq_right hi, hb₂_avoid _ fun j hj ↦ hi ⟨j, hj⟩]
        simp
    · rw [hc₁_avoid x fun j hj ↦ hx ⟨j, hj⟩, cechD_apply]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      rw [hbdef]
      dsimp only
      rw [dite_eq_right fun ⟨j, hj⟩ ↦ hx ⟨_, hj⟩]
      simp

/-- **Vanishing of Čech cohomology above the number of opens** (Stacks Project, Tag 01FM and
Lemma 20.23.6): the Čech complex of a presheaf of abelian groups for `n` opens is exact in every
degree `q ≥ n`. -/
theorem cechComplex_exactAt_of_card_le {n : ℕ} (U : Fin n → Opens X) {q : ℕ} (hq : n ≤ q)
    (hq' : 0 < q) : (cechComplex U P).ExactAt q := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  rw [cechComplex_exactAt_succ_iff]
  exact exists_cechD_eq_of_card_le P n U p hq

end TopCat.Presheaf
