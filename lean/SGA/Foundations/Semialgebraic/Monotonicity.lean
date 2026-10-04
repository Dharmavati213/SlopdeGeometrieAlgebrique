/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Topology.Order.MonotoneContinuity
import SGA.Foundations.Semialgebraic.OneVariable

/-!
# The monotonicity theorem for semialgebraic functions of one variable

**Monotonicity theorem** (`Real.IsSemialgebraicFun.exists_finset_forall_Ioo`): for a semialgebraic
function `g : ℝ → ℝ` there is a finite set `Z ⊆ ℝ` such that on every open interval avoiding `Z`,
`g` is continuous and either strictly increasing, strictly decreasing or constant. In particular
`g` is continuous and monotone or antitone on some interval `(a, a + δ)` to the right of any point
(`Real.IsSemialgebraicFun.exists_pos_continuousOn_monotoneOn_or_antitoneOn`).

The proof is the o-minimal one: it only uses that a semialgebraic subset of `ℝ` is a finite union
of points and intervals, and that first-order definitions give semialgebraic sets
(Tarski–Seidenberg). On any interval, `g` is constant or injective on a subinterval
(`exists_Ioo_const_or_injOn`), an injective `g` is strictly monotone on a subinterval
(`exists_Ioo_strictMonoOn_or_strictAntiOn`), and a strictly monotone `g` is continuous on a
subinterval (`exists_Ioo_continuousOn_of_strictMonoOn`). The set of points near which `g` is not
continuous and strictly monotone or constant is semialgebraic and contains no interval, hence is
finite.

We also record the elementary local-to-global principles used here: a continuous function on an
open interval which is, just to the right of each point, at least its value there, is monotone
(`Real.monotoneOn_of_forall_right`); with both one-sided conditions no continuity is needed
(`Real.strictMonoOn_of_forall_left_right`).

## References

* [L. van den Dries, *Tame topology and o-minimal structures*, Chapter 3, (1.2)][vdD]
* [M. Coste, *An introduction to o-minimal geometry*, Theorem 2.1][Coste]
-/

open Set hiding ofPred_and ofPred_or ofPred_exists ofPred_forall
open Filter Topology MvPolynomial

namespace Real

variable {g : ℝ → ℝ} {a b : ℝ}

/-! ### Local-to-global monotonicity -/

/-- A function continuous on `(a, b)` which, just to the right of each point `x`, is at least
`g x`, is monotone on `(a, b)`. -/
theorem monotoneOn_of_forall_right (hc : ContinuousOn g (Ioo a b))
    (h : ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ y ∈ Ioo x (x + δ), g x ≤ g y) : MonotoneOn g (Ioo a b) := by
  intro x hx z hz hxz
  have hsub : Icc x z ⊆ Ioo a b := Icc_subset_Ioo hx.1 hz.2
  have hS : IsClosed (Icc x z ∩ g ⁻¹' Ici (g x)) :=
    (hc.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hne : (Icc x z ∩ g ⁻¹' Ici (g x)).Nonempty := ⟨x, ⟨le_rfl, hxz⟩, le_refl (g x)⟩
  have hbdd : BddAbove (Icc x z ∩ g ⁻¹' Ici (g x)) := ⟨z, fun y hy ↦ hy.1.2⟩
  have hmem := hS.csSup_mem hne hbdd
  set s := sSup (Icc x z ∩ g ⁻¹' Ici (g x))
  rcases eq_or_lt_of_le hmem.1.2 with hsz | hsz
  · rw [← hsz]
    exact hmem.2
  · exfalso
    obtain ⟨δ, hδ, hδ'⟩ := h s (hsub hmem.1)
    have hy : min (s + δ / 2) z ∈ Icc x z ∩ g ⁻¹' Ici (g x) := by
      refine ⟨⟨le_min (by linarith [hmem.1.1]) hxz, min_le_right _ _⟩, ?_⟩
      exact le_trans (b := g s) hmem.2
        (hδ' _ ⟨lt_min (by linarith) hsz, (min_le_left _ _).trans_lt (by linarith)⟩)
    exact absurd (le_csSup hbdd hy) (not_le.mpr (lt_min (by linarith) hsz))

/-- A function continuous on `(a, b)` which, just to the right of each point `x`, is `> g x`, is
strictly increasing on `(a, b)`. -/
theorem strictMonoOn_of_forall_right (hc : ContinuousOn g (Ioo a b))
    (h : ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ y ∈ Ioo x (x + δ), g x < g y) : StrictMonoOn g (Ioo a b) := by
  have hm := monotoneOn_of_forall_right hc fun x hx ↦
    (h x hx).imp fun δ ⟨hδ, h⟩ ↦ ⟨hδ, fun y hy ↦ (h y hy).le⟩
  intro x hx z hz hxz
  obtain ⟨δ, hδ, h'⟩ := h x hx
  have hy : min (x + δ / 2) ((x + z) / 2) ∈ Ioo x (x + δ) :=
    ⟨lt_min (by linarith) (by linarith), (min_le_left _ _).trans_lt (by linarith)⟩
  have hyz : min (x + δ / 2) ((x + z) / 2) ≤ z := (min_le_right _ _).trans (by linarith)
  exact (h' _ hy).trans_le (hm ⟨hx.1.trans hy.1, hyz.trans_lt hz.2⟩ hz hyz)

/-- A function on `(a, b)` which, near each point `x`, is `< g x` to the left and `> g x` to the
right, is strictly increasing on `(a, b)` (no continuity needed). -/
theorem strictMonoOn_of_forall_left_right
    (h : ∀ x ∈ Ioo a b, ∃ δ > 0, (∀ y ∈ Ioo x (x + δ), g x < g y) ∧
      ∀ y ∈ Ioo (x - δ) x, g y < g x) : StrictMonoOn g (Ioo a b) := by
  intro x hx z hz hxz
  by_contra hcon
  rw [not_lt] at hcon
  -- `S` is the set of points `y > x` of `(a, b)` with `g y ≤ g x`; it contains `z`
  set S := {y ∈ Ioo x b | g y ≤ g x}
  have hzS : z ∈ S := ⟨⟨hxz, hz.2⟩, hcon⟩
  have hbdd : BddBelow S := ⟨x, fun y hy ↦ hy.1.1.le⟩
  obtain ⟨δ, hδ, hR, -⟩ := h x hx
  -- no point of `S` is in `(x, x + δ)`
  have hSδ : ∀ y ∈ S, x + δ ≤ y := fun y hy ↦ by
    by_contra hy'
    exact absurd hy.2 (not_le.mpr (hR y ⟨hy.1.1, not_le.mp hy'⟩))
  set s := sInf S
  have hxs : x + δ ≤ s := le_csInf ⟨z, hzS⟩ hSδ
  have hsz : s ≤ z := csInf_le hbdd hzS
  have hs : s ∈ Ioo a b := ⟨by linarith [hx.1], hsz.trans_lt hz.2⟩
  obtain ⟨δ', hδ', hR', hL'⟩ := h s hs
  by_cases hgs : g s ≤ g x
  · -- points just left of `s` are in `S`
    set y := max (s - δ' / 2) ((x + s) / 2)
    have hy : y ∈ Ioo (s - δ') s :=
      ⟨(by linarith : s - δ' < s - δ' / 2).trans_le (le_max_left _ _),
        max_lt (by linarith) (by linarith)⟩
    have hyS : y ∈ S :=
      ⟨⟨(by linarith : x < (x + s) / 2).trans_le (le_max_right _ _), hy.2.trans hs.2⟩,
        (hL' y hy).le.trans hgs⟩
    exact absurd (csInf_le hbdd hyS) (not_le.mpr hy.2)
  · -- points just right of `s` are not in `S`
    rw [not_le] at hgs
    obtain ⟨y, hyS, hys⟩ := exists_lt_of_csInf_lt ⟨z, hzS⟩ (by linarith : s < s + δ')
    have hsy : s ≤ y := csInf_le hbdd hyS
    rcases eq_or_lt_of_le hsy with rfl | hsy
    · exact absurd hyS.2 (not_le.mpr hgs)
    · exact absurd hyS.2 (not_le.mpr (hgs.trans (hR' y ⟨hsy, hys⟩)))

/-! ### Semialgebraic functions on subintervals -/

namespace IsSemialgebraicFun

open IsSemialgebraic

lemma _root_.Real.IsSemialgebraicSet.of_ofPred {P : ℝ → Prop}
    (h : IsSemialgebraic {v : Unit → ℝ | P (v ())}) : IsSemialgebraicSet {x | P x} :=
  h

/-- On any interval, a semialgebraic function is constant or injective on a subinterval. -/
theorem exists_Ioo_const_or_injOn (hg : IsSemialgebraicFun g) (hab : a < b) :
    ∃ c d, c < d ∧ Ioo c d ⊆ Ioo a b ∧ ((∃ y, ∀ x ∈ Ioo c d, g x = y) ∨ InjOn g (Ioo c d)) := by
  by_cases hfin : ∃ y, (g ⁻¹' {y} ∩ Ioo a b).Infinite
  · obtain ⟨y, hy⟩ := hfin
    have hS : IsSemialgebraicSet (g ⁻¹' {y} ∩ Ioo a b) :=
      (hg.preimage (isSemialgebraicSet_singleton y)).inter (isSemialgebraicSet_Ioo a b)
    obtain ⟨c, d, hcd, hsub⟩ := hS.exists_Ioo_subset_of_infinite hy
    exact ⟨c, d, hcd, hsub.trans inter_subset_right, Or.inl ⟨y, fun x hx ↦ (hsub hx).1⟩⟩
  simp only [not_exists, not_infinite] at hfin
  have hJ : IsSemialgebraicSet (g '' Ioo a b) := hg.image (isSemialgebraicSet_Ioo a b)
  have hJinf : (g '' Ioo a b).Infinite := by
    intro hJf
    refine Set.Ioo_infinite hab ((hJf.biUnion fun y _ ↦ hfin y).subset fun x hx ↦ ?_)
    exact mem_biUnion (mem_image_of_mem g hx) ⟨rfl, hx⟩
  obtain ⟨e, f, hef, hJsub⟩ := hJ.exists_Ioo_subset_of_infinite hJinf
  -- `h y` is the least point of the fibre over `y`
  set h : ℝ → ℝ := fun y ↦ if y ∈ Ioo e f then sInf (g ⁻¹' {y} ∩ Ioo a b) else 0 with h_def
  have hh (y : ℝ) (hy : y ∈ Ioo e f) :
      h y ∈ g ⁻¹' {y} ∩ Ioo a b ∧ ∀ x ∈ g ⁻¹' {y} ∩ Ioo a b, h y ≤ x := by
    obtain ⟨x, hx, hxy⟩ := hJsub hy
    have hne : (g ⁻¹' {y} ∩ Ioo a b).Nonempty := ⟨x, hxy, hx⟩
    simp only [h_def, hy, ite_true]
    exact ⟨hne.csInf_mem (hfin y), fun x hx ↦ csInf_le (hfin y).bddBelow hx⟩
  have hhs : IsSemialgebraicFun h := by
    have key : {v : Fin 2 → ℝ | h (v 0) = v 1} = {v | (e < v 0 ∧ v 0 < f ∧ a < v 1 ∧ v 1 < b ∧
        g (v 1) = v 0 ∧ ∀ t, a < t → t < b → g t = v 0 → v 1 ≤ t) ∨
        (¬ (e < v 0 ∧ v 0 < f) ∧ v 1 = 0)} := by
      ext v
      simp only [mem_ofPred_eq]
      by_cases hv : v 0 ∈ Ioo e f
      · have hv' : e < v 0 ∧ v 0 < f := hv
        simp only [hv', true_and, not_true_eq_false, false_and, or_false]
        obtain ⟨⟨h1, h2⟩, h3⟩ := hh _ hv
        constructor
        · intro hv1
          rw [← hv1]
          exact ⟨h2.1, h2.2, h1, fun t ht ht' htv ↦ h3 t ⟨htv, ht, ht'⟩⟩
        · rintro ⟨hv1, hv1', hgv, hmin⟩
          exact le_antisymm (h3 _ ⟨hgv, hv1, hv1'⟩) (hmin _ h2.1 h2.2 h1)
      · have hv' : ¬ (e < v 0 ∧ v 0 < f) := hv
        have hh0 : h (v 0) = 0 := by
          simp only [h_def]
          split_ifs
          rfl
        rw [hh0]
        constructor
        · intro h0
          exact Or.inr ⟨hv', h0.symm⟩
        · rintro (⟨h1, h2, -⟩ | ⟨-, h0⟩)
          · exact absurd ⟨h1, h2⟩ hv'
          · exact h0.symm
    unfold IsSemialgebraicFun
    rw [key]
    refine ofPred_or (ofPred_and ?_ (ofPred_and ?_ (ofPred_and ?_ (ofPred_and ?_
      (ofPred_and (hg.graph _ _) (ofPred_forall (ofPred_imp ?_ (ofPred_imp ?_
      (ofPred_imp (hg.graph _ _) ?_)))))))))
      (ofPred_and (ofPred_not (ofPred_and ?_ ?_)) ?_)
    all_goals first
      | exact ofPred_lt (by fun_prop) (by fun_prop)
      | exact ofPred_le (by fun_prop) (by fun_prop)
      | exact ofPred_eq (by fun_prop) (by fun_prop)
  have hinj : InjOn h (Ioo e f) := fun y hy y' hy' hyy' ↦ by
    have e1 : g (h y) = y := (hh y hy).1.1
    have e2 : g (h y') = y' := (hh y' hy').1.1
    rw [← e1, ← e2, hyy']
  obtain ⟨c, d, hcd, hsub⟩ := (hhs.image (isSemialgebraicSet_Ioo e f)).exists_Ioo_subset_of_infinite
    ((Set.Ioo_infinite hef).image hinj)
  refine ⟨c, d, hcd, fun x hx ↦ ?_, Or.inr fun x hx x' hx' hxx' ↦ ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hsub hx
    exact (hh y hy).1.2
  · obtain ⟨y, hy, rfl⟩ := hsub hx
    obtain ⟨y', hy', rfl⟩ := hsub hx'
    have e1 : g (h y) = y := (hh y hy).1.1
    have e2 : g (h y') = y' := (hh y' hy').1.1
    rw [← e1, ← e2, hxx']

/-! ### Injective functions are strictly monotone on a subinterval -/

/-- Points `x` such that `g > g x` just to the right of `x`. -/
private def rightUp (g : ℝ → ℝ) : Set ℝ := {x | ∃ δ, 0 < δ ∧ ∀ y, x < y → y < x + δ → g x < g y}

/-- Points `x` such that `g > g x` just to the left of `x`. -/
private def leftUp (g : ℝ → ℝ) : Set ℝ := {x | ∃ δ, 0 < δ ∧ ∀ y, x - δ < y → y < x → g x < g y}

private lemma isSemialgebraicSet_rightUp (hg : IsSemialgebraicFun g) :
    IsSemialgebraicSet (rightUp g) := by
  have : rightUp g = {x | ∃ δ, 0 < δ ∧ ∀ y, x < y → y < x + δ →
      ∀ u, g x = u → ∀ v, g y = v → u < v} := by
    ext x
    simp only [rightUp, mem_ofPred_eq, forall_eq']
  rw [this]
  refine IsSemialgebraicSet.of_ofPred (ofPred_exists (ofPred_and ?_ (ofPred_forall (ofPred_imp ?_
    (ofPred_imp ?_ (ofPred_forall (ofPred_imp (hg.graph _ _) (ofPred_forall
    (ofPred_imp (hg.graph _ _) ?_)))))))))
  all_goals exact ofPred_lt (by fun_prop) (by fun_prop)

private lemma isSemialgebraicSet_leftUp (hg : IsSemialgebraicFun g) :
    IsSemialgebraicSet (leftUp g) := by
  have : leftUp g = {x | ∃ δ, 0 < δ ∧ ∀ y, x - δ < y → y < x →
      ∀ u, g x = u → ∀ v, g y = v → u < v} := by
    ext x
    simp only [leftUp, mem_ofPred_eq, forall_eq']
  rw [this]
  refine IsSemialgebraicSet.of_ofPred (ofPred_exists (ofPred_and ?_ (ofPred_forall (ofPred_imp ?_
    (ofPred_imp ?_ (ofPred_forall (ofPred_imp (hg.graph _ _) (ofPred_forall
    (ofPred_imp (hg.graph _ _) ?_)))))))))
  all_goals exact ofPred_lt (by fun_prop) (by fun_prop)

private lemma mem_rightUp_or (hg : IsSemialgebraicFun g) (hinj : InjOn g (Ioo a b)) {x : ℝ}
    (hx : x ∈ Ioo a b) : x ∈ rightUp g ∨ x ∈ rightUp fun y ↦ -g y := by
  obtain ⟨δ, hδ, h⟩ := (hg.preimage (isSemialgebraicSet_Ioi (g x))).eventually_right x
  have hδ' : 0 < min δ (b - x) := lt_min hδ (by linarith [hx.2])
  have hmem (y : ℝ) (h1 : x < y) (h2 : y < x + min δ (b - x)) : y ∈ Ioo x (x + δ) ∧ y ∈ Ioo a b :=
    ⟨⟨h1, h2.trans_le (by linarith [min_le_left δ (b - x)])⟩,
      ⟨hx.1.trans h1, h2.trans_le (by linarith [min_le_right δ (b - x)])⟩⟩
  rcases h with h | h
  · exact Or.inl ⟨_, hδ', fun y h1 h2 ↦ h (hmem y h1 h2).1⟩
  · refine Or.inr ⟨_, hδ', fun y h1 h2 ↦ neg_lt_neg ?_⟩
    have hy := hmem y h1 h2
    have hle : g y ≤ g x := not_lt.mp fun hlt ↦ disjoint_left.mp h hy.1 hlt
    exact lt_of_le_of_ne hle fun heq ↦ (ne_of_lt h1) (hinj hx hy.2 heq.symm)

private lemma mem_leftUp_or (hg : IsSemialgebraicFun g) (hinj : InjOn g (Ioo a b)) {x : ℝ}
    (hx : x ∈ Ioo a b) : x ∈ leftUp g ∨ x ∈ leftUp fun y ↦ -g y := by
  obtain ⟨δ, hδ, h⟩ := (hg.preimage (isSemialgebraicSet_Ioi (g x))).eventually_left x
  have hδ' : 0 < min δ (x - a) := lt_min hδ (by linarith [hx.1])
  have hmem (y : ℝ) (h1 : x - min δ (x - a) < y) (h2 : y < x) :
      y ∈ Ioo (x - δ) x ∧ y ∈ Ioo a b :=
    ⟨⟨(by linarith [min_le_left δ (x - a)] : x - δ ≤ x - min δ (x - a)).trans_lt h1, h2⟩,
      ⟨(by linarith [min_le_right δ (x - a)] : a ≤ x - min δ (x - a)).trans_lt h1,
        h2.trans hx.2⟩⟩
  rcases h with h | h
  · exact Or.inl ⟨_, hδ', fun y h1 h2 ↦ h (hmem y h1 h2).1⟩
  · refine Or.inr ⟨_, hδ', fun y h1 h2 ↦ neg_lt_neg ?_⟩
    have hy := hmem y h1 h2
    have hle : g y ≤ g x := not_lt.mp fun hlt ↦ disjoint_left.mp h hy.1 hlt
    exact lt_of_le_of_ne hle fun heq ↦ (ne_of_lt h2) (hinj hy.2 hx heq)

private lemma strictMonoOn_of_subset {c d : ℝ}
    (h : Ioo c d ⊆ rightUp g ∩ leftUp fun y ↦ -g y) : StrictMonoOn g (Ioo c d) := by
  refine strictMonoOn_of_forall_left_right fun x hx ↦ ?_
  obtain ⟨⟨δ₁, hδ₁, h₁⟩, ⟨δ₂, hδ₂, h₂⟩⟩ := h hx
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy ↦ h₁ y hy.1 (hy.2.trans_le ?_), fun y hy ↦ ?_⟩
  · linarith [min_le_left δ₁ δ₂]
  · exact neg_lt_neg_iff.mp (h₂ y ((by linarith [min_le_right δ₁ δ₂] :
      x - δ₂ ≤ x - min δ₁ δ₂).trans_lt hy.1) hy.2)

/-- A function cannot have a strict local minimum at every point of an interval. -/
private lemma not_Ioo_subset_rightUp_inter_leftUp (hg : IsSemialgebraicFun g) {c d : ℝ}
    (hcd : c < d) : ¬ Ioo c d ⊆ rightUp g ∩ leftUp g := by
  intro h
  -- `K n`: points of `(c, d)` which are a strict minimum of `g` on their `1/(n+1)`-neighbourhood
  let K : ℕ → Set ℝ := fun n ↦ {x | c < x ∧ x < d ∧ ∀ y, c < y → y < d →
    x - 1 / (n + 1) < y → y < x + 1 / (n + 1) → y ≠ x → ∀ u, g x = u → ∀ v, g y = v → u < v}
  have hK (n : ℕ) : IsSemialgebraicSet (K n) := by
    refine IsSemialgebraicSet.of_ofPred (ofPred_and ?_ (ofPred_and ?_ (ofPred_forall (ofPred_imp ?_
      (ofPred_imp ?_ (ofPred_imp ?_ (ofPred_imp ?_ (ofPred_imp (ofPred_ne (by fun_prop)
      (by fun_prop)) (ofPred_forall (ofPred_imp (hg.graph _ _) (ofPred_forall
      (ofPred_imp (hg.graph _ _) ?_))))))))))))
    all_goals exact ofPred_lt (by fun_prop) (by fun_prop)
  have hcover : Ioo c d ⊆ ⋃ n, K n := by
    intro x hx
    obtain ⟨⟨δ₁, hδ₁, h₁⟩, ⟨δ₂, hδ₂, h₂⟩⟩ := h hx
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hδ₁ hδ₂)
    refine mem_iUnion.mpr ⟨n, hx.1, hx.2, fun y _ _ hy1 hy2 hyx u hu v hv ↦ ?_⟩
    rw [← hu, ← hv]
    rcases lt_or_gt_of_ne hyx with hyx | hyx
    · exact h₂ y (by linarith [min_le_right δ₁ δ₂]) hyx
    · exact h₁ y hyx (by linarith [min_le_left δ₁ δ₂])
  obtain ⟨n, hn⟩ : ∃ n, (K n).Infinite := by
    by_contra hfin
    simp only [not_exists, not_infinite] at hfin
    exact absurd ((countable_iUnion fun n ↦ (hfin n).countable).mono hcover)
      (by rw [Cardinal.Real.Ioo_countable_iff]; exact not_le.mpr hcd)
  obtain ⟨c', d', hcd', hsub⟩ := (hK n).exists_Ioo_subset_of_infinite hn
  set η := min ((d' - c') / 3) (1 / (2 * (n + 1)))
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hη₁ : η ≤ (d' - c') / 3 := min_le_left _ _
  have hη₂ : η < 1 / (n + 1) := (min_le_right _ _).trans_lt (by
    rw [one_div_lt_one_div (by positivity) (by positivity)]; linarith)
  have hx : c' + η ∈ K n := hsub ⟨by linarith, by linarith⟩
  have hx' : c' + 2 * η ∈ K n := hsub ⟨by linarith, by linarith⟩
  have h1 := hx.2.2 (c' + 2 * η) hx'.1 hx'.2.1 (by linarith) (by linarith) (by linarith) _ rfl _ rfl
  have h2 := hx'.2.2 (c' + η) hx.1 hx.2.1 (by linarith) (by linarith) (by linarith) _ rfl _ rfl
  exact lt_asymm h1 h2

/-- An injective semialgebraic function is strictly monotone on a subinterval of any interval. -/
theorem exists_Ioo_strictMonoOn_or_strictAntiOn (hg : IsSemialgebraicFun g) (hab : a < b)
    (hinj : InjOn g (Ioo a b)) :
    ∃ c d, c < d ∧ Ioo c d ⊆ Ioo a b ∧ (StrictMonoOn g (Ioo c d) ∨ StrictAntiOn g (Ioo c d)) := by
  set g' : ℝ → ℝ := fun y ↦ -g y
  have hg' : IsSemialgebraicFun g' := hg.neg
  have hinj' : InjOn g' (Ioo a b) := fun x hx y hy h ↦ hinj hx hy (neg_inj.mp h)
  have hgg : (fun y ↦ -g' y) = g := funext fun y ↦ neg_neg (g y)
  -- the four types of points
  set C₁ := rightUp g ∩ leftUp g'
  set C₂ := rightUp g' ∩ leftUp g
  set C₃ := rightUp g ∩ leftUp g
  set C₄ := rightUp g' ∩ leftUp g'
  have hcov : Ioo a b ⊆ ((C₁ ∩ Ioo a b) ∪ (C₂ ∩ Ioo a b)) ∪ ((C₃ ∩ Ioo a b) ∪ (C₄ ∩ Ioo a b)) := by
    intro x hx
    rcases mem_rightUp_or hg hinj hx with hr | hr <;>
      rcases mem_leftUp_or hg hinj hx with hl | hl
    · exact Or.inr (Or.inl ⟨⟨hr, hl⟩, hx⟩)
    · exact Or.inl (Or.inl ⟨⟨hr, hl⟩, hx⟩)
    · exact Or.inl (Or.inr ⟨⟨hr, hl⟩, hx⟩)
    · exact Or.inr (Or.inr ⟨⟨hr, hl⟩, hx⟩)
  have hS (A B : Set ℝ) (hA : IsSemialgebraicSet A) (hB : IsSemialgebraicSet B) :
      IsSemialgebraicSet (A ∩ B ∩ Ioo a b) :=
    (hA.inter hB).inter (isSemialgebraicSet_Ioo a b)
  have hinf := (Set.Ioo_infinite hab).mono hcov
  simp only [infinite_union] at hinf
  rcases hinf with (h | h) | (h | h)
  · obtain ⟨c, d, hcd, hsub⟩ := (hS _ _ (isSemialgebraicSet_rightUp hg)
      (isSemialgebraicSet_leftUp hg')).exists_Ioo_subset_of_infinite h
    exact ⟨c, d, hcd, fun x hx ↦ (hsub hx).2, Or.inl (strictMonoOn_of_subset fun x hx ↦
      (hsub hx).1)⟩
  · obtain ⟨c, d, hcd, hsub⟩ := (hS _ _ (isSemialgebraicSet_rightUp hg')
      (isSemialgebraicSet_leftUp hg)).exists_Ioo_subset_of_infinite h
    have hm : StrictMonoOn g' (Ioo c d) := strictMonoOn_of_subset fun x hx ↦ by
      rw [hgg]; exact (hsub hx).1
    exact ⟨c, d, hcd, fun x hx ↦ (hsub hx).2, Or.inr fun x hx y hy hxy ↦
      neg_lt_neg_iff.mp (hm hx hy hxy)⟩
  · obtain ⟨c, d, hcd, hsub⟩ := (hS _ _ (isSemialgebraicSet_rightUp hg)
      (isSemialgebraicSet_leftUp hg)).exists_Ioo_subset_of_infinite h
    exact absurd (fun x hx ↦ (hsub hx).1) (not_Ioo_subset_rightUp_inter_leftUp hg hcd)
  · obtain ⟨c, d, hcd, hsub⟩ := (hS _ _ (isSemialgebraicSet_rightUp hg')
      (isSemialgebraicSet_leftUp hg')).exists_Ioo_subset_of_infinite h
    exact absurd (fun x hx ↦ (hsub hx).1) (not_Ioo_subset_rightUp_inter_leftUp hg' hcd)

/-- A strictly increasing semialgebraic function is continuous on a subinterval of any
interval. -/
theorem exists_Ioo_continuousOn_of_strictMonoOn (hg : IsSemialgebraicFun g) (hab : a < b)
    (hm : StrictMonoOn g (Ioo a b)) :
    ∃ c d, c < d ∧ Ioo c d ⊆ Ioo a b ∧ ContinuousOn g (Ioo c d) := by
  obtain ⟨e, f, hef, hJ⟩ := (hg.image (isSemialgebraicSet_Ioo a b)).exists_Ioo_subset_of_infinite
    ((Set.Ioo_infinite hab).image hm.injOn)
  obtain ⟨x₁, hx₁, hgx₁⟩ := hJ (⟨by linarith, by linarith⟩ : e + (f - e) / 3 ∈ Ioo e f)
  obtain ⟨x₂, hx₂, hgx₂⟩ := hJ (⟨by linarith, by linarith⟩ : e + 2 * (f - e) / 3 ∈ Ioo e f)
  have h12 : x₁ < x₂ := by
    by_contra h
    have := hm.monotoneOn hx₂ hx₁ (not_lt.mp h)
    rw [hgx₁, hgx₂] at this
    linarith
  have hsub : Ioo x₁ x₂ ⊆ Ioo a b := Ioo_subset_Ioo hx₁.1.le hx₂.2.le
  refine ⟨x₁, x₂, h12, hsub, fun x hx ↦ ?_⟩
  refine ((hm.mono hsub).continuousAt_of_image_mem_nhds (Ioo_mem_nhds hx.1 hx.2) ?_)
    |>.continuousWithinAt
  have hlt₁ : g x₁ < g x := hm hx₁ (hsub hx) hx.1
  have hlt₂ : g x < g x₂ := hm (hsub hx) hx₂ hx.2
  refine mem_of_superset (Ioo_mem_nhds hlt₁ hlt₂) fun y hy ↦ ?_
  obtain ⟨z, hz, rfl⟩ := hJ (show y ∈ Ioo e f from ⟨by linarith [hy.1], by linarith [hy.2]⟩)
  refine ⟨z, ⟨?_, ?_⟩, rfl⟩
  · by_contra h
    exact absurd (hm.monotoneOn hz hx₁ (not_lt.mp h)) (not_le.mpr hy.1)
  · by_contra h
    exact absurd (hm.monotoneOn hx₂ hz (not_lt.mp h)) (not_le.mpr hy.2)

/-- On any interval, a semialgebraic function is continuous and either strictly increasing,
strictly decreasing or constant on some subinterval. -/
theorem exists_Ioo_continuousOn_and (hg : IsSemialgebraicFun g) (hab : a < b) :
    ∃ c d, c < d ∧ Ioo c d ⊆ Ioo a b ∧ ContinuousOn g (Ioo c d) ∧
      (StrictMonoOn g (Ioo c d) ∨ StrictAntiOn g (Ioo c d) ∨ ∃ y, ∀ x ∈ Ioo c d, g x = y) := by
  obtain ⟨c, d, hcd, hsub, hc | hinj⟩ := hg.exists_Ioo_const_or_injOn hab
  · obtain ⟨y, hy⟩ := hc
    exact ⟨c, d, hcd, hsub, continuousOn_const.congr fun x hx ↦ hy x hx, Or.inr (Or.inr ⟨y, hy⟩)⟩
  obtain ⟨c', d', hcd', hsub', hm | hm⟩ := hg.exists_Ioo_strictMonoOn_or_strictAntiOn hcd hinj
  · obtain ⟨c'', d'', hcd'', hsub'', hcont⟩ := hg.exists_Ioo_continuousOn_of_strictMonoOn hcd' hm
    exact ⟨c'', d'', hcd'', hsub''.trans (hsub'.trans hsub), hcont, Or.inl (hm.mono hsub'')⟩
  · have hm' : StrictMonoOn (fun x ↦ -g x) (Ioo c' d') := fun x hx y hy hxy ↦
      neg_lt_neg (hm hx hy hxy)
    obtain ⟨c'', d'', hcd'', hsub'', hcont⟩ :=
      hg.neg.exists_Ioo_continuousOn_of_strictMonoOn hcd' hm'
    refine ⟨c'', d'', hcd'', hsub''.trans (hsub'.trans hsub), ?_, Or.inr (Or.inl (hm.mono hsub''))⟩
    exact (show (-fun x ↦ -g x) = g from funext fun x ↦ neg_neg (g x)) ▸ hcont.neg

/-! ### The monotonicity theorem -/

/-- Points near which `g` is strictly increasing. -/
private def incPts (g : ℝ → ℝ) : Set ℝ :=
  {x | ∃ δ, 0 < δ ∧ ∀ y z, x - δ < y → y < z → z < x + δ → g y < g z}

/-- Points near which `g` is constant. -/
private def cstPts (g : ℝ → ℝ) : Set ℝ :=
  {x | ∃ δ, 0 < δ ∧ ∀ y, x - δ < y → y < x + δ → g y = g x}

private lemma isSemialgebraicSet_incPts (hg : IsSemialgebraicFun g) :
    IsSemialgebraicSet (incPts g) := by
  have : incPts g = {x | ∃ δ, 0 < δ ∧ ∀ y z, x - δ < y → y < z → z < x + δ →
      ∀ u, g y = u → ∀ v, g z = v → u < v} := by
    ext x
    simp only [incPts, mem_ofPred_eq, forall_eq']
  rw [this]
  refine IsSemialgebraicSet.of_ofPred (ofPred_exists (ofPred_and ?_ (ofPred_forall (ofPred_forall
    (ofPred_imp ?_ (ofPred_imp ?_ (ofPred_imp ?_ (ofPred_forall (ofPred_imp (hg.graph _ _)
    (ofPred_forall (ofPred_imp (hg.graph _ _) ?_)))))))))))
  all_goals exact ofPred_lt (by fun_prop) (by fun_prop)

private lemma isSemialgebraicSet_cstPts (hg : IsSemialgebraicFun g) :
    IsSemialgebraicSet (cstPts g) := by
  have : cstPts g = {x | ∃ δ, 0 < δ ∧ ∀ y, x - δ < y → y < x + δ →
      ∀ u, g y = u → ∀ v, g x = v → u = v} := by
    ext x
    simp only [cstPts, mem_ofPred_eq, forall_eq']
  rw [this]
  refine IsSemialgebraicSet.of_ofPred (ofPred_exists (ofPred_and ?_ (ofPred_forall
    (ofPred_imp ?_ (ofPred_imp ?_ (ofPred_forall (ofPred_imp (hg.graph _ _)
    (ofPred_forall (ofPred_imp (hg.graph _ _) (ofPred_eq (by fun_prop) (by fun_prop)))))))))))
  all_goals exact ofPred_lt (by fun_prop) (by fun_prop)

private lemma isSemialgebraicSet_continuousAt (hg : IsSemialgebraicFun g) :
    IsSemialgebraicSet {x | ContinuousAt g x} := by
  have : {x | ContinuousAt g x} = {x | ∀ e, 0 < e → ∃ d, 0 < d ∧ ∀ z, z - x < d → x - z < d →
      ∀ u, g z = u → ∀ v, g x = v → u - v < e ∧ v - u < e} := by
    ext x
    simp only [Metric.continuousAt_iff, Real.dist_eq, abs_sub_lt_iff, mem_ofPred_eq, forall_eq',
      gt_iff_lt, and_imp]
  rw [this]
  refine IsSemialgebraicSet.of_ofPred (ofPred_forall (ofPred_imp ?_ (ofPred_exists (ofPred_and ?_
    (ofPred_forall (ofPred_imp ?_ (ofPred_imp ?_ (ofPred_forall (ofPred_imp (hg.graph _ _)
    (ofPred_forall (ofPred_imp (hg.graph _ _) (ofPred_and ?_ ?_))))))))))))
  all_goals exact ofPred_lt (by fun_prop) (by fun_prop)

private lemma isOpen_incPts : IsOpen (incPts g) := by
  refine Metric.isOpen_iff.mpr fun x ⟨δ, hδ, h⟩ ↦ ⟨δ / 2, by linarith, fun x' hx' ↦ ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
  exact ⟨δ / 2, by linarith, fun y z hy hyz hz ↦ h y z (by linarith) hyz (by linarith)⟩

private lemma isOpen_cstPts : IsOpen (cstPts g) := by
  refine Metric.isOpen_iff.mpr fun x ⟨δ, hδ, h⟩ ↦ ⟨δ / 2, by linarith, fun x' hx' ↦ ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hx'
  refine ⟨δ / 2, by linarith, fun y hy hy' ↦ ?_⟩
  rw [h y (by linarith) (by linarith), h x' (by linarith) (by linarith)]

private lemma disjoint_incPts_neg : Disjoint (incPts g) (incPts fun x ↦ -g x) := by
  refine disjoint_left.mpr fun x ⟨δ, hδ, h⟩ ⟨δ', hδ', h'⟩ ↦ ?_
  have h1 := h x (x + min δ δ' / 2) (by linarith) (by linarith [lt_min hδ hδ'])
    (by linarith [min_le_left δ δ'])
  have h2 := h' x (x + min δ δ' / 2) (by linarith) (by linarith [lt_min hδ hδ'])
    (by linarith [min_le_right δ δ'])
  linarith

private lemma disjoint_incPts_cstPts : Disjoint (incPts g) (cstPts g) := by
  refine disjoint_left.mpr fun x ⟨δ, hδ, h⟩ ⟨δ', hδ', h'⟩ ↦ ?_
  have h1 := h x (x + min δ δ' / 2) (by linarith) (by linarith [lt_min hδ hδ'])
    (by linarith [min_le_left δ δ'])
  have h2 := h' (x + min δ δ' / 2) (by linarith [lt_min hδ hδ'])
    (by linarith [min_le_right δ δ'])
  linarith

/-- **Monotonicity theorem.** For a semialgebraic function `g : ℝ → ℝ` there is a finite set
`Z ⊆ ℝ` such that on every open interval `(a, b)` avoiding `Z`, `g` is continuous and either
strictly increasing, strictly decreasing or constant. -/
theorem exists_finset_forall_Ioo (hg : IsSemialgebraicFun g) :
    ∃ Z : Finset ℝ, ∀ a b, (∀ z ∈ Z, z ∉ Ioo a b) → ContinuousOn g (Ioo a b) ∧
      (StrictMonoOn g (Ioo a b) ∨ StrictAntiOn g (Ioo a b) ∨ ∃ y, ∀ x ∈ Ioo a b, g x = y) := by
  set g' : ℝ → ℝ := fun x ↦ -g x
  set G := {x | ContinuousAt g x} ∩ (incPts g ∪ incPts g' ∪ cstPts g)
  have hG : IsSemialgebraicSet G := (isSemialgebraicSet_continuousAt hg).inter
    (((isSemialgebraicSet_incPts hg).union (isSemialgebraicSet_incPts hg.neg)).union
      (isSemialgebraicSet_cstPts hg))
  -- the bad points are finite
  have hfin : Gᶜ.Finite := by
    by_contra hinf
    obtain ⟨a, b, hab, hsub⟩ := hG.compl.exists_Ioo_subset_of_infinite hinf
    obtain ⟨c, d, hcd, hsub', hcont, htype⟩ := hg.exists_Ioo_continuousOn_and hab
    obtain ⟨m, hm_def⟩ : ∃ m, m = (c + d) / 2 := ⟨_, rfl⟩
    have hm : m ∈ Ioo c d := ⟨by linarith, by linarith⟩
    refine hsub (hsub' hm) ⟨hcont.continuousAt (Ioo_mem_nhds hm.1 hm.2), ?_⟩
    have hδ : 0 < (d - c) / 2 := by linarith
    have hI (y : ℝ) (h1 : m - (d - c) / 2 < y) (h2 : y < m + (d - c) / 2) : y ∈ Ioo c d :=
      ⟨by linarith, by linarith⟩
    rcases htype with hmono | hanti | ⟨y₀, hy₀⟩
    · exact Or.inl (Or.inl ⟨_, hδ, fun y z hy hyz hz ↦
        hmono (hI y hy (hyz.trans hz)) (hI z (hy.trans hyz) hz) hyz⟩)
    · exact Or.inl (Or.inr ⟨_, hδ, fun y z hy hyz hz ↦
        neg_lt_neg (hanti (hI y hy (hyz.trans hz)) (hI z (hy.trans hyz) hz) hyz)⟩)
    · exact Or.inr ⟨_, hδ, fun y hy hy' ↦ by rw [hy₀ y (hI y hy hy'), hy₀ m hm]⟩
  refine ⟨hfin.toFinset, fun a b hZ ↦ ?_⟩
  have hgood : Ioo a b ⊆ G := fun x hx ↦ by
    by_contra h
    exact hZ x (hfin.mem_toFinset.mpr h) hx
  have hcont : ContinuousOn g (Ioo a b) := fun x hx ↦ (hgood hx).1.continuousWithinAt
  refine ⟨hcont, ?_⟩
  have htypes : Ioo a b ⊆ incPts g ∪ (incPts g' ∪ cstPts g) := fun x hx ↦ by
    rcases (hgood hx).2 with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hdisj : Disjoint (incPts g) (incPts g' ∪ cstPts g) :=
    disjoint_union_right.mpr ⟨disjoint_incPts_neg, disjoint_incPts_cstPts⟩
  have hdisj' : Disjoint (incPts g') (cstPts g) := by
    have := disjoint_incPts_cstPts (g := g')
    have hc : cstPts g' = cstPts g := by
      ext x
      simp only [cstPts, mem_ofPred_eq, g', neg_inj]
    rwa [hc] at this
  -- local right conditions
  have hright (g₀ : ℝ → ℝ) (h : Ioo a b ⊆ incPts g₀) :
      ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ y ∈ Ioo x (x + δ), g₀ x < g₀ y := fun x hx ↦ by
    obtain ⟨δ, hδ, h'⟩ := h hx
    exact ⟨δ, hδ, fun y hy ↦ h' x y (by linarith) hy.1 hy.2⟩
  rcases isPreconnected_Ioo.subset_or_subset isOpen_incPts (isOpen_incPts.union isOpen_cstPts)
    hdisj htypes with h | h
  · exact Or.inl (strictMonoOn_of_forall_right hcont (hright g h))
  rcases isPreconnected_Ioo.subset_or_subset isOpen_incPts isOpen_cstPts hdisj' h with h | h
  · have := strictMonoOn_of_forall_right (g := g') hcont.neg (hright g' h)
    exact Or.inr (Or.inl fun x hx y hy hxy ↦ neg_lt_neg_iff.mp (this hx hy hxy))
  · -- locally constant
    have hloc (g₀ : ℝ → ℝ) (hc₀ : ContinuousOn g₀ (Ioo a b))
        (h₀ : ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ y ∈ Ioo x (x + δ), g₀ y = g₀ x) : MonotoneOn g₀ (Ioo a b) :=
      monotoneOn_of_forall_right hc₀ fun x hx ↦ (h₀ x hx).imp fun δ ⟨hδ, h⟩ ↦
        ⟨hδ, fun y hy ↦ (h y hy).ge⟩
    have hcst : ∀ x ∈ Ioo a b, ∃ δ > 0, ∀ y ∈ Ioo x (x + δ), g y = g x := fun x hx ↦ by
      obtain ⟨δ, hδ, h'⟩ := h hx
      exact ⟨δ, hδ, fun y hy ↦ h' y (by linarith [hy.1]) hy.2⟩
    have h1 := hloc g hcont hcst
    have h2 := hloc g' hcont.neg fun x hx ↦ (hcst x hx).imp fun δ ⟨hδ, h⟩ ↦
      ⟨hδ, fun y hy ↦ by simp only [g', h y hy]⟩
    rcases (Ioo a b).eq_empty_or_nonempty with he | ⟨x₀, hx₀⟩
    · exact Or.inr (Or.inr ⟨0, by simp [he]⟩)
    refine Or.inr (Or.inr ⟨g x₀, fun x hx ↦ ?_⟩)
    rcases le_total x x₀ with hxx | hxx
    · exact le_antisymm (h1 hx hx₀ hxx) (neg_le_neg_iff.mp (h2 hx hx₀ hxx))
    · exact le_antisymm (neg_le_neg_iff.mp (h2 hx₀ hx hxx)) (h1 hx₀ hx hxx)

/-- **Monotonicity theorem**, to the right of a point: a semialgebraic function is continuous and
monotone or antitone on some interval `(a, a + δ)`, `δ > 0`. -/
theorem exists_pos_continuousOn_monotoneOn_or_antitoneOn (hg : IsSemialgebraicFun g) (a : ℝ) :
    ∃ δ > 0, ContinuousOn g (Ioo a (a + δ)) ∧
      (MonotoneOn g (Ioo a (a + δ)) ∨ AntitoneOn g (Ioo a (a + δ))) := by
  obtain ⟨Z, hZ⟩ := hg.exists_finset_forall_Ioo
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ z ∈ Z, z ∉ Ioo a (a + δ) := by
    refine (Filter.eventually_all_finset Z).mpr fun z _ ↦ ?_
    rcases le_or_gt z a with hza | hza
    · exact Filter.Eventually.of_forall fun δ hz ↦ absurd hz.1 (not_lt.mpr hza)
    · filter_upwards [Ioo_mem_nhdsGT (by linarith : (0 : ℝ) < z - a)] with δ hδ hz
      linarith [hz.2, hδ.2]
  obtain ⟨δ, hδZ, hδ⟩ := (hev.and self_mem_nhdsWithin).exists
  obtain ⟨hcont, h | h | ⟨y, hy⟩⟩ := hZ a (a + δ) hδZ
  · exact ⟨δ, hδ, hcont, Or.inl h.monotoneOn⟩
  · exact ⟨δ, hδ, hcont, Or.inr h.antitoneOn⟩
  · exact ⟨δ, hδ, hcont, Or.inl fun x hx z hz _ ↦ by rw [hy x hx, hy z hz]⟩

/-- **Monotonicity theorem**, to the right of a point, in filter form: for all small `δ > 0`, a
semialgebraic function is continuous and monotone or antitone on `(a, a + δ)`. -/
theorem eventually_continuousOn_monotoneOn_or_antitoneOn (hg : IsSemialgebraicFun g) (a : ℝ) :
    ∀ᶠ δ in 𝓝[>] (0 : ℝ), ContinuousOn g (Ioo a (a + δ)) ∧
      (MonotoneOn g (Ioo a (a + δ)) ∨ AntitoneOn g (Ioo a (a + δ))) := by
  obtain ⟨δ₀, hδ₀, hc, hm⟩ := hg.exists_pos_continuousOn_monotoneOn_or_antitoneOn a
  filter_upwards [Ioc_mem_nhdsGT hδ₀] with δ hδ
  have hsub : Ioo a (a + δ) ⊆ Ioo a (a + δ₀) := Ioo_subset_Ioo_right (by linarith [hδ.2])
  exact ⟨hc.mono hsub, hm.imp (fun h ↦ h.mono hsub) fun h ↦ h.mono hsub⟩

end IsSemialgebraicFun

end Real
