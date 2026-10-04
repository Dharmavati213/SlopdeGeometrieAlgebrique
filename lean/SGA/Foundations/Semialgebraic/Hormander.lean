/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.SignDiagram

/-!
# Hörmander's lemma on sign diagrams

The heart of Hörmander's proof of the Tarski–Seidenberg theorem: the sign diagram of a family
`(f₁, …, fₛ₋₁, p)` of real polynomials is determined by
* the sign diagram of `(f₁, …, fₛ₋₁, p')`,
* the signs of `p` at the roots of the nonzero `fᵢ` and of `p'` (in Hörmander's proof these are
  read off from remainders `p mod fᵢ`, `p mod p'`, which have smaller degree),
* the signs of `p` at `±∞`.

Precisely (`Polynomial.exists_orderIso_signs_of_hormander`): if an order automorphism `h` of `ℝ`
matches the signs of `f`, `p'` with those of `g`, `q'`, and the signs of `p` with those of `q` on
the *Hörmander set* `A` (the roots of the nonzero `fᵢ` and of `p'`, `hormanderSet`), and `p`,
`q` have the same signs at `±∞`, then some order automorphism `H` matches the signs of `f`, `p`
with those of `g`, `q`. `H` agrees with `h` on `A` and sends each root of `p` outside `A` to the
root of `q` in the corresponding gap (`exists_root_of_signs`); between consecutive points of `A`,
`p` is strictly monotone, so each gap contains at most one root.

## References

* [L. Hörmander, *The analysis of linear partial differential operators II*, Appendix A.2]
* [J. Bochnak, M. Coste, M.-F. Roy, *Real Algebraic Geometry*, §1.4]
-/

open Set Filter Topology

namespace Polynomial

variable {α : Type*}

/-- The *Hörmander set* of a family `f` and a polynomial `p`: the roots of the nonzero members of
`f` and of `p'`. -/
def hormanderSet (f : α → ℝ[X]) (p : ℝ[X]) : Set ℝ :=
  {x | (∃ i, f i ≠ 0 ∧ (f i).eval x = 0) ∨ p.derivative.eval x = 0}

lemma hormanderSet_finite [Finite α] (f : α → ℝ[X]) {p : ℝ[X]} (hp : p.derivative ≠ 0) :
    (hormanderSet f p).Finite := by
  have : hormanderSet f p ⊆ (⋃ i, {x | f i ≠ 0 ∧ (f i).eval x = 0}) ∪
      {x | p.derivative.eval x = 0} := by
    rintro x (⟨i, hi⟩ | hx)
    · exact Or.inl (mem_iUnion.mpr ⟨i, hi⟩)
    · exact Or.inr hx
  refine ((finite_iUnion fun i ↦ ?_).union (finite_setOfPred_isRoot hp)).subset this
  by_cases hi : f i = 0
  · simp [hi]
  · exact (finite_setOfPred_isRoot hi).subset fun x hx ↦ hx.2

lemma hormanderSet_neg (f : α → ℝ[X]) (p : ℝ[X]) : hormanderSet f (-p) = hormanderSet f p := by
  ext x
  simp [hormanderSet]

/-- If the derivative of `p` has no zero on a preconnected set and is positive at one point,
it is positive on the whole set. -/
lemma derivative_pos_of_isPreconnected {p : ℝ[X]} {s : Set ℝ} (hs : IsPreconnected s)
    (h0 : ∀ x ∈ s, p.derivative.eval x ≠ 0) {b : ℝ} (hb : b ∈ s)
    (hpos : 0 < p.derivative.eval b) {x : ℝ} (hx : x ∈ s) : 0 < p.derivative.eval x := by
  have := hs.sign_eq p.derivative.continuous.continuousOn h0 hx hb
  rw [sign_pos hpos] at this
  exact sign_eq_one_iff.mp this

variable [Finite α]

/-- The key step of Hörmander's lemma, case `p'(b) > 0`: a root `b` of `p` outside the Hörmander
set gives a root of `q` in the corresponding gap of `h(A)`. -/
private lemma exists_root_of_pos {f : α → ℝ[X]} {p q : ℝ[X]} (h : ℝ ≃o ℝ)
    (hA : ∀ x ∈ hormanderSet f p, SignType.sign (q.eval (h x)) = SignType.sign (p.eval x))
    (htop : SignType.sign q.leadingCoeff = SignType.sign p.leadingCoeff)
    (hbot : SignType.sign ((-1) ^ q.natDegree * q.leadingCoeff) =
      SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff))
    (hp' : p.derivative ≠ 0) {b : ℝ} (hb : p.eval b = 0) (hbA : b ∉ hormanderSet f p)
    (hpos : 0 < p.derivative.eval b) :
    ∃ c, q.eval c = 0 ∧ ∀ a ∈ hormanderSet f p, (a < b → h a < c) ∧ (b < a → c < h a) := by
  classical
  set A := hormanderSet f p
  have hAfin : A.Finite := hormanderSet_finite f hp'
  have hbA' : ∀ a ∈ A, a ≠ b := fun a ha hab ↦ hbA (hab ▸ ha)
  have hzA (z : ℝ) (hz : p.derivative.eval z = 0) : z ∈ A := Or.inr hz
  have hp0 : p ≠ 0 := fun h0 ↦ hp' (by simp [h0])
  have hq0 : q ≠ 0 := by
    rintro rfl
    rw [leadingCoeff_zero, sign_zero, eq_comm, sign_eq_zero_iff, leadingCoeff_eq_zero] at htop
    exact hp0 htop
  -- a point on the left of the gap of `b` where `q < 0`
  have hleft : ∃ y₁, q.eval y₁ < 0 ∧ (∀ a ∈ A, a < b → h a ≤ y₁) ∧
      (∀ a ∈ A, b < a → y₁ < h a) := by
    by_cases hL : ({a ∈ A | a < b} : Set ℝ).Nonempty
    · obtain ⟨a₀, ⟨ha₀A, ha₀b⟩, hmax⟩ :=
        Set.exists_max_image _ id (hAfin.subset (sep_subset _ _)) hL
      have hno : ∀ x ∈ Ioc a₀ b, p.derivative.eval x ≠ 0 := by
        intro x hx hx0
        rcases (hx.2).lt_or_eq with hxb | rfl
        · exact absurd (hmax x ⟨hzA x hx0, hxb⟩) (not_le.mpr hx.1)
        · exact hbA (hzA x hx0)
      have hmono : StrictMonoOn (fun x ↦ p.eval x) (Icc a₀ b) := by
        refine strictMonoOn_of_deriv_pos (convex_Icc a₀ b) p.continuous.continuousOn
          fun x hx ↦ ?_
        rw [interior_Icc] at hx
        rw [Polynomial.deriv]
        exact derivative_pos_of_isPreconnected isPreconnected_Ioc hno ⟨ha₀b, le_rfl⟩ hpos
          ⟨hx.1, hx.2.le⟩
      have hpa : p.eval a₀ < 0 := by
        have := hmono ⟨le_rfl, ha₀b.le⟩ ⟨ha₀b.le, le_rfl⟩ ha₀b
        simpa [hb] using this
      refine ⟨h a₀, ?_, fun a ha hab ↦ h.monotone (hmax a ⟨ha, hab⟩),
        fun a ha hab ↦ h.strictMono (ha₀b.trans hab)⟩
      have := hA a₀ ha₀A
      rw [sign_neg hpa] at this
      exact sign_eq_neg_one_iff.mp this
    · have hL' : ∀ a ∈ A, b < a := fun a ha ↦
        lt_of_le_of_ne (not_lt.mp fun hab ↦ hL ⟨a, ha, hab⟩) (hbA' a ha).symm
      have hno : ∀ x ∈ Iic b, p.derivative.eval x ≠ 0 := fun x hx hx0 ↦
        absurd hx (not_le.mpr (hL' x (hzA x hx0)))
      have hmono : StrictMonoOn (fun x ↦ p.eval x) (Iic b) := by
        refine strictMonoOn_of_deriv_pos (convex_Iic b) p.continuous.continuousOn
          fun x hx ↦ ?_
        rw [interior_Iic] at hx
        rw [Polynomial.deriv]
        exact derivative_pos_of_isPreconnected isPreconnected_Iic hno (Set.mem_Iic.mpr le_rfl) hpos
          (Set.mem_Iic.mpr (Set.mem_Iio.mp hx).le)
      obtain ⟨x₀, hx₀, hx₀b⟩ :=
        ((eventually_sign_eval_atBot hp0).and (eventually_lt_atBot b)).exists
      have hpx₀ : p.eval x₀ < 0 := by
        have := hmono (Set.mem_Iic.mpr hx₀b.le) (Set.mem_Iic.mpr le_rfl) hx₀b
        simpa [hb] using this
      have hsign : SignType.sign ((-1) ^ q.natDegree * q.leadingCoeff) = -1 := by
        rw [hbot, ← hx₀, sign_neg hpx₀]
      have hev := (eventually_sign_eval_atBot hq0).and
        ((eventually_all_finite hAfin).mpr fun a _ ↦ eventually_lt_atBot (h a))
      obtain ⟨y, hy, hyA⟩ := hev.exists
      refine ⟨y, sign_eq_neg_one_iff.mp (hy.trans hsign), fun a ha hab ↦ ?_, fun a ha _ ↦ hyA a ha⟩
      exact absurd hab (not_lt.mpr (hL' a ha).le)
  obtain ⟨y₁, hy₁, hy₁l, hy₁r⟩ := hleft
  -- a point on the right of the gap of `b` where `q > 0`
  have hright : ∃ y₂, y₁ < y₂ ∧ 0 < q.eval y₂ ∧ (∀ a ∈ A, b < a → y₂ ≤ h a) ∧
      (∀ a ∈ A, a < b → h a < y₂) := by
    by_cases hR : ({a ∈ A | b < a} : Set ℝ).Nonempty
    · obtain ⟨a₁, ⟨ha₁A, ha₁b⟩, hmin⟩ :=
        Set.exists_min_image _ id (hAfin.subset (sep_subset _ _)) hR
      have hno : ∀ x ∈ Ico b a₁, p.derivative.eval x ≠ 0 := by
        intro x hx hx0
        rcases (hx.1).lt_or_eq with hbx | hbx
        · exact absurd (hmin x ⟨hzA x hx0, hbx⟩) (not_le.mpr hx.2)
        · exact hbA (hbx ▸ hzA x hx0)
      have hmono : StrictMonoOn (fun x ↦ p.eval x) (Icc b a₁) := by
        refine strictMonoOn_of_deriv_pos (convex_Icc b a₁) p.continuous.continuousOn
          fun x hx ↦ ?_
        rw [interior_Icc] at hx
        rw [Polynomial.deriv]
        exact derivative_pos_of_isPreconnected isPreconnected_Ico hno ⟨le_rfl, ha₁b⟩ hpos
          ⟨hx.1.le, hx.2⟩
      have hpa : 0 < p.eval a₁ := by
        have := hmono ⟨le_rfl, ha₁b.le⟩ ⟨ha₁b.le, le_rfl⟩ ha₁b
        simpa [hb] using this
      refine ⟨h a₁, hy₁r a₁ ha₁A ha₁b, ?_, fun a ha hab ↦ h.monotone (hmin a ⟨ha, hab⟩),
        fun a ha hab ↦ h.strictMono (hab.trans ha₁b)⟩
      have := hA a₁ ha₁A
      rw [sign_pos hpa] at this
      exact sign_eq_one_iff.mp this
    · have hR' : ∀ a ∈ A, a < b := fun a ha ↦
        lt_of_le_of_ne (not_lt.mp fun hab ↦ hR ⟨a, ha, hab⟩) (hbA' a ha)
      have hno : ∀ x ∈ Ici b, p.derivative.eval x ≠ 0 := fun x hx hx0 ↦
        absurd hx (not_le.mpr (hR' x (hzA x hx0)))
      have hmono : StrictMonoOn (fun x ↦ p.eval x) (Ici b) := by
        refine strictMonoOn_of_deriv_pos (convex_Ici b) p.continuous.continuousOn
          fun x hx ↦ ?_
        rw [interior_Ici] at hx
        rw [Polynomial.deriv]
        exact derivative_pos_of_isPreconnected isPreconnected_Ici hno (Set.mem_Ici.mpr le_rfl) hpos
          (Set.mem_Ici.mpr (Set.mem_Ioi.mp hx).le)
      obtain ⟨x₀, hx₀, hx₀b⟩ :=
        ((eventually_sign_eval_atTop hp0).and (eventually_gt_atTop b)).exists
      have hpx₀ : 0 < p.eval x₀ := by
        have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx₀b.le) hx₀b
        simpa [hb] using this
      have hsign : SignType.sign q.leadingCoeff = 1 := by
        rw [htop, ← hx₀, sign_pos hpx₀]
      have hev := ((eventually_sign_eval_atTop hq0).and (eventually_gt_atTop y₁)).and
        ((eventually_all_finite hAfin).mpr fun a _ ↦ eventually_gt_atTop (h a))
      obtain ⟨y, ⟨hy, hyy₁⟩, hyA⟩ := hev.exists
      refine ⟨y, hyy₁, sign_eq_one_iff.mp (hy.trans hsign), fun a ha hab ↦ ?_,
        fun a ha _ ↦ hyA a ha⟩
      exact absurd hab (not_lt.mpr (hR' a ha).le)
  obtain ⟨y₂, hy₁₂, hy₂, hy₂r, hy₂l⟩ := hright
  obtain ⟨c, hc, hc0⟩ := intermediate_value_Ioo hy₁₂.le q.continuous.continuousOn
    (show (0 : ℝ) ∈ Ioo (q.eval y₁) (q.eval y₂) from ⟨hy₁, hy₂⟩)
  exact ⟨c, hc0, fun a ha ↦ ⟨fun hab ↦ (hy₁l a ha hab).trans_lt hc.1,
    fun hab ↦ hc.2.trans_le (hy₂r a ha hab)⟩⟩

/-- The key step of Hörmander's lemma: a root `b` of `p` outside the Hörmander set gives a root of
`q` in the corresponding gap of `h(A)`. -/
lemma exists_root_of_signs {f : α → ℝ[X]} {p q : ℝ[X]} (h : ℝ ≃o ℝ)
    (hA : ∀ x ∈ hormanderSet f p, SignType.sign (q.eval (h x)) = SignType.sign (p.eval x))
    (htop : SignType.sign q.leadingCoeff = SignType.sign p.leadingCoeff)
    (hbot : SignType.sign ((-1) ^ q.natDegree * q.leadingCoeff) =
      SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff))
    (hp' : p.derivative ≠ 0) {b : ℝ} (hb : p.eval b = 0) (hbA : b ∉ hormanderSet f p) :
    ∃ c, q.eval c = 0 ∧ ∀ a ∈ hormanderSet f p, (a < b → h a < c) ∧ (b < a → c < h a) := by
  have hb' : p.derivative.eval b ≠ 0 := fun h0 ↦ hbA (Or.inr h0)
  rcases lt_or_gt_of_ne hb' with hneg | hpos
  · obtain ⟨c, hc, hpos⟩ := exists_root_of_pos (f := f) (p := -p) (q := -q) (b := b) h
      (fun x hx ↦ by
        rw [hormanderSet_neg] at hx
        simp [eval_neg, Left.sign_neg, hA x hx])
      (by simp [leadingCoeff_neg, Left.sign_neg, htop])
      (by simp [leadingCoeff_neg, natDegree_neg, mul_neg, Left.sign_neg, hbot])
      (by simpa using hp') (by simp [hb]) (by rwa [hormanderSet_neg])
      (by simpa using hneg)
    exact ⟨c, by simpa using hc, by rwa [hormanderSet_neg] at hpos⟩
  · exact exists_root_of_pos h hA htop hbot hp' hb hbA hpos

/-- **Hörmander's lemma** (one step). Let `h` be an order automorphism of `ℝ` matching the signs of
the family `f` with those of `g`, and of `p'` with those of `q'`, and the signs of `p` with those
of `q` at the roots of the nonzero `fᵢ` and of `p'`; suppose moreover that `p` and `q` have the
same signs at `±∞`. Then some order automorphism of `ℝ` matches the signs of `f` and `p` with
those of `g` and `q`. -/
theorem exists_orderIso_signs_of_hormander {f g : α → ℝ[X]} {p q : ℝ[X]} (h : ℝ ≃o ℝ)
    (hf : ∀ i x, SignType.sign ((g i).eval (h x)) = SignType.sign ((f i).eval x))
    (hd : ∀ x, SignType.sign (q.derivative.eval (h x)) = SignType.sign (p.derivative.eval x))
    (hA : ∀ x ∈ hormanderSet f p, SignType.sign (q.eval (h x)) = SignType.sign (p.eval x))
    (htop : SignType.sign q.leadingCoeff = SignType.sign p.leadingCoeff)
    (hbot : SignType.sign ((-1) ^ q.natDegree * q.leadingCoeff) =
      SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff)) :
    ∃ H : ℝ ≃o ℝ, (∀ i x, SignType.sign ((g i).eval (H x)) = SignType.sign ((f i).eval x)) ∧
      ∀ x, SignType.sign (q.eval (H x)) = SignType.sign (p.eval x) := by
  classical
  by_cases hp' : p.derivative = 0
  · exact ⟨h, hf, fun x ↦ hA x (Or.inr (by simp [hp']))⟩
  set A := hormanderSet f p
  have hAfin : A.Finite := hormanderSet_finite f hp'
  have hp0 : p ≠ 0 := fun h0 ↦ hp' (by simp [h0])
  have hzero (a b : ℝ) (hab : SignType.sign a = SignType.sign b) : a = 0 ↔ b = 0 := by
    rw [← sign_eq_zero_iff, hab, sign_eq_zero_iff]
  -- the Hörmander sets correspond under `h`
  have hfg (i : α) : f i ≠ 0 ↔ g i ≠ 0 := not_congr (SignEquiv.eq_zero_iff ⟨h, hf⟩ i)
  have hmem (x : ℝ) : x ∈ A ↔ h x ∈ hormanderSet g q := by
    simp only [A, hormanderSet, mem_ofPred_eq]
    refine or_congr (exists_congr fun i ↦ and_congr (hfg i) ?_) ?_
    · exact (hzero _ _ (hf i x)).symm
    · exact (hzero _ _ (hd x)).symm
  have hq' : q.derivative ≠ 0 := by
    intro h0
    apply hp'
    refine Polynomial.funext fun x ↦ ?_
    have := hd x
    rw [h0, eval_zero, sign_zero, eq_comm, sign_eq_zero_iff] at this
    simpa using this
  have hq0 : q ≠ 0 := fun h0 ↦ hq' (by simp [h0])
  -- roots of `p` outside `A` and of `q` outside `h(A)`
  have claim := fun b (hb : p.eval b = 0) (hbA : b ∉ A) ↦
    exists_root_of_signs h hA htop hbot hp' hb hbA
  have claim' := fun c (hc : q.eval c = 0) (hcA : c ∉ hormanderSet g q) ↦
    exists_root_of_signs (f := g) (p := q) (q := p) h.symm
      (fun y hy ↦ by
        have hy' : h.symm y ∈ A := by rw [hmem, OrderIso.apply_symm_apply]; exact hy
        rw [← hA _ hy', OrderIso.apply_symm_apply])
      htop.symm hbot.symm hq' hc hcA
  choose! φ hφ0 hφpos using claim
  set Φ : ℝ → ℝ := fun x ↦ if x ∈ A then h x else φ x
  have hB : {x | p.eval x = 0}.Finite := finite_setOfPred_isRoot hp0
  have hC : (A ∪ {x | p.eval x = 0}).Finite := hAfin.union hB
  have hΦ : StrictMonoOn Φ hC.toFinset := by
    intro x hx y hy hxy
    rw [Set.Finite.coe_toFinset] at hx hy
    by_cases hxA : x ∈ A <;> by_cases hyA : y ∈ A <;> simp only [Φ, hxA, hyA, ite_true, ite_false]
    · exact h.strictMono hxy
    · exact ((hφpos y (hy.resolve_left hyA) hyA) x hxA).1 hxy
    · exact ((hφpos x (hx.resolve_left hxA) hxA) y hyA).2 hxy
    · obtain ⟨c, hc, hc0⟩ := exists_isRoot_derivative_between hxy (hx.resolve_left hxA)
        (hy.resolve_left hyA)
      have hcA : c ∈ A := Or.inr hc0
      exact (((hφpos x (hx.resolve_left hxA) hxA) c hcA).2 hc.1).trans
        (((hφpos y (hy.resolve_left hyA) hyA) c hcA).1 hc.2)
  obtain ⟨H, hH⟩ := Real.exists_orderIso_eqOn hC.toFinset hΦ
  have hHA (a : ℝ) (ha : a ∈ A) : H a = h a := by
    rw [hH (by rw [Set.Finite.coe_toFinset]; exact Or.inl ha)]
    simp [Φ, ha]
  have hHB (b : ℝ) (hb : p.eval b = 0) (hbA : b ∉ A) : H b = φ b := by
    rw [hH (by rw [Set.Finite.coe_toFinset]; exact Or.inr hb)]
    simp [Φ, hbA]
  -- `H x` and `h x` lie in the same gap of `h(A)` when `x ∉ A`
  have hgap (x : ℝ) (hxA : x ∉ A) (z : ℝ) (hz : z ∈ uIcc (H x) (h x))
      (hzA : z ∈ hormanderSet g q) : False := by
    obtain ⟨a, rfl⟩ := h.surjective z
    have haA : a ∈ A := (hmem a).mpr hzA
    have hax : a ≠ x := fun hax ↦ hxA (hax ▸ haA)
    rcases lt_or_gt_of_ne hax with hlt | hlt
    · have h1 : h a < H x := (hHA a haA) ▸ H.strictMono hlt
      have h2 : h a < h x := h.strictMono hlt
      exact absurd hz.1 (not_le.mpr (lt_min h1 h2))
    · have h1 : H x < h a := (hHA a haA) ▸ H.strictMono hlt
      have h2 : h x < h a := h.strictMono hlt
      exact absurd hz.2 (not_le.mpr (max_lt h1 h2))
  refine ⟨H, fun i x ↦ ?_, fun x ↦ ?_⟩
  · -- the signs of the `fᵢ`
    by_cases hxA : x ∈ A
    · rw [hHA x hxA, hf]
    by_cases hgi : g i = 0
    · rw [← hf i x, hgi]
      simp
    rw [← hf i x]
    exact isPreconnected_uIcc.sign_eq (g i).continuous.continuousOn
      (fun z hz hz0 ↦ hgap x hxA z hz (Or.inl ⟨i, hgi, hz0⟩)) left_mem_uIcc right_mem_uIcc
  -- the signs of `p`: first the zero sets
  have hroots (x : ℝ) : q.eval (H x) = 0 ↔ p.eval x = 0 := by
    constructor
    · intro hq
      by_cases hc : H x ∈ hormanderSet g q
      · have haA : h.symm (H x) ∈ A := by
          rw [hmem, OrderIso.apply_symm_apply]; exact hc
        have hxa : x = h.symm (H x) :=
          H.injective (by rw [hHA _ haA, OrderIso.apply_symm_apply])
        have := hA _ haA
        rw [OrderIso.apply_symm_apply, ← hxa] at this
        exact (hzero _ _ this).mp hq
      · obtain ⟨b, hb, hbpos⟩ := claim' (H x) hq hc
        have hbA : b ∉ A := by
          intro hbA
          have hy : h b ∈ hormanderSet g q := (hmem b).mp hbA
          have hne : h b ≠ H x := fun he ↦ hc (he ▸ hy)
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · simpa using (hbpos _ hy).1 hlt
          · simpa using (hbpos _ hy).2 hlt
        have hpos' := hφpos b hb hbA
        have hφb := hφ0 b hb hbA
        -- `H x` and `φ b` are roots of `q` in the same gap of `h(A)`
        have heq : H x = φ b := by
          by_contra hne
          have key (u v : ℝ) (huv : u < v) (hu : u = H x ∨ u = φ b) (hv : v = H x ∨ v = φ b) :
              False := by
            have hqu : q.eval u = 0 := by rcases hu with rfl | rfl <;> assumption
            have hqv : q.eval v = 0 := by rcases hv with rfl | rfl <;> assumption
            obtain ⟨z, hz, hz0⟩ := exists_isRoot_derivative_between huv hqu hqv
            have hzg : z ∈ hormanderSet g q := Or.inr hz0
            have hzA : h.symm z ∈ A := by
              rw [hmem, OrderIso.apply_symm_apply]; exact hzg
            have hab : h.symm z ≠ b := fun he ↦ hbA (he ▸ hzA)
            have hzc : z ≠ H x := fun he ↦ hc (he ▸ hzg)
            rcases lt_or_gt_of_ne hab with hlt | hlt
            · -- `z` lies below both roots
              have h1 : z < φ b := by simpa using (hpos' _ hzA).1 hlt
              have h2 : z < H x := by
                rcases lt_or_gt_of_ne hzc with h' | h'
                · exact h'
                · exact absurd hlt (not_lt.mpr ((hbpos z hzg).2 h').le)
              rcases hu with rfl | rfl
              · exact absurd hz.1 (not_lt.mpr h2.le)
              · exact absurd hz.1 (not_lt.mpr h1.le)
            · have h1 : φ b < z := by simpa using (hpos' _ hzA).2 hlt
              have h2 : H x < z := by
                rcases lt_or_gt_of_ne hzc with h' | h'
                · exact absurd hlt (not_lt.mpr ((hbpos z hzg).1 h').le)
                · exact h'
              rcases hv with rfl | rfl
              · exact absurd hz.2 (not_lt.mpr h2.le)
              · exact absurd hz.2 (not_lt.mpr h1.le)
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · exact key _ _ hlt (Or.inl rfl) (Or.inr rfl)
          · exact key _ _ hlt (Or.inr rfl) (Or.inl rfl)
        have hxb : x = b := H.injective (by rw [heq, hHB b hb hbA])
        rw [hxb]
        exact hb
    · intro hpx
      by_cases hxA : x ∈ A
      · rw [hHA x hxA]
        exact (hzero _ _ (hA x hxA)).mpr hpx
      · rw [hHB x hpx hxA]
        exact hφ0 x hpx hxA
  -- then the signs
  by_cases hpx : p.eval x = 0
  · rw [hpx, (hroots x).mpr hpx]
  have hqx : q.eval (H x) ≠ 0 := fun h0 ↦ hpx ((hroots x).mp h0)
  have hsymm_mem (u v w : ℝ) (hw : w ∈ uIcc (H u) (H v)) : H.symm w ∈ uIcc u v := by
    rw [mem_uIcc] at hw ⊢
    rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      exact ⟨by simpa using H.symm.monotone h1, by simpa using H.symm.monotone h2⟩
    · right
      exact ⟨by simpa using H.symm.monotone h1, by simpa using H.symm.monotone h2⟩
  by_cases hcase : ∃ a ∈ A, ∀ z ∈ uIcc x a, p.eval z ≠ 0
  · obtain ⟨a, haA, ha⟩ := hcase
    have h1 := isPreconnected_uIcc.sign_eq p.continuous.continuousOn ha
      left_mem_uIcc right_mem_uIcc
    have h2 := IsPreconnected.sign_eq (s := uIcc (H x) (H a)) isPreconnected_uIcc
      q.continuous.continuousOn (fun w hw hw0 ↦ ha _ (hsymm_mem x a w hw)
        ((hroots _).mp (by rwa [OrderIso.apply_symm_apply])))
      left_mem_uIcc right_mem_uIcc
    rw [h1, h2, hHA a haA, hA a haA]
  · push Not at hcase
    have hB' : {z | p.eval z = 0}.Finite := hB
    have hside : (∀ z, x ≤ z → p.eval z ≠ 0) ∨ (∀ z, z ≤ x → p.eval z ≠ 0) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨⟨z₂, hxz₂, hz₂⟩, ⟨z₁, hz₁x, hz₁⟩⟩ := hcon
      obtain ⟨m₁, ⟨hm₁, hm₁x⟩, hmax⟩ := Set.exists_max_image {z | p.eval z = 0 ∧ z ≤ x} id
        (hB'.subset fun z hz ↦ hz.1) ⟨z₁, hz₁, hz₁x⟩
      obtain ⟨m₂, ⟨hm₂, hm₂x⟩, hmin⟩ := Set.exists_min_image {z | p.eval z = 0 ∧ x ≤ z} id
        (hB'.subset fun z hz ↦ hz.1) ⟨z₂, hz₂, hxz₂⟩
      have hm₁x' : m₁ < x := lt_of_le_of_ne hm₁x fun he ↦ hpx (he ▸ hm₁)
      have hm₂x' : x < m₂ := lt_of_le_of_ne hm₂x fun he ↦ hpx (he ▸ hm₂)
      obtain ⟨c, hc, hc0⟩ := exists_isRoot_derivative_between (hm₁x'.trans hm₂x') hm₁ hm₂
      obtain ⟨z, hz, hz0⟩ := hcase c (Or.inr hc0)
      rw [mem_uIcc] at hz
      have hzm : m₁ < z ∧ z < m₂ := by
        rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨hm₁x'.trans_le h1, h2.trans_lt hc.2⟩
        · exact ⟨hc.1.trans_le h1, h2.trans_lt hm₂x'⟩
      rcases le_total z x with hzx | hzx
      · exact absurd (hmax z ⟨hz0, hzx⟩) (not_le.mpr hzm.1)
      · exact absurd (hmin z ⟨hz0, hzx⟩) (not_le.mpr hzm.2)
    rcases hside with hge | hle
    · rw [sign_eval_eq_of_forall_ge hp0 hge, ← htop]
      refine sign_eval_eq_of_forall_ge hq0 fun w hw hw0 ↦ ?_
      have : x ≤ H.symm w := by simpa using H.symm.monotone hw
      exact hge _ this ((hroots _).mp (by rwa [OrderIso.apply_symm_apply]))
    · rw [sign_eval_eq_of_forall_le hp0 hle, ← hbot]
      refine sign_eval_eq_of_forall_le hq0 fun w hw hw0 ↦ ?_
      have : H.symm w ≤ x := by simpa using H.symm.monotone hw
      exact hle _ this ((hroots _).mp (by rwa [OrderIso.apply_symm_apply]))

end Polynomial
