/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import Mathlib.Topology.FiberBundle.Trivialization
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import SGA.Foundations.Topology.PathConnectedHelpersBasic

/-!
# Homotopy lifting for locally trivial maps and the exact sequence of `π₁`

Let `p : E → B` be *locally trivial with fibre `F`*: every point of `B` lies in the base set of a
`Bundle.Trivialization F p`. We prove:

* `Bundle.exists_lift_square`: a map `H : I × I → B` lifts to `E`, extending any lift given on
  the two sides `{0} × I ∪ I × {0}` of the square (the homotopy lifting property for the square,
  relative to an "L"); in particular paths lift (`Bundle.exists_path_lift`);
* the exact sequence of fundamental groups: for `e₀ ∈ E` over `b₀`, with `ι : p⁻¹(b₀) → E` the
  inclusion of the fibre,
  `π₁(p⁻¹(b₀), e₀) → π₁(E, e₀) → π₁(B, b₀) → 1` is exact at `π₁(E, e₀)`
  (`Bundle.range_fundamentalGroup_map_fibre_eq_ker`), and the last map is surjective when the
  fibre is path-connected (`Bundle.fundamentalGroup_map_surjective`).

Exactness further to the left (the boundary map `π₂(B) → π₁(F)`) is not done here.

## Method

Lifting over a small rectangle mapping into a trivialization is done in the chart, keeping the
fibre coordinate of the given lift along a retraction of the rectangle onto two of its sides
(`(x, y) ↦ (x - m, y - m)`, `m = min (x - a) (y - c)`). The property "every lift on the two sides
extends" passes from the two halves of a rectangle to the rectangle, in both directions, so it
holds for all rectangles of side at most `2ᵏ δ` by induction on `k`, where `δ` is a Lebesgue
number of the cover of `[0, 1]²` by the preimages of the trivializations. No explicit grid is
needed.

## References

* [A. Hatcher, *Algebraic Topology*, §4.2, Proposition 4.48 and Theorem 4.41][hatcher02]
-/

open Set Topology unitInterval

noncomputable section

namespace Bundle

variable {B E F : Type*} [TopologicalSpace B] [TopologicalSpace E] [TopologicalSpace F]
  {p : E → B}

section Rectangle

/-- The closed rectangle `[a, b] × [c, d]` of `ℝ²`. -/
private def rect (a b c d : ℝ) : Set (ℝ × ℝ) := Icc a b ×ˢ Icc c d

/-- The two sides `{a} × [c, d] ∪ [a, b] × {c}` of the rectangle. -/
private def lside (a b c d : ℝ) : Set (ℝ × ℝ) := ({a} ×ˢ Icc c d) ∪ (Icc a b ×ˢ {c})

private lemma lside_subset_rect {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    lside a b c d ⊆ rect a b c d := by
  rintro ⟨x, y⟩ (⟨hx, hy⟩ | ⟨hx, hy⟩)
  · simp only [mem_singleton_iff] at hx
    exact ⟨⟨hx.ge, hx.le.trans hab⟩, hy⟩
  · simp only [mem_singleton_iff] at hy
    exact ⟨hx, ⟨hy.ge, hy.le.trans hcd⟩⟩

private lemma isClosed_rect (a b c d : ℝ) : IsClosed (rect a b c d) :=
  isClosed_Icc.prod isClosed_Icc

private lemma isClosed_lside (a b c d : ℝ) : IsClosed (lside a b c d) :=
  (isClosed_singleton.prod isClosed_Icc).union (isClosed_Icc.prod isClosed_singleton)

variable (p) in
/-- Every lift of `H` given on the two sides `lside a b c d` extends to the rectangle. -/
private def ExtendsOn (H : ℝ × ℝ → B) (a b c d : ℝ) : Prop :=
  ∀ g : ℝ × ℝ → E, ContinuousOn g (lside a b c d) → (∀ z ∈ lside a b c d, p (g z) = H z) →
    ∃ G : ℝ × ℝ → E, ContinuousOn G (rect a b c d) ∧ (∀ z ∈ rect a b c d, p (G z) = H z) ∧
      ∀ z ∈ lside a b c d, G z = g z

/-- The retraction of `[a, b] × [c, d]` onto its two sides `{a} × [c, d] ∪ [a, b] × {c}`. -/
private def retr (a c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (z.1 - min (z.1 - a) (z.2 - c), z.2 - min (z.1 - a) (z.2 - c))

private lemma continuous_retr (a c : ℝ) : Continuous (retr a c) := by
  unfold retr
  fun_prop

private lemma retr_mem {a b c d : ℝ} {z : ℝ × ℝ} (hz : z ∈ rect a b c d) :
    retr a c z ∈ lside a b c d := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  rcases le_total (z.1 - a) (z.2 - c) with h | h
  · left
    simp only [retr, min_eq_left h]
    exact ⟨by simp, by constructor <;> linarith⟩
  · right
    simp only [retr, min_eq_right h]
    exact ⟨by constructor <;> linarith, by simp⟩

private lemma retr_eq {a b c d : ℝ} {z : ℝ × ℝ} (hz : z ∈ lside a b c d) : retr a c z = z := by
  have hm : min (z.1 - a) (z.2 - c) = 0 := by
    rcases hz with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [mem_singleton_iff.mp hx, sub_self]
      exact min_eq_left (by linarith [hy.1])
    · rw [mem_singleton_iff.mp hy, sub_self]
      exact min_eq_right (by linarith [hx.1])
  simp [retr, hm]

/-- **Lifting over a small rectangle**: if `H` maps `[a, b] × [c, d]` into the base of a
trivialization, every lift on the two sides extends (keep the fibre coordinate along the
retraction onto the two sides). -/
private lemma extendsOn_of_subset {H : ℝ × ℝ → B} (hH : Continuous H) (e : Trivialization F p)
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (he : ∀ z ∈ rect a b c d, H z ∈ e.baseSet) :
    ExtendsOn p H a b c d := by
  intro g hg hpg
  have hrs : ∀ z ∈ rect a b c d, g (retr a c z) ∈ e.source := fun z hz ↦ by
    rw [e.mem_source, hpg _ (retr_mem hz)]
    exact he _ (lside_subset_rect hab hcd (retr_mem hz))
  refine ⟨fun z ↦ e.toOpenPartialHomeomorph.symm (H z, (e (g (retr a c z))).2), ?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun z ↦ g (retr a c z)) (rect a b c d) :=
      hg.comp (continuous_retr a c).continuousOn fun z hz ↦ retr_mem hz
    have h2 : ContinuousOn (fun z ↦ (e (g (retr a c z))).2) (rect a b c d) :=
      continuous_snd.comp_continuousOn (e.toOpenPartialHomeomorph.continuousOn.comp h1 hrs)
    refine e.toOpenPartialHomeomorph.continuousOn_symm.comp (hH.continuousOn.prodMk h2)
      fun z hz ↦ ?_
    rw [e.mem_target]
    exact he z hz
  · intro z hz
    exact e.proj_symm_apply' (he z hz)
  · intro z hz
    have hz' := lside_subset_rect hab hcd hz
    simp only [retr_eq hz]
    rw [← hpg z hz]
    exact e.symm_apply_mk_proj (by rw [e.mem_source, hpg z hz]; exact he z hz')

omit [TopologicalSpace F] [TopologicalSpace B] in
/-- Extending over two rectangles side by side. -/
private lemma ExtendsOn.horizontal {H : ℝ × ℝ → B} {a m b c d : ℝ} (ham : a ≤ m) (hmb : m ≤ b)
    (h₁ : ExtendsOn p H a m c d) (h₂ : ExtendsOn p H m b c d) :
    ExtendsOn p H a b c d := by
  classical
  intro g hg hpg
  have hL₁ : lside a m c d ⊆ lside a b c d := by
    rintro z (h | ⟨hx, hy⟩)
    · exact Or.inl h
    · exact Or.inr ⟨⟨hx.1, hx.2.trans hmb⟩, hy⟩
  obtain ⟨G₁, hG₁c, hG₁p, hG₁g⟩ := h₁ g (hg.mono hL₁) fun z hz ↦ hpg z (hL₁ hz)
  -- the data on the two sides of the right half
  set g₂ : ℝ × ℝ → E := fun z ↦ if z.1 ≤ m then G₁ z else g z
  have hg₂l (z : ℝ × ℝ) (hz : z ∈ lside m b c d) : g₂ z = if z.1 ≤ m then G₁ z else g z := rfl
  have hg₂bot (z : ℝ × ℝ) (hz : z ∈ Icc m b ×ˢ {c}) : g₂ z = g z := by
    simp only [g₂]
    split_ifs with h
    · have hz1 : z.1 = m := le_antisymm h hz.1.1
      exact hG₁g z (Or.inr ⟨⟨by rw [hz1]; exact ham, h⟩, hz.2⟩)
    · rfl
  have hg₂left (z : ℝ × ℝ) (hz : z ∈ ({m} : Set ℝ) ×ˢ Icc c d) : g₂ z = G₁ z := by
    simp only [g₂, mem_singleton_iff.mp hz.1, le_refl, ite_true]
  have hrect₁ : ({m} : Set ℝ) ×ˢ Icc c d ⊆ rect a m c d := fun z hz ↦
    ⟨⟨by rw [mem_singleton_iff.mp hz.1]; exact ham, by rw [mem_singleton_iff.mp hz.1]⟩, hz.2⟩
  have hbot : Icc m b ×ˢ ({c} : Set ℝ) ⊆ lside a b c d := fun z hz ↦
    Or.inr ⟨⟨ham.trans hz.1.1, hz.1.2⟩, hz.2⟩
  have hg₂c : ContinuousOn g₂ (lside m b c d) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_singleton.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_singleton)
    · exact (hG₁c.mono hrect₁).congr fun z hz ↦ hg₂left z hz
    · exact (hg.mono hbot).congr fun z hz ↦ hg₂bot z hz
  have hg₂p (z : ℝ × ℝ) (hz : z ∈ lside m b c d) : p (g₂ z) = H z := by
    rcases hz with hz | hz
    · rw [hg₂left z hz]
      exact hG₁p z (hrect₁ hz)
    · rw [hg₂bot z hz]
      exact hpg z (hbot hz)
  obtain ⟨G₂, hG₂c, hG₂p, hG₂g⟩ := h₂ g₂ hg₂c hg₂p
  refine ⟨fun z ↦ if z.1 ≤ m then G₁ z else G₂ z, ?_, ?_, ?_⟩
  · have hsplit : rect a b c d = rect a m c d ∪ rect m b c d := by
      ext ⟨x, y⟩
      simp only [rect, mem_prod, mem_Icc, mem_union]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        rcases le_total x m with h | h
        · exact Or.inl ⟨⟨h1, h⟩, h3⟩
        · exact Or.inr ⟨⟨h, h2⟩, h3⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨h1, h2⟩, h3⟩)
        · exact ⟨⟨h1, h2.trans hmb⟩, h3⟩
        · exact ⟨⟨ham.trans h1, h2⟩, h3⟩
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_rect _ _ _ _) (isClosed_rect _ _ _ _)
    · exact hG₁c.congr fun z hz ↦ by simp only [hz.1.2, ite_true]
    · refine hG₂c.congr fun z hz ↦ ?_
      split_ifs with h
      · have hz1 : z.1 = m := le_antisymm h hz.1.1
        rw [← hg₂left z ⟨by rw [hz1]; rfl, hz.2⟩]
        exact (hG₂g z (Or.inl ⟨by rw [hz1]; rfl, hz.2⟩)).symm
      · rfl
  · intro z hz
    dsimp only
    split_ifs with h
    · exact hG₁p z ⟨⟨hz.1.1, h⟩, hz.2⟩
    · exact hG₂p z ⟨⟨(not_le.mp h).le, hz.1.2⟩, hz.2⟩
  · intro z hz
    dsimp only
    split_ifs with h
    · exact hG₁g z (by
        rcases hz with hz | hz
        · exact Or.inl hz
        · exact Or.inr ⟨⟨hz.1.1, h⟩, hz.2⟩)
    · have hzb : z ∈ Icc m b ×ˢ ({c} : Set ℝ) := by
        rcases hz with hz | hz
        · rw [mem_singleton_iff.mp hz.1] at h
          exact absurd ham h
        · exact ⟨⟨(not_le.mp h).le, hz.1.2⟩, hz.2⟩
      rw [hG₂g z (Or.inr hzb), hg₂bot z hzb]

omit [TopologicalSpace F] [TopologicalSpace B] in
/-- Extending over two rectangles one above the other. -/
private lemma ExtendsOn.vertical {H : ℝ × ℝ → B} {a b c m d : ℝ} (hcm : c ≤ m) (hmd : m ≤ d)
    (h₁ : ExtendsOn p H a b c m) (h₂ : ExtendsOn p H a b m d) :
    ExtendsOn p H a b c d := by
  classical
  intro g hg hpg
  have hL₁ : lside a b c m ⊆ lside a b c d := by
    rintro z (⟨hx, hy⟩ | h)
    · exact Or.inl ⟨hx, ⟨hy.1, hy.2.trans hmd⟩⟩
    · exact Or.inr h
  obtain ⟨G₁, hG₁c, hG₁p, hG₁g⟩ := h₁ g (hg.mono hL₁) fun z hz ↦ hpg z (hL₁ hz)
  set g₂ : ℝ × ℝ → E := fun z ↦ if z.2 ≤ m then G₁ z else g z
  have hg₂left (z : ℝ × ℝ) (hz : z ∈ ({a} : Set ℝ) ×ˢ Icc m d) : g₂ z = g z := by
    simp only [g₂]
    split_ifs with h
    · have hz2 : z.2 = m := le_antisymm h hz.2.1
      exact hG₁g z (Or.inl ⟨hz.1, ⟨by rw [hz2]; exact hcm, h⟩⟩)
    · rfl
  have hg₂bot (z : ℝ × ℝ) (hz : z ∈ Icc a b ×ˢ ({m} : Set ℝ)) : g₂ z = G₁ z := by
    simp only [g₂, mem_singleton_iff.mp hz.2, le_refl, ite_true]
  have hrect₁ : Icc a b ×ˢ ({m} : Set ℝ) ⊆ rect a b c m := fun z hz ↦
    ⟨hz.1, ⟨by rw [mem_singleton_iff.mp hz.2]; exact hcm, by rw [mem_singleton_iff.mp hz.2]⟩⟩
  have hleft : ({a} : Set ℝ) ×ˢ Icc m d ⊆ lside a b c d := fun z hz ↦
    Or.inl ⟨hz.1, ⟨hcm.trans hz.2.1, hz.2.2⟩⟩
  have hg₂c : ContinuousOn g₂ (lside a b m d) := by
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_singleton.prod isClosed_Icc)
      (isClosed_Icc.prod isClosed_singleton)
    · exact (hg.mono hleft).congr fun z hz ↦ hg₂left z hz
    · exact (hG₁c.mono hrect₁).congr fun z hz ↦ hg₂bot z hz
  have hg₂p (z : ℝ × ℝ) (hz : z ∈ lside a b m d) : p (g₂ z) = H z := by
    rcases hz with hz | hz
    · rw [hg₂left z hz]
      exact hpg z (hleft hz)
    · rw [hg₂bot z hz]
      exact hG₁p z (hrect₁ hz)
  obtain ⟨G₂, hG₂c, hG₂p, hG₂g⟩ := h₂ g₂ hg₂c hg₂p
  refine ⟨fun z ↦ if z.2 ≤ m then G₁ z else G₂ z, ?_, ?_, ?_⟩
  · have hsplit : rect a b c d = rect a b c m ∪ rect a b m d := by
      ext ⟨x, y⟩
      simp only [rect, mem_prod, mem_Icc, mem_union]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases le_total y m with h | h
        · exact Or.inl ⟨h1, h2, h⟩
        · exact Or.inr ⟨h1, h, h3⟩
      · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
        · exact ⟨h1, h2, h3.trans hmd⟩
        · exact ⟨h1, hcm.trans h2, h3⟩
    rw [hsplit]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (isClosed_rect _ _ _ _) (isClosed_rect _ _ _ _)
    · exact hG₁c.congr fun z hz ↦ by simp only [hz.2.2, ite_true]
    · refine hG₂c.congr fun z hz ↦ ?_
      split_ifs with h
      · have hz2 : z.2 = m := le_antisymm h hz.2.1
        rw [← hg₂bot z ⟨hz.1, by rw [hz2]; rfl⟩]
        exact (hG₂g z (Or.inr ⟨hz.1, by rw [hz2]; rfl⟩)).symm
      · rfl
  · intro z hz
    dsimp only
    split_ifs with h
    · exact hG₁p z ⟨hz.1, ⟨hz.2.1, h⟩⟩
    · exact hG₂p z ⟨hz.1, ⟨(not_le.mp h).le, hz.2.2⟩⟩
  · intro z hz
    dsimp only
    split_ifs with h
    · exact hG₁g z (by
        rcases hz with hz | hz
        · exact Or.inl ⟨hz.1, ⟨hz.2.1, h⟩⟩
        · exact Or.inr hz)
    · have hzl : z ∈ ({a} : Set ℝ) ×ˢ Icc m d := by
        rcases hz with hz | hz
        · exact ⟨hz.1, ⟨(not_le.mp h).le, hz.2.2⟩⟩
        · rw [mem_singleton_iff.mp hz.2] at h
          exact absurd hcm h
      rw [hG₂g z (Or.inl hzl), hg₂left z hzl]

/-- **Lifting over the unit square of `ℝ²`**, for `p` locally trivial: by induction on the size of
the rectangles, starting from a Lebesgue number of the cover of `[0, 1]²` by the preimages of the
bases of trivializations. -/
private lemma extendsOn_unit (htriv : ∀ b : B, ∃ e : Trivialization F p, b ∈ e.baseSet)
    {H : ℝ × ℝ → B} (hH : Continuous H) : ExtendsOn p H 0 1 0 1 := by
  choose e he using htriv
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_Icc.prod isCompact_Icc : IsCompact (rect 0 1 0 1))
    (c := fun b ↦ H ⁻¹' (e b).baseSet) (fun b ↦ (e b).open_baseSet.preimage hH)
    (fun z _ ↦ mem_iUnion.mpr ⟨H z, he (H z)⟩)
  have hsmall : ∀ a b c d : ℝ, 0 ≤ a → a ≤ b → b ≤ a + δ / 2 → b ≤ 1 → 0 ≤ c → c ≤ d →
      d ≤ c + δ / 2 → d ≤ 1 → ExtendsOn p H a b c d := by
    intro a b c d ha hab hb hb1 hc hcd hd hd1
    obtain ⟨i, hi⟩ := hball (a, c) ⟨⟨ha, hab.trans hb1⟩, ⟨hc, hcd.trans hd1⟩⟩
    refine extendsOn_of_subset hH (e i) hab hcd fun z hz ↦ hi ?_
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq, abs_lt, abs_lt]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  have hind : ∀ k : ℕ, ∀ a b c d : ℝ, 0 ≤ a → a ≤ b → b ≤ a + δ / 2 * 2 ^ k → b ≤ 1 → 0 ≤ c →
      c ≤ d → d ≤ c + δ / 2 * 2 ^ k → d ≤ 1 → ExtendsOn p H a b c d := by
    intro k
    induction k with
    | zero => simpa using hsmall
    | succ k ih =>
      intro a b c d ha hab hb hb1 hc hcd hd hd1
      have h2k : δ / 2 * 2 ^ (k + 1) = 2 * (δ / 2 * 2 ^ k) := by ring
      rw [h2k] at hb hd
      refine ExtendsOn.horizontal (m := (a + b) / 2) (by linarith) (by linarith) ?_ ?_
      · refine ExtendsOn.vertical (m := (c + d) / 2) (by linarith) (by linarith) ?_ ?_
        · exact ih _ _ _ _ ha (by linarith) (by linarith) (by linarith) hc (by linarith)
            (by linarith) (by linarith)
        · exact ih _ _ _ _ ha (by linarith) (by linarith) (by linarith) (by linarith)
            (by linarith) (by linarith) hd1
      · refine ExtendsOn.vertical (m := (c + d) / 2) (by linarith) (by linarith) ?_ ?_
        · exact ih _ _ _ _ (by linarith) (by linarith) (by linarith) hb1 hc (by linarith)
            (by linarith) (by linarith)
        · exact ih _ _ _ _ (by linarith) (by linarith) (by linarith) hb1 (by linarith)
            (by linarith) (by linarith) hd1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (2 / δ) one_lt_two
  have hk' : 1 ≤ δ / 2 * 2 ^ k := by
    rw [div_lt_iff₀ hδ] at hk
    nlinarith
  exact hind k 0 1 0 1 le_rfl zero_le_one (by linarith) le_rfl le_rfl zero_le_one (by linarith)
    le_rfl

end Rectangle

/-- The two sides `{0} × I ∪ I × {0}` of the unit square. -/
def squareSides : Set (I × I) := {z | z.1 = 0 ∨ z.2 = 0}

/-- **Homotopy lifting for the square, relative to two sides**: for `p` locally trivial (every
point of `B` lies in the base of a trivialization), every map `H : I × I → B` lifts to `E`,
extending a given continuous lift on the two sides `{0} × I ∪ I × {0}`. -/
theorem exists_lift_square (htriv : ∀ b : B, ∃ e : Trivialization F p, b ∈ e.baseSet)
    (H : C(I × I, B)) (g : I × I → E) (hg : ContinuousOn g squareSides)
    (hpg : ∀ z ∈ squareSides, p (g z) = H z) :
    ∃ G : C(I × I, E), (∀ z, p (G z) = H z) ∧ ∀ z ∈ squareSides, G z = g z := by
  let pr : ℝ × ℝ → I × I := fun z ↦ (projIcc 0 1 zero_le_one z.1, projIcc 0 1 zero_le_one z.2)
  have hpr : Continuous pr := by fun_prop
  have hprL : MapsTo pr (lside 0 1 0 1) squareSides := by
    rintro z (⟨hx, _⟩ | ⟨_, hy⟩)
    · left
      simp [pr, mem_singleton_iff.mp hx]
    · right
      simp [pr, mem_singleton_iff.mp hy]
  obtain ⟨G', hG'c, hG'p, hG'g⟩ := extendsOn_unit htriv (hH := H.continuous.comp hpr)
    (g ∘ pr) (hg.comp hpr.continuousOn hprL) fun z hz ↦ hpg _ (hprL hz)
  let ι : I × I → ℝ × ℝ := fun z ↦ ((z.1 : ℝ), (z.2 : ℝ))
  have hι : Continuous ι := by fun_prop
  have hιR (z : I × I) : ι z ∈ rect 0 1 0 1 := ⟨z.1.2, z.2.2⟩
  have hprι (z : I × I) : pr (ι z) = z := by
    simp only [pr, ι, projIcc_val]
  refine ⟨⟨G' ∘ ι, hG'c.comp_continuous hι hιR⟩, fun z ↦ ?_, fun z hz ↦ ?_⟩
  · change p (G' (ι z)) = H z
    rw [hG'p _ (hιR z)]
    exact congrArg H (hprι z)
  · change G' (ι z) = g z
    have hzL : ι z ∈ lside 0 1 0 1 := by
      rcases hz with h | h
      · exact Or.inl ⟨by simp [ι, h], z.2.2⟩
      · exact Or.inr ⟨z.1.2, by simp [ι, h]⟩
    rw [hG'g _ hzL]
    exact congrArg g (hprι z)

/-- A locally trivial map is continuous. -/
theorem continuous_of_locallyTrivial
    (htriv : ∀ b : B, ∃ e : Trivialization F p, b ∈ e.baseSet) : Continuous p := by
  refine continuous_iff_continuousAt.mpr fun x ↦ ?_
  obtain ⟨e, he⟩ := htriv (p x)
  exact e.continuousAt_proj (e.mem_source.mpr he)

/-- **Path lifting** for locally trivial maps. -/
theorem exists_path_lift (htriv : ∀ b : B, ∃ e : Trivialization F p, b ∈ e.baseSet) {b₀ b₁ : B}
    (γ : Path b₀ b₁) {e₀ : E} (he₀ : p e₀ = b₀) :
    ∃ (e₁ : E) (Γ : Path e₀ e₁), ∀ t, p (Γ t) = γ t := by
  let H : C(I × I, B) := ⟨fun z ↦ γ (min z.1 z.2), by fun_prop⟩
  obtain ⟨G, hGp, hGg⟩ := exists_lift_square htriv H (fun _ ↦ e₀) continuousOn_const
    fun z hz ↦ by
      rcases hz with h | h
      · simp [H, h, he₀]
      · simp [H, h, he₀]
  refine ⟨G (1, 1), ⟨⟨fun t ↦ G (1, t), by fun_prop⟩, hGg _ (Or.inr rfl), rfl⟩, fun t ↦ ?_⟩
  change p (G (1, t)) = γ t
  rw [hGp]
  change γ (min 1 t) = γ t
  rw [min_eq_right (show t ≤ (1 : I) from Subtype.coe_le_coe.mp t.2.2)]

/-- **The square lemma**: for `G : I × I → E`, going up the left side and along the top is
homotopic to going along the bottom and up the right side. -/
theorem _root_.ContinuousMap.homotopic_sides_square {X : Type*} [TopologicalSpace X]
    (G : C(I × I, X)) :
    ((⟨⟨fun t ↦ G (0, t), by fun_prop⟩, rfl, rfl⟩ : Path (G (0, 0)) (G (0, 1))).trans
      (⟨⟨fun s ↦ G (s, 1), by fun_prop⟩, rfl, rfl⟩ : Path (G (0, 1)) (G (1, 1)))).Homotopic
    ((⟨⟨fun s ↦ G (s, 0), by fun_prop⟩, rfl, rfl⟩ : Path (G (0, 0)) (G (1, 0))).trans
      (⟨⟨fun t ↦ G (1, t), by fun_prop⟩, rfl, rfl⟩ : Path (G (1, 0)) (G (1, 1)))) := by
  let f : C(I, X) := ⟨fun t ↦ G (0, t), by fun_prop⟩
  let g : C(I, X) := ⟨fun t ↦ G (1, t), by fun_prop⟩
  let F : f.Homotopy g :=
    { toContinuousMap := G
      map_zero_left := fun _ ↦ rfl
      map_one_left := fun _ ↦ rfl }
  exact Path.Homotopic.map_trans_evalAt F Path.id

section ExactSequence

open FundamentalGroupoid CategoryTheory

variable (htriv : ∀ b : B, ∃ e : Trivialization F p, b ∈ e.baseSet)

include htriv in
/-- **Exactness of `π₁(p⁻¹(b₀)) → π₁(E) → π₁(B)` at `π₁(E)`** for a locally trivial `p`: a loop in
`E` whose image in `B` is null-homotopic is homotopic to a loop in the fibre. -/
theorem range_fundamentalGroup_map_fibre_eq_ker (e₀ : E) :
    (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩
        (⟨e₀, rfl⟩ : p ⁻¹' {p e₀})).range =
      (FundamentalGroup.map ⟨p, continuous_of_locallyTrivial htriv⟩ e₀).ker := by
  ext x
  constructor
  · rintro ⟨τ, rfl⟩
    induction τ using Path.Homotopic.Quotient.ind with | mk γ => ?_
    rw [MonoidHom.mem_ker]
    change Path.Homotopic.Quotient.mk ((γ.map continuous_subtype_val).map _) =
      Path.Homotopic.Quotient.mk (Path.refl (p e₀))
    congr 1
    exact Path.ext (funext fun t ↦ (γ t).2)
  · intro hσ
    induction x using Path.Homotopic.Quotient.ind with | mk γ => ?_
    rw [MonoidHom.mem_ker] at hσ
    have hhom : (γ.map (continuous_of_locallyTrivial htriv)).Homotopic (Path.refl (p e₀)) :=
      Path.Homotopic.Quotient.eq.mp hσ
    obtain ⟨Fh⟩ := hhom
    classical
    -- lift the null-homotopy, starting from `γ` on the left and `e₀` at the bottom
    let g : I × I → E := fun z ↦ if z.1 = 0 then γ z.2 else e₀
    have hg0 (z : I × I) (h : z.1 = 0) : g z = γ z.2 := by simp only [g, h, ↓reduceIte]
    have hgb (z : I × I) (h : z.2 = 0) : g z = e₀ := by
      by_cases h' : z.1 = 0
      · rw [hg0 z h', h, γ.source]
        rfl
      · simp only [g, h', ↓reduceIte]
    have hsides : squareSides = {z : I × I | z.1 = 0} ∪ {z | z.2 = 0} := rfl
    have hgc : ContinuousOn g squareSides := by
      rw [hsides]
      refine ContinuousOn.union_of_isClosed ?_ ?_
        (isClosed_eq continuous_fst continuous_const) (isClosed_eq continuous_snd continuous_const)
      · exact (γ.continuous.comp continuous_snd).continuousOn.congr fun z hz ↦ hg0 z hz
      · exact continuousOn_const.congr fun z hz ↦ hgb z hz
    have hpg : ∀ z ∈ squareSides, p (g z) = Fh.toContinuousMap z := by
      rintro z (h | h)
      · rw [hg0 z h]
        have := Fh.apply_zero z.2
        rw [show z = (0, z.2) from Prod.ext h rfl]
        exact this.symm
      · rw [hgb z h]
        have := Fh.source z.1
        rw [show z = (z.1, 0) from Prod.ext rfl h]
        exact this.symm
    obtain ⟨G, hGp, hGg⟩ := exists_lift_square htriv Fh.toContinuousMap g hgc hpg
    have hG0 (t : I) : G (0, t) = γ t := (hGg _ (Or.inl rfl)).trans (hg0 _ rfl)
    have hGb (s : I) : G (s, 0) = e₀ := (hGg _ (Or.inr rfl)).trans (hgb _ rfl)
    have hfib1 (t : I) : p (G (1, t)) = p e₀ := (hGp _).trans (Fh.apply_one t)
    have hfib2 (s : I) : p (G (s, 1)) = p e₀ := by
      rw [hGp]
      have := Fh.target s
      exact this
    -- the square
    have hsq := G.homotopic_sides_square
    let right : Path e₀ (G (1, 1)) := ⟨⟨fun t ↦ G (1, t), by fun_prop⟩, hGb 1, rfl⟩
    let top : Path e₀ (G (1, 1)) := ⟨⟨fun s ↦ G (s, 1), by fun_prop⟩, (hG0 1).trans γ.target, rfl⟩
    have hsq' : (γ.trans top).Homotopic ((Path.refl e₀).trans right) := by
      have e₁ : γ.trans top = (((⟨⟨fun t ↦ G (0, t), by fun_prop⟩, rfl, rfl⟩ :
          Path (G (0, 0)) (G (0, 1))).trans
          (⟨⟨fun s ↦ G (s, 1), by fun_prop⟩, rfl, rfl⟩ : Path (G (0, 1)) (G (1, 1)))).cast
          ((hG0 0).trans γ.source).symm rfl) :=
        Path.ext (funext fun t ↦ by
          simp only [Path.cast_coe]
          rw [Path.trans_apply, Path.trans_apply]
          split_ifs
          · exact (hG0 _).symm
          · rfl)
      have e₂ : (Path.refl e₀).trans right = (((⟨⟨fun s ↦ G (s, 0), by fun_prop⟩, rfl, rfl⟩ :
          Path (G (0, 0)) (G (1, 0))).trans
          (⟨⟨fun t ↦ G (1, t), by fun_prop⟩, rfl, rfl⟩ : Path (G (1, 0)) (G (1, 1)))).cast
          ((hG0 0).trans γ.source).symm rfl) :=
        Path.ext (funext fun t ↦ by
          simp only [Path.cast_coe]
          rw [Path.trans_apply, Path.trans_apply]
          split_ifs
          · exact (hGb _).symm
          · rfl)
      rw [e₁, e₂, ← Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk_cast,
        Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.eq.mpr hsq]
    -- the loop `right · top⁻¹` lies in the fibre
    have hrange : range (right.trans top.symm) ⊆ p ⁻¹' {p e₀} := by
      rintro _ ⟨t, rfl⟩
      rw [Path.trans_apply]
      split_ifs
      · exact hfib1 _
      · exact hfib2 _
    refine ⟨Path.Homotopic.Quotient.mk ((right.trans top.symm).codRestrict hrange), ?_⟩
    change Path.Homotopic.Quotient.mk (right.trans top.symm) = Path.Homotopic.Quotient.mk γ
    have h3 : fromPath (Path.Homotopic.Quotient.mk γ) ≫ fromPath (Path.Homotopic.Quotient.mk top) =
        fromPath (Path.Homotopic.Quotient.mk right) := by
      rw [← fromPath_mk_trans, Path.Homotopic.Quotient.eq.mpr hsq', fromPath_mk_trans]
      exact Category.id_comp _
    change fromPath (Path.Homotopic.Quotient.mk (right.trans top.symm)) =
      fromPath (Path.Homotopic.Quotient.mk γ)
    rw [fromPath_mk_trans, fromPath_mk_symm, ← h3, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]

include htriv in
/-- **`π₁(E) → π₁(B)` is surjective** for a locally trivial `p` whose fibre over `p e₀` is
path-connected: lift a loop and close the lift up inside the fibre. -/
theorem fundamentalGroup_map_surjective (e₀ : E) (hF : IsPathConnected (p ⁻¹' {p e₀})) :
    Function.Surjective
      (FundamentalGroup.map ⟨p, continuous_of_locallyTrivial htriv⟩ e₀) := by
  intro β
  induction β using Path.Homotopic.Quotient.ind with | mk β => ?_
  obtain ⟨e₁, Γ, hΓ⟩ := exists_path_lift htriv β rfl
  have he₁ : e₁ ∈ p ⁻¹' {p e₀} := by
    change p e₁ = p e₀
    rw [← Γ.target, hΓ, β.target]
    rfl
  have hjoin := hF.joinedIn e₁ he₁ e₀ rfl
  let δ := hjoin.somePath
  refine ⟨Path.Homotopic.Quotient.mk (Γ.trans δ), ?_⟩
  change Path.Homotopic.Quotient.mk ((Γ.trans δ).map _) = Path.Homotopic.Quotient.mk β
  have e : (Γ.trans δ).map (continuous_of_locallyTrivial htriv) = β.trans (Path.refl _) :=
    Path.ext (funext fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, Path.trans_apply, Path.trans_apply]
      split_ifs
      · exact hΓ _
      · exact hjoin.somePath_mem _)
  rw [e]
  change fromPath (Path.Homotopic.Quotient.mk _) = fromPath (Path.Homotopic.Quotient.mk β)
  rw [fromPath_mk_trans, fromPath_mk_refl, Category.comp_id]

end ExactSequence

end Bundle
