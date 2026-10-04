/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.RungeRect
import SGA.Foundations.Analytic.RungeLaurent
import SGA.Foundations.Analytic.DolbeaultGlobal

/-!
# Runge approximation on products of discs, annuli and rectangles

Let `Kᵢ = A(rᵢ, Rᵢ) ⊆ Lᵢ = A(r'ᵢ, R'ᵢ)` be closed annuli in `ℂ` centred at `0` (closed discs when
the inner radius is `≤ 0`), with `R'ᵢ > Rᵢ` and either `r'ᵢ = 0` or `0 < r'ᵢ < rᵢ`, and let
`Kᵢ ⊆ Ωᵢ ⊆ ℂ`, with `0 ∉ Ωᵢ` whenever `r'ᵢ > 0`. Every function analytic at every point of
`∏ Lᵢ` is, uniformly on `∏ Kᵢ`, a limit of functions analytic on `∏ Ωᵢ`
(`AnalyticGeometry.RungeData.exists_approx`). The approximants are built one coordinate at a
time from truncated Laurent expansions (`AnalyticGeometry.norm_sub_laurentTrunc_le_of_mem`),
whose coefficients are circle integrals with holomorphic parameters
(`AnalyticGeometry.analyticAt_circleIntegral_param`).

Consequently, for a product `Ω = ∏ Ωᵢ` of discs `|z| < ρ`, planes `ℂ`, punctured planes `ℂ*`
and open rectangles (`AnalyticGeometry.FactorKind`), the standard exhaustion of `Ω` by products
of closed discs, annuli and rectangles (`AnalyticGeometry.FactorKind.exhaustion`) has the Runge
property (`AnalyticGeometry.FactorKind.isRunge_exhaustion`; for the rectangle factors the
one-variable schemes are the rectangle schemes `AnalyticGeometry.rectScheme` of
`SGA.Foundations.Analytic.RungeRect`), and **Theorem B for `𝒪`** holds on `Ω`:
`Hⁿ(Ω, 𝒪) = 0` for `n > 0` (`AnalyticGeometry.H'_holomorphicAbSheaf_pi_subsingleton`).

References: Hörmander, *An introduction to complex analysis in several variables*, proof of
Theorem 2.3.3 (Runge approximation by Taylor expansion on polydiscs) and 2.7 (Runge domains);
Gunning–Rossi, *Analytic functions of several complex variables*, I.D.
-/

noncomputable section

open Complex Set Metric Filter Topology
open scoped Real

namespace AnalyticGeometry

/-! ### The Laurent scheme on an annulus -/

/-- The approximating functions of the Laurent scheme: `wᵏ` for `k < N`, and `w^{-(k - N + 1)}`
for `k ≥ N` if the inner radius `r'` is positive (`0` otherwise). -/
def laurentScheme.ψ (r' : ℝ) (N k : ℕ) (w : ℂ) : ℂ :=
  if k < N then w ^ k else if 0 < r' then w⁻¹ ^ (k - N + 1) else 0

/-- The coefficient functionals of the Laurent scheme. -/
def laurentScheme.coeff (r' R' : ℝ) (N k : ℕ) (g : ℂ → ℂ) : ℂ :=
  if k < N then laurentCoeffPos g R' k else laurentCoeffNeg g r' (k - N)

/-- **The Laurent scheme** on the closed annulus `A(r, R)` (closed disc if `r ≤ 0`) for functions
holomorphic on `A(r', R')`, with approximants (Laurent polynomials, polynomials if `r' = 0`)
holomorphic on `Ω`: here `0 ≤ R < R'`, `r ≤ R`, `0 ≤ r'`, either `r' = 0` or `r' < r`, and
`0 ∉ Ω` if `r' > 0`. -/
def laurentScheme {r R r' R' : ℝ} (Ω : Set ℂ) (hR : 0 ≤ R) (hrR : r ≤ R) (hRR : R < R')
    (hr' : 0 ≤ r') (hrr : r' = 0 ∨ r' < r) (hΩ : 0 < r' → (0 : ℂ) ∉ Ω) :
    ApproxScheme (closedAnnulus r R) (closedAnnulus r' R') Ω where
  Γ := sphere 0 R' ∪ sphere 0 r'
  isCompact_Γ := (isCompact_sphere _ _).union (isCompact_sphere _ _)
  Γ_subset := by
    have hr'R' : r' ≤ R' := by
      rcases hrr with h | h
      · rw [h]
        exact hR.trans hRR.le
      · linarith
    exact union_subset (sphere_subset_closedAnnulus_outer hr'R')
      (sphere_subset_closedAnnulus_inner hr'R')
  card N := if 0 < r' then N + N else N
  ψ := laurentScheme.ψ r'
  analyticAt_ψ N k w hw := by
    unfold laurentScheme.ψ
    by_cases hk : k < N
    · simp only [hk, ↓reduceIte]
      exact analyticAt_id.pow k
    · by_cases hr : 0 < r'
      · simp only [hk, hr, ↓reduceIte]
        have hw0 : w ≠ 0 := fun h ↦ hΩ hr (h ▸ hw)
        exact (analyticAt_id.inv hw0).pow _
      · simp only [hk, hr, ↓reduceIte]
        exact analyticAt_const
  coeff := laurentScheme.coeff r' R'
  analyticAt_coeff {σ} _ _ N k j h z hh := by
    have hRpos : 0 < R' := hR.trans_lt hRR
    unfold laurentScheme.coeff
    by_cases hk : k < N
    · simp only [hk, ↓reduceIte, laurentCoeffPos]
      refine analyticAt_const.mul (analyticAt_circleIntegral_param fun ζ hζ ↦ ?_)
      rw [abs_of_pos hRpos] at hζ
      have hζ0 : ζ ≠ 0 := by
        rintro rfl
        rw [mem_sphere_zero_iff_norm, norm_zero] at hζ
        exact hRpos.ne hζ
      exact ((analyticAt_snd.inv hζ0).pow _).mul
        (AnalyticAt.comp (g := h) (f := fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2)
          (hh ζ (Or.inl hζ)) (analyticAt_update_prod j (z, ζ)))
    · simp only [hk, ↓reduceIte, laurentCoeffNeg]
      refine analyticAt_const.mul (analyticAt_circleIntegral_param fun ζ hζ ↦ ?_)
      rw [abs_of_nonneg hr'] at hζ
      exact (analyticAt_snd.pow _).mul
        (AnalyticAt.comp (g := h) (f := fun p : (σ → ℂ) × ℂ ↦ Function.update p.1 j p.2)
          (hh ζ (Or.inr hζ)) (analyticAt_update_prod j (z, ζ)))
  err N := R' * (R' - R)⁻¹ * (R / R') ^ N + r' * (r - r')⁻¹ * (r' / r) ^ N
  tendsto_err := tendsto_laurentTrunc_err hr' hR hRR hrr
  approx N g M hg hM w hw := by
    have htrunc : ∑ k ∈ Finset.range (if 0 < r' then N + N else N),
        laurentScheme.coeff r' R' N k g * laurentScheme.ψ r' N k w = laurentTrunc g r' R' N w := by
      unfold laurentScheme.coeff laurentScheme.ψ laurentTrunc
      by_cases hr : 0 < r'
      · simp only [hr, ↓reduceIte]
        rw [Finset.sum_range_add]
        congr 1
        · exact Finset.sum_congr rfl fun k hk ↦ by simp [Finset.mem_range.mp hk]
        · exact Finset.sum_congr rfl fun k _ ↦ by simp
      · simp only [hr, ↓reduceIte]
        have hr0 : r' = 0 := le_antisymm (not_lt.mp hr) hr'
        simp only [hr0, laurentCoeffNeg_zero, zero_mul, Finset.sum_const_zero, add_zero]
        exact Finset.sum_congr rfl fun k hk ↦ by simp [Finset.mem_range.mp hk]
    rw [htrunc]
    exact norm_sub_laurentTrunc_le_of_mem hr' hg hM hRR hrr hw N

/-! ### Runge approximation on products of annuli -/

/-- The data of Runge approximation on a product of closed annuli: the approximation set
`∏ Kᵢ`, `Kᵢ = A(rᵢ, Rᵢ)`, the set `∏ Lᵢ`, `Lᵢ = A(r'ᵢ, R'ᵢ)`, near which the functions to be
approximated are holomorphic, and the domains `Ωᵢ ⊇ Kᵢ` on which the approximants are
holomorphic. -/
structure RungeData (σ : Type) where
  /-- The domains of the approximants. -/
  Ω : σ → Set ℂ
  /-- Inner radii of the approximation annuli. -/
  r : σ → ℝ
  /-- Outer radii of the approximation annuli. -/
  R : σ → ℝ
  /-- Inner radii of the annuli of holomorphy. -/
  r' : σ → ℝ
  /-- Outer radii of the annuli of holomorphy. -/
  R' : σ → ℝ
  r'_nonneg : ∀ i, 0 ≤ r' i
  r'_lt : ∀ i, r' i = 0 ∨ r' i < r i
  R_lt : ∀ i, R i < R' i
  K_subset : ∀ i, closedAnnulus (r i) (R i) ⊆ Ω i
  zero_notMem : ∀ i, 0 < r' i → (0 : ℂ) ∉ Ω i

namespace RungeData

variable {σ : Type} (D : RungeData σ)

lemma K_subset_L (i : σ) :
    closedAnnulus (D.r i) (D.R i) ⊆ closedAnnulus (D.r' i) (D.R' i) := fun z hz ↦ by
  refine ⟨?_, hz.2.trans (D.R_lt i).le⟩
  rcases D.r'_lt i with h | h
  · rw [h]
    exact norm_nonneg z
  · exact h.le.trans hz.1

/-- The Laurent scheme of coordinate `i` (trivial if the approximation annulus is empty). -/
def scheme (i : σ) :
    ApproxScheme (closedAnnulus (D.r i) (D.R i)) (closedAnnulus (D.r' i) (D.R' i)) (D.Ω i) :=
  if hR : 0 ≤ D.R i ∧ D.r i ≤ D.R i then
    laurentScheme (D.Ω i) hR.1 hR.2 (D.R_lt i) (D.r'_nonneg i) (D.r'_lt i) (D.zero_notMem i)
  else
    (ApproxScheme.ofEmpty _ _).congrK (closedAnnulus_eq_empty hR)

/-- The product data of the Laurent schemes. -/
def toProductRungeData : ProductRungeData σ where
  K i := closedAnnulus (D.r i) (D.R i)
  L i := closedAnnulus (D.r' i) (D.R' i)
  Ω := D.Ω
  isCompact_K _ := isCompact_closedAnnulus _ _
  K_subset_L := D.K_subset_L
  K_subset_Ω := D.K_subset
  scheme := D.scheme

/-- **Runge approximation on a product of closed annuli**: a function analytic at every point
of `∏ A(r'ᵢ, R'ᵢ)` is, uniformly on `∏ A(rᵢ, Rᵢ)`, a limit of functions analytic on `∏ Ωᵢ`. -/
theorem exists_approx [Fintype σ] {h : (σ → ℂ) → ℂ}
    (hh : ∀ z ∈ univ.pi fun i ↦ closedAnnulus (D.r' i) (D.R' i), AnalyticAt ℂ h z)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : (σ → ℂ) → ℂ, (∀ z ∈ univ.pi D.Ω, AnalyticAt ℂ g z) ∧
      ∀ z ∈ univ.pi fun i ↦ closedAnnulus (D.r i) (D.R i), ‖h z - g z‖ < ε :=
  D.toProductRungeData.exists_approx hh hε

end RungeData

end AnalyticGeometry

/-! ### The standard exhaustions of discs, `ℂ`, `ℂ*` and rectangles -/

namespace AnalyticGeometry

/-- The Laurent scheme between two closed annuli (trivial if the smaller one is empty). -/
def annularScheme {r R r' R' : ℝ} (Ω : Set ℂ) (hRR : R < R') (hr' : 0 ≤ r')
    (hrr : r' = 0 ∨ r' < r) (hΩ : 0 < r' → (0 : ℂ) ∉ Ω) :
    ApproxScheme (closedAnnulus r R) (closedAnnulus r' R') Ω :=
  if h : 0 ≤ R ∧ r ≤ R then laurentScheme Ω h.1 h.2 hRR hr' hrr hΩ
  else (ApproxScheme.ofEmpty _ _).congrK (closedAnnulus_eq_empty h)

lemma closedRect_eq_empty {p q : ℂ} (h : ¬(p.re ≤ q.re ∧ p.im ≤ q.im)) : closedRect p q = ∅ :=
  eq_empty_iff_forall_notMem.mpr fun _ hz ↦ h ⟨hz.1.1.trans hz.1.2, hz.2.1.trans hz.2.2⟩

/-- The rectangle scheme (trivial if the smaller rectangle is empty). -/
def rectSchemeOrEmpty {p q p' q' : ℂ} (Ω : Set ℂ) (h1 : p'.re < p.re) (h2 : q.re < q'.re)
    (h3 : p'.im < p.im) (h4 : q.im < q'.im) :
    ApproxScheme (closedRect p q) (closedRect p' q') Ω :=
  if h : p.re ≤ q.re ∧ p.im ≤ q.im then rectScheme Ω h1 h2 h3 h4 h.1 h.2
  else (ApproxScheme.ofEmpty _ _).congrK (closedRect_eq_empty h)

/-- The four kinds of factors of the product domains for which Theorem B for `𝒪` is proved here:
discs, the plane, the punctured plane, and open rectangles. -/
inductive FactorKind
  /-- The open disc `|z| < ρ` (empty for `ρ ≤ 0`). -/
  | disc (ρ : ℝ)
  /-- The plane `ℂ`. -/
  | plane
  /-- The punctured plane `ℂ* = ℂ \ {0}`. -/
  | punctured
  /-- The open rectangle `p.re < Re z < q.re`, `p.im < Im z < q.im` (possibly empty). -/
  | rect (p q : ℂ)

namespace FactorKind

/-- The domain: `{|z| < ρ}`, `ℂ`, `ℂ*` or the open rectangle. -/
def domain : FactorKind → Set ℂ
  | disc ρ => ball 0 ρ
  | plane => univ
  | punctured => {0}ᶜ
  | rect p q => Ioo p.re q.re ×ℂ Ioo p.im q.im

/-- `1 / (ν + 2)`, the shrinking parameter of the standard exhaustions. -/
def gap (ν : ℕ) : ℝ := 1 / ((ν : ℝ) + 2)

lemma gap_pos (ν : ℕ) : 0 < gap ν := by unfold gap; positivity

lemma gap_succ_lt (ν : ℕ) : gap (ν + 1) < gap ν := by
  unfold gap
  apply one_div_lt_one_div_of_lt (by positivity)
  push_cast
  linarith

/-- The lower left corner of the `ν`-th compact rectangle in the open rectangle `(p, q)`. -/
def rectLo (p : ℂ) (ν : ℕ) : ℂ := ⟨p.re + gap ν, p.im + gap ν⟩

/-- The upper right corner of the `ν`-th compact rectangle in the open rectangle `(p, q)`. -/
def rectHi (q : ℂ) (ν : ℕ) : ℂ := ⟨q.re - gap ν, q.im - gap ν⟩

/-- The `ν`-th compact set of the standard exhaustion: `A(0, ρ - 1/(ν + 2))` for the disc of radius
`ρ`, `A(0, ν + 1)` for `ℂ`, `A(1/(ν + 2), ν + 2)` for `ℂ*`, and the closed rectangle shrunk by
`1/(ν + 2)` for an open rectangle. -/
def compact : FactorKind → ℕ → Set ℂ
  | disc ρ, ν => closedAnnulus 0 (ρ - gap ν)
  | plane, ν => closedAnnulus 0 (ν + 1)
  | punctured, ν => closedAnnulus (gap ν) (ν + 2)
  | rect p q, ν => closedRect (rectLo p ν) (rectHi q ν)

lemma isOpen_domain (κ : FactorKind) : IsOpen κ.domain := by
  cases κ with
  | disc ρ => exact isOpen_ball
  | plane => exact isOpen_univ
  | punctured => exact isOpen_compl_singleton
  | rect p q => exact isOpen_Ioo.reProdIm isOpen_Ioo

lemma isCompact_compact (κ : FactorKind) (ν : ℕ) : IsCompact (κ.compact ν) := by
  cases κ with
  | rect p q => exact isCompact_closedRect _ _
  | _ => exact isCompact_closedAnnulus _ _

lemma compact_subset_domain (κ : FactorKind) (ν : ℕ) : κ.compact ν ⊆ κ.domain := by
  have hg := gap_pos ν
  cases κ with
  | disc ρ =>
    intro z hz
    have h1 := hz.2
    simp only [domain, mem_ball_zero_iff]
    linarith
  | plane => exact subset_univ _
  | punctured =>
    intro z hz h0
    have h1 := hz.1
    rw [mem_singleton_iff.mp h0, norm_zero] at h1
    linarith
  | rect p q =>
    intro z hz
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    simp only [rectLo, rectHi] at h1 h2 h3 h4
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

lemma zero_notMem_domain_punctured : (0 : ℂ) ∉ punctured.domain := by simp [domain]

/-- Each compact set of the standard exhaustion lies in the interior of the next one. -/
lemma compact_subset_interior (κ : FactorKind) (ν : ℕ) :
    κ.compact ν ⊆ interior (κ.compact (ν + 1)) := by
  have hg := gap_succ_lt ν
  have hg0 := gap_pos (ν + 1)
  cases κ with
  | disc ρ =>
    exact fun z hz ↦ ball_subset_interior_closedAnnulus le_rfl _
      (mem_ball_zero_iff.mpr (hz.2.trans_lt (by linarith)))
  | plane =>
    exact fun z hz ↦ ball_subset_interior_closedAnnulus le_rfl _
      (mem_ball_zero_iff.mpr (hz.2.trans_lt (by push_cast; linarith)))
  | punctured =>
    exact fun _ hz ↦ subset_interior_closedAnnulus _ _
      ⟨hg.trans_le hz.1, hz.2.trans_lt (by push_cast; linarith)⟩
  | rect p q =>
    intro z hz
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    simp only [rectLo, rectHi] at h1 h2 h3 h4
    refine interior_maximal (t := Ioo (rectLo p (ν + 1)).re (rectHi q (ν + 1)).re ×ℂ
      Ioo (rectLo p (ν + 1)).im (rectHi q (ν + 1)).im) (fun w hw ↦ ?_)
      (isOpen_Ioo.reProdIm isOpen_Ioo) ?_
    · exact ⟨⟨hw.1.1.le, hw.1.2.le⟩, ⟨hw.2.1.le, hw.2.2.le⟩⟩
    · simp only [rectLo, rectHi]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

private lemma eventually_gap_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ ν : ℕ in atTop, gap ν < δ := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  refine eventually_atTop.mpr ⟨n, fun ν hν ↦ lt_of_le_of_lt ?_ hn⟩
  unfold gap
  apply one_div_le_one_div_of_le (by positivity)
  have : (n : ℝ) ≤ ν := by exact_mod_cast hν
  linarith

/-- Every point of the domain lies in the interior of the `ν`-th compact set for large `ν`. -/
lemma eventually_mem_interior (κ : FactorKind) {z : ℂ} (hz : z ∈ κ.domain) :
    ∀ᶠ ν in atTop, z ∈ interior (κ.compact ν) := by
  have hbig : ∀ x : ℝ, ∀ᶠ ν : ℕ in atTop, x < ν :=
    fun x ↦ tendsto_natCast_atTop_atTop.eventually_gt_atTop x
  cases κ with
  | disc ρ =>
    have hzρ : ‖z‖ < ρ := mem_ball_zero_iff.mp hz
    filter_upwards [eventually_gap_lt (sub_pos.mpr hzρ)] with ν hν
    exact ball_subset_interior_closedAnnulus le_rfl _ (mem_ball_zero_iff.mpr (by linarith))
  | plane =>
    filter_upwards [hbig ‖z‖] with ν hν
    exact ball_subset_interior_closedAnnulus le_rfl _ (mem_ball_zero_iff.mpr (by linarith))
  | punctured =>
    have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
    filter_upwards [eventually_gap_lt hz0, hbig ‖z‖] with ν h1 h2
    exact subset_interior_closedAnnulus _ _ ⟨h1, by linarith⟩
  | rect p q =>
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hz
    filter_upwards [eventually_gap_lt (sub_pos.mpr h1), eventually_gap_lt (sub_pos.mpr h2),
      eventually_gap_lt (sub_pos.mpr h3), eventually_gap_lt (sub_pos.mpr h4)] with ν e1 e2 e3 e4
    refine interior_maximal (t := Ioo (rectLo p ν).re (rectHi q ν).re ×ℂ
      Ioo (rectLo p ν).im (rectHi q ν).im) (fun w hw ↦ ?_) (isOpen_Ioo.reProdIm isOpen_Ioo) ?_
    · exact ⟨⟨hw.1.1.le, hw.1.2.le⟩, ⟨hw.2.1.le, hw.2.2.le⟩⟩
    · simp only [rectLo, rectHi]
      exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩

/-- The one-variable approximation scheme between consecutive compact sets of the standard
exhaustion: Laurent (Taylor for discs and `ℂ`) expansions, or the rectangle scheme. -/
def scheme : (κ : FactorKind) → (ν : ℕ) → ApproxScheme (κ.compact ν) (κ.compact (ν + 1)) κ.domain
  | disc ρ, ν => annularScheme (ball 0 ρ) (by linarith [gap_succ_lt ν]) le_rfl (Or.inl rfl)
      fun h ↦ absurd h (lt_irrefl 0)
  | plane, ν => annularScheme univ (by push_cast; linarith) le_rfl (Or.inl rfl)
      fun h ↦ absurd h (lt_irrefl 0)
  | punctured, ν => annularScheme {0}ᶜ (by push_cast; linarith) (gap_pos _).le
      (Or.inr (gap_succ_lt ν)) fun _ ↦ zero_notMem_domain_punctured
  | rect p q, ν => rectSchemeOrEmpty (Ioo p.re q.re ×ℂ Ioo p.im q.im)
      (by simp only [rectLo]; linarith [gap_succ_lt ν])
      (by simp only [rectHi]; linarith [gap_succ_lt ν])
      (by simp only [rectLo]; linarith [gap_succ_lt ν])
      (by simp only [rectHi]; linarith [gap_succ_lt ν])

variable {σ : Type} [Fintype σ]

/-- The **standard exhaustion** of `∏ᵢ (κ i).domain` by the products of the compact sets
`(κ i).compact ν`. -/
def exhaustion (κ : σ → FactorKind) : ProductExhaustion fun i ↦ (κ i).domain where
  K ν i := (κ i).compact ν
  isCompact ν i := (κ i).isCompact_compact ν
  subset_interior ν i := (κ i).compact_subset_interior ν
  subset ν i := (κ i).compact_subset_domain ν
  exhaust _ hz :=
    (eventually_all.mpr fun i ↦ (κ i).eventually_mem_interior (hz i (mem_univ i))).exists

/-- **The standard exhaustion has the Runge property**: functions analytic near the
`(ν + 1)`-st compact product are uniform limits on the `ν`-th of functions analytic on
`∏ᵢ (κ i).domain`. -/
theorem isRunge_exhaustion (κ : σ → FactorKind) : (exhaustion κ).IsRunge := by
  intro ν h hh ε hε
  let D : ProductRungeData σ :=
    { K := fun i ↦ (κ i).compact ν
      L := fun i ↦ (κ i).compact (ν + 1)
      Ω := fun i ↦ (κ i).domain
      isCompact_K := fun i ↦ (κ i).isCompact_compact ν
      K_subset_L := fun i ↦ ((κ i).compact_subset_interior ν).trans interior_subset
      K_subset_Ω := fun i ↦ (κ i).compact_subset_domain ν
      scheme := fun i ↦ (κ i).scheme ν }
  exact D.exists_approx hh hε

end FactorKind

end AnalyticGeometry
