/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Hartogs

/-!
# Homogeneous functions on `(ℂ*)^σ` with only negative Laurent exponents

Let `T = (ℂ*)^σ` (`σ` finite) and let `f` be analytic on `T` with vanishing nonnegative Laurent
part in every variable, `Pⱼf = 0` on `T` for all `j` (`AnalyticGeometry.laurentProj`), and
homogeneous of degree `d ∈ ℤ`: `f(cz) = cᵈ f(z)` for `c ≠ 0`, `z ∈ T`. Then `f` is a Laurent
polynomial all of whose exponents are `≤ -1`
(`AnalyticGeometry.exists_eq_eval_inv_of_laurentProj_eq_zero`): there is a homogeneous polynomial
`P` of degree `-d` (`P = 0` if `d > 0`), every monomial of which contains every variable, with
`f(z) = P(z₁⁻¹, …, zₙ⁻¹)` on `T`.

Proof: `g(w) = f(w⁻¹)` is analytic on `T`, and in each variable `wⱼ` it extends across `wⱼ = 0`,
vanishing there (the Laurent splitting of `f` in `zⱼ` has only the negative part). Applying the
projectors `Pⱼ` to `g` for all `j` produces an entire function `G` equal to `g` on `T`
(`AnalyticGeometry.analyticAt_laurentProjList`, `AnalyticGeometry.laurentProjList_eq`),
homogeneous of degree `-d`, hence a homogeneous polynomial
(`AnalyticGeometry.exists_isHomogeneous_eq_of_homogeneous`), vanishing on the coordinate
hyperplanes, hence divisible by every variable
(`AnalyticGeometry.one_le_of_mem_support_of_eval_eq_zero`).

This is the top-degree case of the comparison of the cohomology of `𝒪(d)` on `ℙⁿ` with that of
`𝒪(d)^an` via the standard affine cover: the part of the analytic Čech complex on which all
`Pⱼ` vanish consists of Laurent polynomials, as in the algebraic case.

Reference: Serre, *Géométrie algébrique et géométrie analytique*, §3, no. 13; Cartan's seminar
1951/52.
-/

noncomputable section

open Complex Set Metric Filter Topology

namespace AnalyticGeometry

variable {σ : Type} [Fintype σ] [DecidableEq σ]

/-! ### Polynomials vanishing on a coordinate hyperplane -/

omit [Fintype σ] [DecidableEq σ] in
/-- If a polynomial vanishes at every point of the hyperplane `{wⱼ = 0}` whose other coordinates
are nonzero, then every monomial of it contains `Xⱼ`. -/
theorem one_le_of_mem_support_of_eval_eq_zero [Finite σ] {P : MvPolynomial σ ℂ} {j : σ}
    (h : ∀ w : σ → ℂ, w j = 0 → (∀ k, k ≠ j → w k ≠ 0) → MvPolynomial.eval w P = 0)
    {m : σ →₀ ℕ} (hm : m ∈ P.support) : 1 ≤ m j := by
  classical
  have := Fintype.ofFinite σ
  by_contra hmj
  have hmj0 : m j = 0 := by omega
  -- the part of `P` not involving `Xⱼ`
  set P₀ : MvPolynomial σ ℂ := ∑ m' ∈ P.support.filter (fun m' ↦ m' j = 0),
    MvPolynomial.monomial m' (P.coeff m')
  have heval : ∀ w : σ → ℂ, w j = 0 → MvPolynomial.eval w P = MvPolynomial.eval w P₀ := by
    intro w hw
    rw [MvPolynomial.eval_eq', map_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m' _ ↦ ?_
    split_ifs with h'
    · rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ fun _ ↦ pow_zero _]
    · have : ∏ i, w i ^ m' i = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hw, zero_pow h'])
      rw [this, mul_zero]
  have hupd : ∀ w : σ → ℂ,
      MvPolynomial.eval w P₀ = MvPolynomial.eval (Function.update w j 0) P₀ := by
    intro w
    simp only [P₀, map_sum, MvPolynomial.eval_monomial]
    refine Finset.sum_congr rfl fun m' hm' ↦ ?_
    congr 1
    refine Finsupp.prod_congr fun i _ ↦ ?_
    by_cases hi : i = j
    · subst hi
      rw [(Finset.mem_filter.mp hm').2, pow_zero, pow_zero]
    · rw [Function.update_of_ne hi]
  -- `P₀` vanishes on the box `∏ₖ sₖ` with `sⱼ = ℂ`, `sₖ = ℂ*`
  have hP₀ : P₀ = 0 := by
    refine MvPolynomial.funext_set (fun k ↦ if k = j then univ else {0}ᶜ)
      (fun k ↦ by split_ifs <;> simp [Set.infinite_univ, (Set.finite_singleton _).infinite_compl])
      fun w hw ↦ ?_
    rw [map_zero, hupd, ← heval _ (by simp)]
    refine h _ (by simp) fun k hk ↦ ?_
    have := hw k (mem_univ k)
    simp only [hk, ite_false, mem_compl_iff, mem_singleton_iff] at this
    rwa [Function.update_of_ne hk]
  have hcoeff : P₀.coeff m = P.coeff m := by
    simp only [P₀, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_eq_single m (fun b _ hb ↦ by simp [hb]) (fun hm' ↦ ?_)]
    · simp
    · exact absurd (Finset.mem_filter.mpr ⟨hm, hmj0⟩) hm'
  rw [hP₀, MvPolynomial.coeff_zero] at hcoeff
  exact (MvPolynomial.mem_support_iff.mp hm) hcoeff.symm

/-! ### Iterated projectors -/

omit [Fintype σ] in
/-- `Pⱼ F` at `w` depends only on `F` along the circle `{w₍ⱼ←ζ₎ : |ζ| = |wⱼ| + 1}`. -/
lemma laurentProj_congr {j : σ} {F₁ F₂ : (σ → ℂ) → ℂ} {w : σ → ℂ}
    (h : ∀ ζ : ℂ, ζ ≠ 0 → F₁ (Function.update w j ζ) = F₂ (Function.update w j ζ)) :
    laurentProj j F₁ w = laurentProj j F₂ w := by
  simp only [laurentProj, laurentPlus]
  congr 1
  refine circleIntegral.integral_congr (by positivity) fun ζ hζ ↦ ?_
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [mem_sphere_zero_iff_norm, norm_zero] at hζ
    have : (0 : ℝ) < ‖w j‖ + 1 := by positivity
    linarith
  simp only [h ζ hζ0]

/-- The projectors `P_{j₁} ⋯ P_{jₖ}` applied to `g`, for the list `[j₁, …, jₖ]`. -/
def laurentProjList (L : List σ) (g : (σ → ℂ) → ℂ) : (σ → ℂ) → ℂ :=
  L.foldr (fun j F ↦ laurentProj j F) g

omit [Fintype σ] in
@[simp] lemma laurentProjList_nil (g : (σ → ℂ) → ℂ) : laurentProjList [] g = g := rfl

omit [Fintype σ] in
@[simp] lemma laurentProjList_cons (j : σ) (L : List σ) (g : (σ → ℂ) → ℂ) :
    laurentProjList (j :: L) g = laurentProj j (laurentProjList L g) := rfl

/-- `P_{j₁} ⋯ P_{jₖ} g` is analytic where the coordinates outside `L` are nonzero, if `g` is
analytic on `(ℂ*)^σ`. -/
theorem analyticAt_laurentProjList {g : (σ → ℂ) → ℂ} (hg : ∀ w, (∀ k, w k ≠ 0) → AnalyticAt ℂ g w)
    (L : List σ) {w : σ → ℂ} (hw : ∀ k, k ∉ L → w k ≠ 0) :
    AnalyticAt ℂ (laurentProjList L g) w := by
  induction L generalizing w with
  | nil => exact hg w fun k ↦ hw k (List.not_mem_nil)
  | cons j L ih =>
    set V : Set (σ → ℂ) := {y | ∀ k, k ∉ j :: L → y k ≠ 0}
    have hVo : IsOpen V := by
      have : V = ⋂ k, {y : σ → ℂ | k ∉ j :: L → y k ≠ 0} := by
        ext y
        simp [V]
      rw [this]
      refine isOpen_iInter_of_finite fun k ↦ ?_
      by_cases hk : k ∈ j :: L
      · simp [hk]
      · simpa [hk] using isOpen_ne_fun (continuous_apply k) continuous_const
    have hVj : ∀ y ∈ V, ∀ t, Function.update y j t ∈ V := fun y hy t k hk ↦ by
      have hkj : k ≠ j := fun h ↦ hk (h ▸ List.mem_cons_self)
      rw [Function.update_of_ne hkj]
      exact hy k hk
    have hf : ∀ y ∈ V, y j ≠ 0 → AnalyticAt ℂ (laurentProjList L g) y := fun y hy hyj ↦
      ih fun k hk ↦ by
        by_cases hkj : k = j
        · exact hkj ▸ hyj
        · exact hy k fun h ↦ (List.mem_cons.mp h).elim hkj hk
    exact analyticAt_laurentProj hVo hVj hf hw

omit [Fintype σ] in
private lemma update_mem_torus {w : σ → ℂ} {j : σ} (hw : ∀ k, k ≠ j → w k ≠ 0) {ζ : ℂ}
    (hζ : ζ ≠ 0) (k : σ) : Function.update w j ζ k ≠ 0 := by
  by_cases hk : k = j
  · subst hk
    simpa using hζ
  · rw [Function.update_of_ne hk]
    exact hw k hk

omit [Fintype σ] in
/-- If `Pⱼ g = g` on `(ℂ*)^σ` for every `j`, then `P_{j₁} ⋯ P_{jₖ} g = g` on `(ℂ*)^σ`. -/
theorem laurentProjList_eq {g : (σ → ℂ) → ℂ}
    (hPg : ∀ j, ∀ w, (∀ k, w k ≠ 0) → laurentProj j g w = g w) (L : List σ) {w : σ → ℂ}
    (hw : ∀ k, w k ≠ 0) : laurentProjList L g w = g w := by
  induction L generalizing w with
  | nil => rfl
  | cons j L ih =>
    have hc : ∀ ζ : ℂ, ζ ≠ 0 → laurentProjList L g (Function.update w j ζ) =
        g (Function.update w j ζ) := fun ζ hζ ↦
      ih (update_mem_torus (fun k _ ↦ hw k) hζ)
    rw [laurentProjList_cons, laurentProj_congr hc, hPg j w hw]

omit [Fintype σ] in
/-- If `Pⱼ g = g` on `(ℂ*)^σ` for every `j`, then `Pⱼ P_{j₁} ⋯ P_{jₖ} g = Pⱼ g` wherever the
coordinates other than `wⱼ` are nonzero. -/
theorem laurentProjList_cons_eq {g : (σ → ℂ) → ℂ}
    (hPg : ∀ j, ∀ w, (∀ k, w k ≠ 0) → laurentProj j g w = g w) (j : σ) (L : List σ)
    {w : σ → ℂ} (hw : ∀ k, k ≠ j → w k ≠ 0) :
    laurentProjList (j :: L) g w = laurentProj j g w :=
  laurentProj_congr fun _ hζ ↦ laurentProjList_eq hPg L (update_mem_torus hw hζ)

/-! ### The main result -/

/-- **Homogeneous functions on `(ℂ*)^σ` with only negative Laurent exponents are Laurent
polynomials**: let `f` be analytic on `(ℂ*)^σ` with `Pⱼ f = 0` there for every `j`, and
homogeneous of degree `d ∈ ℤ` on `(ℂ*)^σ`. Then there is a polynomial `P`, homogeneous of degree
`(-d).toNat`, with `P = 0` if `d > 0`, every monomial of which contains every variable, such that
`f(z) = P(z₁⁻¹, …, zₙ⁻¹)` on `(ℂ*)^σ`. -/
theorem exists_eq_eval_inv_of_laurentProj_eq_zero {f : (σ → ℂ) → ℂ}
    (hf : ∀ z, (∀ k, z k ≠ 0) → AnalyticAt ℂ f z)
    (hP : ∀ j, ∀ z, (∀ k, z k ≠ 0) → laurentProj j f z = 0) {d : ℤ}
    (hd : ∀ c : ℂ, c ≠ 0 → ∀ z, (∀ k, z k ≠ 0) → f (c • z) = c ^ d * f z) :
    ∃ P : MvPolynomial σ ℂ, P.IsHomogeneous (-d).toNat ∧ (∀ m ∈ P.support, ∀ k, 1 ≤ m k) ∧
      (0 < d → P = 0) ∧ ∀ z, (∀ k, z k ≠ 0) → f z = MvPolynomial.eval (fun k ↦ (z k)⁻¹) P := by
  set inv : (σ → ℂ) → σ → ℂ := fun w k ↦ (w k)⁻¹ with hinvdef
  have hinvT : ∀ w : σ → ℂ, (∀ k, w k ≠ 0) → ∀ k, inv w k ≠ 0 := fun w hw k ↦ inv_ne_zero (hw k)
  have hinvinv : ∀ w : σ → ℂ, inv (inv w) = w := fun w ↦ funext fun k ↦ inv_inv (w k)
  have hinvA : ∀ w : σ → ℂ, (∀ k, w k ≠ 0) → AnalyticAt ℂ inv w := fun w hw ↦
    analyticAt_pi_iff.mpr fun k ↦
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) k).analyticAt w).inv (hw k)
  set g : (σ → ℂ) → ℂ := fun w ↦ f (inv w) with hgdef
  have hg : ∀ w, (∀ k, w k ≠ 0) → AnalyticAt ℂ g w := fun w hw ↦
    (hf _ (hinvT w hw)).comp (hinvA w hw)
  -- Step 1: in each variable, `g` extends across `wⱼ = 0` and vanishes there
  have hstep : ∀ j, (∀ w, (∀ k, w k ≠ 0) → laurentProj j g w = g w) ∧
      ∀ w, (∀ k, k ≠ j → w k ≠ 0) → w j = 0 → laurentProj j g w = 0 := by
    intro j
    set Uj : Set (σ → ℂ) := {w | ∀ k, k ≠ j → w k ≠ 0}
    have hUjo : IsOpen Uj := by
      have : Uj = ⋂ k, {y : σ → ℂ | k ≠ j → y k ≠ 0} := by
        ext y
        simp [Uj]
      rw [this]
      refine isOpen_iInter_of_finite fun k ↦ ?_
      by_cases hk : k = j
      · simp [hk]
      · simpa [hk] using isOpen_ne_fun (continuous_apply k) continuous_const
    have hUjj : ∀ y ∈ Uj, ∀ t, Function.update y j t ∈ Uj := fun y hy t k hk ↦ by
      rw [Function.update_of_ne hk]
      exact hy k hk
    have hT : ∀ y ∈ Uj, y j ≠ 0 → ∀ k, y k ≠ 0 := fun y hy hyj k ↦ by
      by_cases hk : k = j
      · exact hk ▸ hyj
      · exact hy k hk
    have hfj : ∀ y ∈ Uj, y j ≠ 0 → AnalyticAt ℂ f y := fun y hy hyj ↦ hf y (hT y hy hyj)
    have hgj : ∀ y ∈ Uj, y j ≠ 0 → AnalyticAt ℂ g y := fun y hy hyj ↦ hg y (hT y hy hyj)
    -- the extension `Gⱼ(w) = Rⱼf(w⁻¹₍ⱼ←wⱼ₎)`
    set Φ : (σ → ℂ) → σ → ℂ := fun w ↦ Function.update (inv w) j (w j)
    have hΦU : ∀ w ∈ Uj, Φ w ∈ Uj := fun w hw k hk ↦ by
      simp only [Φ, Function.update_of_ne hk]
      exact inv_ne_zero (hw k hk)
    have hΦA : ∀ w ∈ Uj, AnalyticAt ℂ Φ w := fun w hw ↦ by
      refine analyticAt_pi_iff.mpr fun k ↦ ?_
      by_cases hk : k = j
      · subst hk
        simp only [Function.update_self]
        exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) k).analyticAt w
      · simp only [Function.update_of_ne hk, inv]
        exact ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : σ ↦ ℂ) k).analyticAt w).inv
          (hw k hk)
    set Gj : (σ → ℂ) → ℂ := fun w ↦ laurentProjInv j f (Φ w)
    have hGj : ∀ w ∈ Uj, AnalyticAt ℂ Gj w := fun w hw ↦
      (analyticAt_laurentProjInv hUjo hUjj hfj (hΦU w hw)).comp (hΦA w hw)
    have hGj0 : ∀ w ∈ Uj, w j = 0 → Gj w = 0 := fun w _ hwj ↦
      laurentProjInv_of_eq_zero (by simp [Φ, hwj])
    have hgGj : ∀ w ∈ Uj, w j ≠ 0 → g w = Gj w + 0 := fun w hw hwj ↦ by
      have hwT := hT w hw hwj
      have hsplit := eq_laurentProj_add_laurentProjInv hUjj hfj (fun k hk ↦ hinvT w hwT k)
        (hinvT w hwT j)
      rw [hP j _ (hinvT w hwT), zero_add] at hsplit
      rw [add_zero]
      simp only [g, Gj, Φ]
      rw [hsplit]
      congr 2
      simp [inv]
    have hchar := fun w (hw : w ∈ Uj) ↦ (laurentProj_eq_of_splitting (h := fun _ ↦ 0) hUjo hUjj
      hgj hGj (fun _ _ ↦ analyticAt_const) (fun _ _ _ ↦ rfl)
      (fun y hy hyj ↦ hgGj y hy hyj) hw).1
    refine ⟨fun w hw ↦ ?_, fun w hw hwj ↦ ?_⟩
    · have hwU : w ∈ Uj := fun k _ ↦ hw k
      rw [hchar w hwU, ← add_zero (Gj w), ← hgGj w hwU (hw j)]
    · rw [hchar w hw, hGj0 w hw hwj]
  have hPg : ∀ j, ∀ w, (∀ k, w k ≠ 0) → laurentProj j g w = g w := fun j ↦ (hstep j).1
  -- Step 2: the entire extension `G`
  set Lall : List σ := (Finset.univ : Finset σ).toList
  have hLall : ∀ k, k ∈ Lall := fun k ↦ Finset.mem_toList.mpr (Finset.mem_univ k)
  set G : (σ → ℂ) → ℂ := laurentProjList Lall g
  have hGA : ∀ w, AnalyticAt ℂ G w := fun w ↦
    analyticAt_laurentProjList hg Lall fun k hk ↦ absurd (hLall k) hk
  have hGc : Continuous G := continuous_iff_continuousAt.mpr fun w ↦ (hGA w).continuousAt
  have hGg : ∀ w, (∀ k, w k ≠ 0) → G w = g w := fun w hw ↦ laurentProjList_eq hPg Lall hw
  have hdense : Dense {w : σ → ℂ | ∀ k, w k ≠ 0} := by
    have := dense_pi (s := fun _ : σ ↦ ({0}ᶜ : Set ℂ)) univ fun _ _ ↦ dense_compl_singleton 0
    simpa [Set.pi, Set.compl_def] using this
  -- `G` vanishes on the coordinate hyperplanes (where the other coordinates are nonzero)
  have hG0 : ∀ j, ∀ w : σ → ℂ, w j = 0 → (∀ k, k ≠ j → w k ≠ 0) → G w = 0 := by
    intro j w hwj hw
    set Lj : List σ := j :: Lall.erase j
    have hLj : ∀ k, k ∈ Lj := fun k ↦ by
      by_cases hk : k = j
      · exact hk ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ ((List.mem_erase_of_ne hk).mpr (hLall k))
    have hGjc : Continuous (laurentProjList Lj g) := continuous_iff_continuousAt.mpr fun w ↦
      (analyticAt_laurentProjList hg Lj fun k hk ↦ absurd (hLj k) hk).continuousAt
    have heq : G = laurentProjList Lj g := Continuous.ext_on hdense hGc hGjc fun y hy ↦ by
      rw [hGg y hy, laurentProjList_eq hPg Lj hy]
    rw [heq, laurentProjList_cons_eq hPg j _ hw]
    exact (hstep j).2 w hw hwj
  -- Step 3: homogeneity of `G`, of degree `-d`
  have hGd : ∀ c : ℂ, c ≠ 0 → ∀ w, G (c • w) = c ^ (-d) * G w := by
    intro c hc
    have hcont1 : Continuous fun w ↦ G (c • w) := hGc.comp (continuous_const_smul c)
    have hcont2 : Continuous fun w ↦ c ^ (-d) * G w := continuous_const.mul hGc
    refine fun w ↦ congrFun (Continuous.ext_on hdense hcont1 hcont2 fun y hy ↦ ?_) w
    have hy' : ∀ k, (c • y) k ≠ 0 := fun k ↦ by simpa using mul_ne_zero hc (hy k)
    have hinvc : inv (c • y) = c⁻¹ • inv y := funext fun k ↦ by
      simp only [inv, Pi.smul_apply, smul_eq_mul, mul_inv]
    rw [hGg _ hy', hGg y hy]
    simp only [g]
    rw [hinvc, hd c⁻¹ (inv_ne_zero hc) _ (hinvT y hy), inv_zpow']
  -- Step 4: conclusion
  have hfG : ∀ z, (∀ k, z k ≠ 0) → f z = G (inv z) := fun z hz ↦ by
    rw [hGg _ (hinvT z hz)]
    simp [g, hinvinv]
  rcases lt_or_ge 0 d with hdpos | hdneg
  · -- negative degree: `G = 0`
    have hG : ∀ w, G w = 0 := eq_zero_of_homogeneous_neg hGc.continuousAt (by omega) hGd
    refine ⟨0, MvPolynomial.isHomogeneous_zero _ _ _, by simp, fun _ ↦ rfl, fun z hz ↦ ?_⟩
    rw [hfG z hz, hG, map_zero]
  · set n : ℕ := (-d).toNat
    have hn : ((n : ℕ) : ℤ) = -d := Int.toNat_of_nonneg (by omega)
    obtain ⟨P, hPh, hPG⟩ := exists_isHomogeneous_eq_of_homogeneous hGA (n := n)
      fun c hc w ↦ by rw [hGd c hc w, ← hn, zpow_natCast]
    refine ⟨P, hPh, fun m hm k ↦ ?_, fun h ↦ absurd h (by omega), fun z hz ↦ ?_⟩
    · exact one_le_of_mem_support_of_eval_eq_zero
        (fun w hwk hw ↦ by rw [← hPG, hG0 k w hwk hw]) hm
    · rw [hfG z hz, hPG]

end AnalyticGeometry
