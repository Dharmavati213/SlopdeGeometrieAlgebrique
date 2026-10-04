/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.DolbeaultParam
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The Dolbeault–Grothendieck lemma near compact products

**Theorem** (`AnalyticGeometry.exists_dbarForm_eq_near_compact`; Hörmander, *An introduction to
complex analysis in several variables*, first step of the proof of Theorem 2.3.3, for products
of arbitrary compact sets instead of closed polydiscs). Let `Wᵢ ⊆ ℂ` be open and `Kᵢ ⊆ Wᵢ`
compact, `i ∈ σ`. Let `g` be a smooth `(0, q + 1)`-form on `W = ∏ Wᵢ` with `∂̄g = 0` (coordinate
forms, `dbarForm`). Then there are open sets `Kᵢ ⊆ W'ᵢ ⊆ Wᵢ` and a smooth `(0, q)`-form `u` on
`W' = ∏ W'ᵢ` with `∂̄u = g` on `W'`.

The proof is Hörmander's induction on the set `A` of variables `j` such that `g` involves `dz̄ⱼ`
(`AnalyticGeometry.exists_dbarForm_eq_of_involves`): if `m ∈ A`, the coefficients `g_{I ∪ {m}}`,
`I ⊆ A ∖ {m}`, are holomorphic in the variables outside `A`
(`dbarPartial_eq_zero_of_dbarForm_eq_zero`); their Cauchy transforms in `zₘ` (after a cutoff in
`zₘ`, `cauchyTransformIn`) are still holomorphic in those variables and give `u` with
`g - ∂̄u` involving only `A ∖ {m}`.

Taking `Kᵢ = {xᵢ}` gives the local exactness of the Dolbeault complex at every point
(`AnalyticGeometry.exists_dbarForm_eq_near`), the `∂̄`-Poincaré lemma.
-/

noncomputable section

open Topology Filter Set Complex Metric
open scoped ContDiff Manifold

namespace AnalyticGeometry

/-! ### Cutoff functions -/

/-- A smooth cutoff function on `ℂ`: `χ = 1` on an open neighbourhood `N` of the compact set `K`,
and `χ = 0` outside a compact subset `k` of the open set `W ⊇ K`. -/
lemma exists_cutoff {K W : Set ℂ} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ ∃ N : Set ℂ, IsOpen N ∧ K ⊆ N ∧ N ⊆ W ∧ (∀ t ∈ N, χ t = 1) ∧
      ∃ k : Set ℂ, IsCompact k ∧ k ⊆ W ∧ ∀ t ∉ k, χ t = 0 := by
  obtain ⟨δ, hδ, hδW⟩ := hK.exists_thickening_subset_open hW hKW
  have hδ3 : 0 < δ / 3 := by positivity
  obtain ⟨f, hf0, hf1, -⟩ := exists_contMDiffMap_zero_one_of_isClosed 𝓘(ℝ, ℂ) (n := ⊤)
    (isOpen_thickening (δ := 2 * (δ / 3)) (E := K)).isClosed_compl
    (isClosed_cthickening (δ := δ / 3) (E := K))
    (disjoint_compl_left_iff_subset.mpr
      (cthickening_subset_thickening' (by positivity) (by linarith) K))
  refine ⟨f, contMDiff_iff_contDiff.mp f.contMDiff, thickening (δ / 3) K, isOpen_thickening,
    self_subset_thickening hδ3 K,
    (thickening_mono (by linarith) K).trans hδW,
    fun t ht ↦ hf1 (thickening_subset_cthickening _ _ ht),
    cthickening (2 * (δ / 3)) K, hK.cthickening,
    (cthickening_subset_thickening' hδ (by linarith) K).trans hδW, fun t ht ↦ ?_⟩
  exact hf0 fun h ↦ ht (thickening_subset_cthickening _ _ h)

/-! ### Two derivative computations -/

section Derivatives

variable {σ : Type} [Fintype σ] [DecidableEq σ]

omit [Fintype σ] in
/-- The Leibniz rule for `∂/∂z̄ⱼ`. -/
lemma dbarPartial_mul [Finite σ] (j : σ) {f g : (σ → ℂ) → ℂ} {z : σ → ℂ}
    (hf : DifferentiableAt ℝ f z) (hg : DifferentiableAt ℝ g z) :
    dbarPartial j (fun y ↦ f y * g y) z = f z * dbarPartial j g z + g z * dbarPartial j f z := by
  have := Fintype.ofFinite σ
  rw [dbarPartial_apply, dbarPartial_apply, dbarPartial_apply, fderiv_fun_mul hf hg]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  ring

omit [Fintype σ] in
/-- A function of `zₘ` alone has `∂/∂z̄ⱼ = 0` for `j ≠ m`. -/
lemma dbarPartial_comp_apply_of_ne [Finite σ] {j m : σ} (hjm : j ≠ m) {φ : ℂ → ℂ} {z : σ → ℂ}
    (hφ : DifferentiableAt ℝ φ (z m)) : dbarPartial j (fun y ↦ φ (y m)) z = 0 := by
  have := Fintype.ofFinite σ
  have h : HasFDerivAt (fun y : σ → ℂ ↦ φ (y m))
      ((fderiv ℝ φ (z m)).comp (ContinuousLinearMap.proj m)) z :=
    hφ.hasFDerivAt.comp z (hasFDerivAt_apply m z)
  rw [dbarPartial_apply, h.fderiv]
  simp [Pi.single_eq_of_ne hjm.symm]

end Derivatives

/-! ### The induction -/

section Local

variable {σ : Type} [Fintype σ] [LinearOrder σ]

/-- The statement proved by induction on `A`. -/
private def LocalStatement (σ : Type) [Fintype σ] [LinearOrder σ] (A : Finset σ) : Prop :=
  ∀ (W K : σ → Set ℂ), (∀ i, IsOpen (W i)) → (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ W i) →
    ∀ (q : ℕ) (g : Finset σ → (σ → ℂ) → ℂ),
      (∀ z ∈ univ.pi W, IsSmoothFormAt g z) →
      (∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi W, g J z = 0) →
      (∀ J, ¬ J ⊆ A → ∀ z ∈ univ.pi W, g J z = 0) →
      (∀ J, ∀ z ∈ univ.pi W, dbarForm g J z = 0) →
      ∃ W' : σ → Set ℂ, (∀ i, IsOpen (W' i)) ∧ (∀ i, K i ⊆ W' i) ∧ (∀ i, W' i ⊆ W i) ∧
        ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ univ.pi W', IsSmoothFormAt u z) ∧
          (∀ I, I.card ≠ q → u I = 0) ∧
          ∀ J, ∀ z ∈ univ.pi W', dbarForm u J z = g J z

omit [Fintype σ] [LinearOrder σ] in
/-- A finite product of open subsets of `ℂ` is open. -/
lemma isOpen_univ_pi [Finite σ] {W : σ → Set ℂ} (hW : ∀ i, IsOpen (W i)) :
    IsOpen (univ.pi W) :=
  isOpen_set_pi finite_univ fun i _ ↦ hW i

private lemma localStatement_empty : LocalStatement σ ∅ := by
  intro W K hW hK hKW q g hgs hdeg hA hcl
  refine ⟨W, hW, hKW, fun _ ↦ subset_rfl, fun _ _ ↦ 0, fun z _ I ↦ contDiffAt_const,
    fun _ _ ↦ rfl, fun J z hz ↦ ?_⟩
  have h0 : g J z = 0 := by
    by_cases hJ : J ⊆ ∅
    · rw [Finset.subset_empty] at hJ
      subst hJ
      exact hdeg ∅ (by simp) z hz
    · exact hA J hJ z hz
  rw [h0]
  exact Finset.sum_eq_zero fun j _ ↦ by
    rw [show (fun _ : σ → ℂ ↦ (0 : ℂ)) = 0 from rfl, dbarPartial_zero, mul_zero]

private lemma localStatement_insert {m : σ} {A : Finset σ} (hm : m ∉ A)
    (ih : LocalStatement σ A) : LocalStatement σ (insert m A) := by
  intro W K hW hK hKW q g hgs hdeg hA hcl
  obtain ⟨χ, hχ, N, hN, hKN, hNW, hχ1, k, hk, hkW, hχ0⟩ :=
    exists_cutoff (hK m) (hW m) (hKW m)
  have hWo : IsOpen (univ.pi W) := isOpen_univ_pi hW
  -- the parameter domain: all coordinates but the `m`-th in `W`
  set s : Set (σ → ℂ) := {z | ∀ i, i ≠ m → z i ∈ W i} with hsdef
  have hs : IsOpen s := by
    have : s = ⋂ i ∈ (Finset.univ.filter (· ≠ m) : Finset σ), (fun z : σ → ℂ ↦ z i) ⁻¹' W i := by
      ext z
      simp [hsdef]
    rw [this]
    exact isOpen_biInter_finset fun i _ ↦ (hW i).preimage (continuous_apply i)
  have hsupd : ∀ z ∈ s, ∀ t, Function.update z m t ∈ s := fun z hz t i hi ↦ by
    rw [Function.update_of_ne hi]
    exact hz i hi
  have hcχ : ContDiff ℝ ∞ fun t : ℂ ↦ (χ t : ℂ) := ofRealCLM.contDiff.comp hχ
  -- the functions to transform
  set h : Finset σ → (σ → ℂ) → ℂ := fun I z ↦ (χ (z m) : ℂ) * g (insert m I) z with hhdef
  have hzero : ∀ I, ∀ z ∈ s, z m ∉ k → h I =ᶠ[𝓝 z] fun _ ↦ 0 := by
    intro I z _ hzk
    have : (fun y : σ → ℂ ↦ y m) ⁻¹' kᶜ ∈ 𝓝 z :=
      (continuous_apply m).continuousAt.preimage_mem_nhds (hk.isClosed.isOpen_compl.mem_nhds hzk)
    filter_upwards [this] with y hy
    simp [hhdef, hχ0 _ hy]
  have hmemW : ∀ z ∈ s, z m ∈ W m → z ∈ univ.pi W := fun z hz hzm i _ ↦ by
    by_cases hi : i = m
    · subst hi; exact hzm
    · exact hz i hi
  have hdata : ∀ I, CauchyTransformInData m (h I) s k := fun I ↦
    { isOpen := hs
      update_mem := hsupd
      isCompact := hk
      eq_zero := fun z _ t ht ↦ by simp [hhdef, hχ0 t ht]
      contDiffAt := fun z hz ↦ by
        by_cases hzm : z m ∈ W m
        · exact (hcχ.contDiffAt.comp z (contDiff_apply ℝ ℂ m).contDiffAt).mul
            (hgs z (hmemW z hz hzm) _)
        · exact contDiffAt_const.congr_of_eventuallyEq (hzero I z hz fun h ↦ hzm (hkW h)) }
  -- the correction `u`
  set u : Finset σ → (σ → ℂ) → ℂ := fun I ↦
    if I ⊆ A ∧ I.card = q then fun z ↦ koszulSign m (insert m I) * cauchyTransformIn m (h I) z
    else 0 with hudef
  have hu_smooth : ∀ z ∈ s, IsSmoothFormAt u z := fun z hz I ↦ by
    simp only [hudef]
    split_ifs
    · exact contDiffAt_const.mul (contDiffAt_cauchyTransformIn (hdata I) hz)
    · exact contDiffAt_const
  have hu_deg : ∀ I, I.card ≠ q → u I = 0 := fun I hI ↦ by
    simp only [hudef]
    rw [ite_eq_right (fun h ↦ hI h.2)]
  -- the new domain: `Wₘ` replaced by `N`
  set W1 : σ → Set ℂ := Function.update W m N with hW1def
  have hW1o : ∀ i, IsOpen (W1 i) := fun i ↦ by
    by_cases hi : i = m
    · subst hi; simp [hW1def, hN]
    · simp [hW1def, hi, hW i]
  have hW1W : ∀ i, W1 i ⊆ W i := fun i ↦ by
    by_cases hi : i = m
    · subst hi; simpa [hW1def] using hNW
    · simp [hW1def, hi]
  have hKW1 : ∀ i, K i ⊆ W1 i := fun i ↦ by
    by_cases hi : i = m
    · subst hi; simpa [hW1def] using hKN
    · simpa [hW1def, hi] using hKW i
  have hW1s : ∀ z ∈ univ.pi W1, z ∈ s := fun z hz i hi ↦ hW1W i (hz i (mem_univ i))
  have hW1W' : ∀ z ∈ univ.pi W1, z ∈ univ.pi W := fun z hz i _ ↦ hW1W i (hz i (mem_univ i))
  have hW1N : ∀ z ∈ univ.pi W1, z m ∈ N := fun z hz ↦ by
    have := hz m (mem_univ m)
    simpa [hW1def] using this
  have hW1o' : IsOpen (univ.pi W1) := isOpen_univ_pi hW1o
  -- `∂̄u = g` in the components containing `m`
  have hdu_m : ∀ J, m ∈ J → J ⊆ insert m A → ∀ z ∈ univ.pi W1, dbarForm u J z = g J z := by
    intro J hmJ hJA z hz
    rw [dbarForm, ← Finset.add_sum_erase _ _ hmJ]
    have hrest : ∑ j ∈ J.erase m, koszulSign j J * dbarPartial j (u (J.erase j)) z = 0 := by
      refine Finset.sum_eq_zero fun j hj ↦ ?_
      have hjm : j ≠ m := Finset.ne_of_mem_erase hj
      have : u (J.erase j) = 0 := by
        simp only [hudef]
        rw [ite_eq_right]
        rintro ⟨hsub, -⟩
        exact hm (hsub (Finset.mem_erase.mpr ⟨hjm.symm, hmJ⟩))
      rw [this, dbarPartial_zero, mul_zero]
    rw [hrest, add_zero]
    have hJm : J.erase m ⊆ A := fun i hi ↦ by
      have := hJA (Finset.mem_of_mem_erase hi)
      rcases Finset.mem_insert.mp this with h | h
      · exact absurd h (Finset.ne_of_mem_erase hi)
      · exact h
    by_cases hcard : (J.erase m).card = q
    · have hu : u (J.erase m) = fun z ↦ koszulSign m (insert m (J.erase m)) *
          cauchyTransformIn m (h (J.erase m)) z := by
        simp only [hudef]
        rw [ite_eq_left ⟨hJm, hcard⟩]
      rw [hu, Finset.insert_erase hmJ, dbarPartial_const_mul m _
        ((contDiffAt_cauchyTransformIn (hdata _) (hW1s z hz)).differentiableAt (by simp)),
        dbarPartial_cauchyTransformIn_self (hdata _) (hW1s z hz)]
      simp only [hhdef, hχ1 _ (hW1N z hz), Complex.ofReal_one, one_mul, Finset.insert_erase hmJ]
      rw [← mul_assoc, koszulSign_mul_self, one_mul]
    · have hu : u (J.erase m) = 0 := hu_deg _ hcard
      have hJcard : J.card ≠ q + 1 := by
        rw [← Finset.card_erase_add_one hmJ]
        omega
      rw [hu, dbarPartial_zero, mul_zero, hdeg J hJcard z (hW1W' z hz)]
  -- `∂̄u = 0` in the components not contained in `insert m A`
  have hdu_out : ∀ J, ¬ J ⊆ insert m A → ∀ z ∈ univ.pi W1, dbarForm u J z = 0 := by
    intro J hJ z hz
    refine Finset.sum_eq_zero fun j hj ↦ ?_
    by_cases hcase : J.erase j ⊆ A ∧ (J.erase j).card = q
    · have hjA : j ∉ insert m A := fun hjA ↦ hJ fun i hi ↦ by
        by_cases hij : i = j
        · exact hij ▸ hjA
        · exact Finset.mem_insert_of_mem (hcase.1 (Finset.mem_erase.mpr ⟨hij, hi⟩))
      have hjm : j ≠ m := fun h ↦ hjA (h ▸ Finset.mem_insert_self m A)
      have hu : u (J.erase j) = fun z ↦ koszulSign m (insert m (J.erase j)) *
          cauchyTransformIn m (h (J.erase j)) z := by
        simp only [hudef]
        rw [ite_eq_left hcase]
      -- `h (J ∖ j)` is holomorphic in `zⱼ`
      have hhol : ∀ y ∈ s, dbarPartial j (h (J.erase j)) y = 0 := by
        intro y hy
        by_cases hym : y m ∈ W m
        · have hyW := hmemW y hy hym
          have hd1 : DifferentiableAt ℝ (fun y : σ → ℂ ↦ (χ (y m) : ℂ)) y :=
            (hcχ.differentiable (by simp) _).comp y (differentiableAt_apply m y)
          have hd2 := (hgs y hyW (insert m (J.erase j))).differentiableAt (by simp)
          have hmul := dbarPartial_mul j hd1 hd2
          have hχj : dbarPartial j (fun y : σ → ℂ ↦ (χ (y m) : ℂ)) y = 0 :=
            dbarPartial_comp_apply_of_ne hjm (φ := fun t ↦ (χ t : ℂ))
              (hcχ.differentiable (by simp) _)
          have hsub : insert m (J.erase j) ⊆ insert m A := Finset.insert_subset_insert m hcase.1
          simp only [hhdef]
          rw [hmul, hχj, mul_zero, add_zero,
            dbarPartial_eq_zero_of_dbarForm_eq_zero hWo hA hcl hsub hjA hyW, mul_zero]
        · exact dbarPartial_eq_zero_of_eventuallyEq_zero j
            (hzero _ y hy fun h ↦ hym (hkW h))
      rw [hu, dbarPartial_const_mul j _
        ((contDiffAt_cauchyTransformIn (hdata _) (hW1s z hz)).differentiableAt (by simp)),
        dbarPartial_cauchyTransformIn_of_ne (hdata _) hjm hhol (hW1s z hz), mul_zero, mul_zero]
    · have hu : u (J.erase j) = 0 := by
        simp only [hudef]
        rw [ite_eq_right hcase]
      rw [hu, dbarPartial_zero, mul_zero]
  -- the remaining form `g' = g - ∂̄u`
  set g' : Finset σ → (σ → ℂ) → ℂ := fun I y ↦ g I y - dbarForm u I y with hg'def
  have hg's : ∀ z ∈ univ.pi W1, IsSmoothFormAt g' z := fun z hz I ↦
    (hgs z (hW1W' z hz) I).sub ((hu_smooth z (hW1s z hz)).dbarForm I)
  have hg'deg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi W1, g' J z = 0 := by
    intro J hJ z hz
    simp only [hg'def]
    rw [hdeg J hJ z (hW1W' z hz), dbarForm_eq_zero_of_card_ne isOpen_univ
      (fun I hI y _ ↦ by rw [hu_deg I hI]; rfl) hJ (mem_univ z), sub_zero]
  have hg'A : ∀ J, ¬ J ⊆ A → ∀ z ∈ univ.pi W1, g' J z = 0 := by
    intro J hJ z hz
    simp only [hg'def]
    by_cases hJm : J ⊆ insert m A
    · have hmJ : m ∈ J := by
        by_contra hmJ
        exact hJ fun i hi ↦ by
          rcases Finset.mem_insert.mp (hJm hi) with h | h
          · exact absurd (h ▸ hi) hmJ
          · exact h
      rw [hdu_m J hmJ hJm z hz, sub_self]
    · rw [hA J hJm z (hW1W' z hz), hdu_out J hJm z hz, sub_zero]
  have hg'cl : ∀ J, ∀ z ∈ univ.pi W1, dbarForm g' J z = 0 := by
    intro J z hz
    rw [hg'def, dbarForm_sub (fun I ↦ (hgs z (hW1W' z hz)).differentiableAt I)
      (fun I ↦ ((hu_smooth z (hW1s z hz)).dbarForm).differentiableAt I),
      hcl J z (hW1W' z hz), dbarForm_dbarForm (hu_smooth z (hW1s z hz)), sub_zero]
  -- the induction hypothesis
  obtain ⟨W', hW'o, hKW', hW'W1, u', hu's, hu'deg, hdu'⟩ :=
    ih W1 K hW1o hK hKW1 q g' hg's hg'deg hg'A hg'cl
  have hW'1 : ∀ z ∈ univ.pi W', z ∈ univ.pi W1 := fun z hz i _ ↦ hW'W1 i (hz i (mem_univ i))
  refine ⟨W', hW'o, hKW', fun i ↦ (hW'W1 i).trans (hW1W i), fun I y ↦ u I y + u' I y,
    fun z hz I ↦ (hu_smooth z (hW1s z (hW'1 z hz)) I).add (hu's z hz I),
    fun I hI ↦ funext fun y ↦ by simp [hu_deg I hI, hu'deg I hI], fun J z hz ↦ ?_⟩
  rw [dbarForm_add (fun I ↦ (hu_smooth z (hW1s z (hW'1 z hz))).differentiableAt I)
    (fun I ↦ (hu's z hz).differentiableAt I), hdu' J z hz]
  simp only [hg'def]
  ring

private lemma localStatement (A : Finset σ) : LocalStatement σ A := by
  induction A using Finset.induction_on with
  | empty => exact localStatement_empty
  | insert m A hm ih => exact localStatement_insert hm ih

/-- **Hörmander's induction** (Hörmander, first step of the proof of Theorem 2.3.3): a smooth
`∂̄`-closed `(0, q + 1)`-form on `∏ Wᵢ` which only involves the `dz̄ⱼ`, `j ∈ A`, is `∂̄`-exact on a
product neighbourhood of `∏ Kᵢ`, with a `(0, q)`-form vanishing in the other degrees. -/
theorem exists_dbarForm_eq_of_involves (A : Finset σ) {W K : σ → Set ℂ}
    (hW : ∀ i, IsOpen (W i)) (hK : ∀ i, IsCompact (K i)) (hKW : ∀ i, K i ⊆ W i) {q : ℕ}
    {g : Finset σ → (σ → ℂ) → ℂ} (hgs : ∀ z ∈ univ.pi W, IsSmoothFormAt g z)
    (hdeg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi W, g J z = 0)
    (hA : ∀ J, ¬ J ⊆ A → ∀ z ∈ univ.pi W, g J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi W, dbarForm g J z = 0) :
    ∃ W' : σ → Set ℂ, (∀ i, IsOpen (W' i)) ∧ (∀ i, K i ⊆ W' i) ∧ (∀ i, W' i ⊆ W i) ∧
      ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ univ.pi W', IsSmoothFormAt u z) ∧
        (∀ I, I.card ≠ q → u I = 0) ∧ ∀ J, ∀ z ∈ univ.pi W', dbarForm u J z = g J z :=
  localStatement A W K hW hK hKW q g hgs hdeg hA hcl

/-- **The Dolbeault–Grothendieck lemma near compact products** (Hörmander, first step of the
proof of Theorem 2.3.3): let `Wᵢ ⊆ ℂ` be open and `Kᵢ ⊆ Wᵢ` compact. A smooth `∂̄`-closed
`(0, q + 1)`-form `g` on `∏ Wᵢ` is `∂̄` of a smooth `(0, q)`-form on `∏ W'ᵢ` for some open
`Kᵢ ⊆ W'ᵢ ⊆ Wᵢ`. -/
theorem exists_dbarForm_eq_near_compact {W K : σ → Set ℂ} (hW : ∀ i, IsOpen (W i))
    (hK : ∀ i, IsCompact (K i)) (hKW : ∀ i, K i ⊆ W i) {q : ℕ}
    {g : Finset σ → (σ → ℂ) → ℂ} (hgs : ∀ z ∈ univ.pi W, IsSmoothFormAt g z)
    (hdeg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi W, g J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi W, dbarForm g J z = 0) :
    ∃ W' : σ → Set ℂ, (∀ i, IsOpen (W' i)) ∧ (∀ i, K i ⊆ W' i) ∧ (∀ i, W' i ⊆ W i) ∧
      ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ univ.pi W', IsSmoothFormAt u z) ∧
        (∀ I, I.card ≠ q → u I = 0) ∧ ∀ J, ∀ z ∈ univ.pi W', dbarForm u J z = g J z :=
  exists_dbarForm_eq_of_involves Finset.univ hW hK hKW hgs hdeg
    (fun J hJ ↦ absurd (Finset.subset_univ J) hJ) hcl

/-- **The `∂̄`-Poincaré lemma**: a smooth `∂̄`-closed `(0, q + 1)`-form near `x` is `∂̄`-exact on a
product neighbourhood of `x` contained in a given one. -/
theorem exists_dbarForm_eq_near {W : σ → Set ℂ} (hW : ∀ i, IsOpen (W i)) {x : σ → ℂ}
    (hx : x ∈ univ.pi W) {q : ℕ} {g : Finset σ → (σ → ℂ) → ℂ}
    (hgs : ∀ z ∈ univ.pi W, IsSmoothFormAt g z)
    (hdeg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ univ.pi W, g J z = 0)
    (hcl : ∀ J, ∀ z ∈ univ.pi W, dbarForm g J z = 0) :
    ∃ W' : σ → Set ℂ, (∀ i, IsOpen (W' i)) ∧ x ∈ univ.pi W' ∧ (∀ i, W' i ⊆ W i) ∧
      ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ univ.pi W', IsSmoothFormAt u z) ∧
        (∀ I, I.card ≠ q → u I = 0) ∧ ∀ J, ∀ z ∈ univ.pi W', dbarForm u J z = g J z := by
  obtain ⟨W', hW'o, hxW', hW'W, u, hu⟩ := exists_dbarForm_eq_near_compact hW
    (K := fun i ↦ {x i}) (fun _ ↦ isCompact_singleton)
    (fun i ↦ singleton_subset_iff.mpr (hx i (mem_univ i))) hgs hdeg hcl
  exact ⟨W', hW'o, fun i _ ↦ hxW' i rfl, hW'W, u, hu⟩

/-- **Dolbeault–Grothendieck lemma on an open set**: a smooth `∂̄`-closed `(0, q + 1)`-form on an
open set `V ⊆ ℂ^σ` is, near every point `x ∈ V`, `∂̄` of a smooth `(0, q)`-form: there is an open
`V'` with `x ∈ V' ⊆ V` (a product of open subsets of `ℂ`) on which `g = ∂̄u`. -/
theorem exists_dbarForm_eq_near_of_isOpen {V : Set (σ → ℂ)} (hV : IsOpen V) {x : σ → ℂ}
    (hx : x ∈ V) {q : ℕ} {g : Finset σ → (σ → ℂ) → ℂ}
    (hgs : ∀ z ∈ V, IsSmoothFormAt g z)
    (hdeg : ∀ J, J.card ≠ q + 1 → ∀ z ∈ V, g J z = 0)
    (hcl : ∀ J, ∀ z ∈ V, dbarForm g J z = 0) :
    ∃ V' : Set (σ → ℂ), IsOpen V' ∧ x ∈ V' ∧ V' ⊆ V ∧
      ∃ u : Finset σ → (σ → ℂ) → ℂ, (∀ z ∈ V', IsSmoothFormAt u z) ∧
        (∀ I, I.card ≠ q → u I = 0) ∧ ∀ J, ∀ z ∈ V', dbarForm u J z = g J z := by
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV x hx
  have hball : ball x r = univ.pi fun i ↦ ball (x i) r := ball_pi x hr
  have hWV : univ.pi (fun i ↦ ball (x i) r) ⊆ V := hball ▸ hrV
  obtain ⟨W', hW'o, hxW', hW'W, u, hus, hudeg, hu⟩ := exists_dbarForm_eq_near
    (W := fun i ↦ ball (x i) r) (fun _ ↦ isOpen_ball) (hball ▸ mem_ball_self hr)
    (fun z hz ↦ hgs z (hWV hz)) (fun J hJ z hz ↦ hdeg J hJ z (hWV hz))
    (fun J z hz ↦ hcl J z (hWV hz))
  exact ⟨univ.pi W', isOpen_univ_pi hW'o, hxW', fun z hz ↦ hWV fun i _ ↦ hW'W i (hz i (mem_univ i)),
    u, hus, hudeg, hu⟩

end Local

end AnalyticGeometry
