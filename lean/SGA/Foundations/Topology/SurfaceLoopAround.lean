/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Analysis.Complex.Convex
import SGA.Foundations.Topology.SurfaceGenusZero

/-!
# Loops winding once around a point of the plane

Let `C ⊆ ℂ` be convex and open, `s ∈ C`, and `j : Y → ℂ` an embedding onto `C ∖ {s}`. A loop
`γ` in `Y` *winds once around `s`* (`Path.WindsOnceAround`) if `j ∘ γ - s` has a continuous
logarithm along `γ` that increases by `2πi`. We show:

* two loops at the same base point that wind once around `s` are homotopic
  (`Path.WindsOnceAround.homotopic`);
* a loop around `s` in the sense of `FundamentalGroup.IsLoopAround` (conjugate to a small circle)
  winds once around `s` (`FundamentalGroup.IsLoopAround.exists_windsOnceAround`), and conversely
  (`Path.WindsOnceAround.isLoopAround`);
* hence two loops around `s` at the same base point are equal (`FundamentalGroup.IsLoopAround.eq`),
  and a loop around `s` is a free generator of `π₁(Y, y) ≅ ℤ`
  (`FundamentalGroup.IsLoopAround.existsUnique_hom`);
* a quadrilateral run counterclockwise around `s` (`s` strictly to the left of every edge) minus
  `s` has a continuous logarithm increasing by `2πi` (`Complex.exists_log_quadPath`), so it winds
  once around `s` in the sense of `Path.WindsOnceAround`.

The last point is how explicit loops (sides of rectangles) are recognized as loops around a point
without any winding-number theory: the logarithm along each edge is `log` of a ratio in the upper
half-plane, and the four arguments, each in `(0, π)`, add up to a multiple of `2π`, hence to `2π`.

## References

* [A. Hatcher, *Algebraic Topology*, §1.1][hatcher02]
-/

open Set Topology CategoryTheory Metric Real

noncomputable section

namespace Path

variable {Y Y' : Type*} [TopologicalSpace Y] [TopologicalSpace Y']

/-- A loop `γ` in `Y` *winds once around `s`* (relative to `j : Y → ℂ`) if `j ∘ γ - s` has a
continuous logarithm `Λ` (`s + exp (Λ t) = j (γ t)`) with `Λ 1 = Λ 0 + 2πi`. -/
def WindsOnceAround (j : Y → ℂ) (s : ℂ) {y : Y} (γ : Path y y) : Prop :=
  ∃ Λ : C(unitInterval, ℂ), (∀ t, s + Complex.exp (Λ t) = j (γ t)) ∧
    Λ 1 = Λ 0 + 2 * π * Complex.I

/-- A loop `γ` in `Y` *winds `k` times around `s`* (relative to `j : Y → ℂ`) if `j ∘ γ - s` has a
continuous logarithm `Λ` (`s + exp (Λ t) = j (γ t)`) with `Λ 1 = Λ 0 + 2πik`. -/
def WindsAround (j : Y → ℂ) (s : ℂ) (k : ℤ) {y : Y} (γ : Path y y) : Prop :=
  ∃ Λ : C(unitInterval, ℂ), (∀ t, s + Complex.exp (Λ t) = j (γ t)) ∧
    Λ 1 = Λ 0 + 2 * π * Complex.I * k

lemma WindsOnceAround.windsAround {j : Y → ℂ} {s : ℂ} {y : Y} {γ : Path y y}
    (h : γ.WindsOnceAround j s) : γ.WindsAround j s 1 := by
  obtain ⟨Λ, hΛ, hΛ'⟩ := h
  exact ⟨Λ, hΛ, by rw [hΛ']; push_cast; ring⟩

lemma WindsAround.windsOnceAround {j : Y → ℂ} {s : ℂ} {y : Y} {γ : Path y y}
    (h : γ.WindsAround j s 1) : γ.WindsOnceAround j s := by
  obtain ⟨Λ, hΛ, hΛ'⟩ := h
  exact ⟨Λ, hΛ, by rw [hΛ']; push_cast; ring⟩

/-- Winding once is preserved by maps compatible with the maps to `ℂ`. -/
lemma WindsOnceAround.map {j : Y → ℂ} {j' : Y' → ℂ} {s : ℂ} {y : Y} {γ : Path y y}
    (h : γ.WindsOnceAround j s) (f : C(Y, Y')) (hf : ∀ x, j' (f x) = j x) :
    (γ.map f.continuous).WindsOnceAround j' s := by
  obtain ⟨Λ, hΛ, hΛ'⟩ := h
  exact ⟨Λ, fun t ↦ (hΛ t).trans (hf _).symm, hΛ'⟩

/-- Pointwise compatibility of two paths is compatible with concatenation. -/
lemma trans_apply_compat {Z Z' W : Type*} [TopologicalSpace Z] [TopologicalSpace Z'] {f : Z → W}
    {g : Z' → W} {a b c : Z} {a' b' c' : Z'} {p : Path a b} {q : Path b c} {p' : Path a' b'}
    {q' : Path b' c'} (hp : ∀ t, f (p t) = g (p' t)) (hq : ∀ t, f (q t) = g (q' t))
    (t : unitInterval) :
    f ((p.trans q) t) = g ((p'.trans q') t) := by
  rw [Path.trans_apply, Path.trans_apply]
  split_ifs
  · exact hp _
  · exact hq _

end Path

namespace Topology.IsEmbedding

variable {Y Y' Z : Type*} [TopologicalSpace Y] [TopologicalSpace Y'] [TopologicalSpace Z]
  {j : Y → Z} (hj : IsEmbedding j)

/-- A path in `Z` inside the range of the embedding `j`, as a path in `Y` (between given points
over its endpoints). -/
def liftPath {a b : Z} (γ : Path a b) (h : ∀ t, γ t ∈ range j) {ya yb : Y} (ha : j ya = a)
    (hb : j yb = b) : Path ya yb where
  toFun t := hj.toHomeomorph.symm ⟨γ t, h t⟩
  continuous_toFun := by fun_prop
  source' := hj.injective ((congrArg Subtype.val
    (hj.toHomeomorph.apply_symm_apply ⟨γ 0, h 0⟩)).trans (γ.source.trans ha.symm))
  target' := hj.injective ((congrArg Subtype.val
    (hj.toHomeomorph.apply_symm_apply ⟨γ 1, h 1⟩)).trans (γ.target.trans hb.symm))

lemma apply_liftPath {a b : Z} (γ : Path a b) (h : ∀ t, γ t ∈ range j) {ya yb : Y}
    (ha : j ya = a) (hb : j yb = b) (t : unitInterval) : j (hj.liftPath γ h ha hb t) = γ t :=
  congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply ⟨γ t, h t⟩)

include hj in
/-- Paths in `Y` are determined by their images in `Z`. -/
lemma path_ext {ya yb : Y} {p q : Path ya yb} (h : ∀ t, j (p t) = j (q t)) : p = q :=
  Path.ext (funext fun t ↦ hj.injective (h t))

lemma liftPath_trans {a b c : Z} (γ : Path a b) (γ' : Path b c) (h : ∀ t, (γ.trans γ') t ∈ range j)
    (h₁ : ∀ t, γ t ∈ range j) (h₂ : ∀ t, γ' t ∈ range j) {ya yb yc : Y} (ha : j ya = a)
    (hb : j yb = b) (hc : j yc = c) :
    hj.liftPath (γ.trans γ') h ha hc = (hj.liftPath γ h₁ ha hb).trans (hj.liftPath γ' h₂ hb hc) :=
  hj.path_ext fun t ↦ by
    rw [hj.apply_liftPath]
    exact Path.trans_apply_compat (f := id) (g := j) (fun t ↦ (hj.apply_liftPath ..).symm)
      (fun t ↦ (hj.apply_liftPath ..).symm) t

lemma liftPath_symm {a b : Z} (γ : Path a b) (h : ∀ t, γ t ∈ range j) (h' : ∀ t, γ.symm t ∈ range j)
    {ya yb : Y} (ha : j ya = a) (hb : j yb = b) :
    hj.liftPath γ.symm h' hb ha = (hj.liftPath γ h ha hb).symm :=
  hj.path_ext fun t ↦ by
    rw [hj.apply_liftPath]
    change γ (unitInterval.symm t) = j (hj.liftPath γ h ha hb (unitInterval.symm t))
    rw [hj.apply_liftPath]

/-- Lifting is compatible with maps over `Z`. -/
lemma map_liftPath {j' : Y' → Z} (hj' : IsEmbedding j') (f : C(Y', Y)) (hf : ∀ y, j (f y) = j' y)
    {a b : Z} (γ : Path a b) (h' : ∀ t, γ t ∈ range j') (h : ∀ t, γ t ∈ range j) {ya yb : Y'}
    (ha : j' ya = a) (hb : j' yb = b) :
    (hj'.liftPath γ h' ha hb).map f.continuous =
      hj.liftPath γ h ((hf ya).trans ha) ((hf yb).trans hb) :=
  hj.path_ext fun t ↦ by
    rw [Path.map_coe, Function.comp_apply, hf, hj.apply_liftPath, hj'.apply_liftPath]

end Topology.IsEmbedding

namespace Topology.IsEmbedding

variable {Y : Type*} [TopologicalSpace Y]

/-- Two paths with the same endpoints in a convex subset of `range j` lift to homotopic paths. -/
lemma liftPath_homotopic_of_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {j : Y → E} (hj : IsEmbedding j) {K : Set E} (hK : Convex ℝ K) (hKj : K ⊆ range j)
    {a b : E} (γ γ' : Path a b) (hγ : ∀ t, γ t ∈ K) (hγ' : ∀ t, γ' t ∈ K) {ya yb : Y}
    (ha : j ya = a) (hb : j yb = b) :
    (hj.liftPath γ (fun t ↦ hKj (hγ t)) ha hb).Homotopic
      (hj.liftPath γ' (fun t ↦ hKj (hγ' t)) ha hb) := by
  have hKne : K.Nonempty := ⟨_, hγ 0⟩
  have : ContractibleSpace K := hK.contractibleSpace hKne
  have hr : range γ ⊆ K := by rintro _ ⟨t, rfl⟩; exact hγ t
  have hr' : range γ' ⊆ K := by rintro _ ⟨t, rfl⟩; exact hγ' t
  let f : C(K, Y) := ⟨fun z ↦ hj.toHomeomorph.symm ⟨z, hKj z.2⟩, by fun_prop⟩
  have hf (z : K) : j (f z) = z := congrArg Subtype.val (hj.toHomeomorph.apply_symm_apply _)
  have hH := (SimplyConnectedSpace.paths_homotopic (γ.codRestrict hr) (γ'.codRestrict hr')).map f
  have e₁ : hj.liftPath γ (fun t ↦ hKj (hγ t)) ha hb =
      ((γ.codRestrict hr).map f.continuous).cast
        (hj.injective (by rw [ha, hf]))
        (hj.injective (by rw [hb, hf])) :=
    hj.path_ext fun t ↦ by
      rw [hj.apply_liftPath]
      exact (hf (γ.codRestrict hr t)).symm
  have e₂ : hj.liftPath γ' (fun t ↦ hKj (hγ' t)) ha hb =
      ((γ'.codRestrict hr').map f.continuous).cast
        (hj.injective (by rw [ha, hf]))
        (hj.injective (by rw [hb, hf])) :=
    hj.path_ext fun t ↦ by
      rw [hj.apply_liftPath]
      exact (hf (γ'.codRestrict hr' t)).symm
  rw [e₁, e₂, ← Path.Homotopic.Quotient.eq, Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.eq.mpr hH]

end Topology.IsEmbedding

namespace FundamentalGroup

variable {Y : Type*} [TopologicalSpace Y] {C : Set ℂ} {s : ℂ} {j : Y → ℂ}

open Complex

section

variable (hCc : Convex ℝ C) (hCo : IsOpen C) (hs : s ∈ C) (hj : IsEmbedding j)
  (hjr : range j = C \ {s})

/-- The inverse of `j`, as a homeomorphism `C ∖ {s} ≃ₜ Y`. -/
private def invHomeomorph : ↥(C \ {s}) ≃ₜ Y :=
  (hj.toHomeomorph.trans (Homeomorph.setCongr hjr)).symm

include hjr in
private lemma j_invHomeomorph (z : ↥(C \ {s})) : j (invHomeomorph hj hjr z) = z := by
  have h := (hj.toHomeomorph.trans (Homeomorph.setCongr hjr)).apply_symm_apply z
  exact congrArg Subtype.val h

/-- The continuous map `exp⁻¹(C - s) → Y`, `w ↦ j⁻¹(s + exp w)`. -/
private def expMap : C({w : ℂ | s + exp w ∈ C}, Y) :=
  ⟨fun w ↦ invHomeomorph hj hjr ⟨s + exp w, w.2, by simp [Complex.exp_ne_zero]⟩, by fun_prop⟩

include hjr in
private lemma j_expMap (w : {w : ℂ | s + exp w ∈ C}) : j (expMap hj hjr w) = s + exp w :=
  j_invHomeomorph hj hjr _

include hCc hCo hs hj hjr in
/-- `Y ≅ C ∖ {s}` is path-connected. -/
lemma pathConnectedSpace_of_range_eq_diff_singleton : PathConnectedSpace Y := by
  have : SimplyConnectedSpace {w : ℂ | s + exp w ∈ C} :=
    (isSimplyConnected_setOf_add_exp_mem hCc hCo hs).simplyConnectedSpace
  refine Function.Surjective.pathConnectedSpace (f := expMap hj hjr) (fun y ↦ ?_)
    (expMap hj hjr).continuous
  have hy : j y ∈ C \ {s} := by rw [← hjr]; exact mem_range_self y
  have hne : j y - s ≠ 0 := sub_ne_zero.mpr hy.2
  refine ⟨⟨log (j y - s), by simp [exp_log hne, hy.1]⟩, hj.injective ?_⟩
  rw [j_expMap hj hjr]
  simp [exp_log hne]

include hCc hCo hs hj hjr in
/-- **Two loops winding once around `s` are homotopic.** Their logarithms, after a translation
by a multiple of `2πi`, are paths with the same endpoints in the simply connected
`exp⁻¹(C - s)`. -/
theorem _root_.Path.WindsOnceAround.homotopic {y : Y} {γ₁ γ₂ : Path y y}
    (h₁ : γ₁.WindsOnceAround j s) (h₂ : γ₂.WindsOnceAround j s) : γ₁.Homotopic γ₂ := by
  obtain ⟨Λ₁, hΛ₁, hΛ₁'⟩ := h₁
  obtain ⟨Λ₂, hΛ₂, hΛ₂'⟩ := h₂
  have : SimplyConnectedSpace {w : ℂ | s + exp w ∈ C} :=
    (isSimplyConnected_setOf_add_exp_mem hCc hCo hs).simplyConnectedSpace
  have hmemC (γ : Path y y) (t : unitInterval) : j (γ t) ∈ C :=
    (hjr ▸ mem_range_self (γ t) : j (γ t) ∈ C \ {s}).1
  set c := Λ₁ 0 - Λ₂ 0
  have hc : exp c = 1 := by
    have h1 := hΛ₁ 0
    have h2 := hΛ₂ 0
    rw [γ₁.source] at h1
    rw [γ₂.source] at h2
    rw [Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero _)]
    linear_combination h1 - h2
  have hm₁ (t : unitInterval) : Λ₁ t ∈ {w : ℂ | s + exp w ∈ C} := by
    change s + exp (Λ₁ t) ∈ C
    rw [hΛ₁]
    exact hmemC γ₁ t
  have hm₂ (t : unitInterval) : Λ₂ t + c ∈ {w : ℂ | s + exp w ∈ C} := by
    change s + exp (Λ₂ t + c) ∈ C
    rw [Complex.exp_add, hc, mul_one, hΛ₂]
    exact hmemC γ₂ t
  have he₂ : Λ₂ 1 + c = Λ₁ 1 := by rw [hΛ₂', hΛ₁']; ring
  let P₁ : Path (⟨Λ₁ 0, hm₁ 0⟩ : {w : ℂ | s + exp w ∈ C}) ⟨Λ₁ 1, hm₁ 1⟩ :=
    { toFun t := ⟨Λ₁ t, hm₁ t⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let P₂ : Path (⟨Λ₁ 0, hm₁ 0⟩ : {w : ℂ | s + exp w ∈ C}) ⟨Λ₁ 1, hm₁ 1⟩ :=
    { toFun t := ⟨Λ₂ t + c, hm₂ t⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp [c]
      target' := by ext; exact he₂ }
  have hP := (SimplyConnectedSpace.paths_homotopic P₁ P₂).map (expMap hj hjr)
  have hy₀ : y = expMap hj hjr ⟨Λ₁ 0, hm₁ 0⟩ := hj.injective (by
    rw [j_expMap hj hjr]
    change j y = s + exp (Λ₁ 0)
    rw [hΛ₁, γ₁.source])
  have hy₁ : y = expMap hj hjr ⟨Λ₁ 1, hm₁ 1⟩ := hj.injective (by
    rw [j_expMap hj hjr]
    change j y = s + exp (Λ₁ 1)
    rw [hΛ₁, γ₁.target])
  have e₁ : γ₁ = (P₁.map (expMap hj hjr).continuous).cast hy₀ hy₁ :=
    Path.ext (funext fun t ↦ hj.injective (by
      change j (γ₁ t) = j (expMap hj hjr ⟨Λ₁ t, hm₁ t⟩)
      rw [j_expMap hj hjr, hΛ₁]))
  have e₂ : γ₂ = (P₂.map (expMap hj hjr).continuous).cast hy₀ hy₁ :=
    Path.ext (funext fun t ↦ hj.injective (by
      change j (γ₂ t) = j (expMap hj hjr ⟨Λ₂ t + c, hm₂ t⟩)
      rw [j_expMap hj hjr, Complex.exp_add, hc, mul_one, hΛ₂]))
  rw [← Path.Homotopic.Quotient.eq, e₁, e₂, Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.eq.mpr hP]

include hCc hCo hs hj hjr in
/-- **Two loops winding `k` times around `s` are homotopic.** Their logarithms, after a
translation by a multiple of `2πi`, are paths with the same endpoints in the simply connected
`exp⁻¹(C - s)`. -/
theorem _root_.Path.WindsAround.homotopic {k : ℤ} {y : Y} {γ₁ γ₂ : Path y y}
    (h₁ : γ₁.WindsAround j s k) (h₂ : γ₂.WindsAround j s k) : γ₁.Homotopic γ₂ := by
  obtain ⟨Λ₁, hΛ₁, hΛ₁'⟩ := h₁
  obtain ⟨Λ₂, hΛ₂, hΛ₂'⟩ := h₂
  have : SimplyConnectedSpace {w : ℂ | s + exp w ∈ C} :=
    (isSimplyConnected_setOf_add_exp_mem hCc hCo hs).simplyConnectedSpace
  have hmemC (γ : Path y y) (t : unitInterval) : j (γ t) ∈ C :=
    (hjr ▸ mem_range_self (γ t) : j (γ t) ∈ C \ {s}).1
  set c := Λ₁ 0 - Λ₂ 0
  have hc : exp c = 1 := by
    have h1 := hΛ₁ 0
    have h2 := hΛ₂ 0
    rw [γ₁.source] at h1
    rw [γ₂.source] at h2
    rw [Complex.exp_sub, div_eq_one_iff_eq (Complex.exp_ne_zero _)]
    linear_combination h1 - h2
  have hm₁ (t : unitInterval) : Λ₁ t ∈ {w : ℂ | s + exp w ∈ C} := by
    change s + exp (Λ₁ t) ∈ C
    rw [hΛ₁]
    exact hmemC γ₁ t
  have hm₂ (t : unitInterval) : Λ₂ t + c ∈ {w : ℂ | s + exp w ∈ C} := by
    change s + exp (Λ₂ t + c) ∈ C
    rw [Complex.exp_add, hc, mul_one, hΛ₂]
    exact hmemC γ₂ t
  have he₂ : Λ₂ 1 + c = Λ₁ 1 := by rw [hΛ₂', hΛ₁']; ring
  let P₁ : Path (⟨Λ₁ 0, hm₁ 0⟩ : {w : ℂ | s + exp w ∈ C}) ⟨Λ₁ 1, hm₁ 1⟩ :=
    { toFun t := ⟨Λ₁ t, hm₁ t⟩
      continuous_toFun := by fun_prop
      source' := rfl
      target' := rfl }
  let P₂ : Path (⟨Λ₁ 0, hm₁ 0⟩ : {w : ℂ | s + exp w ∈ C}) ⟨Λ₁ 1, hm₁ 1⟩ :=
    { toFun t := ⟨Λ₂ t + c, hm₂ t⟩
      continuous_toFun := by fun_prop
      source' := by ext; simp [c]
      target' := by ext; exact he₂ }
  have hP := (SimplyConnectedSpace.paths_homotopic P₁ P₂).map (expMap hj hjr)
  have hy₀ : y = expMap hj hjr ⟨Λ₁ 0, hm₁ 0⟩ := hj.injective (by
    rw [j_expMap hj hjr]
    change j y = s + exp (Λ₁ 0)
    rw [hΛ₁, γ₁.source])
  have hy₁ : y = expMap hj hjr ⟨Λ₁ 1, hm₁ 1⟩ := hj.injective (by
    rw [j_expMap hj hjr]
    change j y = s + exp (Λ₁ 1)
    rw [hΛ₁, γ₁.target])
  have e₁ : γ₁ = (P₁.map (expMap hj hjr).continuous).cast hy₀ hy₁ :=
    Path.ext (funext fun t ↦ hj.injective (by
      change j (γ₁ t) = j (expMap hj hjr ⟨Λ₁ t, hm₁ t⟩)
      rw [j_expMap hj hjr, hΛ₁]))
  have e₂ : γ₂ = (P₂.map (expMap hj hjr).continuous).cast hy₀ hy₁ :=
    Path.ext (funext fun t ↦ hj.injective (by
      change j (γ₂ t) = j (expMap hj hjr ⟨Λ₂ t + c, hm₂ t⟩)
      rw [j_expMap hj hjr, Complex.exp_add, hc, mul_one, hΛ₂]))
  rw [← Path.Homotopic.Quotient.eq, e₁, e₂, Path.Homotopic.Quotient.mk_cast,
    Path.Homotopic.Quotient.mk_cast, Path.Homotopic.Quotient.eq.mpr hP]

end

/-- **A loop around `s` winds once around `s`.** If `j` misses `s`, every loop around `s` (in the
sense of `IsLoopAround`: a path `δ`, a small circle, `δ` backwards) has a representative with a
continuous logarithm increasing by `2πi`: lift `δ` through `exp`, follow the circle, and come back
along the lift of `δ` translated by `2πi`. -/
theorem IsLoopAround.exists_windsOnceAround (hjc : Continuous j) (hjs : ∀ x, j x ≠ s) {y : Y}
    {σ : FundamentalGroup Y y} (h : IsLoopAround j s σ) :
    ∃ γ : Path y y, σ = Path.Homotopic.Quotient.mk γ ∧ γ.WindsOnceAround j s := by
  obtain ⟨r, hr, κ, hκ, δ, rfl⟩ := h
  set c := ((circlePath s r).codRestrict (range_circlePath_subset hr)).map κ.continuous
  refine ⟨(δ.trans c).trans δ.symm, rfl, ?_⟩
  let δ' : C(unitInterval, {z : ℂ // z ≠ 0}) :=
    ⟨fun t ↦ ⟨j (δ t) - s, sub_ne_zero.mpr (hjs _)⟩, by fun_prop⟩
  have hy : j y - s ≠ 0 := sub_ne_zero.mpr (hjs y)
  have h0 : δ' 0 = ⟨exp (log (j y - s)), Complex.exp_ne_zero _⟩ :=
    Subtype.ext (by simp [δ', exp_log hy])
  set Γ := isCoveringMap_exp.liftPath δ' (log (j y - s)) h0
  have hΓ (t : unitInterval) : exp (Γ t) = j (δ t) - s :=
    congrArg Subtype.val (congrFun (isCoveringMap_exp.liftPath_lifts δ' _ h0) t)
  have hδ1 : j (δ 1) = s + r := by
    rw [δ.target, hκ]
  let P₁ : Path (Γ 0) (Γ 1) := ⟨Γ, rfl, rfl⟩
  let P₂ : Path (Γ 1) (Γ 1 + 2 * π * I) :=
    { toFun t := Γ 1 + 2 * π * I * (t : ℝ)
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  let P₃ : Path (Γ 1 + 2 * π * I) (Γ 0 + 2 * π * I) :=
    { toFun t := Γ (unitInterval.symm t) + 2 * π * I
      continuous_toFun := by fun_prop
      source' := by simp
      target' := by simp }
  refine ⟨((P₁.trans P₂).trans P₃).toContinuousMap, fun t ↦ ?_, ?_⟩
  · refine Path.trans_apply_compat (f := fun w ↦ s + Complex.exp w) (g := j)
      (Path.trans_apply_compat (f := fun w ↦ s + Complex.exp w) (g := j) (fun t ↦ ?_)
        (fun t ↦ ?_))
      (fun t ↦ ?_) t
    · change s + exp (Γ t) = j (δ t)
      rw [hΓ]
      ring
    · change s + exp (Γ 1 + 2 * π * I * (t : ℝ)) = j (κ _)
      rw [hκ, Complex.exp_add, hΓ, hδ1]
      change _ = circlePath s r t
      rw [circlePath_apply]
      ring
    · change s + exp (Γ (unitInterval.symm t) + 2 * π * I) = j (δ (unitInterval.symm t))
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, hΓ]
      ring
  · change ((P₁.trans P₂).trans P₃) 1 = ((P₁.trans P₂).trans P₃) 0 + 2 * π * I
    rw [Path.target, Path.source]

section

variable (hCc : Convex ℝ C) (hCo : IsOpen C) (hs : s ∈ C) (hj : IsEmbedding j)
  (hjr : range j = C \ {s})
include hCc hCo hs hj hjr

omit [TopologicalSpace Y] hCc hCo hs hj in
private lemma ne_of_range_eq (x : Y) : j x ≠ s :=
  (hjr ▸ mem_range_self x : j x ∈ C \ {s}).2

/-- **Two loops around `s` at the same base point are equal** (for `j` an embedding onto
`C ∖ {s}`, `C` convex and open). -/
theorem IsLoopAround.eq {y : Y} {σ σ' : FundamentalGroup Y y} (h : IsLoopAround j s σ)
    (h' : IsLoopAround j s σ') : σ = σ' := by
  obtain ⟨γ, rfl, hγ⟩ := h.exists_windsOnceAround hj.continuous (ne_of_range_eq hjr)
  obtain ⟨γ', rfl, hγ'⟩ :=
    h'.exists_windsOnceAround hj.continuous (ne_of_range_eq hjr)
  exact Path.Homotopic.Quotient.eq.mpr (hγ.homotopic hCc hCo hs hj hjr hγ')

/-- **A loop winding once around `s` is a loop around `s`** (for `j` an embedding onto
`C ∖ {s}`, `C` convex and open). -/
theorem _root_.Path.WindsOnceAround.isLoopAround {y : Y} {γ : Path y y}
    (h : γ.WindsOnceAround j s) :
    IsLoopAround j s (Path.Homotopic.Quotient.mk γ : FundamentalGroup Y y) := by
  have : PathConnectedSpace Y := pathConnectedSpace_of_range_eq_diff_singleton hCc hCo hs hj hjr
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp hCo s hs
  set r := r₀ / 2
  have hr : 0 < r := half_pos hr₀
  have hdisc : closedBall s r ⊆ C := (closedBall_subset_ball (half_lt_self hr₀)).trans hball
  let κ : C(↥(closedBall s r \ {s}), Y) :=
    ⟨fun z ↦ invHomeomorph hj hjr ⟨z, hdisc z.2.1, z.2.2⟩, by fun_prop⟩
  have hκ (z : ↥(closedBall s r \ {s})) : j (κ z) = z := j_invHomeomorph hj hjr _
  let δ := PathConnectedSpace.somePath y (κ ⟨s + r, add_ofReal_mem_closedBall_diff hr⟩)
  have h₀ : IsLoopAround j s (Path.Homotopic.Quotient.mk ((δ.trans
      (((circlePath s r).codRestrict (range_circlePath_subset hr)).map κ.continuous)).trans
      δ.symm) : FundamentalGroup Y y) := ⟨r, hr, κ, hκ, δ, rfl⟩
  obtain ⟨γ₀, hγ₀, hw⟩ :=
    h₀.exists_windsOnceAround hj.continuous (ne_of_range_eq hjr)
  rw [Path.Homotopic.Quotient.eq.mpr (h.homotopic hCc hCo hs hj hjr hw), ← hγ₀]
  exact h₀

end

/-- **A loop around `s` freely generates `π₁(Y, y) ≅ ℤ`** (for `j` an open embedding onto
`C ∖ {s}`, `C` convex and open): homomorphisms from `π₁(Y, y)` are determined by the image of
`σ`, which is arbitrary. -/
theorem IsLoopAround.existsUnique_hom {Y : Type} [TopologicalSpace Y] {j : Y → ℂ}
    (hCc : Convex ℝ C) (hCo : IsOpen C) (hs : s ∈ C) (hj : IsOpenEmbedding j)
    (hjr : range j = C \ {s}) {y : Y} {σ : FundamentalGroup Y y} (h : IsLoopAround j s σ)
    {H : Type*} [Group H] (g : H) : ∃! φ : FundamentalGroup Y y →* H, φ σ = g := by
  obtain ⟨b, hb⟩ := exists_freeGroupBasis_fundamentalGroup_of_isOpenEmbedding (S := {s}) hCc hCo
    (by simpa using hs) hj (by simpa using hjr) y
  have hσ : b ⟨s, Finset.mem_singleton_self s⟩ = σ :=
    IsLoopAround.eq hCc hCo hs hj.isEmbedding hjr (hb ⟨s, Finset.mem_singleton_self s⟩) h
  have key (i : ({s} : Finset ℂ)) : b.lift (fun _ ↦ g) (b i) = g :=
    congrFun (b.lift.symm_apply_apply fun _ ↦ g) i
  refine ⟨b.lift fun _ ↦ g, hσ ▸ key _, fun φ hφ ↦ b.ext_hom _ _ fun t ↦ ?_⟩
  have ht : t = ⟨s, Finset.mem_singleton_self s⟩ := Subtype.ext (Finset.mem_singleton.mp t.2)
  rw [ht, hσ, hφ, ← hσ, key]

end FundamentalGroup

namespace Complex

/-- The straight path from `a` to `b` in `ℂ`: mathlib's `Path.segment`, named here for its
formula `segmentPath_apply`. -/
abbrev segmentPath (a b : ℂ) : Path a b := Path.segment a b

lemma segmentPath_apply (a b : ℂ) (t : unitInterval) :
    segmentPath a b t = a + (t : ℝ) * (b - a) := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module', Complex.real_smul]
  ring

/-- The segment path runs in the segment (`Path.range_segment`). -/
lemma segmentPath_mem_segment (a b : ℂ) (t : unitInterval) :
    segmentPath a b t ∈ segment ℝ a b :=
  Path.range_segment a b ▸ mem_range_self t

/-- A segment path lies in every convex set containing its endpoints. -/
lemma segmentPath_mem {K : Set ℂ} (hK : Convex ℝ K) {a b : ℂ} (ha : a ∈ K) (hb : b ∈ K)
    (t : unitInterval) : segmentPath a b t ∈ K :=
  hK.segment_subset ha hb (segmentPath_mem_segment a b t)

private lemma one_add_mul_mem_slitPlane {ρ : ℂ} (hρ : ρ ∈ slitPlane) (t : unitInterval) :
    1 + (t : ℝ) * (ρ - 1) ∈ slitPlane := by
  have h := StarConvex.add_smul_mem starConvex_one_slitPlane (y := ρ - 1)
    (by rwa [add_sub_cancel]) t.2.1 t.2.2
  rwa [Complex.real_smul] at h

/-- A logarithm of `segmentPath a b - s` starting at `L`, for `(b - s) / (a - s)` in the slit
plane: `t ↦ L + log (1 + t ((b - s) / (a - s) - 1))`. -/
def segmentLog (s a b L : ℂ) (h : (b - s) / (a - s) ∈ slitPlane) :
    Path L (L + log ((b - s) / (a - s))) where
  toFun t := L + log (1 + (t : ℝ) * ((b - s) / (a - s) - 1))
  continuous_toFun := continuous_iff_continuousAt.mpr fun t ↦
    continuousAt_const.add (ContinuousAt.comp (g := log)
      (continuousAt_clog (one_add_mul_mem_slitPlane h t))
      (by fun_prop : ContinuousAt (fun t : unitInterval ↦ 1 + (t : ℝ) * ((b - s) / (a - s) - 1)) t))
  source' := by simp
  target' := by simp

lemma segmentLog_apply (s a b L : ℂ) (h : (b - s) / (a - s) ∈ slitPlane) (t : unitInterval) :
    segmentLog s a b L h t = L + log (1 + (t : ℝ) * ((b - s) / (a - s) - 1)) :=
  rfl

/-- `segmentLog` is a logarithm of `segmentPath a b - s`. -/
lemma add_exp_segmentLog {s a b L : ℂ} (h : (b - s) / (a - s) ∈ slitPlane)
    (hL : exp L = a - s) (t : unitInterval) :
    s + exp (segmentLog s a b L h t) = segmentPath a b t := by
  have has : a - s ≠ 0 := by
    intro h0
    rw [h0, div_zero] at h
    exact slitPlane_ne_zero h rfl
  rw [segmentLog_apply, Complex.exp_add, exp_log (slitPlane_ne_zero
    (one_add_mul_mem_slitPlane h t)), hL, segmentPath_apply]
  field_simp
  ring

/-- The closed polygon `v₀ → v₁ → v₂ → v₃ → v₀`. -/
def quadPath (v₀ v₁ v₂ v₃ : ℂ) : Path v₀ v₀ :=
  (((segmentPath v₀ v₁).trans (segmentPath v₁ v₂)).trans (segmentPath v₂ v₃)).trans
    (segmentPath v₃ v₀)

private lemma arg_pos_of_im_pos {z : ℂ} (hz : 0 < z.im) : 0 < arg z :=
  lt_of_le_of_ne (arg_nonneg_iff.mpr hz.le) fun h ↦ hz.ne' (arg_eq_zero_iff.mp h.symm).2

private lemma ne_of_im_div_pos {a b s : ℂ} (h : 0 < ((b - s) / (a - s)).im) : a - s ≠ 0 := by
  intro h0
  rw [h0, div_zero, zero_im] at h
  exact lt_irrefl _ h

private lemma mem_slitPlane_of_im_pos {z : ℂ} (hz : 0 < z.im) : z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inr hz.ne')

/-- **A quadrilateral around `s`, run counterclockwise, winds once around `s`**: if `s` lies
strictly to the left of each edge `vᵢ → vᵢ₊₁` (that is, `(vᵢ₊₁ - s) / (vᵢ - s)` has positive
imaginary part), then `quadPath v₀ v₁ v₂ v₃ - s` has a continuous logarithm increasing by `2πi`. -/
theorem exists_log_quadPath {s v₀ v₁ v₂ v₃ : ℂ} (h₀ : 0 < ((v₁ - s) / (v₀ - s)).im)
    (h₁ : 0 < ((v₂ - s) / (v₁ - s)).im) (h₂ : 0 < ((v₃ - s) / (v₂ - s)).im)
    (h₃ : 0 < ((v₀ - s) / (v₃ - s)).im) :
    ∃ Λ : C(unitInterval, ℂ), (∀ t, s + exp (Λ t) = quadPath v₀ v₁ v₂ v₃ t) ∧
      Λ 1 = Λ 0 + 2 * π * I := by
  have n₀ := ne_of_im_div_pos h₀
  have n₁ := ne_of_im_div_pos h₁
  have n₂ := ne_of_im_div_pos h₂
  have n₃ := ne_of_im_div_pos h₃
  set ρ₀ := (v₁ - s) / (v₀ - s)
  set ρ₁ := (v₂ - s) / (v₁ - s)
  set ρ₂ := (v₃ - s) / (v₂ - s)
  set ρ₃ := (v₀ - s) / (v₃ - s)
  set L₀ := log (v₀ - s)
  have e₀ : exp L₀ = v₀ - s := exp_log n₀
  let P₀ := segmentLog s v₀ v₁ L₀ (mem_slitPlane_of_im_pos h₀)
  let P₁ := segmentLog s v₁ v₂ (L₀ + log ρ₀) (mem_slitPlane_of_im_pos h₁)
  let P₂ := segmentLog s v₂ v₃ (L₀ + log ρ₀ + log ρ₁) (mem_slitPlane_of_im_pos h₂)
  let P₃ := segmentLog s v₃ v₀ (L₀ + log ρ₀ + log ρ₁ + log ρ₂) (mem_slitPlane_of_im_pos h₃)
  have e₁ : exp (L₀ + log ρ₀) = v₁ - s := by
    rw [Complex.exp_add, e₀, exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₀))]
    simp only [ρ₀]
    field_simp
  have e₂ : exp (L₀ + log ρ₀ + log ρ₁) = v₂ - s := by
    rw [Complex.exp_add, e₁, exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₁))]
    simp only [ρ₁]
    field_simp
  have e₃ : exp (L₀ + log ρ₀ + log ρ₁ + log ρ₂) = v₃ - s := by
    rw [Complex.exp_add, e₂, exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₂))]
    simp only [ρ₂]
    field_simp
  -- the total increment is `2πi`
  have hsum : log ρ₀ + log ρ₁ + log ρ₂ + log ρ₃ = 2 * π * I := by
    have hexp : exp (log ρ₀ + log ρ₁ + log ρ₂ + log ρ₃) = 1 := by
      rw [Complex.exp_add, Complex.exp_add, Complex.exp_add,
        exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₀)),
        exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₁)),
        exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₂)),
        exp_log (slitPlane_ne_zero (mem_slitPlane_of_im_pos h₃))]
      simp only [ρ₀, ρ₁, ρ₂, ρ₃]
      field_simp
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hexp
    have him := congrArg Complex.im hn
    simp only [add_im, log_im, mul_im, intCast_re, intCast_im, mul_re, ofReal_re, ofReal_im,
      re_ofNat, im_ofNat, I_re, I_im] at him
    have a₀ := arg_pos_of_im_pos h₀
    have a₁ := arg_pos_of_im_pos h₁
    have a₂ := arg_pos_of_im_pos h₂
    have a₃ := arg_pos_of_im_pos h₃
    have b₀ := arg_le_pi ρ₀
    have b₁ := arg_le_pi ρ₁
    have b₂ := arg_le_pi ρ₂
    have b₃ := arg_le_pi ρ₃
    have hpi := Real.pi_pos
    -- `0 < 2πn < 4π`, so `n = 1`
    have hn1 : n = 1 := by
      have hlo : (0 : ℝ) < n := by nlinarith
      have hhi : (n : ℝ) < 2 := by
        by_contra hc
        replace hc := not_lt.mp hc
        have : (arg ρ₀ = π ∧ arg ρ₁ = π ∧ arg ρ₂ = π ∧ arg ρ₃ = π) := by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
        exact absurd (arg_lt_pi_iff.mpr (Or.inr h₀.ne')) (by rw [this.1]; exact lt_irrefl _)
      have : (0 : ℤ) < n := by exact_mod_cast hlo
      have : n < (2 : ℤ) := by exact_mod_cast hhi
      omega
    rw [hn, hn1]
    push_cast
    ring
  refine ⟨(((P₀.trans P₁).trans P₂).trans P₃).toContinuousMap, fun t ↦ ?_, ?_⟩
  · change s + exp ((((P₀.trans P₁).trans P₂).trans P₃) t) = quadPath v₀ v₁ v₂ v₃ t
    refine Path.trans_apply_compat (f := fun w ↦ s + exp w) (g := id)
      (Path.trans_apply_compat (f := fun w ↦ s + exp w) (g := id)
        (Path.trans_apply_compat (f := fun w ↦ s + exp w) (g := id) (fun t ↦ ?_) (fun t ↦ ?_))
        (fun t ↦ ?_)) (fun t ↦ ?_) t
    · exact add_exp_segmentLog _ e₀ t
    · exact add_exp_segmentLog _ e₁ t
    · exact add_exp_segmentLog _ e₂ t
    · exact add_exp_segmentLog _ e₃ t
  · change (((P₀.trans P₁).trans P₂).trans P₃) 1 = (((P₀.trans P₁).trans P₂).trans P₃) 0 + _
    rw [Path.target, Path.source, ← hsum]
    ring

end Complex
