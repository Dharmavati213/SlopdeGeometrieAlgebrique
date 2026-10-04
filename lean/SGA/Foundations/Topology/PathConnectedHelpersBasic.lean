/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real

/-!
# Basic helpers on paths: subspaces and subintervals

* **Paths with values in a subspace.** A path `γ` in `X` with `range γ ⊆ s` is the same as a path
  in the subspace `s`: `Path.codRestrict γ h` is that path, and `Path.map_subtypeVal_codRestrict`
  says that composing it with the inclusion `s → X` gives back `γ`. The usual operations on paths
  commute with `codRestrict` (`Path.codRestrict_trans`, `Path.codRestrict_symm`,
  `Path.codRestrict_refl`), and so does enlarging `s` (`Path.map_inclusion_codRestrict`). This is
  the step "a path with values in `U`, seen as a path in the subspace `U`", which proofs about `π₁`
  of subspaces (semilocal simple connectedness, Seifert–van Kampen) need again and again.
* **Subintervals.** In the unit interval, a ball around `t` contains the interval between `t` and
  any of its points (`unitInterval.uIcc_subset_ball`); hence if `U` is a neighbourhood of `t`, so
  is the set of `s` with `[t, s] ⊆ U` (`unitInterval.eventually_uIcc_subset`), and a path maps
  `[t, s]` into an open set containing `γ t` for all `s` near `t`
  (`Path.eventually_image_uIcc_subset`). These are what arguments "following a path along
  `[0, 1]`" (finite generation of `π₁`, Seifert–van Kampen) use instead of subdivisions.
* **Classes of paths as arrows.** The arrow of the fundamental groupoid given by the class of a
  path turns `Path.refl`, `Path.trans` and `Path.symm` into identities, composition and inverses
  (`FundamentalGroupoid.fromPath_mk_refl`, `FundamentalGroupoid.fromPath_mk_trans`,
  `FundamentalGroupoid.fromPath_mk_symm`).

## References

* [A. Hatcher, *Algebraic Topology*, §1.1][hatcher02]
-/

open Set Topology Filter
open scoped unitInterval

namespace unitInterval

/-- In the unit interval, balls contain the interval between their centre and any of their
points. -/
theorem uIcc_subset_ball {t s : I} {ε : ℝ} (hs : s ∈ Metric.ball t ε) :
    uIcc t s ⊆ Metric.ball t ε := by
  intro u hu
  rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] at hs ⊢
  rw [mem_uIcc] at hu
  rw [abs_sub_lt_iff] at hs ⊢
  have h1 : (u : ℝ) ≤ s ∨ (u : ℝ) ≤ t := by
    rcases hu with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have h2 : (s : ℝ) ≤ u ∨ (t : ℝ) ≤ u := by
    rcases hu with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inr h
    · exact Or.inl h
  constructor <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> linarith [hs.1, hs.2]

/-- In the unit interval, if `U` is a neighbourhood of `t`, then so is the set of `s` such that the
whole interval between `t` and `s` lies in `U`. -/
theorem eventually_uIcc_subset {t : I} {U : Set I} (hU : U ∈ 𝓝 t) :
    ∀ᶠ s in 𝓝 t, uIcc t s ⊆ U := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  filter_upwards [Metric.ball_mem_nhds t hε] with s hs
  exact (uIcc_subset_ball hs).trans hball

end unitInterval

variable {X : Type*} [TopologicalSpace X] {x y z : X} {s t : Set X}

namespace Path

/-- A path with values in `s`, as a path in the subspace `s`. -/
@[simps]
def codRestrict (γ : Path x y) (h : range γ ⊆ s) :
    Path (⟨x, h ⟨0, γ.source⟩⟩ : s) ⟨y, h ⟨1, γ.target⟩⟩ where
  toFun t := ⟨γ t, h ⟨t, rfl⟩⟩
  continuous_toFun := by fun_prop
  source' := Subtype.ext γ.source
  target' := Subtype.ext γ.target

/-- Composing `γ.codRestrict h` with the inclusion `s → X` gives back `γ`. -/
@[simp]
lemma map_subtypeVal_codRestrict (γ : Path x y) (h : range γ ⊆ s) :
    (γ.codRestrict h).map continuous_subtype_val = γ :=
  rfl

/-- A path in the subspace `s` is the restriction of its image in `X`. -/
@[simp]
lemma codRestrict_map_subtypeVal {a b : s} (γ : Path a b)
    (h : range (γ.map continuous_subtype_val) ⊆ s) :
    (γ.map continuous_subtype_val).codRestrict h = γ :=
  rfl

/-- The range of a path in the subspace `s`, seen in `X`, lies in `s`. -/
lemma range_map_subtypeVal_subset {a b : s} (γ : Path a b) :
    range (γ.map continuous_subtype_val) ⊆ s := by
  rintro _ ⟨t, rfl⟩
  exact (γ t).2

@[simp]
lemma codRestrict_refl (h : range (Path.refl x) ⊆ s) :
    (Path.refl x).codRestrict h = Path.refl (⟨x, h ⟨0, rfl⟩⟩ : s) :=
  rfl

lemma codRestrict_trans (γ : Path x y) (γ' : Path y z) (h : range (γ.trans γ') ⊆ s)
    (h₁ : range γ ⊆ s) (h₂ : range γ' ⊆ s) :
    (γ.trans γ').codRestrict h = (γ.codRestrict h₁).trans (γ'.codRestrict h₂) := by
  ext t
  simp only [codRestrict_apply_coe, Path.trans_apply]
  split_ifs <;> rfl

lemma codRestrict_symm (γ : Path x y) (h : range γ.symm ⊆ s) (h' : range γ ⊆ s) :
    γ.symm.codRestrict h = (γ.codRestrict h').symm :=
  rfl

/-- Restricting to `s` and then including `s` into a larger `t` is restricting to `t`. -/
@[simp]
lemma map_inclusion_codRestrict (γ : Path x y) (h : range γ ⊆ s) (hst : s ⊆ t) :
    (γ.codRestrict h).map (continuous_inclusion hst) = γ.codRestrict (h.trans hst) :=
  rfl

/-- A path maps the interval between `t` and `s` into an open set `U ∋ γ t`, for all `s` close
enough to `t`. -/
theorem eventually_image_uIcc_subset (γ : Path x y) {U : Set X} (hU : IsOpen U)
    {t : I} (ht : γ t ∈ U) : ∀ᶠ s in 𝓝 t, γ '' uIcc t s ⊆ U := by
  filter_upwards [unitInterval.eventually_uIcc_subset ((hU.preimage γ.continuous).mem_nhds ht)]
    with s hs
  exact image_subset_iff.mpr hs

/-- Two paths with values in `s` that are homotopic in `s` are homotopic in `X`. -/
lemma Homotopic.of_codRestrict {γ γ' : Path x y} {h : range γ ⊆ s} {h' : range γ' ⊆ s}
    (hγ : (γ.codRestrict h).Homotopic (γ'.codRestrict h')) : γ.Homotopic γ' :=
  hγ.map ⟨Subtype.val, continuous_subtype_val⟩

end Path

namespace FundamentalGroupoid

open CategoryTheory

@[simp]
lemma fromPath_mk_refl (x : X) :
    fromPath (.mk (Path.refl x)) = 𝟙 (FundamentalGroupoid.mk x) :=
  rfl

@[simp]
lemma fromPath_mk_trans (γ : Path x y) (δ : Path y z) :
    fromPath (.mk (γ.trans δ)) = fromPath (.mk γ) ≫ fromPath (.mk δ) :=
  rfl

@[simp]
lemma fromPath_mk_symm (γ : Path x y) :
    fromPath (.mk γ.symm) = inv (fromPath (.mk γ)) := by
  rw [← Groupoid.inv_eq_inv]
  rfl

end FundamentalGroupoid
