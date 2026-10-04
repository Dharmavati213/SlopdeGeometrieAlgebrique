/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Topology.Subpath
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Topology.UniformSpace.OfCompactT2
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.GroupTheory.Finiteness
import SGA.Foundations.Topology.SemilocallySimplyConnected

/-!
# Fundamental groups of compact spaces are finitely generated

Let `X` be a compact, path-connected, locally path-connected and semilocally simply connected
space (with `X` R₁, e.g. Hausdorff). Then `π₁(X, x)` is a finitely generated group
(`FundamentalGroup.fg_of_compactSpace`). This applies to compact manifolds and to the complex
points of a proper complex variety (given semilocal simple connectedness, proved for `X(ℂ)` as
`SGA.SGA1.ExposeXII.SchemePoints.semilocallySimplyConnectedSpace` in
`SGA1/ExposeXII/LocalTopologySLSC.lean`).

The proof is the classical edge-path argument.

* `FundamentalGroup.eq_top_of_isOpen_cover`: the core. Given an open cover `W i` of `X`, a subgroup
  `H ≤ π₁(X, x)` and arrows `s i y : x ⟶ y` of the fundamental groupoid ("standard paths" to
  `y ∈ W i`) such that `s i y · σ · (s i z)⁻¹ ∈ H` for paths `σ` in `W i`, `s i y · (s j y)⁻¹ ∈ H`
  on `W i ∩ W j` and `s i x ∈ H`, we get `H = π₁(X, x)`. A loop `γ` is followed along `[0, 1]`
  through the subpaths `γ|[0, t]`; the set of good `t` is open and closed. The same lemma gives
  the generation half of the Seifert–van Kampen theorem (`Foundations/Topology/VanKampen.lean`).
* `FundamentalGroup.fg_of_finite_cover`: if `X` is path-connected and covered by finitely many
  open path-connected sets `W i` such that `W i ∪ W j` is relatively simply connected (any two
  paths in it with the same endpoints are homotopic in `X`) whenever `W i ∩ W j` is nonempty,
  then `π₁(X, x)` is finitely generated. Generators: fix base points `wᵢ ∈ W i` and paths
  `aᵢ : x ⟶ wᵢ`; the loops `aᵢ · ρ · aⱼ⁻¹` for `ρ` a path from `wᵢ` to `wⱼ` in `W i ∪ W j`, and
  `aᵢ · ρ` for `ρ` a path from `wᵢ` to `x` in `W i`, depend only on `(i, j)` (resp. `i`).
* `exists_finite_cover_isRelSimplyConnected_union`: such a cover exists on a compact R₁ space
  which is locally path-connected and semilocally simply connected (Lebesgue number lemma for the
  unique uniform structure of a compact R₁ space).

## References

* [A. Hatcher, *Algebraic Topology*, §1.3][hatcher02]
* [W. S. Massey, *A Basic Course in Algebraic Topology*, Chapter VI][massey1991]
-/

open Set Topology Filter CategoryTheory SetRel

universe u

variable {X : Type u} [TopologicalSpace X]

namespace FundamentalGroup

open FundamentalGroupoid

/-- The class of a path, as an arrow of the fundamental groupoid. -/
local notation "⌈" γ "⌉" => FundamentalGroupoid.fromPath (Path.Homotopic.Quotient.mk γ)

/-- The subpaths of `γ` compose: `γ|[t₀, t₁] · γ|[t₁, t₂] = γ|[t₀, t₂]` up to homotopy. -/
private lemma fromPath_subpath_comp {a b : X} (γ : Path a b) (t₀ t₁ t₂ : unitInterval) :
    ⌈(γ.subpath t₀ t₁)⌉ ≫ ⌈(γ.subpath t₁ t₂)⌉ =
      ⌈(γ.subpath t₀ t₂)⌉ :=
  _root_.Quotient.sound ⟨Path.Homotopy.subpathTransSubpath γ t₀ t₁ t₂⟩

/-- `γ|[0, 1]` is `γ`, up to the identifications `γ 0 = a` and `γ 1 = b`. -/
private lemma fromPath_subpath_zero_one {a b : X} (γ : Path a b) :
    ⌈(γ.subpath 0 1)⌉ =
      eqToHom (congrArg mk γ.source) ≫ ⌈γ⌉ ≫
        eqToHom (congrArg mk γ.target.symm) := by
  rw [Path.subpath_zero_one, FundamentalGroupoid.conj_eqToHom]
  rfl

private lemma inv_fromArrow {x : X} (u : mk x ⟶ mk x) :
    (fromArrow u)⁻¹ = fromArrow (inv u) :=
  Groupoid.inv_eq_inv u

/-- **Generation of `π₁` from local data.** Let `W i` be an open cover of `X`, `x ∈ X` and
`H ≤ π₁(X, x)`. Suppose given, for each `i` and `y`, an arrow `s i y : x ⟶ y` of the fundamental
groupoid (only relevant for `y ∈ W i`) such that

* `s i y · σ · (s i z)⁻¹ ∈ H` for every path `σ` from `y` to `z` inside `W i`;
* `s i y · (s j y)⁻¹ ∈ H` for `y ∈ W i ∩ W j`;
* `s i x ∈ H` for `x ∈ W i`.

Then `H = π₁(X, x)`. The proof follows a loop `γ` along `[0, 1]`: the set of `t` such that
`γ|[0, t] · (s i (γ t))⁻¹ ∈ H` for all `i` with `γ t ∈ W i` is open and closed. -/
theorem eq_top_of_isOpen_cover {ι : Type*} (W : ι → Set X) (hWo : ∀ i, IsOpen (W i))
    (hcov : ∀ y, ∃ i, y ∈ W i) {x : X} (H : Subgroup (FundamentalGroup X x))
    (s : ι → ∀ y : X, mk x ⟶ mk y)
    (hs₁ : ∀ i {y z : X} (σ : Path y z), range σ ⊆ W i →
      fromArrow (s i y ≫ ⌈σ⌉ ≫ inv (s i z)) ∈ H)
    (hs₂ : ∀ i j {y : X}, y ∈ W i → y ∈ W j → fromArrow (s i y ≫ inv (s j y)) ∈ H)
    (hs₃ : ∀ i, x ∈ W i → fromArrow (s i x) ∈ H) : H = ⊤ := by
  have hmem : ∀ {u v : mk x ⟶ mk x}, fromArrow u ∈ H → fromArrow v ∈ H → fromArrow (u ≫ v) ∈ H :=
    fun hu hv ↦ H.mul_mem hv hu
  rw [eq_top_iff]
  intro g _
  induction g using Path.Homotopic.Quotient.ind with | mk γ => ?_
  let c : ∀ t : unitInterval, mk x ⟶ mk (γ t) := fun t ↦
    eqToHom (congrArg mk γ.source.symm) ≫ ⌈γ.subpath 0 t⌉
  have hc : ∀ t s, c s = c t ≫ ⌈γ.subpath t s⌉ := by
    intro t s
    simp only [c, Category.assoc, fromPath_subpath_comp]
  let Good : unitInterval → Prop := fun t ↦
    ∀ i, γ t ∈ W i → fromArrow (c t ≫ inv (s i (γ t))) ∈ H
  have step : ∀ t t' (k : ι), γ '' uIcc t t' ⊆ W k → Good t → Good t' := by
    intro t t' k htt' ht j hj
    have hkt : γ t ∈ W k := htt' ⟨t, left_mem_uIcc, rfl⟩
    have hkt' : γ t' ∈ W k := htt' ⟨t', right_mem_uIcc, rfl⟩
    have e : c t' ≫ inv (s j (γ t')) = (c t ≫ inv (s k (γ t))) ≫
        (s k (γ t) ≫ ⌈γ.subpath t t'⌉ ≫ inv (s k (γ t'))) ≫ (s k (γ t') ≫ inv (s j (γ t'))) := by
      rw [hc t t']
      simp
    rw [e]
    exact hmem (ht k hkt) (hmem (hs₁ k _ (by rwa [Path.range_subpath])) (hs₂ k j hkt' hj))
  have hloc : ∀ t, ∀ᶠ t' in 𝓝 t, (Good t ↔ Good t') := by
    intro t
    obtain ⟨k, hk⟩ := hcov (γ t)
    filter_upwards [γ.eventually_image_uIcc_subset (hWo k) hk] with t' ht'
    exact ⟨step t t' k ht', step t' t k (by rwa [uIcc_comm])⟩
  have hA : IsClopen {t | Good t} := by
    constructor
    · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro t ht
      filter_upwards [hloc t] with t' ht' using fun h ↦ ht (ht'.mpr h)
    · rw [isOpen_iff_mem_nhds]
      intro t ht
      filter_upwards [hloc t] with t' ht' using ht'.mp ht
  have h0 : Good 0 := by
    intro i hi
    have key : ∀ (y : X) (h : x = y), y ∈ W i →
        fromArrow (eqToHom (congrArg mk h) ≫ inv (s i y)) ∈ H := by
      rintro y rfl hy
      simpa [inv_fromArrow] using H.inv_mem (hs₃ i hy)
    have := key (γ 0) γ.source.symm hi
    simp only [c, Path.subpath_self, fromPath_mk_refl, Category.comp_id]
    simpa using this
  have h1 : Good 1 := by
    have := hA.eq_univ ⟨0, h0⟩ ▸ mem_univ (1 : unitInterval)
    exact this
  obtain ⟨i, hi⟩ := hcov x
  have key : ∀ (y : X) (h : x = y), y ∈ W i →
      fromArrow (⌈γ⌉ ≫ eqToHom (congrArg mk h) ≫ inv (s i y)) ∈ H → fromArrow ⌈γ⌉ ∈ H := by
    rintro y rfl hy h
    simpa using hmem h (hs₃ i hy)
  have hi' : γ 1 ∈ W i := by rw [γ.target]; exact hi
  refine key (γ 1) γ.target.symm hi' ?_
  have := h1 i hi'
  simp only [c, fromPath_subpath_zero_one, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp] at this
  exact this

/-- **Finite generation of `π₁` from a good finite cover.** Let `X` be path-connected and covered
by finitely many open path-connected sets `W i` such that `W i ∪ W j` is relatively simply
connected whenever `W i` and `W j` meet. Then `π₁(X, x)` is finitely generated. -/
theorem fg_of_finite_cover [PathConnectedSpace X] {ι : Type*} [Finite ι] (W : ι → Set X)
    (hWo : ∀ i, IsOpen (W i)) (hWc : ∀ i, IsPathConnected (W i)) (hcov : ∀ y, ∃ i, y ∈ W i)
    (hrel : ∀ i j, (W i ∩ W j).Nonempty → IsRelSimplyConnected (W i ∪ W j)) (x : X) :
    Group.FG (FundamentalGroup X x) := by
  classical
  -- base points `w i ∈ W i` and arrows `a i : x ⟶ w i`
  let w : ι → X := fun i ↦ (hWc i).nonempty.some
  have hw : ∀ i, w i ∈ W i := fun i ↦ (hWc i).nonempty.some_mem
  let a : ∀ i, mk x ⟶ mk (w i) := fun i ↦ ⌈(PathConnectedSpace.somePath _ _)⌉
  have hrel' : ∀ i, IsRelSimplyConnected (W i) := fun i ↦
    (hrel i i ⟨w i, hw i, hw i⟩).mono subset_union_left
  -- the generators
  let S₁ : ι → ι → Set (FundamentalGroup X x) := fun i j ↦
    {g | (W i ∩ W j).Nonempty ∧ ∃ ρ : Path (w i) (w j), range ρ ⊆ W i ∪ W j ∧
      g = fromArrow (a i ≫ ⌈ρ⌉ ≫ inv (a j))}
  let S₂ : ι → Set (FundamentalGroup X x) := fun i ↦
    {g | ∃ ρ : Path (w i) x, range ρ ⊆ W i ∧ g = fromArrow (a i ≫ ⌈ρ⌉)}
  let S : Set (FundamentalGroup X x) := (⋃ i, ⋃ j, S₁ i j) ∪ ⋃ i, S₂ i
  have hS : S.Finite := by
    refine (finite_iUnion fun i ↦ finite_iUnion fun j ↦ ?_).union (finite_iUnion fun i ↦ ?_)
    · refine Set.Subsingleton.finite ?_
      rintro _ ⟨hij, ρ, hρ, rfl⟩ _ ⟨-, ρ', hρ', rfl⟩
      rw [(hrel i j hij).mk_eq hρ hρ']
    · refine Set.Subsingleton.finite ?_
      rintro _ ⟨ρ, hρ, rfl⟩ _ ⟨ρ', hρ', rfl⟩
      rw [(hrel' i).mk_eq hρ hρ']
  -- the standard arrows `x ⟶ y` for `y ∈ W i`: `a i` followed by a path in `W i`
  let ρ : ∀ i (y : X), y ∈ W i → Path (w i) y := fun i y hy ↦
    ((hWc i).joinedIn _ (hw i) _ hy).somePath
  have hρ : ∀ i y (hy : y ∈ W i), range (ρ i y hy) ⊆ W i := fun i y hy ↦
    range_subset_iff.mpr ((hWc i).joinedIn _ (hw i) _ hy).somePath_mem
  let s : ι → ∀ y : X, mk x ⟶ mk y := fun i y ↦
    if hy : y ∈ W i then a i ≫ ⌈ρ i y hy⌉ else ⌈PathConnectedSpace.somePath _ _⌉
  rw [Group.fg_iff]
  refine ⟨S, eq_top_of_isOpen_cover W hWo hcov _ s ?_ ?_ ?_, hS⟩
  · intro i y z σ hσ
    have hy : y ∈ W i := hσ ⟨0, σ.source⟩
    have hz : z ∈ W i := hσ ⟨1, σ.target⟩
    have e : ⌈ρ i y hy⌉ ≫ ⌈σ⌉ = ⌈ρ i z hz⌉ := by
      rw [← fromPath_mk_trans]
      refine (hrel' i).mk_eq ?_ (hρ i z hz)
      rw [Path.trans_range]
      exact union_subset (hρ i y hy) hσ
    simp only [s, hy, hz, ↓reduceDIte, Category.assoc]
    rw [reassoc_of% e]
    simpa using (Subgroup.closure S).one_mem
  · intro i j y hi hj
    simp only [s, hi, hj, ↓reduceDIte]
    refine Subgroup.subset_closure (Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨j, ⟨y, hi, hj⟩,
      (ρ i y hi).trans (ρ j y hj).symm, ?_, ?_⟩⟩))
    · rw [Path.trans_range, Path.symm_range]
      exact union_subset_union (hρ i y hi) (hρ j y hj)
    · rw [fromPath_mk_trans, fromPath_mk_symm]
      simp
  · intro i hi
    simp only [s, hi, ↓reduceDIte]
    exact Subgroup.subset_closure (Or.inr (mem_iUnion.mpr ⟨i, ρ i x hi, hρ i x hi, rfl⟩))

/-- On a compact R₁ space which is locally path-connected and semilocally simply connected, there
is a finite cover by open path-connected sets `W p` such that `W p ∪ W q` is relatively simply
connected whenever `W p ∩ W q` is nonempty. -/
theorem exists_finite_cover_isRelSimplyConnected_union [CompactSpace X] [R1Space X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] :
    ∃ (s : Finset X) (W : X → Set X), (∀ p, IsOpen (W p) ∧ IsPathConnected (W p)) ∧
      (∀ y, ∃ p ∈ s, y ∈ W p) ∧
      ∀ p ∈ s, ∀ q ∈ s, (W p ∩ W q).Nonempty → IsRelSimplyConnected (W p ∪ W q) := by
  let : UniformSpace X := uniformSpaceOfCompactR1
  have hU (y : X) :
      ∃ V : Set X, IsOpen V ∧ y ∈ V ∧ IsPathConnected V ∧ IsRelSimplyConnected V := by
    obtain ⟨V, -, hVo, hyV, hVc, hVr⟩ := exists_isRelSimplyConnected_subset (x := y) univ_mem
    exact ⟨V, hVo, hyV, hVc, hVr⟩
  choose U hUo hyU hUc hUr using hU
  obtain ⟨n, hn, hnU⟩ := lebesgue_number_lemma (K := univ) isCompact_univ hUo
    (fun y _ ↦ mem_iUnion.mpr ⟨y, hyU y⟩)
  obtain ⟨t, ht, htsymm, htn⟩ := comp_comp_symm_mem_uniformity_sets hn
  have hV (p : X) : ∃ V ⊆ UniformSpace.ball p t, IsOpen V ∧ p ∈ V ∧ IsPathConnected V ∧
      IsRelSimplyConnected V :=
    exists_isRelSimplyConnected_subset (UniformSpace.ball_mem_nhds p ht)
  choose W hWt hWo hpW hWc _ using hV
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover W hWo
    (fun y _ ↦ mem_iUnion.mpr ⟨y, hpW y⟩)
  refine ⟨s, W, fun p ↦ ⟨hWo p, hWc p⟩, fun y ↦ ?_, fun p _ q _ ⟨z, hzp, hzq⟩ ↦ ?_⟩
  · obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hs (mem_univ y))
    exact ⟨p, hp, hyp⟩
  · obtain ⟨i, hi⟩ := hnU p (mem_univ p)
    refine (hUr i).mono ((union_subset ?_ ?_).trans hi)
    · intro b hb
      exact htn ⟨p, ⟨p, refl_mem_uniformity ht, refl_mem_uniformity ht⟩, hWt p hb⟩
    · intro b hb
      exact htn ⟨q, ⟨z, hWt p hzp, htsymm.symm _ _ (hWt q hzq)⟩, hWt q hb⟩

/-- The fundamental group of a compact, R₁ (e.g. Hausdorff), path-connected, locally
path-connected and semilocally simply connected space is finitely generated. -/
theorem fg_of_compactSpace [CompactSpace X] [R1Space X] [PathConnectedSpace X]
    [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X] (x : X) :
    Group.FG (FundamentalGroup X x) := by
  obtain ⟨s, W, hW, hcov, hrel⟩ := exists_finite_cover_isRelSimplyConnected_union (X := X)
  refine fg_of_finite_cover (ι := s) (fun p ↦ W p) (fun p ↦ (hW p).1) (fun p ↦ (hW p).2)
    (fun y ↦ ?_) (fun p q h ↦ hrel p p.2 q q.2 h) x
  obtain ⟨p, hp, hyp⟩ := hcov y
  exact ⟨⟨p, hp⟩, hyp⟩

end FundamentalGroup
