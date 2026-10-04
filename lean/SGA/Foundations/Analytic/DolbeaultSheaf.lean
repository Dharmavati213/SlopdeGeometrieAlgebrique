/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Sheaf
import SGA.Foundations.Cohomology.CartanInfinite
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# The sheaf of smooth functions and its acyclicity

Let `E` be a finite-dimensional real normed space and `F` a real normed space. The `F`-valued
`C^∞` functions on the open subsets of `E` form a sheaf of abelian groups
`AnalyticGeometry.smoothSheaf E F` (for `F = ℂ`, the sheaf of smooth complex functions; for `F` a
space of coefficients, a sheaf of smooth differential forms). It is *fine*: by
smooth partitions of unity, its Čech complex for every family of opens is exact in positive
degrees (`AnalyticGeometry.cechComplex_smoothSheaf_exactAt`), hence by Cartan's criterion for
infinite families (`TopCat.Sheaf.H'_subsingleton_of_forall_cech`)
`Hⁿ(V, 𝒞^∞(F)) = 0` for every open `V ⊆ E` and every `n > 0`
(`AnalyticGeometry.H'_smoothSheaf_subsingleton`). References: Godement, *Théorie des faisceaux*,
II.3.7 and II.4.4; Hörmander, *An introduction to complex analysis in several variables*, 7.4;
Wells, *Differential analysis on complex manifolds*, II.3.

This is the acyclicity of the terms of the Dolbeault resolution `0 → 𝒪 → 𝒞^∞ → 𝒞^∞ → ⋯`, the
first step of the route to Theorem B on product domains
(`AnalyticGeometry.PolydiscProductVanishingStatement`).

## Main results

* `AnalyticGeometry.exists_smoothPartitionOfUnity`: a smooth partition of unity on an open subset
  of `E`, subordinate to an open cover, as functions on `E`.
* `AnalyticGeometry.smoothSheaf E F`: the sheaf of abelian groups of `C^∞` functions `U → F`.
* `AnalyticGeometry.cechComplex_smoothSheaf_exactAt` (fineness),
  `AnalyticGeometry.H'_smoothSheaf_subsingleton` (acyclicity).
-/

universe w u

noncomputable section

open CategoryTheory Topology TopologicalSpace Opposite Filter Set
open scoped Manifold ContDiff

namespace AnalyticGeometry

section Partition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {ι : Type*}

/-- A smooth partition of unity on an open subset `W` of a finite-dimensional real normed space,
subordinate to an open cover of `W`, as functions on `E`: smooth on `W`, vanishing near the
points of `W` outside `Uᵢ`, locally finite on `W`, and summing to `1` on `W`. -/
theorem exists_smoothPartitionOfUnity {W : Set E} (hW : IsOpen W) (U : ι → Set E)
    (hU : ∀ i, IsOpen (U i)) (hcov : W ⊆ ⋃ i, U i) :
    ∃ χ : ι → E → ℝ, (∀ i, ∀ z ∈ W, ContDiffAt ℝ ∞ (χ i) z) ∧
      (∀ i, ∀ z ∈ W, z ∉ U i → χ i =ᶠ[𝓝 z] 0) ∧
      (∀ z ∈ W, ∃ N ∈ 𝓝 z, {i | ∃ y ∈ N, χ i y ≠ 0}.Finite) ∧
      (∀ z ∈ W, ∑ᶠ i, χ i z = 1) := by
  classical
  let B : TopologicalSpace.Opens E := ⟨W, hW⟩
  have : LocallyCompactSpace B := hW.locallyCompactSpace
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, E)) (M := B)
    isClosed_univ (fun i => Subtype.val ⁻¹' U i) (fun i => (hU i).preimage continuous_subtype_val)
    (fun x _ => by simpa using hcov x.2)
  let χ : ι → E → ℝ := fun i z => if h : z ∈ W then ρ i ⟨z, h⟩ else 0
  have hχB : ∀ i (x : B), χ i x = ρ i x := fun i x => by
    have hx : (x : E) ∈ W := x.2
    simp [χ, hx]
  -- the partition near a point of `W`, through the open embedding `B → E`
  have hnhds : ∀ (z : E) (h : z ∈ W) {P : E → Prop},
      (∀ᶠ x : B in 𝓝 ⟨z, h⟩, P x) → ∀ᶠ y in 𝓝 z, P y := by
    intro z h P hP
    have := hW.isOpenEmbedding_subtypeVal.map_nhds_eq ⟨z, h⟩
    rw [← show ((⟨z, h⟩ : B) : E) = z from rfl, ← this]
    exact hP
  refine ⟨χ, fun i z hz => ?_, fun i z hz hzU => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have h1 : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ) ∞ (fun x : B => χ i x) ⟨z, hz⟩ := by
      have := (ρ i).contMDiff.contMDiffAt (x := ⟨z, hz⟩)
      exact this.congr_of_eventuallyEq (Eventually.of_forall fun x => hχB i x)
    rw [contMDiffAt_subtype_iff, contMDiffAt_iff_contDiffAt] at h1
    exact h1
  · have hnot : (⟨z, hz⟩ : B) ∉ tsupport (ρ i) := fun h => hzU (hρ i h)
    have h0 : ∀ᶠ x : B in 𝓝 ⟨z, hz⟩, ρ i x = 0 := notMem_tsupport_iff_eventuallyEq.mp hnot
    have h0' : ∀ᶠ x : B in 𝓝 ⟨z, hz⟩, χ i x = 0 := h0.mono fun x hx => by rw [hχB, hx]
    exact hnhds z hz h0'
  · obtain ⟨N, hN, hfin⟩ := ρ.locallyFinite ⟨z, hz⟩
    refine ⟨Subtype.val '' N, hW.isOpenEmbedding_subtypeVal.image_mem_nhds.mpr hN,
      hfin.subset fun i hi => ?_⟩
    obtain ⟨_, ⟨x, hxN, rfl⟩, hx⟩ := hi
    exact ⟨x, Function.mem_support.mpr (by rwa [← hχB]), hxN⟩
  · have := ρ.sum_eq_one (x := ⟨z, hz⟩) (mem_univ _)
    simp only [show ∀ i, χ i z = ρ i ⟨z, hz⟩ from fun i => hχB i ⟨z, hz⟩]
    exact this

end Partition

section Extend

variable {E : Type*} {F : Type*} [AddCommGroup F]

lemma extendByZero_add {U : Set E} (f g : U → F) :
    extendByZero (f + g) = extendByZero f + extendByZero g := by
  funext y
  by_cases hy : y ∈ U <;> simp [extendByZero, hy]

lemma extendByZero_neg {U : Set E} (f : U → F) : extendByZero (-f) = -extendByZero f := by
  funext y
  by_cases hy : y ∈ U <;> simp [extendByZero, hy]

lemma extendByZero_zero {U : Set E} : extendByZero (0 : U → F) = 0 := by
  funext y
  by_cases hy : y ∈ U <;> simp [extendByZero, hy]

end Extend

section Sheaf

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function on a subset `U` of `E` is smooth if its extension by zero is `C^∞` at every point
of `U` (for `U` open this does not depend on the extension). -/
def IsSmoothOn {U : Set E} (f : U → F) : Prop :=
  ∀ x : U, ContDiffAt ℝ ∞ (extendByZero f) x

variable (E F) in
/-- The smooth `F`-valued functions on an open subset of `E` form an additive subgroup of all
functions. -/
def smoothSections (U : Opens E) : AddSubgroup (U → F) where
  carrier := {f | IsSmoothOn f}
  add_mem' {f g} hf hg x := by
    change ContDiffAt ℝ ∞ (extendByZero (f + g)) x
    rw [extendByZero_add]
    exact (hf x).add (hg x)
  zero_mem' x := by
    change ContDiffAt ℝ ∞ (extendByZero (0 : U → F)) x
    rw [extendByZero_zero]
    exact contDiffAt_const
  neg_mem' {f} hf x := by
    change ContDiffAt ℝ ∞ (extendByZero (-f)) x
    rw [extendByZero_neg]
    exact (hf x).neg

@[simp] lemma mem_smoothSections {U : Opens E} (f : U → F) :
    f ∈ smoothSections E F U ↔ IsSmoothOn f := Iff.rfl

/-- A smooth function on `U` restricts to a smooth function on an open `V ⊆ U`. -/
lemma IsSmoothOn.restrict {U V : Set E} (hV : IsOpen V) (h : V ⊆ U) {f : U → F}
    (hf : IsSmoothOn f) : IsSmoothOn (fun x : V ↦ f ⟨x, h x.2⟩) := fun x ↦
  (hf ⟨x, h x.2⟩).congr_of_eventuallyEq
    (extendByZero_eventuallyEq hV h _ _ (fun _ ↦ rfl) x.2)

/-- A function `E → F` that is `C^∞` at every point of an open set restricts to a smooth
function on it. -/
lemma isSmoothOn_restrict {U : Set E} (hU : IsOpen U) {g : E → F}
    (hg : ∀ x ∈ U, ContDiffAt ℝ ∞ g x) : IsSmoothOn (fun x : U ↦ g x) := fun x ↦
  (hg x x.2).congr_of_eventuallyEq (by
    filter_upwards [hU.mem_nhds x.2] with y hy
    rw [extendByZero_of_mem _ hy])

/-- Restriction of smooth functions to a smaller open set. -/
def smoothRestrict {U V : Opens E} (h : V ≤ U) :
    smoothSections E F U →+ smoothSections E F V where
  toFun f := ⟨fun x ↦ f.1 ⟨x, h x.2⟩, f.2.restrict V.2 h⟩
  map_zero' := rfl
  map_add' _ _ := rfl

variable (E F)

/-- The local predicate "smooth" on `F`-valued functions on open subsets of `E`. -/
def smoothPredicate : TopCat.LocalPredicate fun _ : TopCat.of E ↦ F where
  pred {U} f := IsSmoothOn f
  res {U V} i f hf := hf.restrict U.2 (leOfHom i)
  locality {U} f hf x := by
    obtain ⟨V, hxV, i, hV⟩ := hf x
    exact (hV ⟨x, hxV⟩).congr_of_eventuallyEq
      (extendByZero_eventuallyEq V.2 (leOfHom i) _ _ (fun _ ↦ rfl) hxV).symm

/-- The presheaf of abelian groups of smooth `F`-valued functions on the opens of `E`. -/
def smoothPresheaf : TopCat.Presheaf AddCommGrpCat.{0} (TopCat.of E) where
  obj U := AddCommGrpCat.of (smoothSections E F U.unop)
  map {U V} i := AddCommGrpCat.ofHom (smoothRestrict (leOfHom i.unop))

/-- The sheaf `𝒞^∞_E(F)` of smooth `F`-valued functions on `E`, as a sheaf of abelian groups.
For `F = ℂ` this is the sheaf of smooth complex functions. -/
def smoothSheaf : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of E) where
  obj := smoothPresheaf E F
  property := by
    rw [CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _
      (CategoryTheory.forget AddCommGrpCat)]
    exact (TopCat.subsheafToTypes (smoothPredicate E F)).property

variable {E F}

@[simp] lemma smoothSheaf_map_apply {U V : (Opens (TopCat.of E))ᵒᵖ} (i : U ⟶ V)
    (f : (smoothSheaf E F).obj.obj U) (x : V.unop) :
    ((smoothSheaf E F).obj.map i f).1 x = f.1 ⟨x, leOfHom i.unop x.2⟩ := rfl

lemma smoothSheaf_add_apply {U : (Opens (TopCat.of E))ᵒᵖ} (f g : (smoothSheaf E F).obj.obj U)
    (x : U.unop) : (f + g).1 x = f.1 x + g.1 x := rfl

lemma smoothSheaf_sub_apply {U : (Opens (TopCat.of E))ᵒᵖ} (f g : (smoothSheaf E F).obj.obj U)
    (x : U.unop) : (f - g).1 x = f.1 x - g.1 x := rfl

lemma smoothSheaf_zero_apply {U : (Opens (TopCat.of E))ᵒᵖ} (x : U.unop) :
    (0 : (smoothSheaf E F).obj.obj U).1 x = 0 := rfl

lemma smoothSheaf_zsmul_apply {U : (Opens (TopCat.of E))ᵒᵖ} (n : ℤ)
    (f : (smoothSheaf E F).obj.obj U) (x : U.unop) : (n • f).1 x = n • f.1 x := rfl

lemma smoothSheaf_sum_apply {U : (Opens (TopCat.of E))ᵒᵖ} {α : Type*} (s : Finset α)
    (f : α → (smoothSheaf E F).obj.obj U) (x : U.unop) :
    (∑ a ∈ s, f a).1 x = ∑ a ∈ s, (f a).1 x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, smoothSheaf_add_apply, ih]

lemma smoothSheaf_ext {U : (Opens (TopCat.of E))ᵒᵖ} {f g : (smoothSheaf E F).obj.obj U}
    (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (funext h)

end Sheaf

section Fine

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]

open TopCat.Presheaf

/-- **The sheaf of smooth `F`-valued functions is fine**: its Čech complex for every family of
opens (indexed by any type) is exact in positive degrees. With a smooth partition of unity `(χₖ)`
on `⋃ Uᵢ` subordinate to `(Uᵢ)`, a cocycle `c` is the coboundary of `b_y = ∑ₖ χₖ c_{k, y}`. -/
theorem cechComplex_smoothSheaf_exactAt {ι : Type w} (U : ι → Opens (TopCat.of E)) (p : ℕ) :
    (cechComplex U (smoothSheaf E F).obj).ExactAt (p + 1) := by
  classical
  rw [cechComplex_exactAt_succ_iff]
  intro c hc
  set W : Set E := ⋃ i, (U i : Set E) with hWdef
  have hWo : IsOpen W := isOpen_iUnion fun i ↦ (U i).2
  obtain ⟨χ, hχs, hχ0, hχf, hχ1⟩ := exists_smoothPartitionOfUnity hWo (fun i ↦ (U i : Set E))
    (fun i ↦ (U i).2) subset_rfl
  have hχz : ∀ k, ∀ z ∈ W, z ∉ (U k : Set E) → χ k z = 0 := fun k z hz hzk ↦
    (hχ0 k z hz hzk).eq_of_nhds
  -- the points of a `p`-fold intersection lie in `W`
  have hmemW : ∀ {m : ℕ} (y : Fin (m + 1) → ι) (z : E), z ∈ cechOpen U y → z ∈ W :=
    fun y z hz ↦ mem_iUnion.mpr ⟨y 0, cechOpen_le U y 0 hz⟩
  -- locally, only finitely many `χₖ` are nonzero
  have hloc : ∀ z ∈ W, ∃ N ∈ 𝓝 z, ∃ S : Finset ι, ∀ y ∈ N, ∀ k ∉ S, χ k y = 0 := by
    intro z hz
    obtain ⟨N, hN, hfin⟩ := hχf z hz
    refine ⟨N, hN, hfin.toFinset, fun y hy k hk ↦ ?_⟩
    by_contra hne
    exact hk (hfin.mem_toFinset.mpr ⟨y, hy, hne⟩)
  -- the terms `χₖ c_{k,y}`, extended by zero
  let term : (Fin (p + 1) → ι) → ι → E → F := fun y k z ↦
    χ k z • extendByZero (c (Fin.cons k y : Fin (p + 2) → ι)).1 z
  have hsum : ∀ (y : Fin (p + 1) → ι) (S : Finset ι) (z : E), (∀ k ∉ S, χ k z = 0) →
      ∑ᶠ k, term y k z = ∑ k ∈ S, term y k z := by
    intro y S z hS
    refine finsum_eq_sum_of_support_subset _ fun k hk ↦ ?_
    by_contra hkS
    exact hk (by simp [term, hS k hkS])
  have hsum1 : ∀ (S : Finset ι) (z : E), z ∈ W → (∀ k ∉ S, χ k z = 0) →
      ∑ k ∈ S, χ k z = 1 := by
    intro S z hz hS
    have h1 := hχ1 z hz
    rwa [finsum_eq_sum_of_support_subset _ (s := S) fun k hk ↦ by
      by_contra hkS; exact hk (hS k hkS)] at h1
  -- smoothness of the terms on `U_y`
  have hterm : ∀ (y : Fin (p + 1) → ι) (k : ι) (z : E), z ∈ cechOpen U y →
      ContDiffAt ℝ ∞ (term y k) z := by
    intro y k z hz
    by_cases hzk : z ∈ U k
    · have hz' : z ∈ cechOpen U (Fin.cons k y : Fin (p + 2) → ι) := by
        rw [cechOpen_cons_eq]
        exact ⟨hzk, hz⟩
      exact (hχs k z (hmemW y z hz)).smul ((c (Fin.cons k y)).2 ⟨z, hz'⟩)
    · refine contDiffAt_const (c := (0 : F)).congr_of_eventuallyEq ?_
      filter_upwards [hχ0 k z (hmemW y z hz) hzk] with y' hy'
      simp [term, hy']
  have hsmooth : ∀ (y : Fin (p + 1) → ι) (z : E), z ∈ cechOpen U y →
      ContDiffAt ℝ ∞ (fun z ↦ ∑ᶠ k, term y k z) z := by
    intro y z hz
    obtain ⟨N, hN, S, hS⟩ := hloc z (hmemW y z hz)
    have hev : (fun z ↦ ∑ᶠ k, term y k z) =ᶠ[𝓝 z] fun z ↦ ∑ k ∈ S, term y k z := by
      filter_upwards [hN] with z' hz' using hsum y S z' (hS z' hz')
    exact (ContDiffAt.sum fun k _ ↦ hterm y k z hz).congr_of_eventuallyEq hev
  let b : CechCochain U (smoothSheaf E F).obj p := fun y ↦
    ⟨fun z ↦ ∑ᶠ k, term y k z, isSmoothOn_restrict (cechOpen U y).2 (hsmooth y)⟩
  refine ⟨b, funext fun x ↦ smoothSheaf_ext fun z ↦ ?_⟩
  have hzW : (z : E) ∈ W := hmemW x z z.2
  obtain ⟨N, hN, S, hS⟩ := hloc z hzW
  have hSz := hS z (mem_of_mem_nhds hN)
  rw [cechD_apply, smoothSheaf_sum_apply]
  simp only [smoothSheaf_zsmul_apply, smoothSheaf_map_apply]
  change ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • ∑ᶠ k, term (x ∘ Fin.succAbove j) k z = _
  simp only [hsum _ S z hSz, Finset.smul_sum]
  rw [Finset.sum_comm]
  -- for each `k`, the cocycle condition at `(k, x)`
  have hk : ∀ k ∈ S, ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) • term (x ∘ Fin.succAbove j) k z =
      χ k z • (c x).1 z := by
    intro k _
    by_cases hzk : (z : E) ∈ U k
    · have hz' : (z : E) ∈ cechOpen U (Fin.cons k x : Fin (p + 3) → ι) := by
        rw [cechOpen_cons_eq]
        exact ⟨hzk, z.2⟩
      have h := congrArg (fun s ↦ s.1 ⟨z, hz'⟩)
        ((cechD_cons U (smoothSheaf E F).obj k c x).symm.trans (congrFun hc (Fin.cons k x)))
      simp only [smoothSheaf_sub_apply, smoothSheaf_sum_apply, smoothSheaf_zsmul_apply,
        smoothSheaf_map_apply, Pi.zero_apply, smoothSheaf_zero_apply, sub_eq_zero] at h
      have hmem : ∀ j : Fin (p + 2),
          (z : E) ∈ cechOpen U (Fin.cons k (x ∘ Fin.succAbove j) : Fin (p + 2) → ι) := by
        intro j
        rw [cechOpen_cons_eq]
        exact ⟨hzk, cechOpen_le_comp U x _ z.2⟩
      have h' : (c x).1 z = ∑ j : Fin (p + 2), (-1 : ℤ) ^ (j : ℕ) •
          (c (Fin.cons k (x ∘ Fin.succAbove j))).1 ⟨z, hmem j⟩ := h
      rw [h', Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      simp only [term]
      rw [smul_comm, extendByZero_of_mem _ (hmem j)]
    · simp [term, hχz k z hzW hzk]
  rw [Finset.sum_congr rfl hk, ← Finset.sum_smul, hsum1 S z hzW hSz, one_smul]

/-- **Acyclicity of the sheaf of smooth functions**: `Hⁿ(V, 𝒞^∞_E(F)) = 0` for every open `V` of a
finite-dimensional real normed space `E`, every real normed space `F` and every `n > 0`
(Godement II.4.4). -/
theorem H'_smoothSheaf_subsingleton
    [HasExt.{w} (CategoryTheory.Sheaf (Opens.grothendieckTopology (TopCat.of E)) AddCommGrpCat)]
    (p : ℕ) (V : Opens (TopCat.of E)) : Subsingleton ((smoothSheaf E F).H' (p + 1) V) :=
  TopCat.Sheaf.H'_subsingleton_of_forall_cech _
    (fun _ U q ↦ cechComplex_smoothSheaf_exactAt U q) p V

end Fine

end AnalyticGeometry
