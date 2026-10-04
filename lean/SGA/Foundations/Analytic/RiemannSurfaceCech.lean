/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Montel
import SGA.Foundations.Analytic.CompactPerturbation

/-!
# Čech cochains of bounded holomorphic functions, and a finiteness criterion

Let `M` be a complex manifold of dimension one and `U : ι → Set M` a finite family of open sets.
This file sets up the Banach spaces of bounded holomorphic Čech cochains:

* `Cech0 U = ∏ᵢ 𝒪ᵇ(Uᵢ)`, `Cech1 U = ∏ᵢⱼ 𝒪ᵇ(Uᵢ ∩ Uⱼ)`;
* the cocycles `cocycles U ⊆ Cech1 U` (`ζᵢₖ = ζᵢⱼ + ζⱼₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ`), a closed subspace;
* the coboundary `δ : Cech0 U → cocycles U`, `(δη)ᵢⱼ = ηⱼ - ηᵢ` (`cechδ`);
* the restriction `cocycles U' → cocycles U` for `Uᵢ ⊆ U'ᵢ` (`cechRestrict`).

The main result is Forster's finiteness criterion (*Lectures on Riemann surfaces*, proof of
14.9): if the closures of the `Uᵢ` are compact subsets of open sets `U'ᵢ`, and every cocycle on
`U` is the restriction of a cocycle on `U'` up to a coboundary, then the coboundaries have finite
codimension in the cocycles (`cofg_range_cechδ`). The restriction is compact by Montel's theorem
(`boundedHolomorphic.isCompactOperator_restrict`), and L. Schwartz's theorem
(`ContinuousLinearMap.cofg_range_sub_of_surjective`) applies to
`(ξ, η) ↦ ξ|_U + δη` and its compact perturbation `(ξ, η) ↦ ξ|_U`.
-/

noncomputable section

open Set Filter Topology Metric
open scoped Manifold BoundedContinuousFunction

/-- A product of finitely many compact operators is compact. -/
theorem IsCompactOperator.pi {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] {ι : Type*} [Finite ι] {F : ι → Type*} [∀ i, NormedAddCommGroup (F i)]
    [∀ i, NormedSpace 𝕜 (F i)] {f : ∀ i, E →L[𝕜] F i} (hf : ∀ i, IsCompactOperator (f i)) :
    IsCompactOperator (ContinuousLinearMap.pi f) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  choose V hV K hK hVK using fun i =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact _).mp (hf i)
  refine ⟨⋂ i, V i, iInter_mem.mpr hV, Set.pi univ K, isCompact_univ_pi hK, ?_⟩
  rintro _ ⟨x, hx, rfl⟩ i -
  exact hVK i ⟨x, mem_iInter.mp hx i, rfl⟩

namespace AnalyticGeometry

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {ι : Type*} [Fintype ι]

/-- Bounded holomorphic Čech `0`-cochains for the family `U`. -/
abbrev Cech0 (U : ι → Set M) := ∀ i, boundedHolomorphic (U i)

/-- Bounded holomorphic Čech `1`-cochains for the family `U`. -/
abbrev Cech1 (U : ι → Set M) := ∀ i j, boundedHolomorphic (U i ∩ U j)

variable (U : ι → Set M)

/-- The value at `x : M` of the `(i, j)` component of a `1`-cochain (extended by zero). -/
def Cech1.eval (ζ : Cech1 U) (i j : ι) (x : M) : ℂ :=
  extendByZero ((ζ i j : boundedHolomorphic (U i ∩ U j)) : (U i ∩ U j : Set M) →ᵇ ℂ) x

omit [Fintype ι] in
lemma Cech1.eval_of_mem (ζ : Cech1 U) {i j : ι} {x : M} (hx : x ∈ U i ∩ U j) :
    Cech1.eval U ζ i j x =
      ((ζ i j : boundedHolomorphic (U i ∩ U j)) : (U i ∩ U j : Set M) →ᵇ ℂ)
        (⟨x, hx⟩ : (U i ∩ U j : Set M)) :=
  extendByZero_of_mem _ hx

omit [Fintype ι] in
lemma Cech1.eval_add (ζ ζ' : Cech1 U) (i j : ι) (x : M) :
    Cech1.eval U (ζ + ζ') i j x = Cech1.eval U ζ i j x + Cech1.eval U ζ' i j x := by
  by_cases hx : x ∈ U i ∩ U j
  · simp only [Cech1.eval_of_mem U _ hx]; rfl
  · simp [Cech1.eval, extendByZero_of_notMem _ hx]

omit [Fintype ι] in
lemma Cech1.eval_smul (c : ℂ) (ζ : Cech1 U) (i j : ι) (x : M) :
    Cech1.eval U (c • ζ) i j x = c * Cech1.eval U ζ i j x := by
  by_cases hx : x ∈ U i ∩ U j
  · simp only [Cech1.eval_of_mem U _ hx]; rfl
  · simp [Cech1.eval, extendByZero_of_notMem _ hx]

omit [Fintype ι] in
lemma Cech1.eval_zero (i j : ι) (x : M) : Cech1.eval U 0 i j x = 0 := by
  by_cases hx : x ∈ U i ∩ U j
  · simp only [Cech1.eval_of_mem U _ hx]; rfl
  · simp [Cech1.eval, extendByZero_of_notMem _ hx]

omit [Fintype ι] in
/-- Two `1`-cochains are equal if their components agree at every point. -/
lemma Cech1.ext_eval {ζ ζ' : Cech1 U}
    (h : ∀ i j, ∀ x ∈ U i ∩ U j, Cech1.eval U ζ i j x = Cech1.eval U ζ' i j x) : ζ = ζ' := by
  funext i j
  refine Subtype.ext (BoundedContinuousFunction.ext fun x => ?_)
  have := h i j x x.2
  rwa [Cech1.eval_of_mem U _ x.2, Cech1.eval_of_mem U _ x.2] at this

/-- The `1`-cocycles: `ζᵢₖ = ζᵢⱼ + ζⱼₖ` on `Uᵢ ∩ Uⱼ ∩ Uₖ`. -/
def cocycles : Submodule ℂ (Cech1 U) where
  carrier := {ζ | ∀ i j k, ∀ x ∈ U i ∩ U j ∩ U k,
    Cech1.eval U ζ i k x = Cech1.eval U ζ i j x + Cech1.eval U ζ j k x}
  add_mem' {ζ ζ'} hζ hζ' i j k x hx := by
    simp only [Cech1.eval_add, hζ i j k x hx, hζ' i j k x hx]
    ring
  zero_mem' i j k x hx := by simp [Cech1.eval_zero]
  smul_mem' c ζ hζ i j k x hx := by
    simp only [Cech1.eval_smul, hζ i j k x hx]
    ring

omit [Fintype ι] in
theorem isClosed_cocycles : IsClosed (cocycles U : Set (Cech1 U)) := by
  have hcont : ∀ i j (x : M) (hx : x ∈ U i ∩ U j),
      Continuous fun ζ : Cech1 U => Cech1.eval U ζ i j x := fun i j x hx => by
    simp only [Cech1.eval_of_mem U _ hx]
    exact (continuous_eval_const _).comp
      (continuous_subtype_val.comp ((continuous_apply j).comp (continuous_apply i)))
  have : (cocycles U : Set (Cech1 U)) = ⋂ i, ⋂ j, ⋂ k, ⋂ x, ⋂ (hx : x ∈ U i ∩ U j ∩ U k),
      {ζ | Cech1.eval U ζ i k x = Cech1.eval U ζ i j x + Cech1.eval U ζ j k x} := by
    ext ζ
    simp only [mem_iInter]
    rfl
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun k =>
    isClosed_iInter fun x => isClosed_iInter fun hx => isClosed_eq ?_ ?_
  · exact hcont i k x ⟨hx.1.1, hx.2⟩
  · exact (hcont i j x hx.1).add (hcont j k x ⟨hx.1.2, hx.2⟩)

/-- The Čech coboundary `δ : Cech0 U → Cech1 U`, `(δη)ᵢⱼ = ηⱼ|_{Uᵢ ∩ Uⱼ} - ηᵢ|_{Uᵢ ∩ Uⱼ}`. -/
def cechδ₁ : Cech0 U →L[ℂ] Cech1 U :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (boundedHolomorphic.restrict inter_subset_right).comp (ContinuousLinearMap.proj j) -
      (boundedHolomorphic.restrict inter_subset_left).comp (ContinuousLinearMap.proj i)

omit [Fintype ι] in
lemma cechδ₁_eval (η : Cech0 U) (i j : ι) {x : M} (hx : x ∈ U i ∩ U j) :
    Cech1.eval U (cechδ₁ U η) i j x =
      extendByZero ((η j : boundedHolomorphic (U j)) : U j →ᵇ ℂ) x -
        extendByZero ((η i : boundedHolomorphic (U i)) : U i →ᵇ ℂ) x := by
  simp only [Cech1.eval, extendByZero_of_mem _ hx, extendByZero_of_mem _ hx.1,
    extendByZero_of_mem _ hx.2]
  rfl

omit [Fintype ι] in
lemma cechδ₁_mem_cocycles (η : Cech0 U) : cechδ₁ U η ∈ cocycles U := by
  intro i j k x hx
  rw [cechδ₁_eval U η i k ⟨hx.1.1, hx.2⟩, cechδ₁_eval U η i j hx.1,
    cechδ₁_eval U η j k ⟨hx.1.2, hx.2⟩]
  ring

/-- The Čech coboundary `δ : Cech0 U → cocycles U`. -/
def cechδ : Cech0 U →L[ℂ] cocycles U :=
  (cechδ₁ U).codRestrict _ (cechδ₁_mem_cocycles U)

variable {U} {U' : ι → Set M}

/-- Restriction of `1`-cochains from `U'` to `U`, for `Uᵢ ⊆ U'ᵢ`. -/
def cechRestrict₁ (h : ∀ i, U i ⊆ U' i) : Cech1 U' →L[ℂ] Cech1 U :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (boundedHolomorphic.restrict (inter_subset_inter (h i) (h j))).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun j => boundedHolomorphic (U' i ∩ U' j)) j).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun i => ∀ j, boundedHolomorphic (U' i ∩ U' j))
          i))

omit [Fintype ι] in
lemma cechRestrict₁_eval (h : ∀ i, U i ⊆ U' i) (ζ : Cech1 U') (i j : ι) {x : M}
    (hx : x ∈ U i ∩ U j) :
    Cech1.eval U (cechRestrict₁ h ζ) i j x = Cech1.eval U' ζ i j x := by
  simp only [Cech1.eval, extendByZero_of_mem _ hx,
    extendByZero_of_mem _ (inter_subset_inter (h i) (h j) hx)]
  rfl

omit [Fintype ι] in
lemma cechRestrict₁_mem_cocycles (h : ∀ i, U i ⊆ U' i) (ζ : cocycles U') :
    cechRestrict₁ h ζ ∈ cocycles U := by
  intro i j k x hx
  rw [cechRestrict₁_eval h _ i k ⟨hx.1.1, hx.2⟩, cechRestrict₁_eval h _ i j hx.1,
    cechRestrict₁_eval h _ j k ⟨hx.1.2, hx.2⟩]
  exact ζ.2 i j k x ⟨⟨h i hx.1.1, h j hx.1.2⟩, h k hx.2⟩

/-- Restriction of cocycles from `U'` to `U`. -/
def cechRestrict (h : ∀ i, U i ⊆ U' i) : cocycles U' →L[ℂ] cocycles U :=
  ((cechRestrict₁ h).comp (cocycles U').subtypeL).codRestrict _
    (fun ζ => cechRestrict₁_mem_cocycles h ζ)

variable [IsManifold 𝓘(ℂ) 1 M]

-- `[Fintype ι]` gives the normed structure on the cochain spaces used in the proof; with
-- `[Finite ι]` the two topologies on the product differ syntactically and elaboration times out.
set_option linter.unusedFintypeInType false in
/-- Restriction of cocycles is compact when the closures of the `Uᵢ` are compact subsets of the
open sets `U'ᵢ` (Montel). -/
theorem isCompactOperator_cechRestrict (hU : ∀ i, IsOpen (U i)) (hU' : ∀ i, IsOpen (U' i))
    (hc : ∀ i, IsCompact (closure (U i))) (hcl : ∀ i, closure (U i) ⊆ U' i) :
    IsCompactOperator (cechRestrict fun i => subset_closure.trans (hcl i)) := by
  have hcomp : IsCompactOperator (cechRestrict₁ fun i => subset_closure.trans (hcl i) :
      Cech1 U' →L[ℂ] Cech1 U) := by
    refine IsCompactOperator.pi fun i => IsCompactOperator.pi fun j => ?_
    have hij : closure (U i ∩ U j) ⊆ U' i ∩ U' j :=
      (closure_inter_subset_inter_closure _ _).trans (inter_subset_inter (hcl i) (hcl j))
    have h := boundedHolomorphic.isCompactOperator_restrict ((hU i).inter (hU j))
      ((hU' i).inter (hU' j)) ((hc i).of_isClosed_subset isClosed_closure
        ((closure_inter_subset_inter_closure _ _).trans inter_subset_left)) hij
    exact h.comp_clm _
  exact (hcomp.comp_clm (cocycles U').subtypeL).codRestrict _ (isClosed_cocycles U)

-- `[Fintype ι]` gives the normed structure on the cochain spaces used in the proof; with
-- `[Finite ι]` the two topologies on the product differ syntactically and elaboration times out.
set_option linter.unusedFintypeInType false in
/-- **Forster's finiteness criterion** (*Lectures on Riemann surfaces*, proof of 14.9, with sup
norms): let `U`, `U'` be finite families of open sets with `closure Uᵢ` compact and contained in
`U'ᵢ`. If every bounded holomorphic cocycle on `U` is, up to a coboundary, the restriction of a
bounded holomorphic cocycle on `U'`, then the coboundaries have finite codimension in the
cocycles on `U`. -/
theorem cofg_range_cechδ (hU : ∀ i, IsOpen (U i)) (hU' : ∀ i, IsOpen (U' i))
    (hc : ∀ i, IsCompact (closure (U i))) (hcl : ∀ i, closure (U i) ⊆ U' i)
    (hsurj : ∀ ζ : cocycles U, ∃ (ξ : cocycles U') (η : Cech0 U),
      ζ = cechRestrict (fun i => subset_closure.trans (hcl i)) ξ + cechδ U η) :
    (LinearMap.range (cechδ U : Cech0 U →ₗ[ℂ] cocycles U)).CoFG := by
  have : ∀ i, Fact (IsOpen (U i)) := fun i => ⟨hU i⟩
  have : ∀ i j, Fact (IsOpen (U i ∩ U j)) := fun i j => ⟨(hU i).inter (hU j)⟩
  have : ∀ i j, Fact (IsOpen (U' i ∩ U' j)) := fun i j => ⟨(hU' i).inter (hU' j)⟩
  have : CompleteSpace (cocycles U) := (isClosed_cocycles U).completeSpace_coe
  have : CompleteSpace (cocycles U') := (isClosed_cocycles U').completeSpace_coe
  set ρ := cechRestrict (U := U) (U' := U') fun i => subset_closure.trans (hcl i)
  let ψ : (cocycles U' × Cech0 U) →L[ℂ] cocycles U :=
    ρ.comp (ContinuousLinearMap.fst ℂ _ _) + (cechδ U).comp (ContinuousLinearMap.snd ℂ _ _)
  let φ : (cocycles U' × Cech0 U) →L[ℂ] cocycles U := ρ.comp (ContinuousLinearMap.fst ℂ _ _)
  have hψ : Function.Surjective ψ := fun ζ => by
    obtain ⟨ξ, η, h⟩ := hsurj ζ
    exact ⟨(ξ, η), by simp [ψ, h]⟩
  have hφ : IsCompactOperator φ :=
    (isCompactOperator_cechRestrict hU hU' hc hcl).comp_clm _
  have h := ContinuousLinearMap.cofg_range_sub_of_surjective hψ hφ
  have hrange : LinearMap.range ((ψ - φ : (cocycles U' × Cech0 U) →L[ℂ] cocycles U) :
      (cocycles U' × Cech0 U) →ₗ[ℂ] cocycles U) =
      LinearMap.range (cechδ U : Cech0 U →ₗ[ℂ] cocycles U) := by
    ext ζ
    simp only [LinearMap.mem_range, ContinuousLinearMap.coe_coe]
    constructor
    · rintro ⟨⟨ξ, η⟩, rfl⟩
      exact ⟨η, by simp [ψ, φ]⟩
    · rintro ⟨η, rfl⟩
      exact ⟨(0, η), by simp [ψ, φ]⟩
  rwa [← ContinuousLinearMap.toLinearMap_sub, hrange] at h

end AnalyticGeometry
