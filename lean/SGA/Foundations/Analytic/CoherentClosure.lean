/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.Completion
import SGA.Foundations.Analytic.PowerSeriesExpansion
import Mathlib.RingTheory.Filtration
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Cartan's closure theorem for submodules of `𝕜{X}^ι`

Every submodule `N` of the free module `𝕜{X}^ι` over the ring of convergent power series is
closed for coefficientwise convergence: if a sequence `F_j ∈ N` converges to `G` coefficient by
coefficient, then `G ∈ N` (`AnalyticGeometry.mem_of_tendsto_coeff`). This is H. Cartan's
"théorème de fermeture" (Grauert–Remmert, *Coherent analytic sheaves*, Chapter 2; Gunning–Rossi,
Chapter II.D), the input for the Fréchet topology on the sections of a coherent sheaf and for
limits of sections of coherent subsheaves (Theorem B on open polydiscs by exhaustion, the
Cartan–Serre finiteness theorem). Uniform convergence of analytic functions on a neighbourhood
of the origin implies coefficientwise convergence of their Taylor series.

The proof is algebraic: for each `k` the truncation of the Taylor series in degrees `< k` maps
`N` onto a subspace of a finite-dimensional `𝕜`-vector space, which is closed, so
`G ∈ N + 𝔪ᵏ 𝕜{X}^ι` for every `k`; Krull's intersection theorem
(`Ideal.iInf_pow_smul_eq_bot_of_isLocalRing`) gives `G ∈ N`.
-/

noncomputable section

open Filter Topology MvPowerSeries IsLocalRing

namespace AnalyticGeometry

/-- Krull's intersection theorem, relative form: in a finite module over a noetherian local
ring, an element lying in `N + 𝔪ᵏ M` for every `k` lies in `N`. -/
theorem mem_of_forall_mem_sup_pow_smul {R M : Type*} [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] (N : Submodule R M)
    {x : M} (h : ∀ k : ℕ, x ∈ N ⊔ (maximalIdeal R ^ k • ⊤ : Submodule R M)) : x ∈ N := by
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := R) (M := M ⧸ N)
    (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mem_bot R, ← hbot, Submodule.mem_iInf]
  intro k
  obtain ⟨n, hn, y, hy, rfl⟩ := Submodule.mem_sup.mp (h k)
  rw [Submodule.Quotient.mk_add, (Submodule.Quotient.mk_eq_zero N).mpr hn, zero_add]
  have : Submodule.map N.mkQ (maximalIdeal R ^ k • ⊤ : Submodule R M) ≤
      (maximalIdeal R ^ k • ⊤ : Submodule R (M ⧸ N)) := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact this ⟨y, hy, rfl⟩

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {σ : Type*} [Fintype σ]
  {ι : Type*}

open Classical in
/-- The multi-indices of total degree `< k`. -/
def lowDegreeFinset (σ : Type*) [Fintype σ] (k : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.range k).biUnion (degreeFinset σ)

lemma mem_lowDegreeFinset {k : ℕ} {α : σ →₀ ℕ} : α ∈ lowDegreeFinset σ k ↔ α.degree < k := by
  simp [lowDegreeFinset]

/-- The coefficients of degree `< k` of a vector of power series. -/
def truncCoeff (k : ℕ) :
    (ι → convergent σ 𝕜) →ₗ[𝕜] (ι × lowDegreeFinset σ k → 𝕜) where
  toFun F iα := coeff iα.2.1 (F iα.1).1
  map_add' F G := by
    funext iα
    simp
  map_smul' c F := by
    funext iα
    simp

/-- A vector of power series whose coefficients of degree `< k` vanish lies in `𝔪ᵏ 𝕜{X}^ι`. -/
lemma mem_pow_smul_top_of_truncCoeff_eq_zero [Finite ι] {k : ℕ}
    {F : ι → convergent σ 𝕜} (hF : truncCoeff (𝕜 := 𝕜) k F = 0) :
    F ∈ (maximalIdeal (convergent σ 𝕜) ^ k • ⊤ : Submodule (convergent σ 𝕜)
      (ι → convergent σ 𝕜)) := by
  classical
  have := Fintype.ofFinite ι
  have hcomp (i : ι) : F i ∈ maximalIdeal (convergent σ 𝕜) ^ k := by
    rw [mem_maximalIdeal_pow_convergent_iff]
    refine MvPowerSeries.nat_le_order fun α hα ↦ ?_
    exact congrFun hF (i, ⟨α, mem_lowDegreeFinset.mpr hα⟩)
  have hF' : F = ∑ i, F i • Pi.single i 1 := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hF']
  exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem_smul (hcomp i) Submodule.mem_top

omit [Fintype σ] in
/-- **Cartan's closure theorem**: a submodule of `𝕜{X}^ι` contains every coefficientwise limit of
a sequence of its elements. -/
theorem mem_of_tendsto_coeff [Finite σ] [Finite ι]
    (N : Submodule (convergent σ 𝕜) (ι → convergent σ 𝕜)) {F : ℕ → ι → convergent σ 𝕜}
    (hF : ∀ j, F j ∈ N) {G : ι → convergent σ 𝕜}
    (hG : ∀ i α, Tendsto (fun j ↦ coeff α (F j i).1) atTop (𝓝 (coeff α (G i).1))) :
    G ∈ N := by
  have := Fintype.ofFinite σ
  refine mem_of_forall_mem_sup_pow_smul N fun k ↦ ?_
  -- the truncation of `N` is a closed subspace
  let T := truncCoeff (𝕜 := 𝕜) (ι := ι) (σ := σ) k
  let NT : Submodule 𝕜 (ι × lowDegreeFinset σ k → 𝕜) := (N.restrictScalars 𝕜).map T
  have hclosed : IsClosed (NT : Set (ι × lowDegreeFinset σ k → 𝕜)) :=
    NT.closed_of_finiteDimensional
  have hlim : Tendsto (fun j ↦ T (F j)) atTop (𝓝 (T G)) :=
    tendsto_pi_nhds.mpr fun iα ↦ hG iα.1 iα.2.1
  have hmem : T G ∈ NT :=
    hclosed.mem_of_tendsto hlim (Eventually.of_forall fun j ↦ ⟨F j, hF j, rfl⟩)
  obtain ⟨H, hH, hTH⟩ := hmem
  have hdiff : T (G - H) = 0 := by rw [map_sub, hTH, sub_self]
  have := mem_pow_smul_top_of_truncCoeff_eq_zero hdiff
  rw [show G = H + (G - H) by abel]
  exact Submodule.add_mem_sup hH this

end AnalyticGeometry
