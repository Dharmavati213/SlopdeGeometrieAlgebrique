/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import SGA.SGA1.ExposeXII.LocalTopologyCurves

/-!
# SGA 1, Exposé XII, 5.2: local contractibility at conical points

The topological input of XII.5.2 is pointwise: if every point `x` of `X(ℂ)` has arbitrarily small
open neighbourhoods contracting onto `x` (`HasContractibleNhdsRel x`), then `X(ℂ)` is strongly
locally contractible, and XII.5.2 follows from the Riemann existence theorem XII.5.1
(`schemeFundamentalGroupComparison_of_forall_hasContractibleNhdsRel`). This file proves the
property at the vertex of an affine quasi-homogeneous cone, and its invariance under étale maps:

* `Points.hasContractibleNhdsRel_of_isWeightedHomogeneous`: if `A = ℂ[z₁, …, zₙ]/I` with `I`
  homogeneous for positive weights `wᵢ` (for instance a cone over a projective variety, a union
  of coordinate subspaces such as a normal crossings divisor, or the simple surface singularities
  `x² + y² + zⁿ⁺¹`, …), the origin of `X(ℂ)`, `X = Spec A`, has small neighbourhoods
  `{|zᵢ| < ε}` contracting onto it by the weighted scaling `z ↦ (tʷⁱ zᵢ)`, `t ∈ [0, 1]`;
* `SchemePoints.hasContractibleNhdsRel_iff_of_etale`: the property is invariant under étale maps
  (which induce local homeomorphisms, XII.3.1 (iii)).

Not done: the assembled statement for schemes `X` which are étale-locally isomorphic to
quasi-homogeneous cones at every point (it needs the comparison between `Spec(A)(ℂ)` and the
affine `Points ℂ A` along the étale neighbourhoods), and the passage from analytic to étale-local
isomorphism (Artin approximation) that "varieties with simple singularities" would need. For
XII.5.2 itself this is superseded: `X(ℂ)` is semilocally simply connected for every `X`
(`semilocallySimplyConnectedStatement`, `LocalTopologySLSC.lean`), which is all XII.5.2 needs; what
the cone results add is *strong* local contractibility at such points.
-/

universe u

open Topology Set Filter Metric AlgebraicGeometry

namespace SGA.SGA1.ExposeXII

/-! ### Weighted scaling -/

section Scaling

variable {σ : Type*}

/-- Evaluating a weighted homogeneous polynomial of degree `d` at the weighted scaling
`(tʷⁱ zᵢ)ᵢ` of `z` multiplies its value by `tᵈ`. -/
lemma eval_weightedScaling_of_isWeightedHomogeneous {w : σ → ℕ} {g : MvPolynomial σ ℂ} {d : ℕ}
    (hg : g.IsWeightedHomogeneous w d) (t : ℂ) (z : σ → ℂ) :
    MvPolynomial.eval (fun i ↦ t ^ w i * z i) g = t ^ d * MvPolynomial.eval z g := by
  classical
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm ↦ ?_
  have hwm : Finsupp.weight w m = d := hg (MvPolynomial.mem_support_iff.mp hm)
  simp only [MvPolynomial.eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    ← pow_mul]
  rw [← hwm, Finsupp.weight_apply, Finsupp.sum, ← Finset.prod_pow_eq_pow_sum]
  simp only [smul_eq_mul, mul_comm (w _)]
  ring

/-- The zero set of an ideal which is homogeneous for the weights `w` is stable under weighted
scaling. -/
lemma eval_weightedScaling_eq_zero {w : σ → ℕ} {I : Ideal (MvPolynomial σ ℂ)}
    (hI : ∀ p ∈ I, ∀ d, MvPolynomial.weightedHomogeneousComponent w d p ∈ I) {z : σ → ℂ}
    (hz : ∀ p ∈ I, MvPolynomial.eval z p = 0) (t : ℂ) {p : MvPolynomial σ ℂ} (hp : p ∈ I) :
    MvPolynomial.eval (fun i ↦ t ^ w i * z i) p = 0 := by
  rw [← MvPolynomial.sum_weightedHomogeneousComponent w p,
    map_finsum _ (MvPolynomial.weightedHomogeneousComponent_finsupp p)]
  refine finsum_eq_zero_of_forall_eq_zero fun d ↦ ?_
  rw [eval_weightedScaling_of_isWeightedHomogeneous
    (MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d p),
    hz _ (hI p hp d), mul_zero]

variable [Finite σ]

/-- The vertex of a cone for a weighted scaling with positive weights has small neighbourhoods
contracting onto it: if `Z ⊆ ℂ^σ` contains `0` and is stable under `z ↦ (tʷⁱ zᵢ)ᵢ` for
`t ∈ [0, 1]`, the sets `Z ∩ {‖z‖ < ε}` contract onto `0` by this scaling. -/
theorem hasContractibleNhdsRel_zero_of_weightedScaling {w : σ → ℕ} (hw : ∀ i, 0 < w i)
    {Z : Set (σ → ℂ)} (hZ : ∀ z ∈ Z, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (fun i ↦ (t : ℂ) ^ w i * z i) ∈ Z)
    (h0 : (0 : σ → ℂ) ∈ Z) : HasContractibleNhdsRel (⟨0, h0⟩ : Z) := by
  have := Fintype.ofFinite σ
  intro N hN
  obtain ⟨U, hU, hUN⟩ := (mem_nhds_subtype Z _ N).mp hN
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  set V : Set Z := Subtype.val ⁻¹' ball 0 ε
  have hxV : (⟨0, h0⟩ : Z) ∈ V := mem_ball_self hε
  refine ⟨V, hxV, isOpen_ball.preimage continuous_subtype_val,
    (preimage_mono hεU).trans hUN, ?_⟩
  have hs (s : unitInterval) : 0 ≤ 1 - (s : ℝ) ∧ 1 - (s : ℝ) ≤ 1 :=
    ⟨by linarith [s.2.2], by linarith [s.2.1]⟩
  have hball (s : unitInterval) (z : σ → ℂ) (hz : z ∈ ball (0 : σ → ℂ) ε) :
      (fun i ↦ ((1 - (s : ℝ) : ℝ) : ℂ) ^ w i * z i) ∈ ball (0 : σ → ℂ) ε := by
    rw [mem_ball_zero_iff] at hz ⊢
    refine (pi_norm_lt_iff hε).mpr fun i ↦ ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hs s).1]
    calc (1 - (s : ℝ)) ^ w i * ‖z i‖ ≤ 1 * ‖z i‖ := by
          gcongr
          exact pow_le_one₀ (hs s).1 (hs s).2
      _ = ‖z i‖ := one_mul _
      _ ≤ ‖z‖ := norm_le_pi_norm z i
      _ < ε := hz
  let F : unitInterval × V → V := fun p ↦
    ⟨⟨fun i ↦ ((1 - (p.1 : ℝ) : ℝ) : ℂ) ^ w i * (p.2 : Z).1 i,
      hZ _ (p.2 : Z).2 _ (hs p.1).1 (hs p.1).2⟩, hball p.1 _ p.2.2⟩
  have hFc : Continuous F := by
    refine Continuous.subtype_mk (Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _) _
    exact ((Complex.continuous_ofReal.comp (continuous_const.sub
      (continuous_subtype_val.comp continuous_fst))).pow (w i)).mul
      ((continuous_apply i).comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp continuous_snd)))
  refine ⟨⟨⟨⟨F, hFc⟩, fun v ↦ ?_, fun v ↦ ?_⟩, fun t v hv ↦ ?_⟩⟩
  · refine Subtype.ext (Subtype.ext (funext fun i ↦ ?_))
    simp [F]
  · refine Subtype.ext (Subtype.ext (funext fun i ↦ ?_))
    simp [F, (hw i).ne']
  · rw [mem_singleton_iff] at hv
    subst hv
    refine Subtype.ext (Subtype.ext (funext fun i ↦ ?_))
    simp [F]

end Scaling

/-! ### Complex points of quasi-homogeneous cones -/

namespace Points

/-- The vertex of a quasi-homogeneous cone: let `q : ℂ[zᵢ, i ∈ σ] → A` be a presentation whose
kernel is homogeneous for positive weights `wᵢ`. Then the origin of `X(ℂ)`, `X = Spec A` (the
point with all coordinates `0`), has arbitrarily small open neighbourhoods contracting onto it. -/
theorem hasContractibleNhdsRel_of_isWeightedHomogeneous {A : Type*} [CommRing A] [Algebra ℂ A]
    {σ : Type*} [Finite σ] {q : MvPolynomial σ ℂ →ₐ[ℂ] A} (hq : Function.Surjective q)
    {w : σ → ℕ} (hw : ∀ i, 0 < w i)
    (hI : ∀ p ∈ RingHom.ker q, ∀ d, MvPolynomial.weightedHomogeneousComponent w d p ∈
      RingHom.ker q)
    (x : Points ℂ A) (hx : coords q x = 0) : HasContractibleNhdsRel x := by
  have hZ : ∀ z ∈ range (coords q), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (fun i ↦ (t : ℂ) ^ w i * z i) ∈ range (coords q) := by
    intro z hz t _ _
    rw [range_coords hq] at hz ⊢
    exact fun p hp ↦ eval_weightedScaling_eq_zero hI hz _ hp
  set Z := range (coords q)
  have h0 : (0 : σ → ℂ) ∈ Z := ⟨x, hx⟩
  let e : Points ℂ A ≃ₜ Z := (isClosedEmbedding_coords hq).isEmbedding.toHomeomorph
  have hex : e.symm ⟨0, h0⟩ = x := e.symm_apply_eq.mpr (Subtype.ext hx.symm)
  have := (hasContractibleNhdsRel_zero_of_weightedScaling hw hZ h0).homeomorph e.symm
  rwa [hex] at this

end Points

namespace SchemePoints

/-- `HasContractibleNhdsRel` is invariant under étale maps: for `f : Y → X` étale over `K`
(`K = ℂ`), `y ∈ Y(K)` has small neighbourhoods contracting onto it if and only if `f(y) ∈ X(K)`
does, since `Y(K) → X(K)` is a local homeomorphism (XII.3.1 (iii),
`isLocalHomeomorph_map_of_etale`). -/
theorem hasContractibleNhdsRel_iff_of_etale {K : Type u} [NontriviallyNormedField K]
    [CompleteSpace K] {X Y : Scheme.{u}} [X.Over (Spec (.of K))] [Y.Over (Spec (.of K))]
    (f : Y ⟶ X) [f.IsOver (Spec (.of K))] [Etale f] (y : SchemePoints K Y) :
    HasContractibleNhdsRel y ↔ HasContractibleNhdsRel (map (K := K) f y) :=
  (isLocalHomeomorph_map_of_etale f).hasContractibleNhdsRel_iff y

end SchemePoints

/-- XII.5.2 under a pointwise local condition: for `X` connected and locally of finite type over
`ℂ` such that every point of `X(ℂ)` has arbitrarily small open neighbourhoods contracting onto it
(the property holds at the vertex of an affine quasi-homogeneous cone,
`Points.hasContractibleNhdsRel_of_isWeightedHomogeneous`, and is invariant under étale maps,
`SchemePoints.hasContractibleNhdsRel_iff_of_etale`), the Riemann existence theorem XII.5.1
implies that `π₁(X, x)` is the profinite completion of `π₁(X(ℂ), x)`. -/
theorem schemeFundamentalGroupComparison_of_forall_hasContractibleNhdsRel
    (H : SchemeRiemannExistenceStatement) (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))]
    (hX : ∀ y : SchemePoints ℂ X, HasContractibleNhdsRel y) (hc : ConnectedSpace X)
    (x : SchemePoints ℂ X) :
    Nonempty (ExposeV.etaleFundamentalGroup ℂ x.1 ≃ₜ* ProfiniteGrp.ProfiniteCompletion.completion
      (GrpCat.of (FundamentalGroup (SchemePoints ℂ X) x))) :=
  have := StronglyLocallyContractibleSpace.of_forall_hasContractibleNhdsRel hX
  schemeFundamentalGroupComparison_of_semilocallySimplyConnectedSpace H X hc x

end SGA.SGA1.ExposeXII
