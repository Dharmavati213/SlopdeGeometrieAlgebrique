/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.Analysis.Complex.Convex
import SGA.SGA1.ExposeXII.Etale
import SGA.SGA1.ExposeXII.Comparison

/-!
# SGA 1, Exposé XII, 5.1 for curves: étale coordinates at regular points

Let `A` be a `ℂ`-algebra of finite type and `y ∈ X(ℂ)`, `X = Spec A`, a point at which the local
ring `A_y` is a discrete valuation ring (a regular point of a curve). A *uniformizer* `s ∈ A` at
`y` (`s(y) = 0` and `s` generates the maximal ideal of `A_y`) is an étale coordinate: the map
`ℂ[t] → A`, `t ↦ s`, is étale on a basic open neighbourhood `D(g)` of `y`
(`Points.exists_etale_away_of_irreducible`). Consequently `φ ↦ φ(s)` is a local homeomorphism
`X(ℂ) → ℂ` at `y` (`Points.exists_openPartialHomeomorph_eval`), and `y` has arbitrarily small open
neighbourhoods `N` with `N ∖ {y}` connected and nonempty
(`Points.hasConnectedPuncturedNhds_of_isDiscreteValuationRing`, with the predicate
`HasConnectedPuncturedNhds`).

The algebra: on a basic open `D(g)` mapping injectively to `A_y` (`g` kills the kernel of
`A → A_y`, `Points.exists_mul_eq_zero_of_algebraMap_eq_zero`), `A_g` is a domain into which
`ℂ[t]` injects (`Points.aeval_ne_zero_of_irreducible`), so it is torsion free, hence flat, over
the principal ideal domain `ℂ[t]`; it is unramified at `y` because `t` generates the maximal ideal
of `A_y` (`Points.isUnramifiedAt_of_irreducible`, from `Algebra.isUnramifiedAt_iff_map_eq`), hence
on a smaller `D(g)`; flat, unramified and of finite presentation gives étale
(`Algebra.Etale.of_formallyUnramified_of_flat`), and étale maps are local homeomorphisms on
`ℂ`-points (`Points.isLocalHomeomorph_proj_of_etale`).

This is the local input of the extension of the Riemann existence theorem across finitely many
points of a normal curve (`SGA.SGA1.ExposeXII.RiemannExtensionTopology`,
`SGA.SGA1.ExposeXII.RiemannExtension`); it is this project's route, not SGA's. SGA proves XII.5.1
by reduction to normal `X` (descent along the normalization, 2) a)), then to the regular locus
(extension of coherent analytic sheaves across codimension `2`, 2) b)), and for affine regular `X`
by compactification, Hironaka's resolution [XII.8], XII.5.3 and GAGA (2) c)); the
Grauert–Remmert theorem XII.5.4 is mentioned there as the alternative used before [XII.8] was
available.

References: the étale coordinate is the curve case of "smooth morphisms are étale-locally
affine spaces" (Stacks 054L); the openness of the unramified locus is mathlib's
`Algebra.isOpen_unramifiedLocus`.
-/

noncomputable section

open Topology Set Filter Polynomial

namespace SGA.SGA1.ExposeXII

/-! ### Connected punctured neighbourhoods -/

section Punctured

variable {X : Type*} [TopologicalSpace X]

/-- `x` has arbitrarily small open neighbourhoods `N` such that `N ∖ {x}` is connected (and
nonempty): e.g. a point of a topological surface. -/
def HasConnectedPuncturedNhds (x : X) : Prop :=
  ∀ W ∈ 𝓝 x, ∃ N ⊆ W, IsOpen N ∧ x ∈ N ∧ IsPreconnected (N \ {x}) ∧ (N \ {x}).Nonempty

/-- A point with connected punctured neighbourhoods is not isolated. -/
lemma HasConnectedPuncturedNhds.neBot {x : X} (h : HasConnectedPuncturedNhds x) :
    (𝓝[≠] x).NeBot := by
  rw [nhdsWithin_neBot]
  intro t ht
  obtain ⟨N, hNt, -, -, -, z, hzN, hzx⟩ := h t ht
  exact ⟨z, hNt hzN, hzx⟩

/-- A punctured disc in `ℂ` is connected: it is the image of a half-plane under `exp`. -/
lemma isPreconnected_ball_diff_zero_complex (r : ℝ) :
    IsPreconnected (Metric.ball (0 : ℂ) r \ {0}) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [Metric.ball_eq_empty.mpr hr, empty_sdiff]
    exact isPreconnected_empty
  have : Metric.ball (0 : ℂ) r \ {0} = Complex.exp '' {w : ℂ | w.re < Real.log r} := by
    ext z
    simp only [Set.mem_sdiff, Metric.mem_ball, dist_zero_right, mem_singleton_iff, mem_image,
      mem_ofPred_eq]
    constructor
    · rintro ⟨hz, hz0⟩
      refine ⟨Complex.log z, ?_, Complex.exp_log hz0⟩
      rw [Complex.log_re]
      exact Real.log_lt_log (norm_pos_iff.mpr hz0) hz
    · rintro ⟨w, hw, rfl⟩
      refine ⟨?_, Complex.exp_ne_zero w⟩
      rw [Complex.norm_exp]
      exact (Real.lt_log_iff_exp_lt hr).mp hw
  rw [this]
  exact ((convex_halfSpace_re_lt _).isPreconnected).image _ Complex.continuous_exp.continuousOn

/-- A local homeomorphism `f` at `x` (`f` agrees near `x` with an open partial homeomorphism
whose source contains `x`), with `f x` having connected punctured neighbourhoods, gives `x`
connected punctured neighbourhoods. -/
lemma HasConnectedPuncturedNhds.of_openPartialHomeomorph {Y : Type*} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X Y) {x : X} (hx : x ∈ e.source)
    (h : HasConnectedPuncturedNhds (e x)) : HasConnectedPuncturedNhds x := by
  intro W hW
  have hW' : e.target ∩ e.symm ⁻¹' (interior W) ∈ 𝓝 (e x) :=
    Filter.inter_mem (e.open_target.mem_nhds (e.map_source hx))
      (e.continuousAt_symm (e.map_source hx) <| by
        rw [e.left_inv hx]; exact interior_mem_nhds.mpr hW)
  obtain ⟨N, hNW, hNo, hxN, hNc, hNn⟩ := h _ hW'
  have hNt : N ⊆ e.target := fun z hz ↦ (hNW hz).1
  refine ⟨e.symm '' N, ?_, e.isOpen_image_symm_of_subset_target hNo hNt,
    ⟨e x, hxN, e.left_inv hx⟩, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact interior_subset (hNW hz).2
  · have : e.symm '' N \ {x} = e.symm '' (N \ {e x}) := by
      rw [image_sdiff_of_injOn (e.symm.injOn.mono (e.symm_source ▸ hNt)) ?_, image_singleton,
        e.left_inv hx]
      exact singleton_subset_iff.mpr hxN
    rw [this]
    exact hNc.image _ (e.continuousOn_symm.mono (sdiff_subset.trans hNt))
  · obtain ⟨z, hzN, hzx⟩ := hNn
    refine ⟨e.symm z, mem_image_of_mem _ hzN, fun h ↦ hzx ?_⟩
    rw [mem_singleton_iff] at h ⊢
    rw [← h, e.right_inv (hNt hzN)]

/-- Every point of `ℂ` has connected punctured neighbourhoods (punctured discs). -/
lemma HasConnectedPuncturedNhds.complex (z : ℂ) : HasConnectedPuncturedNhds z := by
  intro W hW
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨Metric.ball z r, hrW, Metric.isOpen_ball, Metric.mem_ball_self hr, ?_, ?_⟩
  · have : Metric.ball z r \ {z} = (fun w ↦ w + z) '' (Metric.ball 0 r \ {0}) := by
      ext w
      simp only [Set.mem_sdiff, Metric.mem_ball, mem_singleton_iff, mem_image, dist_zero_right]
      constructor
      · rintro ⟨hw, hwz⟩
        refine ⟨w - z, ⟨?_, sub_ne_zero.mpr hwz⟩, sub_add_cancel w z⟩
        rwa [← dist_eq_norm]
      · rintro ⟨u, ⟨hu, hu0⟩, rfl⟩
        refine ⟨?_, fun h ↦ hu0 (by simpa using h)⟩
        rwa [dist_eq_norm, add_sub_cancel_right]
    rw [this]
    exact (isPreconnected_ball_diff_zero_complex r).image _ (by fun_prop)
  · refine ⟨z + (r / 2 : ℝ), ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    · rw [mem_singleton_iff, add_eq_left, Complex.ofReal_eq_zero]
      positivity

end Punctured

namespace Points

/-! ### `ℂ`-points of the affine line -/

/-- The `ℂ`-points of `ℂ[t]` are `ℂ`, through the value at `t`. -/
def polynomialHomeomorph : Points ℂ ℂ[X] ≃ₜ ℂ where
  toFun φ := φ X
  invFun z := ofAlgHom (aeval z)
  left_inv φ := by
    refine AlgHom.ext fun p ↦ ?_
    change aeval (φ X) p = φ p
    rw [aeval_algHom_apply, aeval_X_left, AlgHom.id_apply]
  right_inv z := by
    change aeval z X = z
    simp
  continuous_toFun := continuous_apply _
  continuous_invFun := continuous_iff.mpr fun p ↦ by
    change Continuous fun z : ℂ ↦ aeval z p
    simp_rw [coe_aeval_eq_eval]
    exact p.continuous

@[simp]
lemma polynomialHomeomorph_apply (φ : Points ℂ ℂ[X]) : polynomialHomeomorph φ = φ X := rfl

/-- A `ℂ`-point of `ℂ[t]` is evaluation at its value at `t`. -/
lemma apply_eq_eval_polynomial (φ : Points ℂ ℂ[X]) (p : ℂ[X]) : φ p = p.eval (φ X) := by
  rw [← coe_aeval_eq_eval, aeval_algHom_apply, aeval_X_left, AlgHom.id_apply]

/-! ### The étale coordinate -/

section Uniformizer

variable {A : Type*} [CommRing A] [Algebra ℂ A]

/-- The `ℂ[t]`-algebra structure on `A` given by `t ↦ s`. -/
abbrev coordAlgebra (s : A) : Algebra ℂ[X] A := (aeval s).toRingHom.toAlgebra

lemma coordAlgebra_isScalarTower (s : A) :
    letI := coordAlgebra s
    IsScalarTower ℂ ℂ[X] A :=
  letI := coordAlgebra s
  .of_algebraMap_eq fun c ↦ by
    change algebraMap ℂ A c = aeval s (algebraMap ℂ ℂ[X] c)
    rw [← C_eq_algebraMap, aeval_C]

lemma coordAlgebra_algebraMap (s : A) (p : ℂ[X]) :
    letI := coordAlgebra s
    algebraMap ℂ[X] A p = aeval s p := rfl

/-- In a domain, a nonzero polynomial over `ℂ` does not vanish at an irreducible element. -/
lemma aeval_ne_zero_of_irreducible {D : Type*} [CommRing D] [IsDomain D] [Algebra ℂ D] {ϖ : D}
    (hϖ : Irreducible ϖ) {p : ℂ[X]} (hp : p ≠ 0) : aeval ϖ p ≠ 0 := by
  rw [← C_leadingCoeff_mul_prod_multiset_X_sub_C (IsAlgClosed.card_roots_eq_natDegree (p := p)),
    map_mul,
    aeval_C, map_multiset_prod, Multiset.map_map]
  refine mul_ne_zero ((map_ne_zero_iff _ (algebraMap ℂ D).injective).mpr
    (leadingCoeff_ne_zero.mpr hp)) (Multiset.prod_ne_zero fun h ↦ ?_)
  obtain ⟨a, -, ha⟩ := Multiset.mem_map.mp h
  simp only [Function.comp_apply, map_sub, aeval_X, aeval_C] at ha
  rw [sub_eq_zero] at ha
  by_cases ha0 : a = 0
  · rw [ha0, map_zero] at ha
    exact hϖ.ne_zero ha
  · exact hϖ.not_isUnit (ha ▸ (Ne.isUnit ha0).map (algebraMap ℂ D))

omit [Algebra ℂ A] in
/-- If `A` is noetherian and `Q` is a prime, some `g ∉ Q` kills the kernel of `A → A_Q`. -/
lemma exists_mul_eq_zero_of_algebraMap_eq_zero [IsNoetherianRing A] (Q : Ideal A) [Q.IsPrime] :
    ∃ g ∉ Q, ∀ c : A, algebraMap A (Localization.AtPrime Q) c = 0 → g * c = 0 := by
  classical
  obtain ⟨t, ht⟩ := IsNoetherian.noetherian (RingHom.ker (algebraMap A
    (Localization.AtPrime Q)))
  have hk (k : A) (hk : k ∈ t) : ∃ m : Q.primeCompl, (m : A) * k = 0 := by
    have : k ∈ RingHom.ker (algebraMap A (Localization.AtPrime Q)) := ht ▸ Ideal.subset_span hk
    exact (IsLocalization.map_eq_zero_iff Q.primeCompl _ k).mp this
  choose m hm using hk
  refine ⟨∏ k ∈ t.attach, (m k.1 k.2 : A),
    Q.primeCompl.prod_mem fun k _ ↦ (m k.1 k.2).2, fun c hc ↦ ?_⟩
  have hc' : c ∈ Ideal.span (t : Set A) := by
    change c ∈ Submodule.span A (t : Set A)
    rw [ht]
    exact hc
  refine Submodule.span_induction (p := fun c _ ↦ (∏ k ∈ t.attach, (m k.1 k.2 : A)) * c = 0)
    (fun k hk ↦ ?_) (mul_zero _) (fun x y _ _ hx hy ↦ by rw [mul_add, hx, hy, add_zero])
    (fun a x _ hx ↦ by rw [smul_eq_mul, mul_left_comm, hx, mul_zero]) hc'
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_attach _ ⟨k, hk⟩), mul_right_comm, hm, zero_mul]

/-- A uniformizer at `y` vanishes at `y`: if the image of `s` in the discrete valuation ring
`A_y` is irreducible, then `s ∈ ker y`. -/
lemma apply_eq_zero_of_irreducible (y : Points ℂ A) {s : A}
    [IsDomain (Localization.AtPrime (ker y))]
    [IsDiscreteValuationRing (Localization.AtPrime (ker y))]
    (hϖ : Irreducible (algebraMap A (Localization.AtPrime (ker y)) s)) : y s = 0 := by
  refine mem_ker.mp ((IsLocalization.AtPrime.to_map_mem_maximal_iff
    (Localization.AtPrime (ker y)) (ker y) s).mp ?_)
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ]
  exact Ideal.mem_span_singleton_self _

variable [Algebra.FiniteType ℂ A]

/-- The étale coordinate, unramified at the point: for `y ∈ X(ℂ)` with `A_y` a discrete
valuation ring and `s` a uniformizer (so `s(y) = 0`, `apply_eq_zero_of_irreducible`),
`ℂ[t] → A`, `t ↦ s`, is unramified at `y`. -/
theorem isUnramifiedAt_of_irreducible (y : Points ℂ A) {s : A}
    [IsDomain (Localization.AtPrime (ker y))]
    [IsDiscreteValuationRing (Localization.AtPrime (ker y))]
    (hϖ : Irreducible (algebraMap A (Localization.AtPrime (ker y)) s)) :
    letI := coordAlgebra s
    Algebra.IsUnramifiedAt ℂ[X] (ker y) := by
  have hs := apply_eq_zero_of_irreducible y hϖ
  let := coordAlgebra s
  have := coordAlgebra_isScalarTower s
  set Q := ker y
  let p := Q.under ℂ[X]
  have hQm : IsLocalRing.maximalIdeal (Localization.AtPrime Q) =
      Ideal.span {algebraMap A (Localization.AtPrime Q) s} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp hϖ
  have hXp : (X : ℂ[X]) ∈ p := by
    change algebraMap ℂ[X] A X ∈ Q
    rw [coordAlgebra_algebraMap, aeval_X]
    exact mem_ker.mpr hs
  -- `p` is the kernel of the surjection `ℂ[t] → A → ℂ`, hence maximal
  have hpker : p = RingHom.ker (y.toRingHom.comp (algebraMap ℂ[X] A)) := by
    ext q
    simp [p, Q, Ideal.mem_comap, mem_ker]
  have : p.IsMaximal := by
    rw [hpker]
    refine RingHom.ker_isMaximal_of_surjective _ fun z ↦ ⟨Polynomial.C z, ?_⟩
    simp [coordAlgebra_algebraMap]
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have hsurj : Function.Surjective (algebraMap (ℂ[X] ⧸ p) (A ⧸ Q)) := by
    intro c
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨Ideal.Quotient.mk p (Polynomial.C (y c)), ?_⟩
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq]
    rw [coordAlgebra_algebraMap, aeval_C]
    exact sub_algebraMap_mem_ker y c |> fun h ↦ by
      rw [← neg_sub]; exact Q.neg_mem_iff.mpr h
  have : Algebra.IsIntegral (ℂ[X] ⧸ p) (A ⧸ Q) := .of_surjective (f := Algebra.ofId _ _) hsurj
  let := Ideal.Quotient.field p
  let := Ideal.Quotient.field Q
  have : CharZero (ℂ[X] ⧸ p) := charZero_of_injective_algebraMap
    (algebraMap ℂ (ℂ[X] ⧸ p)).injective
  have : Algebra.IsSeparable (ℂ[X] ⧸ p) (A ⧸ Q) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FiniteType ℂ[X] A := .of_restrictScalars_finiteType ℂ ℂ[X] A
  rw [Algebra.isUnramifiedAt_iff_map_eq ℂ[X] p Q]
  refine ⟨inferInstance, le_antisymm ?_ ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply ℂ[X] A,
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ Q]
    exact hq
  · rw [hQm, Ideal.span_le, Set.singleton_subset_iff]
    have : algebraMap A (Localization.AtPrime Q) s =
        algebraMap ℂ[X] (Localization.AtPrime Q) X := by
      rw [IsScalarTower.algebraMap_apply ℂ[X] A, coordAlgebra_algebraMap, aeval_X]
    rw [this]
    exact Ideal.mem_map_of_mem _ hXp

/-- **The étale coordinate** (the curve case of Stacks 054L): for `y ∈ X(ℂ)` with `A_y` a
discrete valuation ring and `s` a uniformizer at `y`, the map `ℂ[t] → A_g`, `t ↦ s`,
is étale for some `g ∈ A` with `g(y) ≠ 0` (on the basic open neighbourhood `D(g)` of `y`). -/
theorem exists_etale_away_of_irreducible (y : Points ℂ A) {s : A}
    [IsDomain (Localization.AtPrime (ker y))]
    [IsDiscreteValuationRing (Localization.AtPrime (ker y))]
    (hϖ : Irreducible (algebraMap A (Localization.AtPrime (ker y)) s)) :
    letI := coordAlgebra s
    ∃ g : A, y g ≠ 0 ∧ Algebra.Etale ℂ[X] (Localization.Away g) := by
  let := coordAlgebra s
  have := coordAlgebra_isScalarTower s
  set Q := ker y
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  have : Algebra.FiniteType ℂ[X] A := .of_restrictScalars_finiteType ℂ ℂ[X] A
  have hU := isUnramifiedAt_of_irreducible y hϖ
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hfQ, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show (⟨Q, inferInstance⟩ : PrimeSpectrum A) ∈ Algebra.unramifiedLocus ℂ[X] A from hU)
      Algebra.isOpen_unramifiedLocus
  have hfQ' : f ∉ Q := hfQ
  obtain ⟨g, hgQ, hg⟩ := exists_mul_eq_zero_of_algebraMap_eq_zero Q
  have hgfQ : g * f ∉ Q := fun h ↦ (Ideal.IsPrime.mem_or_mem inferInstance h).elim hgQ hfQ'
  refine ⟨g * f, fun h ↦ hgfQ (mem_ker.mpr h), ?_⟩
  let D := Localization.Away (g * f)
  have hfu : Algebra.FormallyUnramified ℂ[X] D :=
    Algebra.basicOpen_subset_unramifiedLocus_iff.mp
      (Set.Subset.trans (fun x hx ↦ PrimeSpectrum.basicOpen_mul_le_right g f hx) hf)
  let AQ := Localization.AtPrime Q
  have hunit : IsUnit (algebraMap A AQ (g * f)) :=
    IsLocalization.map_units AQ (⟨g * f, hgfQ⟩ : Q.primeCompl)
  let φ : D →ₐ[A] AQ := IsLocalization.Away.liftAlgHom (g * f) (f := Algebra.ofId A AQ) hunit
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨n, c, hc⟩ := IsLocalization.Away.surj (g * f) z
    have hc0 : algebraMap A AQ c = 0 := by
      rw [← φ.commutes, ← hc, map_mul, hz, zero_mul]
    have hgc : algebraMap A D c = 0 := by
      have h1 : algebraMap A D (g * f * c) = 0 := by
        rw [mul_right_comm, hg c hc0, zero_mul, map_zero]
      rwa [map_mul, IsUnit.mul_right_eq_zero (IsLocalization.Away.algebraMap_isUnit (g * f))] at h1
    rw [← hc] at hgc
    exact (IsUnit.mul_left_eq_zero ((IsLocalization.Away.algebraMap_isUnit (g * f)).pow n)).mp hgc
  have : IsDomain D := hφ.isDomain
  have hRD : Function.Injective (algebraMap ℂ[X] D) := by
    rw [injective_iff_map_eq_zero]
    intro q hq
    by_contra hq0
    refine aeval_ne_zero_of_irreducible hϖ hq0 ?_
    have : algebraMap ℂ[X] D q = algebraMap A D (aeval s q) := by
      rw [IsScalarTower.algebraMap_apply ℂ[X] A D]; rfl
    rw [this] at hq
    have h2 := congrArg φ hq
    rw [φ.commutes, map_zero] at h2
    rw [← h2]
    exact aeval_algHom_apply (IsScalarTower.toAlgHom ℂ A AQ) s q
  have : Module.IsTorsionFree ℂ[X] D := Module.isTorsionFree_iff_algebraMap_injective.mpr hRD
  have : Algebra.FiniteType ℂ[X] D :=
    .trans (S := A) inferInstance (IsLocalization.finiteType_of_monoid_fg (.powers (g * f)) D)
  have : Algebra.FinitePresentation ℂ[X] D := Algebra.FinitePresentation.of_finiteType.mp this
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- **The étale coordinate is a local chart**: for `y ∈ X(ℂ)` with `A_y` a discrete valuation
ring and `s` a uniformizer at `y`, the map `φ ↦ φ(s)` is a local homeomorphism
`X(ℂ) → ℂ` at `y`. -/
theorem exists_openPartialHomeomorph_eval (y : Points ℂ A) {s : A}
    [IsDomain (Localization.AtPrime (ker y))]
    [IsDiscreteValuationRing (Localization.AtPrime (ker y))]
    (hϖ : Irreducible (algebraMap A (Localization.AtPrime (ker y)) s)) :
    ∃ e : OpenPartialHomeomorph (Points ℂ A) ℂ, y ∈ e.source ∧ (fun φ : Points ℂ A ↦ φ s) = e := by
  obtain ⟨g, hg, hD⟩ := exists_etale_away_of_irreducible y hϖ
  let := coordAlgebra s
  have := coordAlgebra_isScalarTower s
  let D := Localization.Away g
  have : IsScalarTower ℂ ℂ[X] D := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply ℂ[X] A D, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] A,
      ← IsScalarTower.algebraMap_apply ℂ A D]
  let ι : Points ℂ D → Points ℂ A := map (IsScalarTower.toAlgHom ℂ A D)
  have hι : IsOpenEmbedding ι := isOpenEmbedding_map_of_isLocalizationAway g
  have hy : y ∈ ι '' univ := by
    rw [image_univ, range_map_of_isLocalizationAway g]
    exact hg
  have hloc : IsLocalHomeomorph (fun ψ : Points ℂ D ↦ ψ (algebraMap A D s)) := by
    have : (fun ψ : Points ℂ D ↦ ψ (algebraMap A D s)) =
        polynomialHomeomorph ∘ proj ℂ[X] D := by
      funext ψ
      simp only [Function.comp_apply, polynomialHomeomorph_apply, proj_apply]
      rw [IsScalarTower.algebraMap_apply ℂ[X] A D, coordAlgebra_algebraMap, aeval_X]
    rw [this]
    exact polynomialHomeomorph.isLocalHomeomorph.comp isLocalHomeomorph_proj_of_etale
  have h₁ : IsLocalHomeomorphOn ((fun φ : Points ℂ A ↦ φ s) ∘ ι) univ :=
    hloc.isLocalHomeomorphOn
  exact h₁.of_comp_right hι.isLocalHomeomorph.isLocalHomeomorphOn y hy

/-- At a point `y ∈ X(ℂ)` where `A_y` is a discrete valuation ring, `X(ℂ)` has arbitrarily small
open neighbourhoods `N` of `y` with `N ∖ {y}` connected and nonempty (preimages of discs under an
étale coordinate). -/
theorem hasConnectedPuncturedNhds_of_isDiscreteValuationRing (y : Points ℂ A)
    [IsDomain (Localization.AtPrime (ker y))]
    [IsDiscreteValuationRing (Localization.AtPrime (ker y))] :
    HasConnectedPuncturedNhds y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime (ker y))
  obtain ⟨⟨a, u⟩, hau⟩ := IsLocalization.mk'_surjective (ker y).primeCompl ϖ
  -- `a = ϖ u` is again a uniformizer
  have ha : Irreducible (algebraMap A (Localization.AtPrime (ker y)) a) := by
    have : algebraMap A (Localization.AtPrime (ker y)) a =
        ϖ * algebraMap A (Localization.AtPrime (ker y)) u := by
      rw [← hau, IsLocalization.mk'_spec]
    rw [this]
    exact (irreducible_mul_isUnit (IsLocalization.map_units _ u)).mpr hϖ
  obtain ⟨e, hye, he⟩ := exists_openPartialHomeomorph_eval y ha
  refine HasConnectedPuncturedNhds.of_openPartialHomeomorph e hye ?_
  rw [← congrFun he y]
  exact HasConnectedPuncturedNhds.complex _

end Uniformizer

end Points

end SGA.SGA1.ExposeXII
