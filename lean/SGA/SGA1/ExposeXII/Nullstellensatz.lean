/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Flat.TorsionFree
import SGA.SGA1.ExposeXII.AnalyticAffine
import SGA.SGA1.ExposeXII.Comparison
import SGA.SGA1.ExposeXII.JacobsonConstructible
import SGA.SGA1.ExposeXII.SchemePoints
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import SGA.SGA1.ExposeI.Permanence

/-!
# SGA 1, Exposé XII, 2.2: the closure comparison from the analytic Nullstellensatz

SGA proves XII.2.2 (for `T` locally constructible in `X`, the closure of `T(ℂ)` in `X(ℂ)` is
`(closure T)(ℂ)`) with Rückert's Nullstellensatz for the local rings of `X^an`, recorded here as
`AffineAnalytification.RueckertNullstellensatzStatement`. We derive XII.2.2 from it:

* for `a` a non-zero-divisor of `A = ℂ[x]/(g)`, the points where `a` does not vanish are dense in
  `X(ℂ)` (`AffineAnalytification.dense_evalPoint_ne_zero`): otherwise the germ of `a` at some
  point would be nilpotent, while `A → 𝒪_{X^an, x}` is flat (`SGA.Foundations.Analytic`);
* hence (prime avoidance, `exists_mem_nonZeroDivisors_basicOpen_le`) every dense open subset `U`
  of `Spec A`, `A` reduced of finite type, has `U(ℂ)` dense (`Points.dense_preimage_of_isOpen`);
* passing to the reduced closure of a locally closed set and decomposing a constructible set,
  XII.2.2 for affine `X` (`Points.closureComparisonStatement_of_rueckert`) and then for all `X`
  locally of finite type (`SchemePoints.closureComparisonStatement_of_rueckert`).

Consequently XII.2.3, XII.3.2 (ii), XII.3.1 (viii) for `X → Spec ℂ`, and the closedness part of
the converse of XII.3.2 (v), all proved from `ClosureComparisonStatement`, hold given the
Nullstellensatz.
-/

noncomputable section

open CategoryTheory Topology Set Filter AlgebraicGeometry AnalyticGeometry

namespace SGA.SGA1.ExposeXII

namespace AffineAnalytification

/-- XII.2.2, analytic input (statement only), Rückert's Nullstellensatz: for `x ∈ Z(g) ⊆ ℂⁿ` and
a function `G` analytic at `x` vanishing on `Z(g)` near `x`, the class of `G` in
`𝒪_{X^an, x} = 𝒪_{ℂⁿ, x}/(g)` is nilpotent. -/
def RueckertNullstellensatzStatement : Prop :=
  ∀ (n k : ℕ) (g : Fin k → MvPolynomial (Fin n) ℂ) (x : (polynomialModel g).zeroSet)
    (G : (Fin n → ℂ) → ℂ) (hG : AnalyticAt ℂ G x),
    (∀ᶠ y in 𝓝 x, G ((y : (polynomialModel g).zeroSet) : Fin n → ℂ) = 0) →
      IsNilpotent ((polynomialModel g).classOf x G hG)

variable {n k : ℕ} (g : Fin k → MvPolynomial (Fin n) ℂ)

/-- XII.2.2 for `D(a) ⊆ Spec A`, `a` a non-zero-divisor of `A = ℂ[x]/(g)`, from Rückert's
Nullstellensatz: the points of `Z(g)` where `a` does not vanish are dense. The germ of `a` at a
point where `a` vanishes identically nearby would be nilpotent, while it is a non-zero-divisor
since `A → 𝒪_{X^an, x}` is flat. -/
theorem dense_evalPoint_ne_zero (H : RueckertNullstellensatzStatement) {a : PresentedAlgebra g}
    (ha : a ∈ nonZeroDivisors (PresentedAlgebra g)) :
    Dense {y : (polynomialModel g).zeroSet | evalPoint y a ≠ 0} := by
  rw [dense_iff_inter_open]
  intro W hW ⟨x, hxW⟩
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hvan : ∀ᶠ y in 𝓝 x, (fun z : Fin n → ℂ ↦ MvPolynomial.eval z p)
      ((y : (polynomialModel g).zeroSet) : Fin n → ℂ) = 0 := by
    filter_upwards [hW.mem_nhds hxW] with y hy
    by_contra hne
    exact (eq_empty_iff_forall_notMem.mp hempty) y ⟨hy, by rwa [mem_ofPred_eq, evalPoint_mk]⟩
  have hnil := H n k g x _ (analyticAt_eval_mvPolynomial p _) hvan
  rw [← fiberHom_mk, ← stalkIso_stalkGermHom] at hnil
  have hnil' : IsNilpotent (stalkGermHom g x (Ideal.Quotient.mk _ p)) :=
    (IsNilpotent.map_iff ((polynomialModel g).stalkIso x).injective).mp hnil
  let := (stalkGermHom g x).toAlgebra
  have : Module.Flat (PresentedAlgebra g) ((analytification g).presheaf.stalk x) :=
    flat_stalkGermHom g x
  have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (M := (analytification g).presheaf.stalk x) ha
  obtain ⟨m, hm⟩ := hnil'
  have hreg' := hreg.pow m
  have : (Ideal.Quotient.mk (Ideal.span (range g)) p) ^ m •
      (1 : (analytification g).presheaf.stalk x) =
      (Ideal.Quotient.mk (Ideal.span (range g)) p) ^ m • 0 := by
    rw [smul_zero, Algebra.smul_def, map_pow, mul_one]
    exact hm
  exact one_ne_zero (hreg' this)

end AffineAnalytification

/-- In a reduced noetherian ring `A`, a dense open subset of `Spec A` contains a basic open set
`D(f)` with `f` a non-zero-divisor (prime avoidance). -/
lemma exists_mem_nonZeroDivisors_basicOpen_le {A : Type*} [CommRing A] [IsReduced A]
    [IsNoetherianRing A] (U : TopologicalSpace.Opens (PrimeSpectrum A))
    (hU : Dense (U : Set (PrimeSpectrum A))) :
    ∃ f ∈ nonZeroDivisors A, PrimeSpectrum.basicOpen f ≤ U := by
  classical
  set Z : Set (PrimeSpectrum A) := (U : Set (PrimeSpectrum A))ᶜ
  have hZ : IsClosed Z := U.2.isClosed_compl
  set I := PrimeSpectrum.vanishingIdeal Z
  have hmemZ (P : PrimeSpectrum A) : I ≤ P.asIdeal ↔ P ∈ Z := by
    have : P ∈ PrimeSpectrum.zeroLocus (I : Set A) ↔ P ∈ Z := by
      rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq]
    rw [← this, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hmin : ∀ p ∈ minimalPrimes A, ¬ I ≤ p := by
    intro p hp hIp
    have hpp : p.IsPrime := hp.1.1
    let P : PrimeSpectrum A := ⟨p, hpp⟩
    set s := hfin.toFinset.erase p
    have hJ : ¬ s.inf id ≤ p := by
      intro hJp
      obtain ⟨q, hqs, hqp⟩ := (hpp.inf_le' (s := s) (f := id)).mp hJp
      rw [Finset.mem_erase, Set.Finite.mem_toFinset] at hqs
      exact hqs.1 (le_antisymm hqp (hp.2 ⟨hqs.2.1.1, bot_le⟩ hqp))
    obtain ⟨h, hhJ, hhp⟩ := SetLike.not_le_iff_exists.mp hJ
    have hhq : ∀ q ∈ minimalPrimes A, q ≠ p → h ∈ q := fun q hq hqp ↦ by
      have : s.inf id ≤ q := Finset.inf_le (by
        rw [Finset.mem_erase, Set.Finite.mem_toFinset]
        exact ⟨hqp, hq⟩)
      exact this hhJ
    obtain ⟨R, hRh, hRU⟩ := hU.inter_open_nonempty (PrimeSpectrum.basicOpen h)
      (PrimeSpectrum.isOpen_basicOpen) ⟨P, hhp⟩
    obtain ⟨q, hq, hqR⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ R.asIdeal)
    by_cases hqp : q = p
    · subst hqp
      exact ((hmemZ R).mp (hIp.trans hqR)) hRU
    · exact hRh (hqR (hhq q hq hqp))
  have hnot : ¬ (I : Set A) ⊆ ⋃ q ∈ minimalPrimes A, (q : Set A) := by
    intro hsub
    obtain ⟨q, hq, hIq⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
      (fun q hq _ _ ↦ hq.1.1)).mp hsub
    exact hmin q hq hIq
  obtain ⟨f, hfI, hf⟩ := not_subset.mp hnot
  simp only [mem_iUnion, SetLike.mem_coe, not_exists] at hf
  refine ⟨f, SGA.SGA1.ExposeI.mem_nonZeroDivisors_of_forall_notMem_minimalPrimes
    fun q hq hfq ↦ hf q hq hfq, fun P hP ↦ ?_⟩
  by_contra hPU
  exact hP (((hmemZ P).mpr hPU) hfI)

namespace Points

open AffineAnalytification

variable (H : RueckertNullstellensatzStatement) {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra.FiniteType ℂ A]
include H

/-- XII.2.2 for `D(a)`, `a` a non-zero-divisor of `A` of finite type over `ℂ`, from Rückert's
Nullstellensatz: the points of `X(ℂ)` where `a` does not vanish are dense. -/
theorem dense_apply_ne_zero {a : A} (ha : a ∈ nonZeroDivisors A) :
    Dense {φ : Points ℂ A | φ a ≠ 0} := by
  have : Algebra.FinitePresentation ℂ A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  obtain ⟨n, k, g, ⟨e⟩⟩ := exists_presentedAlgebra_algEquiv ℂ A
  have ha' : e.symm a ∈ nonZeroDivisors (PresentedAlgebra g) := by
    refine mem_nonZeroDivisors_iff_right.mpr fun y hy ↦ ?_
    have h₀ : e y * a = 0 := by
      have := congrArg e hy
      rwa [map_mul, AlgEquiv.apply_symm_apply, map_zero] at this
    have := mem_nonZeroDivisors_iff_right.mp ha _ h₀
    rwa [map_eq_zero_iff _ e.injective] at this
  have h₁ := dense_evalPoint_ne_zero g H ha'
  have h₂ : Dense ((pointsHomeomorph g) ⁻¹'
      {y : (polynomialModel g).zeroSet | evalPoint y (e.symm a) ≠ 0}) :=
    h₁.preimage (pointsHomeomorph g).isOpenMap
  have h₃ := h₂.preimage (Points.homeomorph e).isOpenMap
  convert h₃ using 1
  ext φ
  simp only [mem_ofPred_eq, mem_preimage, evalPoint_pointsHomeomorph]
  change φ a ≠ 0 ↔ φ (e (e.symm a)) ≠ 0
  rw [AlgEquiv.apply_symm_apply]

/-- XII.2.2 for a dense open subset `U` of `X = Spec A`, `A` reduced of finite type over `ℂ`, from
Rückert's Nullstellensatz: `U(ℂ)` is dense in `X(ℂ)`. -/
theorem dense_preimage_of_isOpen [IsReduced A] (U : TopologicalSpace.Opens (PrimeSpectrum A))
    (hU : Dense (U : Set (PrimeSpectrum A))) :
    Dense (toPrimeSpectrum ⁻¹' (U : Set (PrimeSpectrum A)) : Set (Points ℂ A)) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A
  obtain ⟨f, hf, hfU⟩ := exists_mem_nonZeroDivisors_basicOpen_le U hU
  refine (dense_apply_ne_zero H hf).mono fun φ hφ ↦ hfU ?_
  exact toPrimeSpectrum_mem_basicOpen.mpr hφ

/-- XII.2.2 for a locally closed subset `L` of `X = Spec A`, from Rückert's Nullstellensatz: the
`ℂ`-points of the Zariski closure of `L` are in the closure of `L(ℂ)`. The closure of `L` is
`Spec A/J` (`J` the ideal of `L`, radical), in which `L` is a dense open subset. -/
theorem preimage_closure_subset_of_isLocallyClosed {L : Set (PrimeSpectrum A)}
    (hL : IsLocallyClosed L) :
    toPrimeSpectrum ⁻¹' closure L ⊆ closure (toPrimeSpectrum ⁻¹' L : Set (Points ℂ A)) := by
  intro φ hφ
  set J := PrimeSpectrum.vanishingIdeal L
  let q : A →ₐ[ℂ] A ⧸ J := Ideal.Quotient.mkₐ ℂ J
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective ℂ J
  have hker : RingHom.ker q = J := Ideal.Quotient.mkₐ_ker ℂ J
  have : IsReduced (A ⧸ J) :=
    (Ideal.isRadical_iff_quotient_reduced J).mp (PrimeSpectrum.isRadical_vanishingIdeal L)
  have : Algebra.FiniteType ℂ (A ⧸ J) := Algebra.FiniteType.of_surjective q hq
  have hcl : closure L = PrimeSpectrum.zeroLocus (J : Set A) :=
    (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure L).symm
  let c := PrimeSpectrum.comap q.toRingHom
  have hc : Topology.IsClosedEmbedding c :=
    PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ q.toRingHom hq
  have hrange : range c = closure L := by
    rw [range_comap_of_surjective _ q.toRingHom hq, hcl]
    congr 1
    exact congrArg (fun I : Ideal A ↦ (I : Set A)) hker
  have hmap (ψ : Points ℂ (A ⧸ J)) : toPrimeSpectrum (map q ψ) = c (toPrimeSpectrum ψ) :=
    PrimeSpectrum.ext (Ideal.ext fun a ↦ by simp [mem_ker, c])
  -- the open subset `U` of `Spec A/J` corresponding to `L`
  let U : TopologicalSpace.Opens (PrimeSpectrum (A ⧸ J)) :=
    ⟨c ⁻¹' coborder L, hL.isOpen_coborder.preimage hc.continuous⟩
  have himage : c '' (U : Set (PrimeSpectrum (A ⧸ J))) = L := by
    change c '' (c ⁻¹' coborder L) = L
    rw [image_preimage_eq_inter_range, hrange, inter_comm, closure_inter_coborder]
  have hUdense : Dense (U : Set (PrimeSpectrum (A ⧸ J))) := by
    rw [dense_iff_closure_eq]
    apply hc.injective.image_injective
    rw [← hc.closure_image_eq, himage, image_univ, hrange]
  have hD := dense_preimage_of_isOpen H U hUdense
  have hsub : map q '' (toPrimeSpectrum ⁻¹' (U : Set (PrimeSpectrum (A ⧸ J)))) ⊆
      toPrimeSpectrum ⁻¹' L := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [mem_preimage, hmap, ← himage]
    exact mem_image_of_mem c hψ
  have hφr : φ ∈ range (map (K := ℂ) q) := by
    rw [range_map_of_surjective hq, hker]
    intro a ha
    have : toPrimeSpectrum φ ∈ PrimeSpectrum.zeroLocus (J : Set A) := hcl ▸ hφ
    exact mem_ker.mp (this ha)
  obtain ⟨ψ₀, rfl⟩ := hφr
  have h₁ : map (K := ℂ) q ψ₀ ∈ map q '' closure
      (toPrimeSpectrum ⁻¹' (U : Set (PrimeSpectrum (A ⧸ J)))) :=
    mem_image_of_mem _ (hD.closure_eq ▸ mem_univ ψ₀)
  exact closure_mono hsub (image_closure_subset_closure_image (continuous_map q) h₁)

/-- XII.2.2, affine case, from Rückert's Nullstellensatz: for a constructible subset `T` of
`X = Spec A`, `A` of finite type over `ℂ`, the closure of `T(ℂ)` is the set of `ℂ`-points of the
Zariski closure of `T`. -/
theorem closure_preimage_eq {T : Set (PrimeSpectrum A)} (hT : IsConstructible T) :
    closure (toPrimeSpectrum ⁻¹' T : Set (Points ℂ A)) = toPrimeSpectrum ⁻¹' closure T := by
  refine subset_antisymm (closure_preimage_subset T) ?_
  obtain ⟨S, hS, hSlc, rfl⟩ := SGA.SGA1.ExposeXII.IsConstructible.exists_finite_isLocallyClosed hT
  rw [hS.closure_sUnion]
  intro φ hφ
  simp only [mem_preimage, mem_iUnion] at hφ
  obtain ⟨L, hL, hφL⟩ := hφ
  exact closure_mono (preimage_mono (subset_sUnion_of_mem hL))
    (preimage_closure_subset_of_isLocallyClosed H (hSlc L hL) hφL)

omit H in
/-- XII.2.2, affine case: Rückert's Nullstellensatz implies `ClosureComparisonStatement`. -/
theorem closureComparisonStatement_of_rueckert (H : RueckertNullstellensatzStatement) :
    ClosureComparisonStatement.{0} :=
  fun _ _ _ _ _ hT ↦ closure_preimage_eq H hT

end Points

namespace SchemePoints

attribute [local instance] sectionsAlgebra

variable {K : Type} [Field K] {X : Scheme.{0}} [X.Over (Spec (.of K))] {U : X.Opens}
  (hU : IsAffineOpen U)

lemma pt_chart_eq (φ : Points K Γ(X, U)) :
    (chart hU φ).pt = hU.fromSpec (Points.toPrimeSpectrum φ) := by
  change hU.fromSpec ((Spec.map (CommRingCat.ofHom φ.toRingHom)) (IsLocalRing.closedPoint K)) = _
  congr 1
  apply PrimeSpectrum.ext
  ext a
  change a ∈ (IsLocalRing.maximalIdeal K).comap φ.toRingHom ↔ _
  simp [Points.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

/-- XII.2.2: the scheme-level closure comparison follows from the affine one (closures are local,
and an affine open `U` of `X` has `U(ℂ) ≅ Points ℂ Γ(X, U)` over `Spec Γ(X, U) ≅ U`). -/
theorem closureComparisonStatement_of_affine (H : Points.ClosureComparisonStatement.{0}) :
    ClosureComparisonStatement := by
  intro X _ _ T hT
  refine subset_antisymm (continuous_pt.closure_preimage_subset T) fun y hy ↦ ?_
  obtain ⟨U, hU, hyU⟩ := exists_isAffineOpen_mem y
  obtain ⟨φ, rfl⟩ := exists_chart_eq hU y hyU
  have : Algebra.FiniteType ℂ Γ(X, U) := finiteType_sections hU
  have hemb : IsOpenEmbedding hU.fromSpec := hU.fromSpec.isOpenEmbedding
  set T' : Set (PrimeSpectrum Γ(X, U)) := hU.fromSpec ⁻¹' T
  have hT' : IsConstructible T' :=
    (hT.preimage_of_isOpenEmbedding hemb).isConstructible
  have hcl : closure T' = hU.fromSpec ⁻¹' closure T :=
    (hemb.isOpenMap.preimage_closure_eq_closure_preimage hemb.continuous T).symm
  have hφ : Points.toPrimeSpectrum φ ∈ closure T' := by
    rw [hcl]
    change hU.fromSpec (Points.toPrimeSpectrum φ) ∈ closure T
    rw [← pt_chart_eq]
    exact hy
  have h₁ : φ ∈ closure (Points.toPrimeSpectrum ⁻¹' T' : Set (Points ℂ Γ(X, U))) := by
    rw [H _ T' hT']
    exact hφ
  have h₂ : chart (K := ℂ) hU '' (Points.toPrimeSpectrum ⁻¹' T') ⊆ pt ⁻¹' T := by
    rintro _ ⟨ψ, hψ, rfl⟩
    rw [mem_preimage, pt_chart_eq]
    exact hψ
  exact closure_mono h₂ (image_closure_subset_closure_image (continuous_chart hU) ⟨φ, h₁, rfl⟩)

/-- XII.2.2 from Rückert's Nullstellensatz. -/
theorem closureComparisonStatement_of_rueckert
    (H : AffineAnalytification.RueckertNullstellensatzStatement) :
    ClosureComparisonStatement :=
  closureComparisonStatement_of_affine (Points.closureComparisonStatement_of_rueckert H)

end SchemePoints

end SGA.SGA1.ExposeXII
