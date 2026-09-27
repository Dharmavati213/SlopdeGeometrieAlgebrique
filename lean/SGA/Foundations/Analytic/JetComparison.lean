/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Analytic.Completion
import SGA.Foundations.Analytic.Analytification

/-!
# Jets of algebraic and analytic functions

Let `A = 𝕜[x₁, …, xₙ]/(g)` and `x` a point of `Z(g)`, with maximal ideal `𝔪ₓ ⊆ A`. The canonical
homomorphism `A → 𝒪_{Spec(A)^an, x}` induces isomorphisms
`A/𝔪ₓᵐ ≅ 𝒪_{Spec(A)^an, x}/𝔪ᵐ` for every `m` (`bijective_quotientMap_germHom`): an analytic
germ agrees with its Taylor polynomial up to order `m`, and a polynomial which lies in
`𝔪ᵐ + (g)` analytically already does so algebraically (truncate the Taylor expansions). In other
words `𝒪_{X,x} → 𝒪_{X^an,x}` induces an isomorphism of completions ([SGA 1, XII.2.1];
[Serre, *GAGA*, §1, Prop. 3]).
-/

universe u

noncomputable section

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace Filter MvPowerSeries IsLocalRing

namespace AnalyticGeometry

/-! ### Translations of polynomials -/

section Translate

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] {n : ℕ}

/-- The translation `p ↦ p(z + a)` of polynomials. -/
def translate (a : Fin n → 𝕜) : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] MvPolynomial (Fin n) 𝕜 :=
  MvPolynomial.aeval fun i ↦ MvPolynomial.X i + MvPolynomial.C (a i)

@[simp] lemma eval_translate (a w : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    MvPolynomial.eval w (translate a p) = MvPolynomial.eval (w + a) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [translate]
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, hp, map_mul]
    simp [translate]

lemma translate_translate (a b : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    translate a (translate b p) = translate (a + b) p := by
  have : (translate a).comp (translate b) = translate (a + b) :=
    MvPolynomial.algHom_ext fun i ↦ by
      simp only [AlgHom.comp_apply, translate, MvPolynomial.aeval_X, map_add,
        MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Pi.add_apply]
      ring
  exact congr($this p)

@[simp] lemma translate_zero (p : MvPolynomial (Fin n) 𝕜) : translate 0 p = p := by
  have : translate (0 : Fin n → 𝕜) = AlgHom.id 𝕜 _ :=
    MvPolynomial.algHom_ext fun i ↦ by simp [translate]
  exact congr($this p)

lemma translate_neg_translate (a : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    translate (-a) (translate a p) = p := by
  rw [translate_translate, neg_add_cancel, translate_zero]

lemma translate_translate_neg (a : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    translate a (translate (-a) p) = p := by
  rw [translate_translate, add_neg_cancel, translate_zero]

/-- The translate of the ideal of the origin is the ideal of the point `a`. -/
lemma map_translate_idealOfVars_le (a : Fin n → 𝕜) :
    (MvPolynomial.idealOfVars (Fin n) 𝕜).map (translate (-a)) ≤
      RingHom.ker (MvPolynomial.eval a) := by
  rw [Ideal.map_le_iff_le_comap, MvPolynomial.idealOfVars, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  simp

end Translate

/-! ### Polynomials as convergent power series and as germs -/

section Germs

lemma tsumEval_coe_mvPolynomial {𝕜 : Type u} [NontriviallyNormedField 𝕜] {σ : Type*}
    (q : MvPolynomial σ 𝕜) (w : σ → 𝕜) :
    tsumEval (q : MvPowerSeries σ 𝕜) w = MvPolynomial.eval w q := by
  rw [tsumEval, tsum_eq_sum (s := q.support), MvPolynomial.eval_eq]
  · refine Finset.sum_congr rfl fun d _ ↦ ?_
    rw [MvPolynomial.coeff_coe]
    rfl
  · intro d hd
    rw [MvPolynomial.coeff_coe, MvPolynomial.notMem_support_iff.mp hd, zero_mul]

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n : ℕ}

/-- The germ at `a` of a polynomial function is the convergent series of its translate. -/
lemma germOf_eval_eq_convergentStalkEquiv (a : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    germOf (fun z ↦ MvPolynomial.eval z p) (analyticAt_eval_mvPolynomial p a) =
      convergentStalkEquiv a (polynomialToConvergent (translate a p)) := by
  rw [convergentStalkEquiv_apply, convergentToStalk_apply, germOf_eq_germOf_iff]
  refine Eventually.of_forall fun y ↦ ?_
  dsimp only
  rw [coe_polynomialToConvergent, tsumEval_coe_mvPolynomial, eval_translate, sub_add_cancel]

lemma map_maximalIdeal_convergentStalkEquiv (a : Fin n → 𝕜) :
    (maximalIdeal (convergent (Fin n) 𝕜)).map (convergentStalkEquiv a) =
      maximalIdeal
        ((analyticPresheaf 𝕜 (Fin n → 𝕜)).stalk a) := by
  ext t
  rw [Ideal.mem_map_of_equiv, mem_maximalIdeal_stalk_iff]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [convergentStalkEquiv_apply, evalStalk_convergentToStalk]
    exact mem_maximalIdeal_convergent_iff.mp hf
  · intro ht
    refine ⟨(convergentStalkEquiv a).symm t, ?_, by simp⟩
    rw [mem_maximalIdeal_convergent_iff, ← evalStalk_convergentToStalk a,
      ← convergentStalkEquiv_apply, RingEquiv.apply_symm_apply]
    exact ht

/-- Germs at `a` of polynomial functions, as a ring homomorphism `𝕜[x] → 𝒪_{𝕜ⁿ,a}`. -/
def polyGermHom (a : Fin n → 𝕜) :
    MvPolynomial (Fin n) 𝕜 →+* (analyticPresheaf 𝕜 (Fin n → 𝕜)).stalk
      a :=
  (convergentStalkEquiv a : convergent (Fin n) 𝕜 →+* _).comp
    ((polynomialToConvergent : MvPolynomial (Fin n) 𝕜 →ₐ[𝕜] _).toRingHom.comp
      (translate a).toRingHom)

lemma polyGermHom_apply (a : Fin n → 𝕜) (p : MvPolynomial (Fin n) 𝕜) :
    polyGermHom a p = germOf (fun z ↦ MvPolynomial.eval z p) (analyticAt_eval_mvPolynomial p a) :=
  (germOf_eval_eq_convergentStalkEquiv a p).symm

end Germs

/-! ### Truncation of products -/

lemma coeff_truncTotal_mul_of_lt {σ : Type*} [Finite σ] {R : Type*} [CommRing R] {m : ℕ}
    (C G : MvPowerSeries σ R) {d : σ →₀ ℕ} (hd : d.degree < m) :
    coeff d ((truncTotal m C : MvPowerSeries σ R) * G) = coeff d (C * G) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  rw [MvPolynomial.coeff_coe, coeff_truncTotal]
  have := Finset.mem_antidiagonal.mp hq
  have h : q.1.degree ≤ d.degree := by
    rw [← this, map_add]
    exact Nat.le_add_right _ _
  omega

/-! ### Comparison of jets -/

section Jets

variable {𝕜 : Type} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] {n k : ℕ}
  (g : Fin k → MvPolynomial (Fin n) 𝕜) (x : (polynomialModel g).zeroSet)

lemma polyGermHom_mem_ideal (i : Fin k) :
    polyGermHom (x : Fin n → 𝕜) (g i) ∈ (polynomialModel g).ideal x
      ((polynomialModel g).mem_U x) := by
  rw [polyGermHom_apply]
  exact Ideal.subset_span ⟨i, rfl⟩

/-- The homomorphism `A → 𝒪_{𝕜ⁿ,x}/(g)`, `A = 𝕜[x]/(g)`. -/
def fiberHom : PresentedAlgebra g →+* (polynomialModel g).Fiber x :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (polyGermHom (x : Fin n → 𝕜))) fun a ha ↦ by
    have : Ideal.span (Set.range g) ≤ RingHom.ker
        ((Ideal.Quotient.mk ((polynomialModel g).ideal x ((polynomialModel g).mem_U x))).comp
          (polyGermHom (x : Fin n → 𝕜))) := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (polyGermHom_mem_ideal g x i)
    exact RingHom.mem_ker.mp (this ha)

lemma fiberHom_mk (p : MvPolynomial (Fin n) 𝕜) :
    fiberHom g x (Ideal.Quotient.mk _ p) =
      (polynomialModel g).classOf x (fun z ↦ MvPolynomial.eval z p)
        (analyticAt_eval_mvPolynomial p _) := by
  rw [fiberHom, Ideal.Quotient.lift_mk, RingHom.comp_apply, polyGermHom_apply]
  rfl

lemma maximalIdeal_fiber :
    maximalIdeal ((polynomialModel g).Fiber x) =
      (maximalIdeal ((analyticPresheaf 𝕜 (Fin n → 𝕜)).stalk
        (x : Fin n → 𝕜))).map (Ideal.Quotient.mk _) :=
  (IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm

lemma maximalIdeal_fiber_pow (m : ℕ) :
    maximalIdeal ((polynomialModel g).Fiber x) ^ m =
      ((maximalIdeal (convergent (Fin n) 𝕜) ^ m).map
        (convergentStalkEquiv (x : Fin n → 𝕜))).map (Ideal.Quotient.mk _) := by
  rw [maximalIdeal_fiber, ← map_maximalIdeal_convergentStalkEquiv, Ideal.map_pow,
    Ideal.map_pow]

/-- Every class in `𝒪_{𝕜ⁿ,x}/(g)` agrees with a polynomial up to order `m`. -/
lemma exists_fiberHom_sub_mem (m : ℕ) (t : (polynomialModel g).Fiber x) :
    ∃ a : PresentedAlgebra g, fiberHom g x a - t ∈ maximalIdeal _ ^ m := by
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective t
  obtain ⟨F, rfl⟩ := (convergentStalkEquiv (x : Fin n → 𝕜)).surjective s
  refine ⟨Ideal.Quotient.mk _ (translate (-(x : Fin n → 𝕜)) (truncTotal m F.1)), ?_⟩
  rw [fiberHom, Ideal.Quotient.lift_mk, RingHom.comp_apply, ← map_sub, maximalIdeal_fiber_pow]
  refine Ideal.mem_map_of_mem _ ?_
  rw [polyGermHom, RingHom.comp_apply, RingHom.comp_apply]
  change convergentStalkEquiv _ (polynomialToConvergent (translate _ (translate _ _))) -
    convergentStalkEquiv _ F ∈ _
  rw [translate_translate_neg, ← map_sub]
  refine Ideal.mem_map_of_mem _ ?_
  rw [mem_maximalIdeal_pow_convergent_iff]
  change (m : ℕ∞) ≤ ((polynomialToConvergent _).1 - F.1).order
  rw [coe_polynomialToConvergent]
  exact le_order_truncTotal_sub _ le_rfl

/-- A polynomial whose germ at `x` lies in `𝔪ᵐ + (g)` lies in `𝔪ₓᵐ + (g)`: truncate the Taylor
expansions of the coefficients at order `m`. -/
lemma mem_pow_of_fiberHom_mem (m : ℕ) (a : PresentedAlgebra g)
    (ha : fiberHom g x a ∈ maximalIdeal _ ^ m) : a ∈ RingHom.ker (evalPoint x) ^ m := by
  classical
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  set e := convergentStalkEquiv (𝕜 := 𝕜) (x : Fin n → 𝕜)
  rw [fiberHom, Ideal.Quotient.lift_mk, RingHom.comp_apply, maximalIdeal_fiber_pow,
    Ideal.mem_quotient_iff_mem_sup] at ha
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ha
  rw [LocalModelData.ideal, Ideal.mem_span_range_iff_exists_fun] at hv
  obtain ⟨c, rfl⟩ := hv
  obtain ⟨U, hU, rfl⟩ := (Ideal.mem_map_of_equiv e _).mp hu
  -- the relation among convergent series
  have hpoly : ∀ q : MvPolynomial (Fin n) 𝕜,
      e (polynomialToConvergent (translate (x : Fin n → 𝕜) q)) = polyGermHom (x : Fin n → 𝕜) q :=
    fun _ ↦ rfl
  have hrel : polynomialToConvergent (translate (x : Fin n → 𝕜) p) =
      U + ∑ i, e.symm (c i) * polynomialToConvergent (translate (x : Fin n → 𝕜) (g i)) := by
    apply e.injective
    rw [map_add, map_sum, hpoly, ← huv]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, RingEquiv.apply_symm_apply, hpoly, polyGermHom_apply]
    rfl
  -- truncation at order `m`
  set Q : MvPolynomial (Fin n) 𝕜 := translate (x : Fin n → 𝕜) p -
    ∑ i, truncTotal m (e.symm (c i)).1 * translate (x : Fin n → 𝕜) (g i) with hQ
  have hQm : Q ∈ MvPolynomial.idealOfVars (Fin n) 𝕜 ^ m := by
    refine (MvPolynomial.mem_pow_idealOfVars_iff' m Q).mpr fun d hd ↦ ?_
    have h₁ := congr_arg (fun F : convergent (Fin n) 𝕜 ↦ coeff d F.1) hrel
    simp only [coe_polynomialToConvergent, AddMemClass.coe_add, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul, map_add, map_sum, MvPolynomial.coeff_coe] at h₁
    have hU0 : coeff d U.1 = 0 :=
      coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hd)
        (mem_maximalIdeal_pow_convergent_iff.mp hU))
    rw [hQ, MvPolynomial.coeff_sub, MvPolynomial.coeff_sum, h₁, hU0, zero_add, sub_eq_zero]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← MvPolynomial.coeff_coe, MvPolynomial.coe_mul, coeff_truncTotal_mul_of_lt _ _ hd]
  -- translating back
  have hp : p = translate (-(x : Fin n → 𝕜)) Q +
      ∑ i, translate (-(x : Fin n → 𝕜)) (truncTotal m (e.symm (c i)).1) * g i := by
    rw [hQ, map_sub, translate_neg_translate, map_sum]
    simp only [map_mul, translate_neg_translate]
    ring
  rw [hp, map_add, map_sum]
  have hg0 : ∀ i, (Ideal.Quotient.mk (Ideal.span (Set.range g))) (g i) = 0 := fun i ↦
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  rw [Finset.sum_eq_zero fun i _ ↦ by rw [map_mul, hg0 i, mul_zero], add_zero]
  have hle : (MvPolynomial.idealOfVars (Fin n) 𝕜 ^ m).map (translate (-(x : Fin n → 𝕜))) ≤
      (RingHom.ker (MvPolynomial.eval (x : Fin n → 𝕜))) ^ m := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono (map_translate_idealOfVars_le _) m
  have hker : (RingHom.ker (MvPolynomial.eval (x : Fin n → 𝕜))).map
      (Ideal.Quotient.mk (Ideal.span (Set.range g))) ≤ RingHom.ker (evalPoint x) := by
    rw [Ideal.map_le_iff_le_comap]
    intro q hq
    rw [Ideal.mem_comap, RingHom.mem_ker, evalPoint_mk]
    exact hq
  have h₂ : translate (-(x : Fin n → 𝕜)) Q ∈ RingHom.ker (MvPolynomial.eval (x : Fin n → 𝕜)) ^ m :=
    hle (Ideal.mem_map_of_mem _ hQm)
  have h₃ := Ideal.mem_map_of_mem (Ideal.Quotient.mk (Ideal.span (Set.range g))) h₂
  rw [Ideal.map_pow] at h₃
  exact Ideal.pow_right_mono hker m h₃

lemma ker_evalPoint_pow_le_comap_fiber (m : ℕ) :
    RingHom.ker (evalPoint x) ^ m ≤ (maximalIdeal ((polynomialModel g).Fiber x) ^ m).comap
      (fiberHom g x) := by
  refine (Ideal.pow_right_mono ?_ m).trans (Ideal.le_comap_pow _ m)
  intro a ha
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [RingHom.mem_ker, evalPoint_mk] at ha
  rw [Ideal.mem_comap, fiberHom_mk, LocalModelData.mem_maximalIdeal_fiber_iff,
    LocalModelData.evalFiber_classOf]
  exact ha

/-- **Jets of algebraic and analytic functions agree**: `A/𝔪ₓᵐ ≅ (𝒪_{𝕜ⁿ,x}/(g))/𝔪ᵐ`. -/
theorem bijective_quotientMap_fiberHom (m : ℕ)
    (h : RingHom.ker (evalPoint x) ^ m ≤ (maximalIdeal ((polynomialModel g).Fiber x) ^ m).comap
      (fiberHom g x)) :
    Function.Bijective (Ideal.quotientMap _ (fiberHom g x) h) := by
  refine ⟨Ideal.quotientMap_injective' fun a ha ↦ mem_pow_of_fiberHom_mem g x m a ha, ?_⟩
  intro y
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨a, ha⟩ := exists_fiberHom_sub_mem g x m t
  exact ⟨Ideal.Quotient.mk _ a, by
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    exact ha⟩

omit [CompleteSpace 𝕜] in
lemma mem_maximalIdeal_pow_iff_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) (r : R) (m : ℕ) :
    e r ∈ maximalIdeal S ^ m ↔ r ∈ maximalIdeal R ^ m := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, ← Ideal.map_pow, Ideal.mem_map_of_equiv]
  constructor
  · rintro ⟨r', hr', h⟩
    rwa [e.injective h] at hr'
  · exact fun hr ↦ ⟨r, hr, rfl⟩

instance isLocalRing_stalk_analytification :
    IsLocalRing ((analytification g).presheaf.stalk x) :=
  (analytification g).isLocalRing x

/-- The homomorphism `A → 𝒪_{Spec(A)^an, x}` sending an element of `A` to the germ of the analytic
function it defines. -/
def stalkGermHom : PresentedAlgebra g →+* (analytification g).presheaf.stalk x :=
  ((analytification g).presheaf.Γgerm x).hom.comp (algebraToSections g)

lemma stalkIso_stalkGermHom (a : PresentedAlgebra g) :
    (polynomialModel g).stalkIso x (stalkGermHom g x a) = fiberHom g x a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [fiberHom_mk]
  exact (polynomialModel g).stalkToFiber_germ_globalSection x _
    fun y _ ↦ analyticAt_eval_mvPolynomial p y

lemma ker_evalPoint_pow_le_comap (m : ℕ) :
    RingHom.ker (evalPoint x) ^ m ≤
      (maximalIdeal ((analytification g).presheaf.stalk x) ^ m).comap (stalkGermHom g x) := by
  intro a ha
  have h₁ : (polynomialModel g).stalkIso x (stalkGermHom g x a) ∈
      maximalIdeal ((polynomialModel g).Fiber x) ^ m := by
    rw [stalkIso_stalkGermHom]
    exact ker_evalPoint_pow_le_comap_fiber g x m ha
  exact (mem_maximalIdeal_pow_iff_of_ringEquiv ((polynomialModel g).stalkIso x) _ m).mp h₁

/-- **XII.2.1, comparison of jets**: for `A = 𝕜[x]/(g)` and a point `x ∈ Z(g)` with maximal ideal
`𝔪ₓ ⊆ A`, the canonical homomorphism `A → 𝒪_{Spec(A)^an, x}` induces isomorphisms
`A/𝔪ₓᵐ ≅ 𝒪_{Spec(A)^an, x}/𝔪ᵐ` for every `m`. Equivalently, `𝒪_{X,x} → 𝒪_{X^an,x}` induces an
isomorphism of completions. -/
theorem bijective_quotientMap_stalkGermHom (m : ℕ)
    (h : RingHom.ker (evalPoint x) ^ m ≤
      (maximalIdeal ((analytification g).presheaf.stalk x) ^ m).comap (stalkGermHom g x)) :
    Function.Bijective (Ideal.quotientMap _ (stalkGermHom g x) h) := by
  set e := (polynomialModel g).stalkIso x
  refine ⟨Ideal.quotientMap_injective' fun a ha ↦ ?_, ?_⟩
  · refine mem_pow_of_fiberHom_mem g x m a ?_
    rw [← stalkIso_stalkGermHom]
    exact (mem_maximalIdeal_pow_iff_of_ringEquiv e _ m).mpr ha
  · intro y
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_fiberHom_sub_mem g x m (e s)
    refine ⟨Ideal.Quotient.mk _ a, ?_⟩
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
    refine (mem_maximalIdeal_pow_iff_of_ringEquiv e _ m).mp ?_
    have h₁ : e (stalkGermHom g x a - s) = fiberHom g x a - e s := by
      rw [← stalkIso_stalkGermHom]
      exact map_sub e _ _
    rw [h₁]
    exact ha

end Jets

end AnalyticGeometry
