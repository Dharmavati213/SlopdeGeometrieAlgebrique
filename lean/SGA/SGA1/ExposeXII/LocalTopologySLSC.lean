/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Semialgebraic.LocalContractibility
import SGA.SGA1.ExposeXII.LocalTopologyLPC

/-!
# SGA 1, Exposé XII, 5.2: `X(ℂ)` is semilocally simply connected

For `X` locally of finite type over `ℂ`, the space `X(ℂ)` is semilocally simply connected
(`SchemePoints.semilocallySimplyConnectedSpace`, an instance;
`semilocallySimplyConnectedStatement`). With the local path-connectedness of `X(ℂ)`
(`LocalTopologyLPC.lean`) this is the whole topological input of XII.5.2, which SGA uses
implicitly ("every finite étale covering of `X^an` is a quotient of the universal covering by a
subgroup of finite index"). Hence XII.5.2 holds for every `X` connected and locally of finite type
over `ℂ`, singular or not, conditional only on the Riemann existence
theorem XII.5.1 (`schemeFundamentalGroupComparison_of_riemannExistence`).

The proof uses no triangulation. Writing `ℂⁿ = ℝ²ⁿ`, the space `Spec(ℂ[z₁, …, zₙ]/(g₁, …, g_k))(ℂ)`
is the real algebraic set `{w ∈ ℝ²ⁿ | ∑ⱼ |gⱼ(w)|² = 0}`
(`Points.exists_homeomorph_setOf_eval_eq_zero`), and real algebraic sets are semilocally simply
connected (`MvPolynomial.semilocallySimplyConnectedSpace_setOf_eval_eq_zero`: they are locally
contractible in the classical sense, by the Kurdyka–Łojasiewicz inequality and gradient descent,
`Foundations/Semialgebraic/`). The property is local on `X` and invariant under homeomorphisms
(`SemilocallySimplyConnectedSpace.of_isOpenEmbedding_cover`).

More precisely, `X(ℂ)` is locally contractible in the classical sense (every neighbourhood `U` of
a point contains a neighbourhood whose inclusion into `U` is null-homotopic):
`SchemePoints.locallyContractibleSpace`. The strong form, a basis of contractible neighbourhoods
(`LocallyContractibleStatement`), remains open in dimension `≥ 2` (it needs the local conic
structure); it is not needed for XII.5.2.
-/

universe u

open Topology Set AlgebraicGeometry MvPolynomial

namespace SGA.SGA1.ExposeXII

namespace Points

/-- The point `(Re w, Im w) ∈ ℝ^(Fin n ⊕ Fin n)` as a point of `ℂⁿ`. -/
def complexify {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : Fin n → ℂ := fun k ↦ ⟨w (.inl k), w (.inr k)⟩

/-- The real and imaginary parts of a point of `ℂⁿ`, as a point of `ℝ^(Fin n ⊕ Fin n)`. -/
def realify {n : ℕ} (z : Fin n → ℂ) : Fin n ⊕ Fin n → ℝ :=
  Sum.elim (fun k ↦ (z k).re) fun k ↦ (z k).im

lemma complexify_realify {n : ℕ} (z : Fin n → ℂ) : complexify (realify z) = z := by
  funext k
  simp [complexify, realify]

lemma realify_complexify {n : ℕ} (w : Fin n ⊕ Fin n → ℝ) : realify (complexify w) = w := by
  funext i
  rcases i with k | k <;> simp [complexify, realify]

lemma continuous_complexify {n : ℕ} : Continuous (complexify (n := n)) := by
  refine continuous_pi fun k ↦ ?_
  have : Continuous fun w : Fin n ⊕ Fin n → ℝ ↦
      ((w (.inl k) : ℂ) + (w (.inr k) : ℂ) * Complex.I) := by fun_prop
  exact this.congr fun w ↦ (Complex.mk_eq_add_mul_I _ _).symm

lemma continuous_realify {n : ℕ} : Continuous (realify (n := n)) := by
  refine continuous_pi fun i ↦ ?_
  rcases i with k | k
  · exact Complex.continuous_re.comp (_root_.continuous_apply k)
  · exact Complex.continuous_im.comp (_root_.continuous_apply k)

/-- The real and imaginary parts of a complex polynomial function are real polynomial functions
of the real and imaginary parts of the variables. -/
lemma isPolynomialFun_re_im {n : ℕ} (g : MvPolynomial (Fin n) ℂ) :
    IsPolynomialFun (fun w ↦ (MvPolynomial.eval (complexify w) g).re) ∧
      IsPolynomialFun (fun w ↦ (MvPolynomial.eval (complexify w) g).im) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp only [eval_C]
    exact ⟨IsPolynomialFun.const _, IsPolynomialFun.const _⟩
  | add p q hp hq =>
    simp only [map_add, Complex.add_re, Complex.add_im]
    exact ⟨hp.1.add hq.1, hp.2.add hq.2⟩
  | mul_X p k hp =>
    simp only [map_mul, eval_X, Complex.mul_re, Complex.mul_im, complexify]
    exact ⟨(hp.1.mul (IsPolynomialFun.apply _)).sub (hp.2.mul (IsPolynomialFun.apply _)),
      (hp.1.mul (IsPolynomialFun.apply _)).add (hp.2.mul (IsPolynomialFun.apply _))⟩

/-- XII.5.2, topological input: `Spec(ℂ[z₁, …, zₙ]/I)(ℂ)` is homeomorphic to a real algebraic
set `{w ∈ ℝ²ⁿ | P(w) = 0}`. -/
theorem exists_homeomorph_setOf_eval_eq_zero {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    ∃ P : MvPolynomial (Fin n ⊕ Fin n) ℝ,
      Nonempty (Points ℂ (MvPolynomial (Fin n) ℂ ⧸ I) ≃ₜ {w | eval w P = 0}) := by
  set q := Ideal.Quotient.mkₐ ℂ I
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective ℂ I
  have hker : RingHom.ker q = I := Ideal.Quotient.mkₐ_ker ℂ I
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian I : I.FG)
  -- `P = ∑_{g ∈ s} |g|²`
  obtain ⟨P, hP⟩ : IsPolynomialFun fun w ↦
      ∑ g ∈ s, ((MvPolynomial.eval (complexify w) g).re ^ 2 +
        (MvPolynomial.eval (complexify w) g).im ^ 2) :=
    IsPolynomialFun.sum _ fun g ↦ ((isPolynomialFun_re_im g).1.pow 2).add
      ((isPolynomialFun_re_im g).2.pow 2)
  refine ⟨P, ?_⟩
  -- the zero set of `P` is the zero set of `I`
  have hzero (w : Fin n ⊕ Fin n → ℝ) :
      eval w P = 0 ↔ ∀ p ∈ RingHom.ker q, eval (complexify w) p = 0 := by
    rw [← hP w, hker, ← hs]
    rw [Finset.sum_eq_zero_iff_of_nonneg fun g _ ↦ by positivity]
    constructor
    · intro h p hp
      refine Submodule.span_induction (fun g hg ↦ ?_) (by simp) (fun a b _ _ ha hb ↦ by
        simp [ha, hb]) (fun a b _ hb ↦ by simp [hb]) hp
      obtain ⟨hre, him⟩ := (add_eq_zero_iff_of_nonneg (sq_nonneg _) (sq_nonneg _)).mp (h g hg)
      exact Complex.ext (pow_eq_zero_iff two_ne_zero |>.mp hre)
        (pow_eq_zero_iff two_ne_zero |>.mp him)
    · intro h g hg
      rw [h g (Ideal.subset_span hg)]
      simp
  -- the embedding `X(ℂ) → ℝ²ⁿ`
  set E : Points ℂ (MvPolynomial (Fin n) ℂ ⧸ I) → (Fin n ⊕ Fin n → ℝ) :=
    fun φ ↦ realify (coords q φ)
  have hE : IsEmbedding E :=
    (Function.LeftInverse.isEmbedding (f := complexify) complexify_realify continuous_complexify
      continuous_realify).comp (isClosedEmbedding_coords hq).isEmbedding
  have hrange : range E = {w | eval w P = 0} := by
    ext w
    simp only [mem_range, mem_ofPred_eq, hzero]
    constructor
    · rintro ⟨φ, rfl⟩
      rw [show complexify (E φ) = coords q φ from complexify_realify _]
      have : coords q φ ∈ range (coords q) := mem_range_self φ
      rw [range_coords hq] at this
      exact this
    · intro hw
      have : complexify w ∈ range (coords q) := by
        rw [range_coords hq]
        exact hw
      obtain ⟨φ, hφ⟩ := this
      refine ⟨φ, ?_⟩
      simp only [E, hφ, realify_complexify]
  exact ⟨hE.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

/-- XII.5.2, topological input, affine case: for `A` of finite type over `ℂ`, the space `X(ℂ)`
of `X = Spec A` is semilocally simply connected. -/
instance semilocallySimplyConnectedSpace (A : Type u) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : SemilocallySimplyConnectedSpace (Points ℂ A) := by
  obtain ⟨n, I, ⟨e⟩⟩ := exists_algEquiv_quotient A
  obtain ⟨P, ⟨h⟩⟩ := exists_homeomorph_setOf_eval_eq_zero I
  have := MvPolynomial.semilocallySimplyConnectedSpace_setOf_eval_eq_zero P
  exact (h.symm.trans (Points.homeomorph e).symm).semilocallySimplyConnectedSpace

/-- `X(ℂ)` is locally contractible in the classical sense (small neighbourhoods contract inside
larger ones), for `X = Spec A`, `A` of finite type over `ℂ`. (The strong form, a basis of
contractible neighbourhoods, is `LocallyContractibleStatement`.) -/
theorem locallyContractibleSpace (A : Type u) [CommRing A] [Algebra ℂ A]
    [Algebra.FiniteType ℂ A] : LocallyContractibleSpace (Points ℂ A) := by
  obtain ⟨n, I, ⟨e⟩⟩ := exists_algEquiv_quotient A
  obtain ⟨P, ⟨h⟩⟩ := exists_homeomorph_setOf_eval_eq_zero I
  exact (h.symm.trans (Points.homeomorph e).symm).locallyContractibleSpace
    (MvPolynomial.locallyContractibleSpace_setOf_eval_eq_zero' P)

end Points

namespace SchemePoints

/-- For `X` locally of finite type over `ℂ`, `X(ℂ)` is locally contractible in the classical sense
(small neighbourhoods contract inside larger ones). This is the weak form of
`LocallyContractibleStatement`; it implies the local path-connectedness and the semilocal simple
connectedness of `X(ℂ)`. -/
theorem locallyContractibleSpace (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] : LocallyContractibleSpace (SchemePoints ℂ X) := by
  refine .of_isOpenEmbedding_cover fun p ↦ ?_
  obtain ⟨A, _, _, _, f, hf, hp, -⟩ := exists_isOpenEmbedding_points X p
  exact ⟨Points ℂ A, inferInstance, Points.locallyContractibleSpace A, f, hf, hp⟩

/-- XII.5.2, topological input: for `X` locally of finite type over `ℂ`, the space `X(ℂ)` is
semilocally simply connected. -/
instance semilocallySimplyConnectedSpace (X : Scheme.{0}) [X.Over (Spec (.of ℂ))]
    [LocallyOfFiniteType (X ↘ Spec (.of ℂ))] :
    SemilocallySimplyConnectedSpace (SchemePoints ℂ X) := by
  refine .of_isOpenEmbedding_cover fun p ↦ ?_
  obtain ⟨A, _, _, _, f, hf, hp, -⟩ := exists_isOpenEmbedding_points X p
  exact ⟨Points ℂ A, inferInstance, inferInstance, f, hf, hp⟩

end SchemePoints

/-- XII.5.2, topological input, second half: `X(ℂ)` is semilocally simply connected for every `X`
locally of finite type over `ℂ`. -/
theorem semilocallySimplyConnectedStatement : SemilocallySimplyConnectedStatement :=
  fun X _ _ ↦ SchemePoints.semilocallySimplyConnectedSpace X

/-- XII.5.2 (conditional only on the Riemann existence theorem XII.5.1): for `X` connected and
locally of finite type over `ℂ`, singular or not, `π₁(X, x)` is the profinite completion of
`π₁(X(ℂ), x)`. The topological input (`X(ℂ)` locally path-connected and semilocally simply
connected) is proved; SGA uses it without comment. -/
theorem schemeFundamentalGroupComparison_of_riemannExistence
    (H : SchemeRiemannExistenceStatement) : SchemeFundamentalGroupComparisonStatement :=
  schemeFundamentalGroupComparison_of_lpc_slsc H locallyPathConnectedStatement
    semilocallySimplyConnectedStatement

end SGA.SGA1.ExposeXII
