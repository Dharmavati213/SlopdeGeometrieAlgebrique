/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic

/-!
# SGA 1, Exposé X.1.10: Artin–Schreier coverings of the affine line

X.1.10 shows that X.1.7–X.1.9 fail without properness in characteristic `p > 0`: over an
algebraically closed field `k`, the equation `x^p - x = s t` defines an étale covering of the
plane `Spec k[s, t]`, i.e. a family of étale coverings of the line `X = Spec k[t]` parametrized
by the line `Y = Spec k[s]`, whose members `x^p - x = c t` (`c ∈ k`) are not all isomorphic.

We prove, for any field `k` of characteristic `p`:

* `R[x]/(x^p - x - a)` is a finite étale `R`-algebra for every `a` in a ring `R` of
  characteristic `p` (`etale_artinSchreier`), in particular for the whole family over
  `k[s, t]` and for each member over `k[t]`;
* the member `c = 0` is the trivial covering (not a domain), while the member `c = 1` is
  isomorphic to the affine line (a domain), so the family is not constant
  (`not_nonempty_algEquiv_zero_one`), contradicting X.1.9 for non-proper `X` and `Y`.

SGA asserts that the members are *pairwise* non-isomorphic. This is not quite right: `x ↦ -x`
identifies the members for `c` and `-c` when `p` is odd (`algEquivNeg`), and more generally
`x ↦ j x` identifies `c` and `j c` for `j ∈ 𝔽_p^×`. There are still infinitely many
isomorphism classes when `k` is infinite, which is what the counterexample needs.
-/

open Polynomial

namespace SGA.SGA1.ExposeX

section General

variable (R : Type*) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (a : R)

/-- The Artin–Schreier polynomial `X ^ p - X - a`. -/
noncomputable abbrev artinSchreier : R[X] := X ^ p - X - C a

omit [CharP R p] in
lemma natDegree_artinSchreier [Nontrivial R] : (artinSchreier R p a).natDegree = p := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h1 : (X ^ p - X : R[X]).natDegree = p := by
    rw [natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp]
  rw [natDegree_sub_C, h1]

omit [CharP R p] in
lemma monic_artinSchreier : (artinSchreier R p a).Monic := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  rw [artinSchreier, sub_sub]
  apply monic_X_pow_sub
  refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
  · exact degree_X_le.trans_lt (by exact_mod_cast hp)
  · exact degree_C_le.trans_lt (by exact_mod_cast (zero_lt_one.trans hp))

omit [Fact p.Prime] in
lemma derivative_artinSchreier : derivative (artinSchreier R p a) = -1 := by
  simp [artinSchreier, derivative_X_pow]

/-- The standard étale pair `(X^p - X - a, 1)`. -/
noncomputable def artinSchreierPair : StandardEtalePair R where
  f := artinSchreier R p a
  monic_f := monic_artinSchreier R p a
  g := 1
  cond := ⟨-1, 0, 0, by rw [derivative_artinSchreier]; simp⟩

/-- X.1.10: in characteristic `p`, `R[x]/(x^p - x - a)` is étale over `R`. -/
instance etale_artinSchreier : Algebra.Etale R (AdjoinRoot (artinSchreier R p a)) := by
  let P := artinSchreierPair R p a
  have hu : IsUnit (AdjoinRoot.mk P.f P.g) := by
    change IsUnit (AdjoinRoot.mk P.f 1)
    rw [map_one]
    exact isUnit_one
  exact Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ _ (AdjoinRoot.mk P.f P.g) hu).symm.restrictScalars R))

/-- X.1.10: `R[x]/(x^p - x - a)` is finite over `R`; with `etale_artinSchreier`, it is an étale
covering of `Spec R`. -/
instance finite_artinSchreier : Module.Finite R (AdjoinRoot (artinSchreier R p a)) :=
  (monic_artinSchreier R p a).finite_adjoinRoot

end General

variable (k : Type*) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]

/-- X.1.10: the family of coverings `x^p - x = s t` is an étale covering of `Spec k[s, t]`. -/
example : Algebra.Etale (MvPolynomial (Fin 2) k)
    (AdjoinRoot (artinSchreier (MvPolynomial (Fin 2) k) p
      (MvPolynomial.X 0 * MvPolynomial.X 1))) :=
  inferInstance

/-- X.1.10: the member `x^p - x = c t` of the family, a covering of the line `Spec k[t]` (the
fibre of the family at `s = c`). -/
abbrev artinSchreierCovering (c : k) : Type _ := AdjoinRoot (artinSchreier k[X] p (C c * X))

omit [CharP k p] in
/-- The member `c = 0` is the trivial covering `x^p = x`: it is not a domain. -/
theorem not_isDomain_artinSchreierCovering_zero : ¬ IsDomain (artinSchreierCovering k p 0) := by
  intro hdom
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  set f := artinSchreier k[X] p (C 0 * X)
  have hf : f = X ^ p - X := by simp [f]
  have hdeg : f.natDegree = p := natDegree_artinSchreier _ p _
  let r := AdjoinRoot.root f
  have hr : r * (r ^ (p - 1) - 1) = 0 := by
    have : r ^ p - r = 0 := by
      have := AdjoinRoot.eval₂_root f
      simpa [hf] using this
    rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hp.le, this]
  rcases mul_eq_zero.mp hr with h | h
  · rw [show r = AdjoinRoot.mk f X from rfl, AdjoinRoot.mk_eq_zero] at h
    have := natDegree_le_of_dvd h X_ne_zero
    rw [hdeg, natDegree_X] at this
    omega
  · have hne : (X ^ (p - 1) - 1 : k[X][X]) ≠ 0 := by
      rw [← C_1]
      exact X_pow_sub_C_ne_zero (by omega) 1
    rw [show r ^ (p - 1) - 1 = AdjoinRoot.mk f (X ^ (p - 1) - 1) by simp [r],
      AdjoinRoot.mk_eq_zero] at h
    have := natDegree_le_of_dvd h hne
    rw [hdeg, ← C_1, natDegree_X_pow_sub_C] at this
    omega

omit [Fact p.Prime] [CharP k p] in
/-- The member `c = 1`, `x^p - x = t`, is isomorphic to the affine line `Spec k[x]`
(`t ↦ x^p - x`); in particular it is a domain. -/
theorem isDomain_artinSchreierCovering_one : IsDomain (artinSchreierCovering k p 1) := by
  set f := artinSchreier k[X] p (C 1 * X)
  have hf : f = X ^ p - X - C X := by simp [f]
  -- `ψ : k[t][x]/(f) → k[x]`, `t ↦ x^p - x`, `x ↦ x`
  let i : k[X] →+* k[X] := (aeval (X ^ p - X : k[X])).toRingHom
  have hψ : f.eval₂ i X = 0 := by simp [hf, i]
  let ψ : AdjoinRoot f →+* k[X] := AdjoinRoot.lift i X hψ
  -- `χ : k[x] → k[t][x]/(f)`, `x ↦ root f`
  let χ : k[X] →+* AdjoinRoot f := (aeval (AdjoinRoot.root f)).toRingHom
  have hroot : AdjoinRoot.root f ^ p - AdjoinRoot.root f = AdjoinRoot.of f X := by
    have h2 : (X ^ p - X - C X : k[X][X]).eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) = 0 := by
      rw [← hf]
      exact AdjoinRoot.eval₂_root f
    simpa [sub_eq_zero] using h2
  have hχψ : χ.comp ψ = RingHom.id _ := by
    apply AdjoinRoot.ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro a
        simp [ψ, χ, i, AdjoinRoot.algebraMap_eq']
      · simp [ψ, χ, i, hroot]
    · simp [ψ, χ]
  have hinj : Function.Injective ψ :=
    Function.LeftInverse.injective (g := χ) fun x ↦ by
      simpa using DFunLike.congr_fun hχψ x
  exact hinj.isDomain ψ

omit [CharP k p] in
/-- X.1.10: the members `c = 0` and `c = 1` of the family `x^p - x = c t` are not isomorphic as
coverings of the line; the family is not constant although its parameter space is connected. -/
theorem not_nonempty_algEquiv_zero_one :
    ¬ Nonempty (artinSchreierCovering k p 0 ≃ₐ[k[X]] artinSchreierCovering k p 1) := by
  rintro ⟨e⟩
  have := isDomain_artinSchreierCovering_one k p
  exact not_isDomain_artinSchreierCovering_zero k p
    (e.toRingEquiv.injective.isDomain e.toRingEquiv.toRingHom)

/-- The members `c` and `-c` of the family are isomorphic when `p` is odd (`x ↦ -x`); so the
coverings of X.1.10 are not pairwise non-isomorphic, contrary to what SGA states. -/
noncomputable def algEquivNeg (hp : Odd p) (c : k) :
    artinSchreierCovering k p c ≃ₐ[k[X]] artinSchreierCovering k p (-c) := by
  have key (c : k) : aeval (-AdjoinRoot.root (artinSchreier k[X] p (C (-c) * X)))
      (artinSchreier k[X] p (C c * X)) = 0 := by
    have := AdjoinRoot.eval₂_root (artinSchreier k[X] p (C (-c) * X))
    simp only [artinSchreier, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C] at this
    simp only [artinSchreier, map_sub, map_pow, aeval_X, aeval_C, hp.neg_pow,
      AdjoinRoot.algebraMap_eq]
    rw [← neg_eq_zero, ← this]
    simp only [map_mul, map_neg, neg_mul]
    ring
  have key' : aeval (-AdjoinRoot.root (artinSchreier k[X] p (C c * X)))
      (artinSchreier k[X] p (C (-c) * X)) = 0 := by
    have := key (-c)
    rwa [neg_neg] at this
  refine AlgEquiv.ofAlgHom
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ (by rw [← key c, aeval_def]; rfl))
    (AdjoinRoot.liftAlgHom _ (Algebra.ofId _ _) _ (by rw [← key', aeval_def]; rfl)) ?_ ?_
  · apply AdjoinRoot.algHom_ext
    simp [AdjoinRoot.liftAlgHom_root]
  · apply AdjoinRoot.algHom_ext
    simp [AdjoinRoot.liftAlgHom_root]

end SGA.SGA1.ExposeX
