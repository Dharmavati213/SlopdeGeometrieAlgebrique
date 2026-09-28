/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.RamifiedLattice
import SGA.SGA1.ExposeXI.TameDiscriminant

/-!
# Coverings of `ℙ¹` étale over `𝔸¹` and tamely ramified at `∞` (for XIII.2.12)

A connected covering of `ℙ¹` which is étale over `𝔸¹ = Spec k[T]`, tamely ramified over `∞` and
has a rational point over `T = 0` is trivial (`finrank_eq_one_of_tame`). This is the case
`g = 0`, `n = 1` of XIII.2.12 in algebraic form, proved without Riemann's existence theorem by
the lattice method of XI.1.1 (`ProjectiveLineAlgebra`): with `d` the degree and `δ` the degree
of the discriminant at `∞`,

* the Riemann–Roch inequality gives `2 d ≤ 2 + δ` (`two_mul_finrank_le_of_isDomain`);
* tameness gives `δ ≤ d - 1` (`natDegree_discr_lt_of_tame`),

so `d = 1` (this is the Riemann–Hurwitz contradiction `2g - 2 = -2d + δ ≥ -2` with `δ ≤ d - 1`).
-/

open Polynomial LaurentPolynomial Module

namespace SGA.SGA1.ExposeXI

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {k : Type*} [Field k]
  {B₀ B₁ W : Type*} [CommRing B₀] [CommRing B₁] [CommRing W]
  [Algebra k[X] B₀] [Algebra k[X] B₁] [Algebra k[T;T⁻¹] W] [Algebra B₀ W] [Algebra B₁ W]
  [Algebra k W] [IsScalarTower k k[T;T⁻¹] W]
  [Algebra.Etale k[X] B₀] [Module.Finite k[X] B₀]
  [IsDedekindDomain B₁] [Module.IsTorsionFree k[X] B₁] [Module.Finite k[X] B₁]
  [Algebra.IsSeparable (FractionRing k[X]) (FractionRing B₁)]

/-- XIII.2.12 for `g = 0`, `n = 1`, algebraic form: let `B₀` be a finite étale `k[T]`-algebra and
`B₁` a Dedekind domain finite over `k[T⁻¹]`, with a common localization `W` over `k[T, T⁻¹]`
(a covering of `ℙ¹` étale over `𝔸¹`), such that `W` is a domain (the covering is connected),
`B₁` is tamely ramified over `T⁻¹ = 0` (for each prime `P` over `T⁻¹`, writing `T⁻¹B₁ = Pⁿ Q`
with `P ⊔ Q = ⊤`, some `x ∈ Q` has trace `∉ (T⁻¹)`; see `exists_mem_intTrace_notMem_of_finrank`
for this from `dim B₁/Pⁿ` prime to the characteristic), and `B₀` has a rational point over
`T = 0`. Then `B₀ = k[T]`: the covering is trivial. -/
theorem finrank_eq_one_of_tame
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁ : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W)
    (hW : Nontrivial W → IsDomain W) (χ : B₀ →+* k)
    (hχ : ∀ p, χ (algebraMap k[X] B₀ p) = p.eval 0)
    (htame : ∀ P : Ideal B₁, P.IsMaximal → algebraMap k[X] B₁ X ∈ P → ∀ Q : Ideal B₁,
      P ⊔ Q = ⊤ → ∀ n : ℕ, (Ideal.span {X}).map (algebraMap k[X] B₁) = P ^ n * Q →
        ∃ x ∈ Q, Algebra.intTrace k[X] B₁ x ∉ Ideal.span {(X : k[X])}) :
    finrank k[X] B₀ = 1 := by
  classical
  let e₁ := Module.Free.chooseBasis k[X] B₁
  -- `B₁` is unramified outside `T⁻¹ = 0`: its discriminant is a monomial.
  obtain ⟨c, hc, n, hdisc⟩ :=
    exists_eq_C_mul_X_pow_of_isUnit (isUnit_toLaurentInv_discr h₀ h₁ hW₀ hW₁ e₁)
  have hunr : ∀ P : Ideal B₁, P.IsPrime → P ∣ differentIdeal k[X] B₁ →
      algebraMap k[X] B₁ X ∈ P := by
    intro P hP hPD
    have h1 := Ideal.le_of_dvd hPD (algebraMap_discr_mem_differentIdeal k[X] e₁)
    rw [hdisc, map_mul, map_pow] at h1
    rcases hP.mem_or_mem h1 with h | h
    · exact absurd (Ideal.eq_top_of_isUnit_mem P h
        ((Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc)).map _)) hP.ne_top
    · exact hP.mem_of_pow_mem n h
  have h2 := two_mul_finrank_le_of_isDomain h₀ h₁ hW₀ hW₁ hW χ hχ e₁
  have h3 := natDegree_discr_lt_of_tame e₁ hunr htame
  have h4 := card_eq_finrank_of_basis h₀ h₁ hW₀ hW₁ e₁
  have : Nontrivial B₀ := χ.domain_nontrivial
  have h5 : 0 < finrank k[X] B₀ := Module.finrank_pos
  omega

end SGA.SGA1.ExposeXI
