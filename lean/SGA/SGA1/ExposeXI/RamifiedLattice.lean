/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXI.ProjectiveLineAlgebra

/-!
# Coverings of `ℙ¹` ramified at `∞` (for XIII.2.12)

The lattice argument of `ProjectiveLineAlgebra`, for a covering of `ℙ¹` which is étale over
`𝔸¹ = Spec k[T]` but possibly ramified over `∞`: it is given by a finite étale `k[T]`-algebra
`B₀` and a finite free `k[T⁻¹]`-algebra `B₁` with a common localization `W` over `k[T, T⁻¹]`.
The Riemann–Roch inequality now reads `2 d ≤ 2 dim_k (B₀ ∩ B₁) + δ`, where `d` is the degree
and `δ` the degree of the discriminant of `B₁` (`exists_le_finrank_inter_range_of_basis`); for a
connected covering with a rational point over `T = 0`, `B₀ ∩ B₁ = k`, so `2 d ≤ 2 + δ`
(`two_mul_finrank_le_of_isDomain`).
-/

open Polynomial LaurentPolynomial Module

namespace SGA.SGA1.ExposeXI

/-- A polynomial `f` such that `f(T⁻¹)` is a unit of `k[T, T⁻¹]` is a monomial `c Xⁿ`. -/
lemma exists_eq_C_mul_X_pow_of_isUnit {k : Type*} [Field k] {f : k[X]}
    (hf : IsUnit (toLaurentInv k f)) : ∃ c : k, c ≠ 0 ∧ ∃ n : ℕ, f = Polynomial.C c * X ^ n := by
  have hf' : IsUnit (toLaurent f) := by
    rw [toLaurentInv_apply] at hf
    simpa [involutive_invert _] using hf.map (invert : k[T;T⁻¹] ≃ₐ[k] k[T;T⁻¹])
  obtain ⟨g, hg⟩ := hf'.exists_right_inv
  obtain ⟨N, g', hg'⟩ := exists_T_pow g
  have hfg : f * g' = X ^ N := by
    apply Polynomial.toLaurent_injective
    rw [map_mul, hg', ← mul_assoc, hg, one_mul, Polynomial.toLaurent_X_pow]
  obtain ⟨i, -, u, hu⟩ := (dvd_prime_pow prime_X N).mp ⟨g', hfg.symm⟩
  obtain ⟨r, hr, hru⟩ := Polynomial.isUnit_iff.mp (u⁻¹).isUnit
  refine ⟨r, hr.ne_zero, i, ?_⟩
  rw [hru, ← hu, mul_comm, Units.mul_inv_cancel_right]

section Sections

variable {k : Type*} [Field k]
  {B₀ B₁ W : Type*} [CommRing B₀] [CommRing B₁] [CommRing W]
  [Algebra k[X] B₀] [Algebra k[X] B₁] [Algebra k[T;T⁻¹] W] [Algebra B₀ W] [Algebra B₁ W]
  [Algebra k W] [IsScalarTower k k[T;T⁻¹] W]
  [Algebra.Etale k[X] B₀] [Module.Finite k[X] B₀]

/-- The Riemann–Roch inequality for a covering of `ℙ¹` étale over `𝔸¹`: let `B₀` be a finite
étale `k[T]`-algebra and `B₁` a free `k[T⁻¹]`-algebra with basis `e₁` (`k` any field), with a
common localization `W` over `k[T, T⁻¹]`. Then `B₀ ∩ B₁ ⊆ W` is a finite-dimensional `k`-vector
space `Γ` with `2 deg B₀ ≤ 2 dim Γ + deg (disc e₁)`. -/
theorem exists_le_finrank_inter_range_of_basis
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁ : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W)
    {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] (e₁ : Basis ι₁ k[X] B₁) :
    ∃ Γ : Submodule k W, (∀ w, w ∈ Γ ↔
        w ∈ Set.range (algebraMap B₀ W) ∧ w ∈ Set.range (algebraMap B₁ W)) ∧
      FiniteDimensional k Γ ∧
        2 * finrank k[X] B₀ ≤ 2 * finrank k Γ + (Algebra.discr k[X] e₁).natDegree := by
  classical
  let e₀ := Module.Free.chooseBasis k[X] B₀
  obtain ⟨b₀, -, hb₀, hd₀⟩ := exists_basis_of_isLocalization (toLaurent : k[X] →+* k[T;T⁻¹])
    (X : k[X]) LaurentPolynomial.isLocalization hW₀ h₀ e₀
  obtain ⟨b₁, -, -, -⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom (X : k[X])
    (isLocalization_toLaurentInv k) hW₁ h₁ e₁
  let σ := b₁.indexEquiv b₀
  obtain ⟨b₁', -, hb₁', hd₁'⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom
    (X : k[X]) (isLocalization_toLaurentInv k) hW₁ h₁ (e₁.reindex σ)
  obtain ⟨c₀, hc₀, hdisc₀⟩ := exists_discr_eq_C e₀
  set M := b₀.toMatrix b₁'
  have hvec : ⇑b₁' = Matrix.vecMul b₀ (M.map (algebraMap k[T;T⁻¹] W)) := by
    funext j
    rw [← b₀.sum_toMatrix_smul_self b₁' j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def, mul_comm]
    rfl
  have hdet : M.det ^ 2 * LaurentPolynomial.C c₀ = toLaurentInv k (Algebra.discr k[X] e₁) := by
    have := Algebra.discr_of_matrix_vecMul (A := k[T;T⁻¹]) b₀ M
    rw [← hvec, hd₁', hd₀, hdisc₀, Basis.coe_reindex, Algebra.discr_reindex] at this
    change toLaurentInv k (Algebra.discr k[X] e₁) = M.det ^ 2 * toLaurent (Polynomial.C c₀) at this
    rw [this, toLaurent_C]
  obtain ⟨hfin, hle⟩ := le_finrank_latticeSections_of_det_sq b₀ b₁' c₀ hc₀ _ hdet
  refine ⟨latticeSections b₀ b₁', fun w ↦ ?_, hfin, ?_⟩
  · rw [mem_latticeSections, hb₀, hb₁']
    rfl
  · rw [Module.finrank_eq_card_basis e₀]
    exact hle

omit [Algebra k W] [IsScalarTower k k[T;T⁻¹] W] in
/-- In the situation of `exists_le_finrank_inter_range_of_basis`, the discriminant of a basis of
`B₁` becomes a unit of `k[T, T⁻¹]`: `B₁` is unramified away from `T⁻¹ = 0`. -/
theorem isUnit_toLaurentInv_discr
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁ : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W)
    {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] (e₁ : Basis ι₁ k[X] B₁) :
    IsUnit (toLaurentInv k (Algebra.discr k[X] e₁)) := by
  classical
  let e₀ := Module.Free.chooseBasis k[X] B₀
  obtain ⟨b₀, -, -, hd₀⟩ := exists_basis_of_isLocalization (toLaurent : k[X] →+* k[T;T⁻¹])
    (X : k[X]) LaurentPolynomial.isLocalization hW₀ h₀ e₀
  obtain ⟨b₁, -, -, -⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom (X : k[X])
    (isLocalization_toLaurentInv k) hW₁ h₁ e₁
  let σ := b₁.indexEquiv b₀
  obtain ⟨b₁', -, -, hd₁'⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom
    (X : k[X]) (isLocalization_toLaurentInv k) hW₁ h₁ (e₁.reindex σ)
  obtain ⟨c₀, hc₀, hdisc₀⟩ := exists_discr_eq_C e₀
  set M := b₀.toMatrix b₁'
  have hvec : ⇑b₁' = Matrix.vecMul b₀ (M.map (algebraMap k[T;T⁻¹] W)) := by
    funext j
    rw [← b₀.sum_toMatrix_smul_self b₁' j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def, mul_comm]
    rfl
  have hdet : toLaurentInv k (Algebra.discr k[X] e₁) = M.det ^ 2 * LaurentPolynomial.C c₀ := by
    have := Algebra.discr_of_matrix_vecMul (A := k[T;T⁻¹]) b₀ M
    rw [← hvec, hd₁', hd₀, hdisc₀, Basis.coe_reindex, Algebra.discr_reindex] at this
    change toLaurentInv k (Algebra.discr k[X] e₁) = M.det ^ 2 * toLaurent (Polynomial.C c₀) at this
    rw [this, toLaurent_C]
  rw [hdet]
  refine (IsUnit.pow 2 (Matrix.isUnit_det_of_left_inverse (Basis.toMatrix_mul_toMatrix_flip
    b₁' b₀))).mul ?_
  rw [LaurentPolynomial.C_eq_algebraMap]
  exact (isUnit_iff_ne_zero.mpr hc₀).map _

omit [Algebra k W] [IsScalarTower k k[T;T⁻¹] W] in
/-- The lattices `B₀` and `B₁` of `exists_le_finrank_inter_range_of_basis` have the same rank. -/
theorem card_eq_finrank_of_basis
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁ : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W)
    {ι₁ : Type*} [Fintype ι₁] (e₁ : Basis ι₁ k[X] B₁) :
    Fintype.card ι₁ = finrank k[X] B₀ := by
  classical
  let e₀ := Module.Free.chooseBasis k[X] B₀
  obtain ⟨b₀, -, -, -⟩ := exists_basis_of_isLocalization (toLaurent : k[X] →+* k[T;T⁻¹])
    (X : k[X]) LaurentPolynomial.isLocalization hW₀ h₀ e₀
  obtain ⟨b₁, -, -, -⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom (X : k[X])
    (isLocalization_toLaurentInv k) hW₁ h₁ e₁
  rw [Module.finrank_eq_card_basis e₀]
  exact Fintype.card_congr (b₁.indexEquiv b₀)

/-- The key step for coverings of `ℙ¹` étale over `𝔸¹`: in the situation of
`exists_le_finrank_inter_range_of_basis`, if `W` is a domain (as soon as it is nonzero) and `B₀`
has a rational point over `T = 0` (a ring homomorphism `B₀ → k` over the evaluation at `0`), then
`2 deg B₀ ≤ 2 + deg (disc e₁)`: `B₀ ∩ B₁` is a field, embedded in `k` by the rational point. -/
theorem two_mul_finrank_le_of_isDomain
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁' : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W)
    (hW : Nontrivial W → IsDomain W) (χ₁ : B₀ →+* k)
    (h₁ : ∀ p, χ₁ (algebraMap k[X] B₀ p) = p.eval 0)
    {ι₁ : Type*} [Fintype ι₁] [DecidableEq ι₁] (e₁ : Basis ι₁ k[X] B₁) :
    2 * finrank k[X] B₀ ≤ 2 + (Algebra.discr k[X] e₁).natDegree := by
  classical
  obtain ⟨Γ', hΓ', hfin, hle⟩ := exists_le_finrank_inter_range_of_basis h₀ h₁' hW₀ hW₁ e₁
  have hinj₀ : Function.Injective (algebraMap B₀ W) := by
    refine IsLocalization.injective (M := Algebra.algebraMapSubmonoid B₀
      (Submonoid.powers (Polynomial.X : Polynomial k))) _ ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    rw [mem_nonZeroDivisors_iff_right]
    intro z hz
    have : (Polynomial.X ^ n : Polynomial k) • z = 0 := by rw [Algebra.smul_def, mul_comm]; exact hz
    exact (smul_eq_zero.1 this).resolve_left (pow_ne_zero _ Polynomial.X_ne_zero)
  have : Nontrivial B₀ := χ₁.domain_nontrivial
  have : IsDomain W := hW hinj₀.nontrivial
  -- `Γ' = B₀ ∩ B₁` is a subalgebra of the domain `W`, hence a field.
  let Γ'' : Subalgebra k W :=
    { carrier := Γ'
      mul_mem' := fun {a b} ha hb ↦ by
        obtain ⟨⟨a₀, ha₀⟩, ⟨a₁, ha₁⟩⟩ := (hΓ' a).1 ha
        obtain ⟨⟨b₀, hb₀⟩, ⟨b₁, hb₁⟩⟩ := (hΓ' b).1 hb
        exact (hΓ' _).2 ⟨⟨a₀ * b₀, by rw [map_mul, ha₀, hb₀]⟩,
          ⟨a₁ * b₁, by rw [map_mul, ha₁, hb₁]⟩⟩
      add_mem' := fun ha hb ↦ Γ'.add_mem ha hb
      algebraMap_mem' := fun c ↦ by
        refine (hΓ' _).2 ⟨⟨algebraMap k[X] _ (Polynomial.C c), ?_⟩,
          ⟨algebraMap k[X] _ (Polynomial.C c), ?_⟩⟩
        · rw [h₀, Polynomial.toLaurent_C, LaurentPolynomial.C_eq_algebraMap]
          exact (IsScalarTower.algebraMap_apply k k[T;T⁻¹] W c).symm
        · rw [h₁', toLaurentInv_apply, Polynomial.toLaurent_C, invert_C,
            LaurentPolynomial.C_eq_algebraMap]
          exact (IsScalarTower.algebraMap_apply k k[T;T⁻¹] W c).symm }
  have hΓ'' : Subalgebra.toSubmodule Γ'' = Γ' := SetLike.coe_injective rfl
  have hfin'' : FiniteDimensional k Γ'' := by
    rw [← Subalgebra.finiteDimensional_toSubmodule, hΓ'']
    exact hfin
  have : IsArtinianRing Γ'' := IsArtinianRing.of_finite k Γ''
  have hfield : IsField Γ'' := IsArtinianRing.isField_of_isDomain Γ''
  -- `χ₁` gives a `k`-algebra map `Γ'' → k`, necessarily injective: so `dim Γ'' ≤ 1`.
  have hmem₀ : ∀ x : Γ'', ∃ b, algebraMap B₀ W b = x.1 := fun x ↦
    ((hΓ' x.1).1 x.2).1
  choose σ₀ hσ₀ using hmem₀
  let χ' : Γ'' →+* k :=
    { toFun := fun x ↦ χ₁ (σ₀ x)
      map_one' := by
        have : σ₀ 1 = 1 := hinj₀ (by rw [hσ₀, map_one]; rfl)
        rw [this, map_one]
      map_mul' := fun x y ↦ by
        have : σ₀ (x * y) = σ₀ x * σ₀ y := hinj₀ (by rw [hσ₀, map_mul, hσ₀, hσ₀]; rfl)
        rw [this, map_mul]
      map_zero' := by
        have : σ₀ 0 = 0 := hinj₀ (by rw [hσ₀, map_zero]; rfl)
        rw [this, map_zero]
      map_add' := fun x y ↦ by
        have : σ₀ (x + y) = σ₀ x + σ₀ y := hinj₀ (by rw [hσ₀, map_add, hσ₀, hσ₀]; rfl)
        rw [this, map_add] }
  have hχ'c : ∀ c : k, χ' (algebraMap k Γ'' c) = c := by
    intro c
    have : σ₀ (algebraMap k Γ'' c) = algebraMap k[X] _ (Polynomial.C c) := hinj₀ (by
      rw [hσ₀, h₀, Polynomial.toLaurent_C, LaurentPolynomial.C_eq_algebraMap]
      exact IsScalarTower.algebraMap_apply k k[T;T⁻¹] W c)
    change χ₁ (σ₀ (algebraMap k Γ'' c)) = c
    rw [this]
    exact (h₁ (Polynomial.C c)).trans (Polynomial.eval_C)
  have hχ'inj : Function.Injective χ' := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx0
    have := congrArg χ' hy
    rw [map_mul, hx, zero_mul, map_one] at this
    exact zero_ne_one this
  let χA : Γ'' →ₐ[k] k := { χ' with commutes' := hχ'c }
  have hdim : Module.finrank k Γ'' ≤ 1 := by
    have := LinearMap.finrank_le_finrank_of_injective (f := χA.toLinearMap) hχ'inj
    rwa [Module.finrank_self] at this
  rw [← hΓ'', Subalgebra.finrank_toSubmodule] at hle
  omega

end Sections

end SGA.SGA1.ExposeXI
