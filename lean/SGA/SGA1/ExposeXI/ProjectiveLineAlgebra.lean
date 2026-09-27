/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Localization.NormTrace
import SGA.SGA1.ExposeXI.EtaleDiscriminant
import SGA.SGA1.ExposeXI.LatticeIndex
import Mathlib.RingTheory.Artinian.Module

/-!
# Étale coverings of the projective line: the algebraic part (for XI.1.1)

An étale covering of `ℙ¹_k = Spec k[T] ∪ Spec k[T⁻¹]` is given by finite étale algebras `B₀` over
`k[T]` and `B₁` over `k[T⁻¹]` with the same localization `W` over `k[T, T⁻¹]`; its global
sections are `B₀ ∩ B₁ ⊆ W`. Choosing bases of `B₀` and `B₁`, the discriminants are nonzero
constants (`exists_discr_eq_C`), so the change of basis matrix has
constant square determinant and the Riemann–Roch inequality `le_finrank_latticeSections` shows
that `B₀ ∩ B₁` has dimension at least the degree of the covering
(`exists_le_finrank_inter_range`).
-/

open Polynomial LaurentPolynomial Module

namespace SGA.SGA1.ExposeXI

section Chart

variable {A K B W : Type*} [CommRing A] [CommRing K] [CommRing B] [CommRing W] [Algebra A B]
  [Algebra K W] [Algebra B W]

/-- A basis of a finite free `A`-algebra `B` localizes to a basis of `W = B[1/t]` over
`K = A[1/t]`; an element of `W` lies in `B` if and only if its coordinates lie in `A`. -/
theorem exists_basis_of_isLocalization (φ : A →+* K) (t : A)
    (hK : letI := φ.toAlgebra; IsLocalization.Away t K)
    (hW : IsLocalization (Algebra.algebraMapSubmonoid B (Submonoid.powers t)) W)
    (h : ∀ a, algebraMap B W (algebraMap A B a) = algebraMap K W (φ a))
    {ι : Type*} [Fintype ι] [DecidableEq ι] (e : Basis ι A B) :
    ∃ b : Basis ι K W, (∀ i, b i = algebraMap B W (e i)) ∧
      (∀ w, w ∈ Set.range (algebraMap B W) ↔ ∀ i, b.repr w i ∈ Set.range φ) ∧
      Algebra.discr K b = φ (Algebra.discr A e) := by
  let _ : Algebra A K := φ.toAlgebra
  let _ : Algebra A W := ((algebraMap K W).comp φ).toAlgebra
  have : IsScalarTower A K W := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A B W := IsScalarTower.of_algebraMap_eq fun a ↦ (h a).symm
  have := hK
  let b := e.localizationLocalization K (Submonoid.powers t) W
  refine ⟨b, fun i ↦ e.localizationLocalization_apply K (Submonoid.powers t) W i,
    fun w ↦ ⟨?_, fun hw ↦ ?_⟩, Algebra.discr_localizationLocalization A (Submonoid.powers t) W e⟩
  · rintro ⟨x, rfl⟩ i
    exact ⟨e.repr x i,
      (e.localizationLocalization_repr_algebraMap K (Submonoid.powers t) W x i).symm⟩
  · choose a ha using hw
    refine ⟨∑ i, a i • e i, ?_⟩
    rw [← b.sum_repr w, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← ha i, Algebra.smul_def, map_mul, h, Algebra.smul_def,
      e.localizationLocalization_apply K (Submonoid.powers t) W i]

end Chart

/-- `k[T, T⁻¹]` is the localization of `k[T⁻¹]` at `T⁻¹`. -/
theorem isLocalization_toLaurentInv (k : Type*) [Field k] :
    letI := (toLaurentInv k).toRingHom.toAlgebra
    IsLocalization.Away (X : k[X]) k[T;T⁻¹] := by
  let _ := (toLaurentInv k).toRingHom.toAlgebra
  have hX : algebraMap k[X] k[T;T⁻¹] X = T (-1) := by
    change toLaurentInv k X = _
    rw [toLaurentInv_apply, toLaurent_X, invert_T]
  refine IsLocalization.Away.mk _ (hX ▸ isUnit_T _) (fun f ↦ ?_) fun a b hab ↦
    ⟨0, by rw [toLaurentInv_injective hab]⟩
  obtain ⟨n, hn⟩ := exists_T_neg_mul_mem f
  obtain ⟨a, ha⟩ := hn n le_rfl
  refine ⟨n, a, ?_⟩
  rw [hX, T_pow, mul_comm]
  change _ = toLaurentInv k a
  rw [ha]
  congr 2
  ring

section RankOne

/-- A commutative algebra which is free of rank one over `R` is `R` itself. -/
lemma bijective_algebraMap_of_finrank_eq_one {R B : Type*} [CommRing R] [Nontrivial R]
    [CommRing B] [Algebra R B] [Module.Free R B] [Module.Finite R B]
    (h : Module.finrank R B = 1) : Function.Bijective (algebraMap R B) := by
  let e := Module.finBasisOfFinrankEq R B h
  set u := e 0
  have hrepr : ∀ b : B, b = e.repr b 0 • u := fun b ↦ by
    conv_lhs => rw [← e.sum_repr b]
    simp [u]
  set c := e.repr 1 0
  set a := e.repr (u * u) 0
  have hca : c * a = 1 := by
    have h1 : u = (c * a) • u := by
      calc u = u * 1 := (mul_one u).symm
        _ = u * (c • u) := by rw [← hrepr 1]
        _ = c • (u * u) := by rw [mul_smul_comm]
        _ = c • (a • u) := by rw [← hrepr (u * u)]
        _ = (c * a) • u := by rw [smul_smul]
    have := congrArg (fun b ↦ e.repr b 0) h1
    simp only [u, map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at this
    exact this.symm
  have hu : u = a • (1 : B) := by
    rw [hrepr 1, smul_smul, mul_comm, hca, one_smul]
  refine ⟨fun r s hrs ↦ ?_, fun b ↦ ⟨e.repr b 0 * a, ?_⟩⟩
  · have h1 : ∀ r : R, algebraMap R B r = (r * c) • u := fun r ↦ by
      rw [Algebra.algebraMap_eq_smul_one, hrepr 1, smul_smul]
    have := congrArg (fun b ↦ e.repr b 0) ((h1 r).symm.trans (hrs.trans (h1 s)))
    simp only [u, map_smul, Finsupp.smul_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      smul_eq_mul, mul_one] at this
    have hc : IsUnit c := (Units.mkOfMulEqOne c a hca).isUnit
    exact hc.mul_left_injective this
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul, ← hu, ← hrepr]

end RankOne

section Sections

variable {k : Type*} [Field k]
  {B₀ B₁ W : Type*} [CommRing B₀] [CommRing B₁] [CommRing W]
  [Algebra k[X] B₀] [Algebra k[X] B₁] [Algebra k[T;T⁻¹] W] [Algebra B₀ W] [Algebra B₁ W]
  [Algebra k W] [IsScalarTower k k[T;T⁻¹] W]
  [Algebra.Etale k[X] B₀] [Algebra.Etale k[X] B₁] [Module.Finite k[X] B₀] [Module.Finite k[X] B₁]

/-- XI.1.1, algebraic form: let `B₀`, `B₁` be finite étale algebras over `k[T]` and `k[T⁻¹]`
(`k` any field) with a common localization `W` over `k[T, T⁻¹]`. Then `B₀ ∩ B₁ ⊆ W`
(the global sections of the corresponding étale covering of `ℙ¹`) is a finite-dimensional
`k`-vector space of dimension at least the degree of `B₀` over `k[T]`. -/
theorem exists_le_finrank_inter_range
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁ : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W) :
    ∃ Γ : Submodule k W, (∀ w, w ∈ Γ ↔
        w ∈ Set.range (algebraMap B₀ W) ∧ w ∈ Set.range (algebraMap B₁ W)) ∧
      FiniteDimensional k Γ ∧ finrank k[X] B₀ ≤ finrank k Γ := by
  classical
  let e₀ := Module.Free.chooseBasis k[X] B₀
  let e₁ := Module.Free.chooseBasis k[X] B₁
  obtain ⟨b₀, -, hb₀, hd₀⟩ := exists_basis_of_isLocalization (toLaurent : k[X] →+* k[T;T⁻¹])
    (X : k[X])
    LaurentPolynomial.isLocalization hW₀ h₀ e₀
  obtain ⟨b₁, -, -, -⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom (X : k[X])
    (isLocalization_toLaurentInv k) hW₁ h₁ e₁
  let σ := b₁.indexEquiv b₀
  obtain ⟨b₁', -, hb₁', hd₁'⟩ := exists_basis_of_isLocalization (toLaurentInv k).toRingHom
    (X : k[X])
    (isLocalization_toLaurentInv k) hW₁ h₁ (e₁.reindex σ)
  obtain ⟨c₀, hc₀, hdisc₀⟩ := exists_discr_eq_C e₀
  obtain ⟨c₁, -, hdisc₁⟩ := exists_discr_eq_C (e₁.reindex σ)
  -- The change of basis matrix has constant square determinant.
  set M := b₀.toMatrix b₁'
  have hvec : ⇑b₁' = Matrix.vecMul b₀ (M.map (algebraMap k[T;T⁻¹] W)) := by
    funext j
    rw [← b₀.sum_toMatrix_smul_self b₁' j]
    simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Algebra.smul_def, mul_comm]
    rfl
  have hdet : M.det ^ 2 = LaurentPolynomial.C (c₁ / c₀) := by
    have := Algebra.discr_of_matrix_vecMul (A := k[T;T⁻¹]) b₀ M
    rw [← hvec, hd₁', hd₀, hdisc₀, hdisc₁] at this
    change toLaurentInv k (Polynomial.C c₁) = M.det ^ 2 * toLaurent (Polynomial.C c₀) at this
    rw [toLaurentInv_apply, toLaurent_C, invert_C, toLaurent_C] at this
    rw [div_eq_mul_inv, map_mul, this, mul_assoc, ← map_mul, mul_inv_cancel₀ hc₀, map_one,
      mul_one]
  obtain ⟨hfin, hle⟩ := le_finrank_latticeSections b₀ b₁' (c₁ / c₀) hdet
  refine ⟨latticeSections b₀ b₁', fun w ↦ ?_, hfin, ?_⟩
  · rw [mem_latticeSections, hb₀, hb₁']
    rfl
  · rw [Module.finrank_eq_card_basis e₀]
    exact hle

/-- XI.1.1, algebraic form of the key step for `r ≥ 2`: in the situation of
`exists_le_finrank_inter_range`, if `W` is a domain (as soon as it is nonzero), then a ring
homomorphism `B₀ → k` over the evaluation `k[T] → k` at `T = 0` (a rational point over `T = 0`) is
unique. Indeed `B₀ ∩ B₁` is then a field of dimension at least the degree of `B₀`, which such a
homomorphism embeds into `k`, so `B₀ = k[T]`. -/
theorem ringHom_eq_of_isDomain_of_isLocalization
    (h₀ : ∀ p, algebraMap B₀ W (algebraMap k[X] B₀ p) = algebraMap k[T;T⁻¹] W (toLaurent p))
    (h₁' : ∀ p, algebraMap B₁ W (algebraMap k[X] B₁ p) =
      algebraMap k[T;T⁻¹] W (toLaurentInv k p))
    (hW₀ : IsLocalization (Algebra.algebraMapSubmonoid B₀ (Submonoid.powers (X : k[X]))) W)
    (hW₁ : IsLocalization (Algebra.algebraMapSubmonoid B₁ (Submonoid.powers (X : k[X]))) W)
    (hW : Nontrivial W → IsDomain W) (χ₁ χ₂ : B₀ →+* k)
    (h₁ : ∀ p, χ₁ (algebraMap k[X] B₀ p) = p.eval 0)
    (h₂ : ∀ p, χ₂ (algebraMap k[X] B₀ p) = p.eval 0) : χ₁ = χ₂ := by
  classical
  obtain ⟨Γ', hΓ', hfin, hle⟩ := exists_le_finrank_inter_range h₀ h₁' hW₀ hW₁
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
  -- `χ₁` gives a `k`-algebra map `Γ'' → k`, necessarily injective: so `d ≤ 1`.
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
  have hrank : Module.finrank k[X] B₀ ≤ 1 := by
    refine hle.trans ?_
    rw [← hΓ'', Subalgebra.finrank_toSubmodule]
    exact hdim
  -- Conclusion: `B₀ = k[t]`, so `χ₁ = χ₂ = ev₀`.
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hrank with h0 | h1
  · rw [Module.finrank_eq_zero_iff_of_free] at h0
    exact absurd (by rw [Subsingleton.elim (1 : B₀) 0, map_zero] :
      χ₁ 1 = 0) (by rw [map_one]; exact one_ne_zero)
  · obtain ⟨-, hsurj⟩ := bijective_algebraMap_of_finrank_eq_one h1
    ext b
    obtain ⟨p, rfl⟩ := hsurj b
    exact (h₁ p).trans (h₂ p).symm

end Sections

end SGA.SGA1.ExposeXI
