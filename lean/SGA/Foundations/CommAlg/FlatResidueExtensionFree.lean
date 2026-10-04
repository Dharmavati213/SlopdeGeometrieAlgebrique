/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Adjoining `q`-th roots of a family of elements

Let `A` be a commutative ring, `a : B → A` a family of elements and `q > 0`. The `A`-algebra

  `AdjoinRoots q a = A[Y_i : i ∈ B] / (Y_i ^ q - a_i : i ∈ B)`

is a free `A`-module, with basis the monomials `Y^e` whose exponents are all `< q`
(`AdjoinRoots.basis`). The proof writes down the coordinates: `Y^β = (∏ a_i^{⌊β_i/q⌋}) Y^{β mod q}`.

This is the algebra used in the construction of flat local extensions with a prescribed purely
inseparable residue field extension (EGA 0_III 10.3.1; Bourbaki, *Algèbre commutative* IX,
Appendice): over a local ring `R` whose residue field `E` sits in a field `L` with `L^p ⊆ E`,
adjoining `p`-th roots of lifts of the `p`-th powers of a `p`-basis of `L` over `E` gives a free
local `R`-algebra with residue field `L` (see
`SGA.Foundations.CommAlg.FlatResidueExtensionInseparable`).

## Main definitions and results

* `AdjoinRoots q a`, its generators `AdjoinRoots.root q a i` with `root_pow`.
* `AdjoinRoots.basis`: the basis `(Y^e)_{e < q}`; hence `AdjoinRoots.free`, `AdjoinRoots.flat`;
  `AdjoinRoots.isIntegral`.
* `AdjoinRoots.map`: base change along a ring map `φ : A → A'`, and
  `AdjoinRoots.mem_map_ker_of_map_eq_zero`: an element killed by `map φ` has its coordinates in
  `ker φ`.
-/

open MvPolynomial

noncomputable section

universe u v

variable {A : Type u} [CommRing A] {B : Type v}

namespace AdjoinRoots

/-- The ideal `(Y_i ^ q - a_i)_i` of `A[Y_i : i ∈ B]`. -/
def ideal (q : ℕ) (a : B → A) : Ideal (MvPolynomial B A) :=
  Ideal.span (Set.range fun i ↦ X i ^ q - C (a i))

end AdjoinRoots

/-- `A[Y_i : i ∈ B] / (Y_i ^ q - a_i)`: the `A`-algebra obtained from `A` by adjoining a `q`-th
root of each `a_i`. -/
abbrev AdjoinRoots (q : ℕ) (a : B → A) : Type (max u v) :=
  MvPolynomial B A ⧸ AdjoinRoots.ideal q a

namespace AdjoinRoots

variable (q : ℕ) (a : B → A)

/-- The quotient map `A[Y_i] → AdjoinRoots q a`. -/
abbrev mk : MvPolynomial B A →ₐ[A] AdjoinRoots q a := Ideal.Quotient.mkₐ A (ideal q a)

lemma mk_surjective : Function.Surjective (mk q a) := Ideal.Quotient.mkₐ_surjective A _

/-- The generator `Y_i`, a `q`-th root of `a_i`. -/
abbrev root (i : B) : AdjoinRoots q a := mk q a (X i)

lemma root_pow (i : B) : root q a i ^ q = algebraMap A _ (a i) := by
  rw [root, ← map_pow, ← sub_eq_zero, ← AlgHom.commutes (mk q a), ← map_sub,
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, algebraMap_eq]
  exact Ideal.subset_span ⟨i, rfl⟩

@[ext]
lemma algHom_ext {S : Type*} [CommRing S] [Algebra A S] {f g : AdjoinRoots q a →ₐ[A] S}
    (h : ∀ i, f (root q a i) = g (root q a i)) : f = g :=
  Ideal.Quotient.algHom_ext A (MvPolynomial.algHom_ext h)

/-- The exponents `e : B →₀ ℕ` with `e i < q` for all `i`: they index the basis of
`AdjoinRoots q a`. -/
abbrev Exponents (B : Type v) (q : ℕ) : Type v := {e : B →₀ ℕ // ∀ i, e i < q}

variable {q}

/-- The reduction `β mod q` of an exponent. -/
def reduceExp (hq : 0 < q) (β : B →₀ ℕ) : Exponents B q :=
  ⟨β.mapRange (· % q) (Nat.zero_mod q), fun i ↦ by simpa using Nat.mod_lt (β i) hq⟩

lemma reduceExp_coe (hq : 0 < q) (β : B →₀ ℕ) :
    (reduceExp hq β).1 = β.mapRange (· % q) (Nat.zero_mod q) := rfl

lemma reduceExp_add_single (hq : 0 < q) (β : B →₀ ℕ) (i : B) :
    reduceExp hq (β + Finsupp.single i q) = reduceExp hq β := by
  classical
  apply Subtype.ext
  ext j
  simp only [reduceExp_coe, Finsupp.mapRange_apply, Finsupp.add_apply]
  rw [Finsupp.single_apply]
  split_ifs <;> simp

lemma reduceExp_of_lt (hq : 0 < q) (e : Exponents B q) : reduceExp hq e.1 = e := by
  apply Subtype.ext
  ext j
  simp [reduceExp_coe, Nat.mod_eq_of_lt (e.2 j)]

variable (q) in
/-- The coefficient `∏ a_i ^ ⌊β_i / q⌋`, so that `Y^β = carry q a β • Y^{β mod q}`. -/
def carry (β : B →₀ ℕ) : A := β.prod fun i n ↦ a i ^ (n / q)

lemma carry_add_single (hq : 0 < q) (β : B →₀ ℕ) (i : B) :
    carry q a (β + Finsupp.single i q) = a i * carry q a β := by
  unfold carry
  rw [← Finsupp.mul_prod_erase' _ i _ (fun _ ↦ by simp),
    ← Finsupp.mul_prod_erase' β i _ (fun _ ↦ by simp), Finsupp.erase_add, Finsupp.erase_single,
    add_zero, Finsupp.add_apply, Finsupp.single_eq_same, Nat.add_div_right _ hq, pow_succ]
  ring

lemma carry_of_lt (e : Exponents B q) : carry q a e.1 = 1 := by
  unfold carry Finsupp.prod
  exact Finset.prod_eq_one fun i _ ↦ by simp [Nat.div_eq_of_lt (e.2 i)]

/-- The coordinates on `A[Y_i]`: `Y^β ↦ (∏ a_i ^ ⌊β_i / q⌋) e_{β mod q}`. -/
def coordAux (hq : 0 < q) : MvPolynomial B A →ₗ[A] (Exponents B q →₀ A) :=
  (basisMonomials B A).constr A fun β ↦ Finsupp.single (reduceExp hq β) (carry q a β)

lemma coordAux_monomial (hq : 0 < q) (β : B →₀ ℕ) (c : A) :
    coordAux a hq (monomial β c) = Finsupp.single (reduceExp hq β) (c * carry q a β) := by
  have : monomial β c = c • (basisMonomials B A) β := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, coordAux, Module.Basis.constr_basis, Finsupp.smul_single, smul_eq_mul]

lemma coordAux_monomial_mul (hq : 0 < q) (γ : B →₀ ℕ) (c : A) (i : B) :
    coordAux a hq (monomial γ c * (X i ^ q - C (a i))) = 0 := by
  rw [mul_sub, X_pow_eq_monomial, monomial_mul_monomial, mul_comm (monomial γ c),
    C_mul_monomial, map_sub,
    coordAux_monomial, coordAux_monomial, reduceExp_add_single, carry_add_single a hq, sub_eq_zero]
  congr 1
  ring

lemma ideal_le_ker (hq : 0 < q) :
    (ideal q a).restrictScalars A ≤ LinearMap.ker (coordAux a hq) := by
  suffices h : ∀ x ∈ ideal q a, ∀ r, coordAux a hq (r * x) = 0 by
    intro x hx
    simpa using h x hx 1
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    intro r
    induction r using MvPolynomial.induction_on' with
    | monomial γ c => exact coordAux_monomial_mul a hq γ c i
    | add r s hr hs => rw [add_mul, map_add, hr, hs, add_zero]
  | zero => simp
  | add x y _ _ hx hy => intro r; rw [mul_add, map_add, hx, hy, add_zero]
  | smul s x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc]; exact hx _

/-- The coordinates on `AdjoinRoots q a` in the basis `(Y^e)_{e < q}`. -/
def coord (hq : 0 < q) : AdjoinRoots q a →ₗ[A] (Exponents B q →₀ A) :=
  ((ideal q a).restrictScalars A).liftQ (coordAux a hq) (ideal_le_ker a hq) ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv A (ideal q a)).symm.toLinearMap

lemma coord_mk (hq : 0 < q) (P : MvPolynomial B A) :
    coord a hq (mk q a P) = coordAux a hq P := rfl

variable (q) in
/-- The `A`-linear map `(Exponents B q →₀ A) → AdjoinRoots q a`, `e ↦ Y^e`. -/
def ofCoord : (Exponents B q →₀ A) →ₗ[A] AdjoinRoots q a :=
  Finsupp.linearCombination A fun e ↦ mk q a (monomial e.1 1)

lemma mk_monomial_one (hq : 0 < q) (β : B →₀ ℕ) :
    mk q a (monomial β 1) =
      algebraMap A _ (carry q a β) * mk q a (monomial (reduceExp hq β).1 1) := by
  have hY : ∀ i n, mk q a (X i) ^ n =
      algebraMap A (AdjoinRoots q a) (a i ^ (n / q)) * mk q a (X i) ^ (n % q) := by
    intro i n
    conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, root_pow, ← map_pow]
  rw [monomial_eq, monomial_eq, C_1, one_mul, one_mul, map_finsuppProd, map_finsuppProd,
    reduceExp_coe, Finsupp.prod_mapRange_index (fun _ ↦ by simp)]
  simp only [map_pow]
  rw [Finsupp.prod_congr (g2 := fun i n ↦
      algebraMap A (AdjoinRoots q a) (a i ^ (n / q)) * mk q a (X i) ^ (n % q))
      (fun i _ ↦ hY i (β i)), Finsupp.prod_mul, carry, map_finsuppProd]

lemma coord_ofCoord (hq : 0 < q) : coord a hq ∘ₗ ofCoord q a = LinearMap.id := by
  ext e
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lsingle_apply, ofCoord,
    Finsupp.linearCombination_single, one_smul, LinearMap.id_coe, id_eq]
  rw [coord_mk, coordAux_monomial, reduceExp_of_lt, carry_of_lt, one_mul]

lemma ofCoord_coord (hq : 0 < q) : ofCoord q a ∘ₗ coord a hq = LinearMap.id := by
  refine LinearMap.ext fun z ↦ ?_
  obtain ⟨P, rfl⟩ := mk_surjective q a z
  induction P using MvPolynomial.induction_on' with
  | monomial β c =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
    rw [coord_mk, coordAux_monomial, ofCoord, Finsupp.linearCombination_single,
      Algebra.smul_def, map_mul, mul_assoc, ← mk_monomial_one a hq, ← AlgHom.commutes (mk q a) c,
      ← map_mul, algebraMap_eq, C_mul_monomial, mul_one]
  | add P Q hP hQ =>
    simp only [map_add, LinearMap.coe_comp, Function.comp_apply] at hP hQ ⊢
    rw [hP, hQ]

/-- The coordinates of `AdjoinRoots q a` in the basis `(Y^e)_{e < q}`, as a linear equivalence. -/
def coordEquiv (hq : 0 < q) : AdjoinRoots q a ≃ₗ[A] (Exponents B q →₀ A) :=
  LinearEquiv.ofLinearMap (coord a hq) (ofCoord q a) (coord_ofCoord a hq) (ofCoord_coord a hq)

/-- The basis `(Y^e)_{e < q}` of the `A`-module `AdjoinRoots q a`. -/
def basis (hq : 0 < q) : Module.Basis (Exponents B q) A (AdjoinRoots q a) :=
  Module.Basis.ofRepr (coordEquiv a hq)

lemma basis_apply (hq : 0 < q) (e : Exponents B q) :
    basis a hq e = mk q a (monomial e.1 1) := by
  simp [basis, coordEquiv, ofCoord]

lemma free (hq : 0 < q) : Module.Free A (AdjoinRoots q a) := Module.Free.of_basis (basis a hq)

lemma flat (hq : 0 < q) : Module.Flat A (AdjoinRoots q a) := by
  have := free a hq
  infer_instance

/-- `AdjoinRoots q a` is integral over `A`: it is generated by the roots `Y_i` of the monic
polynomials `X^q - a_i`. -/
lemma isIntegral (hq : 0 < q) : Algebra.IsIntegral A (AdjoinRoots q a) := by
  constructor
  intro z
  obtain ⟨P, rfl⟩ := mk_surjective q a z
  induction P using MvPolynomial.induction_on with
  | C c => rw [← algebraMap_eq, AlgHom.commutes]; exact isIntegral_algebraMap
  | add P Q hP hQ => rw [map_add]; exact hP.add hQ
  | mul_X P i hP =>
    rw [map_mul]
    refine hP.mul ⟨Polynomial.X ^ q - Polynomial.C (a i), Polynomial.monic_X_pow_sub_C _ hq.ne',
      ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, root_pow, sub_self]

/-! ### Base change along a ring map -/

variable {A' : Type*} [CommRing A'] (φ : A →+* A')

/-- Base change along `φ : A → A'`: the ring map `AdjoinRoots q a → AdjoinRoots q (φ ∘ a)`
induced by `MvPolynomial.map φ`. -/
def map : AdjoinRoots q a →+* AdjoinRoots q (fun i ↦ φ (a i)) :=
  Ideal.quotientMap _ (MvPolynomial.map φ) (by
    rw [ideal, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, map_sub, map_pow, map_X, map_C]
    exact Ideal.subset_span ⟨i, rfl⟩)

lemma map_mk (P : MvPolynomial B A) :
    map a φ (mk q a P) = mk q (fun i ↦ φ (a i)) (MvPolynomial.map φ P) := rfl

lemma map_root (i : B) : map a φ (root q a i) = root q (fun i ↦ φ (a i)) i := by
  rw [root, map_mk, map_X]

lemma map_algebraMap (c : A) :
    map (q := q) a φ (algebraMap A _ c) = algebraMap A' _ (φ c) := by
  rw [← AlgHom.commutes (mk q a), map_mk, algebraMap_eq, map_C, ← algebraMap_eq,
    AlgHom.commutes]

lemma map_surjective (hφ : Function.Surjective φ) : Function.Surjective (map (q := q) a φ) :=
  Ideal.quotientMap_surjective (MvPolynomial.map_surjective φ hφ)

lemma map_basis (hq : 0 < q) (e : Exponents B q) :
    map a φ (basis a hq e) = basis (fun i ↦ φ (a i)) hq e := by
  rw [basis_apply, basis_apply, map_mk, MvPolynomial.map_monomial, map_one]

lemma map_smul' (c : A) (z : AdjoinRoots q a) : map a φ (c • z) = φ c • map a φ z := by
  rw [Algebra.smul_def, map_mul, map_algebraMap, ← Algebra.smul_def]

lemma map_repr_symm (hq : 0 < q) (f : Exponents B q →₀ A) :
    map a φ ((basis a hq).repr.symm f) =
      (basis (fun i ↦ φ (a i)) hq).repr.symm (f.mapRange φ (map_zero φ)) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, Finsupp.mapRange_add (map_add φ), map_add]
  | single e c =>
    rw [Module.Basis.repr_symm_single, Finsupp.mapRange_single, Module.Basis.repr_symm_single,
      map_smul', map_basis]

/-- If `map φ z = 0`, then the coordinates of `z` lie in `ker φ`, so
`z ∈ (ker φ) · AdjoinRoots q a`. -/
lemma mem_map_ker_of_map_eq_zero (hq : 0 < q) {z : AdjoinRoots q a} (hz : map a φ z = 0) :
    z ∈ (RingHom.ker φ).map (algebraMap A (AdjoinRoots q a)) := by
  have h0 : ∀ e, φ ((basis a hq).repr z e) = 0 := by
    have := map_repr_symm a φ hq ((basis a hq).repr z)
    rw [Module.Basis.repr_symm_apply, Module.Basis.linearCombination_repr, hz] at this
    intro e
    have h' := congrArg (fun f ↦ f e) ((basis (fun i ↦ φ (a i)) hq).repr.symm.injective
      (this.symm.trans (map_zero _).symm))
    simpa using h'
  rw [← (basis a hq).linearCombination_repr z, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun e _ ↦ ?_
  rw [Algebra.smul_def]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h0 e))

end AdjoinRoots
