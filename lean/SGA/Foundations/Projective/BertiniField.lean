/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# A regular sequence for the Bertini field lemma

Let `k` be algebraically closed, `L ⊇ k` a field and `x, y ∈ L` algebraically independent over
`k`. The Matsusaka–Zariski proof of Bertini's theorem for the generic hyperplane section compares
two generic points `P`, `Q` of a variety and the line `x + s y = z` through their images. Its one
commutative-algebra input is that in `L ⊗_k L` the differences of coordinates
`a = x ⊗ 1 − 1 ⊗ x`, `b = y ⊗ 1 − 1 ⊗ y` form a regular sequence: `a` is a nonzerodivisor modulo
`b` (geometrically: the pairs of points on a common line have no extra component over the locus
`φ(P) = φ(Q)`). This file proves it in three steps:

* `MvPolynomial.mem_span_C_sub_X_of_mul_mem`: in `L[X₀, X₁]`, `x − X₀` is a nonzerodivisor
  modulo `y − X₁` (`x, y ∈ L`, `L` a domain): substitute `X₁ := y`;
* `Bertini.mem_span_of_mul_mem_fractionRing`: the same for `L ⊗_k k(X₀, X₁)`, with
  `a = x ⊗ 1 − 1 ⊗ X₀`, `b = y ⊗ 1 − 1 ⊗ X₁`, by clearing denominators
  (`Bertini.exists_mul_mem_range_lTensor`; `L ⊗_k k[X₀, X₁] ≅ L[X₀, X₁]`,
  `MvPolynomial.algebraTensorAlgEquiv`);
* `Bertini.mem_span_of_mul_mem`: the same for `L ⊗_k L`. Through `k(X₀, X₁) ≅ k(x, y) ⊆ L`
  (`Bertini.fractionRingEmbedding`), the right factor `L` is free over `k(X₀, X₁)`, so
  `L ⊗_k L ≅ ⊕_β L ⊗_k k(X₀, X₁)` as a module over `L ⊗_k k(X₀, X₁)`
  (`Bertini.tensorFinsuppEquiv`), and the statement holds coordinatewise.

The field lemma itself is in `SGA.Foundations.Projective.BertiniFieldLemma`.

## References

* [J.-P. Jouanolou, *Théorèmes de Bertini et applications*, §6]
* [M. Fried, M. Jarden, *Field Arithmetic*, §10.5]
-/

open MvPolynomial TensorProduct

namespace MvPolynomial

variable {L : Type*} [CommRing L] [IsDomain L]

/-- In `L[X₀, X₁]` (`L` a domain), `x − X₀` is a nonzerodivisor modulo `y − X₁`: if
`(x − X₀) c ∈ (y − X₁)` then `c ∈ (y − X₁)`. Substituting `X₁ := y` kills `y − X₁`, does not kill
`x − X₀`, and changes `c` only modulo `y − X₁`. -/
theorem mem_span_C_sub_X_of_mul_mem (x y : L) {c : MvPolynomial (Fin 2) L}
    (h : (C x - X 0) * c ∈ Ideal.span {C y - X 1}) : c ∈ Ideal.span {C y - X 1} := by
  let I : Ideal (MvPolynomial (Fin 2) L) := Ideal.span {C y - X 1}
  let σ : MvPolynomial (Fin 2) L →ₐ[L] MvPolynomial (Fin 2) L := aeval ![X 0, C y]
  -- `σ` is the identity modulo `I`
  have hσ (p : MvPolynomial (Fin 2) L) : p - σ p ∈ I := by
    have e : (Ideal.Quotient.mkₐ L I).comp σ = Ideal.Quotient.mkₐ L I := by
      refine MvPolynomial.algHom_ext fun i ↦ ?_
      fin_cases i
      · simp [σ]
      · simp only [σ, AlgHom.comp_apply, aeval_X, Fin.isValue, Ideal.Quotient.mkₐ_eq_mk]
        exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton_self (C y - X 1))
    have := congrArg (fun φ ↦ φ p) e
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq.mp this.symm
  have hb : σ (C y - X 1) = 0 := by simp [σ]
  have h0 : σ ((C x - X 0) * c) = 0 := by
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
    rw [← hd, map_mul, hb, mul_zero]
  have hσa : σ (C x - X 0) ≠ 0 := by
    have : σ (C x - X 0) = C x - X 0 := by simp [σ]
    rw [this, sub_ne_zero]
    intro hx
    have := congrArg (totalDegree) hx
    rw [totalDegree_C, totalDegree_X] at this
    exact zero_ne_one this
  rw [map_mul] at h0
  have hσc : σ c = 0 := (mul_eq_zero.mp h0).resolve_left hσa
  have := hσ c
  rwa [hσc, sub_zero] at this

end MvPolynomial

namespace Bertini

variable (k : Type*) [Field k] {L : Type*} [CommRing L] [IsDomain L] [Algebra k L]

/-- The field of rational functions `k(X₀, X₁)`. -/
local notation "K₁" => FractionRing (MvPolynomial (Fin 2) k)

omit [IsDomain L] in
/-- Every element of `L ⊗_k k(X₀, X₁)` becomes, after multiplication by `1 ⊗ s` for some nonzero
polynomial `s`, the image of an element of `L ⊗_k k[X₀, X₁]`. -/
lemma exists_mul_mem_range_lTensor (c : L ⊗[k] K₁) :
    ∃ s ∈ nonZeroDivisors (MvPolynomial (Fin 2) k),
      (1 ⊗ₜ algebraMap (MvPolynomial (Fin 2) k) K₁ s) * c ∈
        Set.range (Algebra.TensorProduct.map (AlgHom.id k L)
          (IsScalarTower.toAlgHom k (MvPolynomial (Fin 2) k) K₁)) := by
  let P := MvPolynomial (Fin 2) k
  let ι := Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k P K₁)
  induction c using TensorProduct.induction_on with
  | zero => exact ⟨1, one_mem _, 0, by simp⟩
  | tmul l q =>
    obtain ⟨p, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := P) q
    refine ⟨t, ht, l ⊗ₜ p, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, IsScalarTower.coe_toAlgHom',
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    rw [mul_div_cancel₀]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  | add c c' hc hc' =>
    obtain ⟨s, hs, w, hw⟩ := hc
    obtain ⟨s', hs', w', hw'⟩ := hc'
    refine ⟨s * s', mul_mem hs hs', (1 ⊗ₜ s') * w + (1 ⊗ₜ s) * w', ?_⟩
    rw [map_add, map_mul, map_mul, hw, hw', mul_add]
    simp only [Algebra.TensorProduct.map_tmul, map_one, IsScalarTower.coe_toAlgHom', map_mul]
    rw [← mul_assoc, ← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul]
    rw [mul_comm (algebraMap (MvPolynomial (Fin 2) k) K₁ s'), mul_one]

/-- **The regular sequence for the Bertini field lemma, over `k(X₀, X₁)`**: in
`L ⊗_k k(X₀, X₁)` (`L` a domain), `a = x ⊗ 1 − 1 ⊗ X₀` is a nonzerodivisor modulo
`b = y ⊗ 1 − 1 ⊗ X₁`. -/
theorem mem_span_of_mul_mem_fractionRing (x y : L) {c : L ⊗[k] K₁}
    (h : (x ⊗ₜ 1 - 1 ⊗ₜ algebraMap (MvPolynomial (Fin 2) k) K₁ (X 0)) * c ∈
      Ideal.span {y ⊗ₜ 1 - 1 ⊗ₜ algebraMap (MvPolynomial (Fin 2) k) K₁ (X 1)}) :
    c ∈ Ideal.span {y ⊗ₜ 1 - 1 ⊗ₜ algebraMap (MvPolynomial (Fin 2) k) K₁ (X 1)} := by
  let P := MvPolynomial (Fin 2) k
  have : Module.Flat k L := Module.Flat.of_free
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
  obtain ⟨s, hs, c₀, hc₀⟩ := exists_mul_mem_range_lTensor k c
  obtain ⟨s', hs', d₀, hd₀⟩ := exists_mul_mem_range_lTensor k d
  set ι := Algebra.TensorProduct.map (AlgHom.id k L) (IsScalarTower.toAlgHom k P K₁) with hιdef
  have hι : Function.Injective ι := by
    have : Function.Injective (LinearMap.lTensor L
        (IsScalarTower.toAlgHom k P K₁).toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective P K₁)
    exact this
  let a₁ : L ⊗[k] P := x ⊗ₜ 1 - 1 ⊗ₜ X 0
  let b₁ : L ⊗[k] P := y ⊗ₜ 1 - 1 ⊗ₜ X 1
  have ha : ι a₁ = x ⊗ₜ 1 - 1 ⊗ₜ algebraMap P K₁ (X 0) := by simp [ι, a₁]
  have hb : ι b₁ = y ⊗ₜ 1 - 1 ⊗ₜ algebraMap P K₁ (X 1) := by simp [ι, b₁]
  -- the units `1 ⊗ s`
  have hu (t : P) (ht : t ∈ nonZeroDivisors P) : IsUnit ((1 : L) ⊗ₜ[k] algebraMap P K₁ t) := by
    have ht' : algebraMap P K₁ t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
    have h1 : ((1 : L) ⊗ₜ[k] algebraMap P K₁ t) * (1 ⊗ₜ (algebraMap P K₁ t)⁻¹) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ ht',
        Algebra.TensorProduct.one_def]
    exact ⟨⟨_, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
  -- clear denominators
  let c₁ : L ⊗[k] P := (1 ⊗ₜ s') * c₀
  let d₁ : L ⊗[k] P := (1 ⊗ₜ s) * d₀
  have hc₁ : ι c₁ = (1 ⊗ₜ algebraMap P K₁ (s * s')) * c := by
    rw [map_mul, hc₀, hιdef, Algebra.TensorProduct.map_tmul, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [AlgHom.id_apply, IsScalarTower.coe_toAlgHom', one_mul, map_mul]
    rw [mul_comm (algebraMap P K₁ s')]
  have hd₁ : ι d₁ = (1 ⊗ₜ algebraMap P K₁ (s * s')) * d := by
    rw [map_mul, hd₀, hιdef, Algebra.TensorProduct.map_tmul, ← mul_assoc,
      Algebra.TensorProduct.tmul_mul_tmul]
    simp only [AlgHom.id_apply, IsScalarTower.coe_toAlgHom', one_mul, map_mul]
    rfl
  have hrel : a₁ * c₁ = b₁ * d₁ := by
    refine hι ?_
    have e1 : ι (a₁ * c₁) = ι a₁ * ι c₁ := map_mul ι a₁ c₁
    have e2 : ι (b₁ * d₁) = ι b₁ * ι d₁ := map_mul ι b₁ d₁
    rw [e1, e2, ha, hb, hc₁, hd₁, mul_left_comm, ← hd]
    ring
  -- transport to `L[X₀, X₁]`
  let e := MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) k L
  have hea : e a₁ = C x - X 0 := by simp [e, a₁, MvPolynomial.smul_eq_C_mul]
  have heb : e b₁ = C y - X 1 := by simp [e, b₁, MvPolynomial.smul_eq_C_mul]
  have hmem : (C x - X 0) * e c₁ ∈ Ideal.span {C y - X 1} := by
    rw [← hea, ← heb, ← map_mul, hrel, map_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (MvPolynomial.mem_span_C_sub_X_of_mul_mem x y hmem)
  have hc₁b : c₁ = e.symm q * b₁ := by
    apply e.injective
    have e3 : e (e.symm q * b₁) = q * e b₁ := by rw [map_mul, AlgEquiv.apply_symm_apply]
    rw [e3, heb, hq]
  -- conclude
  have hu' := hu (s * s') (mul_mem hs hs')
  obtain ⟨u, hu''⟩ := hu'
  have : c = (u⁻¹ : (L ⊗[k] K₁)ˣ) * (ι (e.symm q) * ι b₁) := by
    rw [← map_mul, ← hc₁b, hc₁, ← hu'', ← mul_assoc, Units.inv_mul, one_mul]
  rw [this, hb]
  exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))

section TensorSquare

variable {k} {F : Type*} [Field F] [Algebra k F] {x y : F}

/-- The embedding `k(X₀, X₁) → F`, `X₀ ↦ x`, `X₁ ↦ y`, for `x, y` algebraically independent. -/
noncomputable def fractionRingEmbedding (hxy : AlgebraicIndependent k ![x, y]) : K₁ →ₐ[k] F :=
  IsFractionRing.liftAlgHom (K := K₁) (g := aeval ![x, y])
    (algebraicIndependent_iff_injective_aeval.mp hxy)

lemma fractionRingEmbedding_algebraMap (hxy : AlgebraicIndependent k ![x, y])
    (p : MvPolynomial (Fin 2) k) :
    fractionRingEmbedding hxy (algebraMap (MvPolynomial (Fin 2) k) K₁ p) = aeval ![x, y] p := by
  rw [fractionRingEmbedding, IsFractionRing.liftAlgHom_apply, IsFractionRing.lift_algebraMap]
  rfl

variable (hxy : AlgebraicIndependent k ![x, y])

open Classical in
/-- `F ⊗_k F` as a module over `F ⊗_k k(X₀, X₁)` (acting on the right factor through
`fractionRingEmbedding`) is free: `F ⊗_k F ≅ ⊕_β F ⊗_k k(X₀, X₁)` for a basis `(e_β)` of `F` over
`k(X₀, X₁)`. -/
noncomputable def tensorFinsuppEquiv :
    letI : Algebra K₁ F := (fractionRingEmbedding hxy).toRingHom.toAlgebra
    F ⊗[k] F ≃ₗ[k] (Module.Basis.ofVectorSpaceIndex K₁ F →₀ F ⊗[k] K₁) :=
  letI : Algebra K₁ F := (fractionRingEmbedding hxy).toRingHom.toAlgebra
  haveI : IsScalarTower k K₁ F :=
    IsScalarTower.of_algebraMap_eq fun r ↦ ((fractionRingEmbedding hxy).commutes r).symm
  LinearEquiv.lTensor F ((Module.Basis.ofVectorSpace K₁ F).repr.restrictScalars k) ≪≫ₗ
    TensorProduct.finsuppRight k k F K₁ _

open Classical in
lemma tensorFinsuppEquiv_tmul_apply (l m : F) (i) :
    letI : Algebra K₁ F := (fractionRingEmbedding hxy).toRingHom.toAlgebra
    tensorFinsuppEquiv hxy (l ⊗ₜ m) i = l ⊗ₜ (Module.Basis.ofVectorSpace K₁ F).repr m i := by
  simp [tensorFinsuppEquiv, TensorProduct.finsuppRight_apply_tmul_apply]

open Classical in
/-- `tensorFinsuppEquiv` is linear over `F ⊗_k k(X₀, X₁)`. -/
lemma tensorFinsuppEquiv_map_mul (c : F ⊗[k] K₁) (w : F ⊗[k] F) :
    tensorFinsuppEquiv hxy
        (Algebra.TensorProduct.map (AlgHom.id k F) (fractionRingEmbedding hxy) c * w) =
      c • tensorFinsuppEquiv hxy w := by
  let _ : Algebra K₁ F := (fractionRingEmbedding hxy).toRingHom.toAlgebra
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c c' hc hc' => simp only [map_add, add_mul, hc, hc', add_smul]
  | tmul l q =>
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add w w' hw hw' => simp only [mul_add, map_add, hw, hw', smul_add]
    | tmul l' m =>
      ext i
      have hq : (fractionRingEmbedding hxy) q * m = q • m := rfl
      rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.tmul_mul_tmul, AlgHom.id_apply,
        hq, tensorFinsuppEquiv_tmul_apply, Finsupp.smul_apply, tensorFinsuppEquiv_tmul_apply,
        map_smul, Finsupp.smul_apply, smul_eq_mul, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul]

include hxy in
/-- For `y` transcendental over `k` (here: part of an algebraically independent pair),
`y ⊗ 1 ≠ 1 ⊗ y` in `F ⊗_k F`. -/
lemma tmul_one_sub_one_tmul_ne_zero : y ⊗ₜ[k] (1 : F) - 1 ⊗ₜ y ≠ 0 := by
  let P := MvPolynomial (Fin 2) k
  let j : P →ₐ[k] F := aeval ![x, y]
  have hj : Function.Injective j := algebraicIndependent_iff_injective_aeval.mp hxy
  let ι := Algebra.TensorProduct.map (AlgHom.id k F) j
  have hι : Function.Injective ι := by
    have : Function.Injective (LinearMap.lTensor F j.toLinearMap) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ hj
    exact this
  have hj1 : j (X 1) = y := by
    change aeval ![x, y] (X 1 : MvPolynomial (Fin 2) k) = y
    rw [aeval_X]
    rfl
  have h : ι (y ⊗ₜ 1 - 1 ⊗ₜ X 1) = y ⊗ₜ 1 - 1 ⊗ₜ y := by
    simp only [ι, map_sub, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, hj1]
  rw [← h]
  intro h0
  have e0 := congrArg (MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) k F)
    (hι (h0.trans (map_zero ι).symm))
  rw [map_zero] at e0
  have he : MvPolynomial.algebraTensorAlgEquiv (σ := Fin 2) k F (y ⊗ₜ 1 - 1 ⊗ₜ X 1) =
      C y - X 1 := by
    simp [MvPolynomial.smul_eq_C_mul]
  rw [he, sub_eq_zero] at e0
  have := congrArg totalDegree e0
  rw [totalDegree_C, totalDegree_X] at this
  exact zero_ne_one this

include hxy in
/-- **The regular sequence for the Bertini field lemma**: let `F ⊇ k` be a field and `x, y ∈ F`
algebraically independent over `k`. In `F ⊗_k F`, `a = x ⊗ 1 − 1 ⊗ x` is a nonzerodivisor
modulo `b = y ⊗ 1 − 1 ⊗ y`: if `a c ∈ (b)` then `c ∈ (b)`. -/
theorem mem_span_of_mul_mem {c : F ⊗[k] F}
    (h : (x ⊗ₜ[k] (1 : F) - 1 ⊗ₜ x) * c ∈ Ideal.span {y ⊗ₜ[k] (1 : F) - 1 ⊗ₜ y}) :
    c ∈ Ideal.span {y ⊗ₜ[k] (1 : F) - 1 ⊗ₜ y} := by
  classical
  let P := MvPolynomial (Fin 2) k
  let φ := fractionRingEmbedding hxy
  let ι := Algebra.TensorProduct.map (AlgHom.id k F) φ
  let Θ := tensorFinsuppEquiv hxy
  let a₁ : F ⊗[k] K₁ := x ⊗ₜ 1 - 1 ⊗ₜ algebraMap P K₁ (X 0)
  let b₁ : F ⊗[k] K₁ := y ⊗ₜ 1 - 1 ⊗ₜ algebraMap P K₁ (X 1)
  have h0 : φ (algebraMap P K₁ (X 0)) = x := by
    rw [fractionRingEmbedding_algebraMap]; simp
  have h1 : φ (algebraMap P K₁ (X 1)) = y := by
    rw [fractionRingEmbedding_algebraMap]; simp
  have ha : ι a₁ = x ⊗ₜ 1 - 1 ⊗ₜ x := by
    simp only [ι, a₁, map_sub, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, h0]
  have hb : ι b₁ = y ⊗ₜ 1 - 1 ⊗ₜ y := by
    simp only [ι, b₁, map_sub, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one, h1]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
  -- coordinatewise
  have hco (i) : Θ c i ∈ Ideal.span {b₁} := by
    have e : Θ (ι a₁ * c) = Θ (ι b₁ * d) := by rw [ha, hb, ← hd, mul_comm]
    rw [tensorFinsuppEquiv_map_mul, tensorFinsuppEquiv_map_mul] at e
    have ei := congrArg (fun f ↦ f i) e
    simp only [Finsupp.smul_apply, smul_eq_mul] at ei
    refine mem_span_of_mul_mem_fractionRing k x y ?_
    rw [ei]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  -- reassemble
  have hsymm (f : _ →₀ F ⊗[k] K₁) : Θ.symm (b₁ • f) = ι b₁ * Θ.symm f := by
    apply Θ.injective
    rw [LinearEquiv.apply_symm_apply, tensorFinsuppEquiv_map_mul, LinearEquiv.apply_symm_apply]
  rw [← Θ.symm_apply_apply c, ← (Θ c).sum_single, map_finsuppSum, ← hb]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.mp (hco i)
  change Θ.symm (Finsupp.single i (Θ c i)) ∈ _
  rw [← hq, mul_comm, ← smul_eq_mul, ← Finsupp.smul_single, hsymm]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end TensorSquare

end Bertini
