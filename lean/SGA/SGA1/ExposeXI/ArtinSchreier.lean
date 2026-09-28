/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat
import SGA.SGA1.ExposeXI.Kummer

/-!
# SGA 1, Exposé XI, §6: Artin–Schreier theory

Let `S` have characteristic `p` (`p · 𝒪_S = 0`), `F` the Frobenius of `𝔾_a` and `℘ = id - F`.
The Artin–Schreier sequence `0 → (ℤ/p)_S → 𝔾_a → 𝔾_a → 0` is exact (XI.6.7), and the coboundary
of `a ∈ H⁰(S, 𝒪_S)` is the Artin–Schreier covering `℘⁻¹(a) = Spec A[T]/(Tᵖ - T + a)`, a
principal covering with group `ℤ/p`, `k` acting by `T ↦ T + k`.

For `S = Spec A` (`p` prime, `(p : A) = 0`) we prove:

* `ArtinSchreier.etale`: `A[T]/(Tᵖ - T + a)` is finite étale;
* `ArtinSchreier.pointsEquiv`: its `B`-points are the solutions of `x - xᵖ = a`, i.e. it is
  the fibre of `℘` over `a`;
* `ArtinSchreier.nonempty_algHom_iff`: it is trivial if and only if `a ∈ ℘(A)`
  (exactness of XI.6.8 at `H⁰(S, 𝒪_S)`, affine case);
* `ArtinSchreier.isPrincipalCovering`: it is a principal covering with group `ℤ/p`;
* `ArtinSchreier.nonempty_equivariant_iff`: the coverings of `a` and `b` are isomorphic principal
  coverings if and only if `a - b ∈ ℘(A)` (injectivity of `A/℘A → H¹(S, ℤ/p)`, XI.6.8–XI.6.9);
* `ArtinSchreier.bijective_kernelEval`: `℘⁻¹(0) ≅ (ℤ/p)_S`, i.e. `(ℤ/p)_S` is the kernel of `℘`;
* `ArtinSchreier.polynomialEquiv`, `wp_faithfullyFlat`: `℘ : A[s] → A[t]` is the universal
  Artin–Schreier covering, hence faithfully flat, and `𝔾_a ×_{𝔾_a} 𝔾_a ≅ (ℤ/p) × 𝔾_a`
  (XI.6.7, exactness of the Artin–Schreier sequence).

SGA writes `℘ = id - F`, so `℘⁻¹(a)` is `T - Tᵖ = a`; the classical equation `Tᵖ - T = a` is
`℘⁻¹(-a)`.
-/

namespace SGA.SGA1.ExposeXI

open Polynomial TensorProduct

variable (A : Type*) [CommRing A]

/-- XI.6.7: the Artin–Schreier covering `℘⁻¹(a) = Spec A[T]/(Tᵖ - T + a)`, where `℘ = id - F`. -/
abbrev ArtinSchreierAlgebra (p : ℕ) (a : A) : Type _ := AdjoinRoot (X ^ p - X + C a : A[X])

variable {A} {p : ℕ} {a : A}

namespace ArtinSchreier

/-- In a ring where the prime `p` is zero, the `p`-th power map is additive. -/
theorem add_pow_of_natCast_eq_zero {R : Type*} [CommRing R] (hp : p.Prime) (hpR : (p : R) = 0)
    (x y : R) : (x + y) ^ p = x ^ p + y ^ p := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp x y
  rw [hr, hpR, zero_mul, zero_mul, zero_mul, add_zero]

theorem natCast_eq_zero {B : Type*} [CommRing B] [Algebra A B] (hpA : (p : A) = 0) :
    (p : B) = 0 := by
  rw [← map_natCast (algebraMap A B), hpA, map_zero]

theorem root_pow (p : ℕ) (a : A) :
    AdjoinRoot.root (X ^ p - X + C a) ^ p =
      AdjoinRoot.root (X ^ p - X + C a) - algebraMap A (ArtinSchreierAlgebra A p a) a := by
  have := AdjoinRoot.eval₂_root (X ^ p - X + C a)
  rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, ← AdjoinRoot.algebraMap_eq] at this
  linear_combination this

theorem eq_sub (p : ℕ) (a : A) : (X ^ p - X + C a : A[X]) = X ^ p - (X - C a) := by ring

theorem monic (hp : p.Prime) (a : A) : (X ^ p - X + C a : A[X]).Monic := by
  rw [eq_sub]
  exact monic_X_pow_sub ((degree_X_sub_C_le a).trans_lt (by exact_mod_cast hp.one_lt))

theorem natDegree_eq [Nontrivial A] (hp : p.Prime) (a : A) :
    (X ^ p - X + C a : A[X]).natDegree = p := by
  rw [eq_sub, natDegree_sub_eq_left_of_natDegree_lt] <;> simp [hp.one_lt]

/-- XI.6.7: the Artin–Schreier covering is étale (`Tᵖ - T + a` has derivative `-1`). -/
theorem etale (hp : p.Prime) (hpA : (p : A) = 0) (a : A) :
    Algebra.Etale A (ArtinSchreierAlgebra A p a) := by
  refine etale_adjoinRoot (monic hp a) (p₁ := -1) (p₂ := 0) ?_
  simp [derivative_X_pow, hpA]

instance [hp : Fact p.Prime] : Module.Finite A (ArtinSchreierAlgebra A p a) :=
  (AdjoinRoot.powerBasis' (monic hp.out a)).finite

instance [hp : Fact p.Prime] : Module.Free A (ArtinSchreierAlgebra A p a) :=
  .of_basis (AdjoinRoot.powerBasis' (monic hp.out a)).basis

/-- XI.6.7: the Artin–Schreier covering is faithfully flat (free of rank `p`). -/
instance [hp : Fact p.Prime] : Module.FaithfullyFlat A (ArtinSchreierAlgebra A p a) := by
  cases subsingleton_or_nontrivial A
  · exact { toFlat := inferInstance
            submodule_ne_top := fun _ hm ↦ (hm.ne_top (Subsingleton.elim _ _)).elim }
  · have : Nonempty (Fin (AdjoinRoot.powerBasis' (monic hp.out a)).dim) := by
      rw [AdjoinRoot.powerBasis'_dim, natDegree_eq hp.out]
      exact ⟨⟨0, hp.out.pos⟩⟩
    exact faithfullyFlat_of_basis (AdjoinRoot.powerBasis' (monic hp.out a)).basis

variable (p a) in
/-- XI.6.7, XI.6.8: the `B`-points of `A[T]/(Tᵖ - T + a)` are the solutions of `x - xᵖ = a`:
the Artin–Schreier covering is the fibre `℘⁻¹(a)`, the coboundary of `a` as in XI.4. -/
noncomputable def pointsEquiv (B : Type*) [CommRing B] [Algebra A B] :
    (ArtinSchreierAlgebra A p a →ₐ[A] B) ≃ {x : B // x - x ^ p = algebraMap A B a} where
  toFun φ := ⟨φ (AdjoinRoot.root _), by
    rw [← map_pow, root_pow, map_sub, AlgHom.commutes, sub_sub_cancel]⟩
  invFun x := AdjoinRoot.liftAlgHom _ (Algebra.ofId A B) x.1 (by
    change aeval x.1 (X ^ p - X + C a) = 0
    rw [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C]
    linear_combination -x.2)
  left_inv φ := by ext; simp
  right_inv x := by simp

/-- XI.6.8, exactness at the middle `H⁰(S, 𝒪_S)` (affine case): the Artin–Schreier covering of
`a` is trivial, i.e. has a section, if and only if `a = x - xᵖ` for some `x ∈ A`. -/
theorem nonempty_algHom_iff :
    Nonempty (ArtinSchreierAlgebra A p a →ₐ[A] A) ↔ ∃ x : A, x - x ^ p = a :=
  ⟨fun ⟨φ⟩ ↦ ⟨_, (pointsEquiv p a A φ).2⟩, fun ⟨x, hx⟩ ↦ ⟨(pointsEquiv p a A).symm ⟨x, hx⟩⟩⟩

section Translation

variable (hp : p.Prime) (hpA : (p : A) = 0)
include hp hpA

variable (p a) in
/-- The endomorphism `T ↦ T + c` of `A[T]/(Tᵖ - T + a)` for `cᵖ = c`. -/
noncomputable def translateHom (c : A) (hc : c ^ p = c) :
    ArtinSchreierAlgebra A p a →ₐ[A] ArtinSchreierAlgebra A p a :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AdjoinRoot.root _ + algebraMap A _ c) (by
    change aeval _ (X ^ p - X + C a) = 0
    rw [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C,
      add_pow_of_natCast_eq_zero hp (natCast_eq_zero hpA), root_pow, ← map_pow, hc]
    ring)

theorem translateHom_root (c : A) (hc : c ^ p = c) :
    translateHom p a hp hpA c hc (AdjoinRoot.root _) = AdjoinRoot.root _ + algebraMap A _ c :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem translateHom_comp (c d : A) (hc : c ^ p = c) (hd : d ^ p = d) :
    (translateHom p a hp hpA c hc).comp (translateHom p a hp hpA d hd) =
      translateHom p a hp hpA (c + d) (by rw [add_pow_of_natCast_eq_zero hp hpA, hc, hd]) := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, translateHom_root, map_add, AlgHom.commutes, translateHom_root,
    translateHom_root, map_add]
  ring

theorem translateHom_zero :
    translateHom p a hp hpA 0 (zero_pow hp.ne_zero) = AlgHom.id A _ := by
  refine AdjoinRoot.algHom_ext ?_
  rw [translateHom_root, map_zero, add_zero, AlgHom.id_apply]

end Translation

theorem algEquiv_ext {e₁ e₂ : ArtinSchreierAlgebra A p a ≃ₐ[A] ArtinSchreierAlgebra A p a}
    (h : e₁ (AdjoinRoot.root _) = e₂ (AdjoinRoot.root _)) : e₁ = e₂ :=
  AlgEquiv.coe_toAlgHom_injective (AdjoinRoot.algHom_ext h)

section Galois

variable (p a) [hp : Fact p.Prime] [CharP A p]

theorem castHom_pow (k : ZMod p) :
    ZMod.castHom (dvd_refl p) A k ^ p = ZMod.castHom (dvd_refl p) A k := by
  rw [← map_pow, ZMod.pow_card]

/-- The automorphism `T ↦ T + k` of the Artin–Schreier covering, for `k ∈ ℤ/p`. -/
noncomputable def translateEquiv (k : ZMod p) :
    ArtinSchreierAlgebra A p a ≃ₐ[A] ArtinSchreierAlgebra A p a :=
  AlgEquiv.ofAlgHom
    (translateHom p a hp.out (CharP.cast_eq_zero A p) _ (castHom_pow p k))
    (translateHom p a hp.out (CharP.cast_eq_zero A p) _ (castHom_pow p (-k)))
    (by rw [translateHom_comp, ← translateHom_zero hp.out (CharP.cast_eq_zero A p)]; simp)
    (by rw [translateHom_comp, ← translateHom_zero hp.out (CharP.cast_eq_zero A p)]; simp)

theorem translateEquiv_root (k : ZMod p) :
    translateEquiv p a k (AdjoinRoot.root _) =
      AdjoinRoot.root _ + algebraMap A _ (ZMod.castHom (dvd_refl p) A k) :=
  translateHom_root hp.out (CharP.cast_eq_zero A p) _ (castHom_pow p k)

/-- XI.6.7: the action of `ℤ/p` on the Artin–Schreier covering, `k` acting by `T ↦ T + k`. -/
noncomputable def action :
    Multiplicative (ZMod p) →* (ArtinSchreierAlgebra A p a ≃ₐ[A] ArtinSchreierAlgebra A p a) where
  toFun k := translateEquiv p a (Multiplicative.toAdd k)
  map_one' := algEquiv_ext (by
    rw [translateEquiv_root, toAdd_one, map_zero, map_zero, add_zero, AlgEquiv.one_apply])
  map_mul' k l := algEquiv_ext (by
    rw [AlgEquiv.mul_apply, translateEquiv_root, translateEquiv_root, map_add, AlgEquiv.commutes,
      translateEquiv_root, toAdd_mul, map_add, map_add]
    ring)

theorem action_root (k : Multiplicative (ZMod p)) :
    action p a k (AdjoinRoot.root _) =
      AdjoinRoot.root _ + algebraMap A _ (ZMod.castHom (dvd_refl p) A (Multiplicative.toAdd k)) :=
  translateEquiv_root p a _

/-- XI.6.7–XI.6.9 (affine case): over a ring of characteristic `p`, the Artin–Schreier covering
of any `a` is a principal covering with group `ℤ/p`, `k` acting by `T ↦ T + k`; in particular it
is finite étale. -/
theorem isPrincipalCovering [Nontrivial A] : IsPrincipalCovering (action p a (A := A)) := by
  refine isPrincipalCovering_adjoinRoot (monic hp.out a)
    (by rw [natDegree_eq hp.out, Fintype.card_multiplicative, ZMod.card]) _ fun k l hkl ↦ ?_
  dsimp only
  rw [action_root, action_root, add_sub_add_left_eq_sub, ← map_sub, ← map_sub]
  have : Multiplicative.toAdd k - Multiplicative.toAdd l ≠ 0 :=
    sub_ne_zero.mpr fun e ↦ hkl (Multiplicative.toAdd.injective e)
  exact ((isUnit_iff_ne_zero.mpr this).map _).map _

end Galois

section Classification

variable [hp : Fact p.Prime] [CharP A p]

variable (p) in
/-- The morphism `A[T]/(Tᵖ - T + a) → A[T]/(Tᵖ - T + b)`, `T ↦ T + c`, for `a - b = c - cᵖ`. -/
noncomputable def shiftHom (a b c : A) (h : a - b = c - c ^ p) :
    ArtinSchreierAlgebra A p a →ₐ[A] ArtinSchreierAlgebra A p b :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (AdjoinRoot.root _ + algebraMap A _ c) (by
    change aeval _ (X ^ p - X + C a) = 0
    have h' := congrArg (algebraMap A (ArtinSchreierAlgebra A p b)) h
    rw [map_sub, map_sub, map_pow] at h'
    rw [map_add, map_sub, aeval_X_pow, aeval_X, aeval_C,
      add_pow_of_natCast_eq_zero hp.out (natCast_eq_zero (CharP.cast_eq_zero A p)), root_pow]
    linear_combination h')

theorem shiftHom_root (a b c : A) (h : a - b = c - c ^ p) :
    shiftHom p a b c h (AdjoinRoot.root _) = AdjoinRoot.root _ + algebraMap A _ c :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

theorem neg_pow_char (c : A) : (-c) ^ p = -c ^ p := by
  have := add_pow_of_natCast_eq_zero hp.out (CharP.cast_eq_zero A p) c (-c)
  rw [add_neg_cancel, zero_pow hp.out.ne_zero] at this
  linear_combination -this

theorem shiftHom_comp (a b c : A) (h : a - b = c - c ^ p) (h' : b - a = -c - (-c) ^ p) :
    (shiftHom p b a (-c) h').comp (shiftHom p a b c h) = AlgHom.id A _ := by
  refine AdjoinRoot.algHom_ext ?_
  rw [AlgHom.comp_apply, shiftHom_root, map_add, shiftHom_root, AlgHom.commutes, map_neg,
    neg_add_cancel_right, AlgHom.id_apply]

/-- XI.6.8, XI.6.9 (affine case): the map `A/℘A → H¹(S, ℤ/p)` is well defined and injective:
the Artin–Schreier coverings of `a` and `b` are isomorphic as principal coverings with group
`ℤ/p` if and only if `a - b ∈ ℘(A)`. -/
theorem nonempty_equivariant_iff [Nontrivial A] (a b : A) :
    (∃ e : ArtinSchreierAlgebra A p a ≃ₐ[A] ArtinSchreierAlgebra A p b,
      ∀ k x, e (action p a k x) = action p b k (e x)) ↔ ∃ c : A, a - b = c - c ^ p := by
  constructor
  · rintro ⟨e, he⟩
    set x := e (AdjoinRoot.root _)
    have hfix : ∀ k, action p b k (x - AdjoinRoot.root _) = x - AdjoinRoot.root _ := by
      intro k
      rw [map_sub, ← he, action_root, map_add, AlgEquiv.commutes, action_root]
      ring
    obtain ⟨c, hc⟩ := ((isPrincipalCovering p b).mem_range_algebraMap_iff _).mpr hfix
    have hx : x = AdjoinRoot.root _ + algebraMap A _ c := by rw [hc]; ring
    have hrel : x ^ p = x - algebraMap A _ a := by
      rw [← map_pow, root_pow, map_sub, AlgEquiv.commutes]
    rw [hx, add_pow_of_natCast_eq_zero hp.out (natCast_eq_zero (CharP.cast_eq_zero A p)),
      root_pow] at hrel
    have hff := (isPrincipalCovering p b).faithfullyFlat
    have hinj := (RingHom.faithfullyFlat_algebraMap_iff.mpr hff).injective
    refine ⟨c, hinj ?_⟩
    rw [map_sub, map_sub, map_pow]
    linear_combination hrel
  · rintro ⟨c, hc⟩
    have hc' : b - a = -c - (-c) ^ p := by rw [neg_pow_char]; linear_combination -hc
    refine ⟨AlgEquiv.ofAlgHom (shiftHom p a b c hc) (shiftHom p b a (-c) hc') ?_
      (shiftHom_comp a b c hc hc'), fun k x ↦ ?_⟩
    · have hc'' : a - b = -(-c) - (-(-c)) ^ p := by rw [neg_neg]; exact hc
      have := shiftHom_comp b a (-c) hc' hc''
      simp only [neg_neg] at this
      exact this
    · have : (shiftHom p a b c hc).comp (action p a k : _ →ₐ[A] _) =
          (action p b k : _ →ₐ[A] _).comp (shiftHom p a b c hc) := by
        refine AdjoinRoot.algHom_ext ?_
        rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.coe_toAlgHom,
          action_root, map_add, shiftHom_root, AlgHom.commutes, map_add, action_root,
          AlgEquiv.commutes]
        ring
      exact AlgHom.congr_fun this x

end Classification

section Kernel

variable [hp : Fact p.Prime] [CharP A p]

theorem X_pow_sub_X_eq_prod :
    (X ^ p - X + C 0 : A[X]) = ∏ k : ZMod p, (X - C (ZMod.castHom (dvd_refl p) A k)) := by
  refine eq_prod_X_sub_C_of_isUnit_sub (monic hp.out 0) ?_ (fun k l hkl ↦ ?_) fun k ↦ ?_
  · rw [ZMod.card, eq_sub]
    exact (natDegree_sub_le _ _).trans (max_le (natDegree_X_pow_le p)
      ((natDegree_X_sub_C_le _).trans hp.out.one_lt.le))
  · dsimp only
    rw [← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hkl)).map _
  · rw [eval_add, eval_sub, eval_pow, eval_X, eval_C, castHom_pow, sub_self, zero_add]

variable (p) in
/-- XI.6.7: the morphism `(ℤ/p)_S → ker ℘` sending the generator to `1`; on rings it is
`A[T]/(Tᵖ - T) → A^{ℤ/p}`, `T ↦ (k)_k`. -/
noncomputable def kernelEval : ArtinSchreierAlgebra A p 0 →ₐ[A] (ZMod p → A) :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId A _) (fun k ↦ ZMod.castHom (dvd_refl p) A k) (by
    rw [X_pow_sub_X_eq_prod]
    exact eval₂_prod_X_sub_C_eq_zero _ Finset.univ Finset.mem_univ)

/-- XI.6.7: `(ℤ/p)_S` is the kernel of `℘ = id - F : 𝔾_a → 𝔾_a`: the fibre `℘⁻¹(0)`, i.e.
`A[T]/(Tᵖ - T)`, is isomorphic to the constant group scheme `A^{ℤ/p}` via `T ↦ (k)_k`. -/
theorem bijective_kernelEval : Function.Bijective (kernelEval p (A := A)) := by
  have hc : Pairwise fun k l : ZMod p ↦
      IsUnit (ZMod.castHom (dvd_refl p) A k - ZMod.castHom (dvd_refl p) A l) := fun k l hkl ↦ by
    dsimp only
    rw [← map_sub]
    exact (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hkl)).map _
  let E := (AdjoinRoot.algEquivOfEq A _ _ X_pow_sub_X_eq_prod).trans
    (adjoinRootProdXSubCEquiv (fun k : ZMod p ↦ ZMod.castHom (dvd_refl p) A k) hc)
  have : kernelEval p = E.toAlgHom := AdjoinRoot.algHom_ext (by
    change AdjoinRoot.liftAlgHom _ _ _ _ (AdjoinRoot.root _) = E (AdjoinRoot.root _)
    rw [AdjoinRoot.liftAlgHom_root, AlgEquiv.trans_apply, AdjoinRoot.algEquivOfEq_root,
      adjoinRootProdXSubCEquiv_root])
  rw [this]
  exact E.bijective

end Kernel

section Universal

variable (A p)

/-- XI.6.7: `℘ = id - F : 𝔾_a → 𝔾_a` on rings: `A[s] → A[t]`, `s ↦ t - tᵖ`. -/
noncomputable def wp : A[X] →ₐ[A] A[X] := aeval (X - X ^ p)

theorem wp_X : wp A p X = X - X ^ p := aeval_X _

/-- The map `A[s][T]/(Tᵖ - T + s) → A[t]`, `T ↦ t`, `s ↦ t - tᵖ`. -/
noncomputable def polynomialHom : ArtinSchreierAlgebra A[X] p X →+* A[X] :=
  AdjoinRoot.lift (wp A p).toRingHom X (by
    rw [eval₂_add, eval₂_sub, eval₂_X_pow, eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, wp_X]
    ring)

theorem polynomialHom_of (x : A[X]) : polynomialHom A p (AdjoinRoot.of _ x) = wp A p x :=
  AdjoinRoot.lift_of _

theorem polynomialHom_root : polynomialHom A p (AdjoinRoot.root _) = X :=
  AdjoinRoot.lift_root _

theorem algebraMap_artinSchreier_polynomial (c : A) :
    algebraMap A (ArtinSchreierAlgebra A[X] p X) c = AdjoinRoot.of _ (C c) := by
  rw [IsScalarTower.algebraMap_apply A A[X], Polynomial.algebraMap_apply,
    Algebra.algebraMap_self_apply, AdjoinRoot.algebraMap_eq]

/-- XI.6.7: `A[t]` is the universal Artin–Schreier covering: `A'[T]/(Tᵖ - T + s) ≅ A[t]` for
`A' = A[s]`, compatibly with `℘ : A' → A[t]` (`polynomialEquiv_algebraMap`). -/
noncomputable def polynomialEquiv : ArtinSchreierAlgebra A[X] p X ≃+* A[X] :=
  RingEquiv.ofRingHom (polynomialHom A p) (aeval (AdjoinRoot.root (X ^ p - X + C X))).toRingHom
    (Polynomial.ringHom_ext
      (fun c ↦ by
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_C,
          algebraMap_artinSchreier_polynomial, polynomialHom_of, wp, aeval_C, RingHom.id_apply,
          Polynomial.algebraMap_apply, Algebra.algebraMap_self_apply])
      (by
        rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X,
          polynomialHom_root, RingHom.id_apply]))
    (AdjoinRoot.ringHom_ext
      (Polynomial.ringHom_ext
        (fun c ↦ by
          rw [RingHom.comp_apply, RingHom.comp_apply, polynomialHom_of, wp, aeval_C,
            AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.algebraMap_apply,
            Algebra.algebraMap_self_apply, aeval_C, algebraMap_artinSchreier_polynomial,
            RingHom.comp_apply,
            RingHom.id_apply])
        (by
          rw [RingHom.comp_apply, RingHom.comp_apply, polynomialHom_of, wp_X,
            AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sub, map_pow, aeval_X, root_pow,
            sub_sub_cancel, AdjoinRoot.algebraMap_eq, RingHom.comp_apply, RingHom.id_apply]))
      (by
        rw [RingHom.comp_apply, polynomialHom_root, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          aeval_X, RingHom.id_apply]))

theorem polynomialEquiv_algebraMap (x : A[X]) :
    polynomialEquiv A p (algebraMap _ (ArtinSchreierAlgebra A[X] p X) x) = wp A p x := by
  rw [AdjoinRoot.algebraMap_eq]
  exact polynomialHom_of A p x

/-- XI.6.7: `℘ : 𝔾_a → 𝔾_a` is faithfully flat. -/
theorem wp_faithfullyFlat [hp : Fact p.Prime] :
    ((wp A p : A[X] →ₐ[A] A[X]) : A[X] →+* A[X]).FaithfullyFlat := by
  have h : ((wp A p : A[X] →ₐ[A] A[X]) : A[X] →+* A[X]) = (polynomialEquiv A p).toRingHom.comp
      (algebraMap A[X] (ArtinSchreierAlgebra A[X] p X)) :=
    RingHom.ext fun x ↦ (polynomialEquiv_algebraMap A p x).symm
  rw [h]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance)
    (RingHom.FaithfullyFlat.of_bijective (polynomialEquiv A p).bijective)

/-- XI.6.7: exactness of the Artin–Schreier sequence in the sense of XI.4: over the base `𝔾_a`,
`℘ : 𝔾_a → 𝔾_a` (identified with the universal Artin–Schreier covering by `polynomialEquiv`) is
a principal covering with group `ℤ/p`: `𝔾_a ×_{𝔾_a} 𝔾_a ≅ ∏_{ℤ/p} 𝔾_a`. -/
theorem isPrincipalCovering_universal [Fact p.Prime] [CharP A p] [Nontrivial A] :
    IsPrincipalCovering (action p (X : A[X])) :=
  isPrincipalCovering p X

end Universal

end ArtinSchreier

end SGA.SGA1.ExposeXI
