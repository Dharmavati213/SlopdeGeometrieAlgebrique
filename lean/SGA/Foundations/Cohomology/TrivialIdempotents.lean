/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Idempotents of finite algebras over a field under base change

Algebra for the geometric form of Zariski's connectedness theorem (EGA III 4.3.4; EGA IV 4.5.1):
a scheme is connected iff its ring of global functions has only trivial idempotents
(`CohomologyAux.TrivialIdempotents`), and for proper schemes over a field this ring is finite.

* `CohomologyAux.isLocalRing_of_trivialIdempotents`: artinian rings with only trivial idempotents
  are local;
* `CohomologyAux.TrivialIdempotents.of_ker_isNilpotent`, `TrivialIdempotents.of_surjective`:
  invariance under nil ideals;
* `CohomologyAux.trivialIdempotents_tensor_of_isPurelyInseparable`: `k' ⊗_k K` has only trivial
  idempotents for `k'/k` purely inseparable;
* `CohomologyAux.not_trivialIdempotents_tensor_adjoinRoot`: `k' ⊗_k k(α)` has a non-trivial
  idempotent if `α ∈ k' \ k` is separable over `k`;
* `CohomologyAux.trivialIdempotents_tensor_of_forall_separable`: if a finite `k`-algebra `B` has
  only trivial idempotents after every finite separable simple extension of `k` (including `k`
  itself), then after every field extension.
-/

open Polynomial TensorProduct

namespace AlgebraicGeometry.CohomologyAux

section Idempotents

variable (R : Type*) [CommRing R]

/-- A commutative ring *has only trivial idempotents* (equivalently, `Spec R` is connected or
empty). -/
def TrivialIdempotents : Prop := ∀ e : R, IsIdempotentElem e → e = 0 ∨ e = 1

variable {R}

/-- An artinian ring with only trivial idempotents is local. -/
lemma isLocalRing_of_trivialIdempotents [IsArtinianRing R] [Nontrivial R]
    (h : TrivialIdempotents R) : IsLocalRing R := by
  have hsub : ∀ p : PrimeSpectrum R, ({p} : Set (PrimeSpectrum R)) = Set.univ := by
    intro p
    obtain ⟨e, he, hpe⟩ := PrimeSpectrum.isClopen_iff.mp (isClopen_discrete {p})
    rcases h e he with rfl | rfl
    · have : p ∈ (PrimeSpectrum.basicOpen (0 : R) : Set (PrimeSpectrum R)) :=
        hpe ▸ Set.mem_singleton p
      simp at this
    · rw [hpe, PrimeSpectrum.basicOpen_one]
      rfl
  obtain ⟨M, hM⟩ := Ideal.exists_maximal R
  refine IsLocalRing.of_unique_max_ideal ⟨M, hM, fun M' hM' ↦ ?_⟩
  have h' : (⟨M', hM'.isPrime⟩ : PrimeSpectrum R) ∈
      ({⟨M, hM.isPrime⟩} : Set (PrimeSpectrum R)) := by
    rw [hsub]
    trivial
  exact congrArg PrimeSpectrum.asIdeal (Set.mem_singleton_iff.mp h')

variable {S : Type*} [CommRing S]

/-- Trivial idempotents descend along ring maps with nil kernel. -/
lemma TrivialIdempotents.of_ker_isNilpotent (f : R →+* S)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) (hS : TrivialIdempotents S) :
    TrivialIdempotents R := by
  intro e he
  have hnil' : ∀ x : R, IsIdempotentElem x → IsNilpotent x → x = 0 := fun x hx ⟨n, hn⟩ ↦ by
    rw [← hx.pow_succ_eq n, pow_succ, hn, zero_mul]
  rcases hS (f e) (he.map f) with h | h
  · exact Or.inl (hnil' e he (hnil e h))
  · refine Or.inr (sub_eq_zero.mp (hnil' (1 - e) he.one_sub (hnil _ ?_))).symm
    rw [RingHom.mem_ker, map_sub, map_one, h, sub_self]

/-- Trivial idempotents ascend along surjective ring maps with nil kernel. -/
lemma TrivialIdempotents.of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (hnil : ∀ x ∈ RingHom.ker f, IsNilpotent x) (hR : TrivialIdempotents R) :
    TrivialIdempotents S := by
  intro e he
  obtain ⟨e', he', rfl⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent f hnil e (hf e) he
  rcases hR e' he' with rfl | rfl
  · exact Or.inl (map_zero f)
  · exact Or.inr (map_one f)

end Idempotents

section PurelyInseparable

variable (k k' K : Type*) [Field k] [Field k'] [Field K] [Algebra k k'] [Algebra k K]

/-- **Purely inseparable extensions stay connected under base change**: for `k'/k` purely
inseparable and any field `K ⊇ k`, `k' ⊗_k K` has only trivial idempotents. Every element of
`k' ⊗_k K` has a `q^n`-th power in `K` (`q` the characteristic exponent). -/
lemma trivialIdempotents_tensor_of_isPurelyInseparable [IsPurelyInseparable k k'] :
    TrivialIdempotents (k' ⊗[k] K) := by
  have : Nontrivial (k' ⊗[k] K) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left k k' K
      (algebraMap k K).injective
  let q := ringExpChar k
  have : ExpChar k q := ringExpChar.expChar k
  have : ExpChar (k' ⊗[k] K) q :=
    expChar_of_injective_algebraMap (algebraMap k (k' ⊗[k] K)).injective q
  have hpow : ∀ z : k' ⊗[k] K, ∃ n : ℕ, ∃ c : K,
      z ^ q ^ n = Algebra.TensorProduct.includeRight c := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => exact ⟨0, 0, by simp⟩
    | tmul a b =>
      obtain ⟨n, c, hc⟩ := IsPurelyInseparable.pow_mem k q a
      refine ⟨n, algebraMap k K c * b ^ q ^ n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, ← hc, Algebra.TensorProduct.includeRight_apply,
        ← Algebra.smul_def, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_one]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨n₁, c₁, hc₁⟩ := h₁
      obtain ⟨n₂, c₂, hc₂⟩ := h₂
      refine ⟨n₁ + n₂, c₁ ^ q ^ n₂ + c₂ ^ q ^ n₁, ?_⟩
      rw [add_pow_expChar_pow, map_add, map_pow, map_pow, ← hc₁, ← hc₂, ← pow_mul, ← pow_mul,
        ← pow_add, ← pow_add, add_comm n₂ n₁]
  intro e he
  obtain ⟨n, c, hc⟩ := hpow e
  have heq : e = Algebra.TensorProduct.includeRight c := by
    rw [← hc, he.pow_eq (pow_ne_zero n (expChar_pos k q).ne')]
  have hinj : Function.Injective (Algebra.TensorProduct.includeRight :
      K →ₐ[k] k' ⊗[k] K) := RingHom.injective (Algebra.TensorProduct.includeRight :
        K →ₐ[k] k' ⊗[k] K).toRingHom
  have hcc : IsIdempotentElem c := by
    refine hinj ?_
    rw [map_mul, ← heq]
    exact he
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hcc with rfl | rfl
  · exact Or.inl (heq.trans (map_zero _))
  · exact Or.inr (heq.trans (map_one _))

end PurelyInseparable

section Separable

variable {k k' : Type*} [Field k] [Field k'] [Algebra k k']

/-- For `α ∈ k'` separable over `k` but not in `k`, `k' ⊗_k k(α)` has a non-trivial idempotent:
over `k'`, the minimal polynomial `p` of `α` splits as `(t - α) q` with `t - α`, `q` coprime. -/
lemma not_trivialIdempotents_tensor_adjoinRoot (α : k') (hsep : IsSeparable k α)
    (hα : α ∉ (algebraMap k k').range) :
    ¬ TrivialIdempotents (k' ⊗[k] AdjoinRoot (minpoly k α)) := by
  intro hT
  set p := minpoly k α with hp
  have hint : IsIntegral k α := hsep.isIntegral
  set p' := p.map (algebraMap k k') with hp'
  have hroot : p'.IsRoot α := by
    rw [IsRoot, hp', eval_map_algebraMap]
    exact minpoly.aeval k α
  set q' := p' /ₘ (X - C α) with hq'
  have hfac : (X - C α) * q' = p' := mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hsep' : p'.Separable := Polynomial.Separable.map hsep
  have hcop : IsCoprime (X - C α) q' := by
    rw [← hfac] at hsep'
    exact hsep'.isCoprime
  obtain ⟨u, v, huv⟩ := hcop
  let T := k' ⊗[k] AdjoinRoot p
  let θ : T := Algebra.TensorProduct.includeRight (AdjoinRoot.root p)
  have hθ : aeval θ p' = 0 := by
    rw [hp', aeval_map_algebraMap, aeval_algHom_apply, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
      map_zero]
  let e : T := aeval θ (v * q')
  have hidem : IsIdempotentElem e := by
    have hpoly : v * q' * (v * q') - v * q' = -(u * v) * p' := by
      rw [← hfac]
      linear_combination (v * q') * huv
    have h2 : aeval θ (v * q' * (v * q')) - aeval θ (v * q') = 0 := by
      rw [← map_sub, hpoly, map_mul, hθ, mul_zero]
    change aeval θ (v * q') * aeval θ (v * q') = aeval θ (v * q')
    rw [← map_mul]
    exact sub_eq_zero.mp h2
  -- `e ↦ 1` under `t ↦ α`
  have hαp : p.eval₂ (Algebra.ofId k k') α = 0 := by
    have := minpoly.aeval k α
    rw [aeval_def] at this
    exact this
  let Ψ : T →ₐ[k'] k' := Algebra.TensorProduct.lift (AlgHom.id k' k')
    (AdjoinRoot.liftAlgHom p (Algebra.ofId k k') α hαp) fun _ _ ↦ Commute.all _ _
  have hΨθ : Ψ θ = α := by
    change Ψ (1 ⊗ₜ AdjoinRoot.root p) = α
    rw [Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AdjoinRoot.liftAlgHom_root, one_mul]
  have hΨe : Ψ e = 1 := by
    change Ψ (aeval θ (v * q')) = 1
    rw [← aeval_algHom_apply, hΨθ]
    have h1 := congrArg (aeval α) huv
    rw [map_add, map_mul, map_mul, map_one, map_sub, aeval_X, aeval_C, Algebra.algebraMap_self,
      RingHom.id_apply, sub_self, mul_zero, zero_add] at h1
    rw [map_mul]
    exact h1
  -- `e ↦ 0` under `t ↦ β` for a root `β` of `q`
  have hdeg : 2 ≤ p.natDegree := (minpoly.two_le_natDegree_iff hint).mpr hα
  have hq'deg : 1 ≤ q'.natDegree := by
    rw [hq', natDegree_divByMonic _ (monic_X_sub_C α), natDegree_X_sub_C, hp',
      natDegree_map]
    omega
  have hq'0 : q' ≠ 0 := fun h ↦ by simp [h] at hq'deg
  obtain ⟨r, hr, hrq⟩ := WfDvdMonoid.exists_irreducible_factor
    (Polynomial.not_isUnit_of_natDegree_pos _ (by omega)) hq'0
  have : Fact (Irreducible r) := ⟨hr⟩
  let F := AdjoinRoot r
  let β : F := AdjoinRoot.root r
  have hβq : aeval β q' = 0 := by
    obtain ⟨s, hs⟩ := hrq
    rw [hs, map_mul, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self, zero_mul]
  have hβp : p.eval₂ (Algebra.ofId k F) β = 0 := by
    have : aeval β p = 0 := by
      rw [← aeval_map_algebraMap k', ← hp', ← hfac, map_mul, hβq, mul_zero]
    rw [aeval_def] at this
    exact this
  let χ : T →ₐ[k'] F := Algebra.TensorProduct.lift (Algebra.ofId k' F)
    (AdjoinRoot.liftAlgHom p (Algebra.ofId k F) β hβp) fun _ _ ↦ Commute.all _ _
  have hχθ : χ θ = β := by
    change χ (1 ⊗ₜ AdjoinRoot.root p) = β
    rw [Algebra.TensorProduct.lift_tmul, map_one, AdjoinRoot.liftAlgHom_root, one_mul]
  have hχe : χ e = 0 := by
    change χ (aeval θ (v * q')) = 0
    rw [← aeval_algHom_apply, hχθ, map_mul, hβq, mul_zero]
  rcases hT e hidem with h | h
  · rw [h, map_zero] at hΨe
    exact zero_ne_one hΨe
  · rw [h, map_one] at hχe
    exact one_ne_zero hχe

end Separable

section Main

variable (k B : Type*) [Field k] [CommRing B] [Algebra k B]

/-- For `B` local with nilpotent maximal ideal, `B ⊗_k L → κ(B) ⊗_k L` is surjective with nil
kernel. -/
lemma isNilpotent_of_mem_ker_map_residue [IsLocalRing B]
    (hm : IsNilpotent (IsLocalRing.maximalIdeal B)) (L : Type*) [CommRing L] [Algebra k L] :
    ∀ x ∈ RingHom.ker (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k B (IsLocalRing.ResidueField B)) (AlgHom.id k L)),
      IsNilpotent x := by
  obtain ⟨N, hN⟩ := hm
  intro x hx
  rw [Algebra.TensorProduct.rTensor_ker _ IsLocalRing.residue_surjective] at hx
  have hker : RingHom.ker (IsScalarTower.toAlgHom k B (IsLocalRing.ResidueField B)) =
      IsLocalRing.maximalIdeal B := IsLocalRing.ker_residue
  rw [hker] at hx
  refine ⟨N, ?_⟩
  have : x ^ N ∈ ((IsLocalRing.maximalIdeal B).map
      (Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] L)) ^ N := Ideal.pow_mem_pow hx N
  rwa [← Ideal.map_pow, hN, Ideal.zero_eq_bot, Ideal.map_bot, Ideal.mem_bot] at this

lemma surjective_map_residue [IsLocalRing B] (L : Type*) [CommRing L] [Algebra k L] :
    Function.Surjective (Algebra.TensorProduct.map
      (IsScalarTower.toAlgHom k B (IsLocalRing.ResidueField B)) (AlgHom.id k L)) :=
  Algebra.TensorProduct.map_surjective _ (AlgHom.id k L) IsLocalRing.residue_surjective
    Function.surjective_id

/-- **Geometric connectedness of a finite algebra** (EGA IV 4.5.1 for `Spec B`). Let `B` be a
nonzero finite `k`-algebra with only trivial idempotents such that `B ⊗_k L` has only trivial
idempotents for every finite separable simple extension `L = k[t]/(p)`. Then `B ⊗_k K` has only
trivial idempotents for every field `K ⊇ k`. (`B` is local; its residue field has no separable
elements outside `k`, by `not_trivialIdempotents_tensor_adjoinRoot`, so it is purely inseparable
over `k` and `trivialIdempotents_tensor_of_isPurelyInseparable` applies modulo the nilpotent
maximal ideal.) -/
theorem trivialIdempotents_tensor_of_forall_separable [Module.Finite k B] [Nontrivial B]
    (h₀ : TrivialIdempotents B)
    (h₁ : ∀ p : k[X], p.Monic → Irreducible p → p.Separable →
      TrivialIdempotents (B ⊗[k] AdjoinRoot p))
    (K : Type*) [Field K] [Algebra k K] : TrivialIdempotents (B ⊗[k] K) := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : IsLocalRing B := isLocalRing_of_trivialIdempotents h₀
  let k' := IsLocalRing.ResidueField B
  let π : B →ₐ[k] k' := IsScalarTower.toAlgHom k B k'
  have hm : IsNilpotent (IsLocalRing.maximalIdeal B) := by
    have h := IsArtinianRing.isNilpotent_jacobson_bot (R := B)
    rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at h
  have : Module.Finite k k' := Module.Finite.of_surjective π.toLinearMap
    IsLocalRing.residue_surjective
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  have hpi : IsPurelyInseparable k k' := by
    rw [← separableClosure.eq_bot_iff, eq_bot_iff]
    intro α hα
    rw [mem_separableClosure_iff] at hα
    rw [IntermediateField.mem_bot]
    by_contra hne
    have hint : IsIntegral k α := hα.isIntegral
    refine not_trivialIdempotents_tensor_adjoinRoot α hα (fun h ↦ hne h) ?_
    exact TrivialIdempotents.of_surjective (Algebra.TensorProduct.map π (AlgHom.id k _)).toRingHom
      (surjective_map_residue k B _) (isNilpotent_of_mem_ker_map_residue k B hm _)
      (h₁ _ (minpoly.monic hint) (minpoly.irreducible hint) hα)
  exact TrivialIdempotents.of_ker_isNilpotent
    (Algebra.TensorProduct.map π (AlgHom.id k K)).toRingHom
    (isNilpotent_of_mem_ker_map_residue k B hm K)
    (trivialIdempotents_tensor_of_isPurelyInseparable k k' K)

end Main

end AlgebraicGeometry.CohomologyAux
