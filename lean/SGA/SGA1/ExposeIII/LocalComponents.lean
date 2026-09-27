/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.Semilocal
import SGA.SGA1.ExposeIII.PowerSeriesStructure
import SGA.SGA1.ExposeIII.ResidueLift
import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# SGA 1, Exposé III, 1.4, 1.6 and 2.1: finite residue extensions

Let `A → B` be a local homomorphism of complete noetherian local rings whose residue extension
`L / k` is finite. SGA reduces the study of formal smoothness to the case of a trivial residue
extension by a finite free local extension `A'` of `A` whose residue field `k'` makes the residue
extensions of the local components of `B' = A' ⊗[A] B` trivial (proof of III.1.6). We formalize:

* `exists_finite_free_residue_trivial`: such an `A'` exists (take `k'` a normal closure of `L/k`
  and lift it, `exists_finite_free_residue_lift`);
* `adicFormallySmooth_of_formallySmoothLocal'` and `formallySmoothLocal_of_adicFormallySmooth'`:
  Theorem III.2.1, (i) ⇔ (iii), for a finite residue extension;
* `formallySmoothLocal_iff_adicFormallySmooth'`, `formallySmooth_tfae'`: III.2.1 (i) ⇔ (ii) ⇔
  (iii) ⇔ (iv) for a finite residue extension;
* `formallySmoothLocal_localization`: Proposition III.1.4 (i) in the form of Definition III.1.1;
* `formallySmoothLocal_of_localization`: Proposition III.1.4 (ii) in the form of Definition III.1.1;
* `exists_algEquiv_mvPowerSeries_of_formallySmoothLocal`: Corollary III.1.6: for every finite
  free local `A'` making the residue extensions of `A' ⊗ B` trivial, the local components of
  `A' ⊗ B` are power series rings over `A'`.

The local components of `A' ⊗[A] B` are its localizations `(A' ⊗ B)_P` at maximal ideals; they
are complete, being the quotients `(A' ⊗ B) ⧸ (1 - e_P)` by idempotents (`Semilocal.lean`).
-/

universe u

open IsLocalRing TensorProduct Polynomial

namespace SGA.SGA1.ExposeIII

section TensorFinite

variable (A A' B : Type*) [CommRing A] [CommRing A'] [CommRing B] [Algebra A A'] [Algebra A B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- `A' ⊗[A] B` is finite over `B` when `A'` is finite over `A`. -/
lemma finite_tensorProduct_right [Module.Finite A A'] : Module.Finite B (A' ⊗[A] B) := by
  let e : (B ⊗[A] A') ≃ₗ[B] (A' ⊗[A] B) :=
    { (TensorProduct.comm A B A') with
      map_smul' := fun b x ↦ by
        induction x using TensorProduct.induction_on with
        | zero => simp
        | tmul c a =>
          simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
            TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.comm_tmul, RingHom.id_apply]
          rw [Algebra.smul_def, Algebra.TensorProduct.right_algebraMap_apply,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul]
        | add x y hx hy =>
          simp only [smul_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
            map_add] at hx hy ⊢
          rw [hx, hy] }
  exact Module.Finite.equiv e

end TensorFinite

section Local

variable {A A' : Type*} [CommRing A] [CommRing A'] [Algebra A A'] [IsLocalRing A] [IsLocalRing A']
  [Module.Finite A A']

/-- For a local ring `A'` finite over a local ring `A`, `𝔪 A' ⊆ 𝔪'`. -/
lemma map_maximalIdeal_le_of_finite :
    (maximalIdeal A).map (algebraMap A A') ≤ maximalIdeal A' :=
  Ideal.map_le_iff_le_comap.mpr (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal A'))).ge

/-- A local ring `A'` finite over a local ring `A` is local over `A`. -/
lemma isLocalHom_of_finite : IsLocalHom (algebraMap A A') :=
  ⟨fun a ha ↦ by
    by_contra h
    exact (mem_maximalIdeal _).mp (map_maximalIdeal_le_of_finite
      (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr h))) ha⟩

/-- A local ring finite over a complete noetherian local ring is complete. -/
lemma isAdicComplete_maximalIdeal_of_finite [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] : IsAdicComplete (maximalIdeal A') A' := by
  have := isAdicComplete_map_of_finite (B' := A') (maximalIdeal A)
  have := isArtinianRing_quotient_map_maximalIdeal (B := A) (B' := A')
  obtain ⟨N, hN⟩ :=
    exists_pow_maximalIdeal_le_of_isArtinianRing ((maximalIdeal A).map (algebraMap A A'))
  exact IsAdicComplete.of_pow_le (k := 1) (by rw [pow_one]; exact map_maximalIdeal_le_of_finite)
    hN

end Local

section Components

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalRing A']
  [Module.Finite A A']

attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] [IsLocalRing A'] in
/-- Every maximal ideal of `A' ⊗[A] B` contains `𝔫 (A' ⊗ B)`, since `A' ⊗ B` is finite over
`B`. -/
lemma map_maximalIdeal_le_of_isMaximal (P : Ideal (A' ⊗[A] B)) [P.IsMaximal] :
    (maximalIdeal B).map (algebraMap B (A' ⊗[A] B)) ≤ P := by
  have := finite_tensorProduct_right A A' B
  exact Ideal.map_le_iff_le_comap.mpr
    (IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).ge

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsLocalRing A']
  [Module.Finite A A'] in
lemma algebraMap_algebraMap_eq (a : A) :
    algebraMap A' (A' ⊗[A] B) (algebraMap A A' a) =
      algebraMap B (A' ⊗[A] B) (algebraMap A B a) := by
  rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.right_algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one,
    Algebra.algebraMap_eq_smul_one (A := B), TensorProduct.smul_tmul]

/-- Every maximal ideal of `A' ⊗[A] B` contains `𝔪_{A'} (A' ⊗ B)`. -/
lemma map_maximalIdeal_left_le (P : Ideal (A' ⊗[A] B)) [hP : P.IsMaximal] :
    (maximalIdeal A').map (algebraMap A' (A' ⊗[A] B)) ≤ P := by
  have := isArtinianRing_quotient_map_maximalIdeal (B := A) (B' := A')
  obtain ⟨N, hN⟩ :=
    exists_pow_maximalIdeal_le_of_isArtinianRing ((maximalIdeal A).map (algebraMap A A'))
  have hle : (maximalIdeal A).map (algebraMap A A') ≤ P.comap (algebraMap A' (A' ⊗[A] B)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, algebraMap_algebraMap_eq]
    exact map_maximalIdeal_le_of_isMaximal A' P (Ideal.mem_map_of_mem _
      ((mem_maximalIdeal _).mpr (map_nonunit _ a ((mem_maximalIdeal _).mp ha))))
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  have := hle (hN (Ideal.pow_mem_pow hx N))
  rw [Ideal.mem_comap, map_pow] at this
  exact hP.isPrime.mem_of_pow_mem N this

omit [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsLocalRing A']
  [Module.Finite A A'] in
/-- The condition that the residue extensions of `A' ⊗ B` over `A'` are trivial at `P` reduces to
the elements `1 ⊗ b`. -/
lemma exists_sub_mem_of_forall_tmul (P : Ideal (A' ⊗[A] B))
    (h : ∀ b : B, ∃ a' : A', (1 : A') ⊗ₜ b - algebraMap A' (A' ⊗[A] B) a' ∈ P)
    (x : A' ⊗[A] B) : ∃ a' : A', x - algebraMap A' (A' ⊗[A] B) a' ∈ P := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul a b =>
    obtain ⟨a'', ha''⟩ := h b
    refine ⟨a * a'', ?_⟩
    have : a ⊗ₜ[A] b - algebraMap A' (A' ⊗[A] B) (a * a'') =
        algebraMap A' (A' ⊗[A] B) a * ((1 : A') ⊗ₜ b - algebraMap A' (A' ⊗[A] B) a'') := by
      rw [mul_sub, map_mul, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
        RingHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [this]
    exact P.mul_mem_left _ ha''
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨a', ha'⟩ := hy
    refine ⟨a + a', ?_⟩
    rw [map_add, show x + y - (algebraMap A' _ a + algebraMap A' _ a') =
      (x - algebraMap A' _ a) + (y - algebraMap A' _ a') by ring]
    exact add_mem ha ha'

variable [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [IsNoetherianRing B]
  [IsAdicComplete (maximalIdeal B) B]

/-- III.2.1, (iv ter) ⇒ (i), on one local component: let `A'` be finite and local over `A`, and
`P` a maximal ideal of `B' = A' ⊗[A] B` at which the residue extension of `B'` over `A'` is
trivial. If the local component `B' ⧸ (1 - e)` at `P` has the lifting property (iv ter) of III.2.2
over `A'`, then the localization `B'_P` is `A'`-isomorphic to a power series ring over `A'`. As in
SGA, the local component is complete (it is the quotient of the complete ring `B'` by an
idempotent), and III.2.2 applies. -/
theorem exists_algEquiv_localization_of_artinianLiftingProperty
    (P : Ideal (A' ⊗[A] B)) [P.IsMaximal]
    (hP : ∀ x : A' ⊗[A] B, ∃ a' : A', x - algebraMap A' (A' ⊗[A] B) a' ∈ P)
    (H : ∀ e : A' ⊗[A] B, IsIdempotentElem e → e ∉ P →
      (∀ Q : Ideal (A' ⊗[A] B), Q.IsMaximal → Q ≠ P → e ∈ Q) →
      ∀ [IsLocalRing ((A' ⊗[A] B) ⧸ Ideal.span {1 - e})]
        [IsNoetherianRing ((A' ⊗[A] B) ⧸ Ideal.span {1 - e})]
        [IsAdicComplete (maximalIdeal ((A' ⊗[A] B) ⧸ Ideal.span {1 - e}))
          ((A' ⊗[A] B) ⧸ Ideal.span {1 - e})]
        [IsLocalHom (algebraMap A' ((A' ⊗[A] B) ⧸ Ideal.span {1 - e}))]
        [IsNoetherianRing A'] [IsAdicComplete (maximalIdeal A') A'],
      (∀ s : (A' ⊗[A] B) ⧸ Ideal.span {1 - e}, ∃ a' : A',
        s - algebraMap A' _ a' ∈ maximalIdeal ((A' ⊗[A] B) ⧸ Ideal.span {1 - e})) →
        ArtinianLiftingProperty A' ((A' ⊗[A] B) ⧸ Ideal.span {1 - e})) :
    ∃ n, Nonempty (Localization.AtPrime P ≃ₐ[A'] MvPowerSeries (Fin n) A') := by
  have := finite_tensorProduct_right A A' B
  have : IsNoetherianRing (A' ⊗[A] B) := IsNoetherianRing.of_finite B _
  set I := (maximalIdeal B).map (algebraMap B (A' ⊗[A] B))
  have : IsAdicComplete I (A' ⊗[A] B) := isAdicComplete_map_of_finite (maximalIdeal B)
  have : IsArtinianRing ((A' ⊗[A] B) ⧸ I) := isArtinianRing_quotient_map_maximalIdeal
  obtain ⟨e, he, heP, hQ⟩ := exists_isIdempotentElem_notMem_forall_mem I P
  set S := (A' ⊗[A] B) ⧸ Ideal.span {1 - e}
  have := isLocalization_atPrime_quotient he heP hQ
  have := isLocalRing_quotient he heP hQ
  have hmS : P.map (algebraMap (A' ⊗[A] B) S) = maximalIdeal S :=
    IsLocalization.AtPrime.map_eq_maximalIdeal P S
  have : IsAdicComplete (maximalIdeal S) S := isAdicComplete_maximalIdeal_of_finite (A := B)
  have : IsAdicComplete (maximalIdeal A') A' := isAdicComplete_maximalIdeal_of_finite (A := A)
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  have : IsLocalHom (algebraMap A' S) := ⟨fun a' ha' ↦ by
    by_contra h
    have hmem : algebraMap A' (A' ⊗[A] B) a' ∈ P := map_maximalIdeal_left_le A' P
      (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr h))
    have : algebraMap A' S a' ∈ maximalIdeal S := by
      rw [← hmS, IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) S]
      exact Ideal.mem_map_of_mem _ hmem
    exact (mem_maximalIdeal _).mp this ha'⟩
  have htriv : ∀ s : S, ∃ a' : A', s - algebraMap A' S a' ∈ maximalIdeal S := by
    intro s
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective s
    obtain ⟨a', ha'⟩ := hP x
    refine ⟨a', ?_⟩
    rw [← hmS, IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) S, Ideal.Quotient.algebraMap_eq,
      ← map_sub]
    exact Ideal.mem_map_of_mem _ ha'
  obtain ⟨n, ⟨φ⟩⟩ := ((formallySmooth_tfae htriv).out 3 5).mp (H e he heP hQ htriv)
  exact ⟨n, ⟨((IsLocalization.algEquiv P.primeCompl _ S).restrictScalars A').trans φ⟩⟩

/-- III.2.1, (iii) ⇒ (i), on one local component: under the hypotheses of
`exists_algEquiv_localization_of_artinianLiftingProperty`, if `B' = A' ⊗[A] B` is formally smooth
over `A'` for the `𝔫 B'`-adic topology, the local component `B'_P` is a power series ring over
`A'`. -/
theorem exists_algEquiv_localization_of_adicFormallySmooth
    (h : AdicFormallySmooth A'
      ((maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B)))
    (P : Ideal (A' ⊗[A] B)) [P.IsMaximal]
    (hP : ∀ x : A' ⊗[A] B, ∃ a' : A', x - algebraMap A' (A' ⊗[A] B) a' ∈ P) :
    ∃ n, Nonempty (Localization.AtPrime P ≃ₐ[A'] MvPowerSeries (Fin n) A') := by
  refine exists_algEquiv_localization_of_artinianLiftingProperty A' P hP
    fun e he heP hQ _ _ _ _ _ _ _ ↦ ?_
  have := isLocalization_atPrime_quotient he heP hQ
  refine AdicFormallySmooth.artinianLiftingProperty ((h.quotient_span_one_sub he).mono ?_)
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P ((A' ⊗[A] B) ⧸ Ideal.span {1 - e}),
    Ideal.Quotient.algebraMap_eq]
  exact Ideal.map_mono (map_maximalIdeal_le_of_isMaximal A' P)

end Components

section ResidueTrivial

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The key step of the proof of III.1.6: let `φ : A' → K` be a surjection onto a field with
kernel inside `𝔪 A'`, such that every element of `B` is a root modulo `𝔫` of a monic polynomial
over `A` which splits in `K`. Then at every maximal ideal `P` of `A' ⊗[A] B` (containing
`𝔫 (A' ⊗ B)`), each `1 ⊗ b` is congruent to an element of `A'`: the image of `b` in the residue
field of `P` is a root of a polynomial all of whose roots come from `K`. -/
lemma exists_tmul_sub_mem_of_splits {K : Type*} [Field K] [Algebra A K] (A' : Type u)
    [CommRing A'] [Algebra A A'] (φ : A' →ₐ[A] K) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ ≤ (maximalIdeal A).map (algebraMap A A'))
    (hsplit : ∀ b : B, ∃ p : A[X], p.Monic ∧ aeval b p ∈ maximalIdeal B ∧
      (p.map (algebraMap A K)).Splits)
    (P : Ideal (A' ⊗[A] B)) [P.IsMaximal]
    (hP : (maximalIdeal B).map (algebraMap B (A' ⊗[A] B)) ≤ P) (b : B) :
    ∃ a' : A', (1 : A') ⊗ₜ b - algebraMap A' (A' ⊗[A] B) a' ∈ P := by
  let := Ideal.Quotient.field P
  set ψ : A' ⊗[A] B →ₐ[A] (A' ⊗[A] B) ⧸ P := Ideal.Quotient.mkₐ A P
  have hψB (x : B) (hx : x ∈ maximalIdeal B) : ψ ((1 : A') ⊗ₜ x) = 0 := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hP (Ideal.mem_map_of_mem _ hx)
  let ψA : A' →ₐ[A] (A' ⊗[A] B) ⧸ P := ψ.comp Algebra.TensorProduct.includeLeft
  have hkerA : RingHom.ker φ.toRingHom ≤ RingHom.ker ψA.toRingHom := by
    refine hker.trans (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_)
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, IsScalarTower.algebraMap_apply A B, IsScalarTower.algebraMap_apply B
      (A' ⊗[A] B), Ideal.Quotient.algebraMap_eq, Algebra.TensorProduct.right_algebraMap_apply]
    exact hψB _ ((mem_maximalIdeal _).mpr (map_nonunit _ a ((mem_maximalIdeal _).mp ha)))
  let θ : K →ₐ[A] (A' ⊗[A] B) ⧸ P := AlgHom.liftOfSurjective φ hφ ψA hkerA
  have hθ (a' : A') : θ (φ a') = ψA a' := AlgHom.liftOfSurjective_apply φ hφ ψA hkerA a'
  obtain ⟨p, hmon, hpb, hps⟩ := hsplit b
  have hroot : ((p.map (algebraMap A K)).map (θ : K →+* (A' ⊗[A] B) ⧸ P)).IsRoot
      (ψ ((1 : A') ⊗ₜ b)) := by
    rw [Polynomial.map_map, θ.comp_algebraMap, IsRoot, eval_map_algebraMap,
      show (1 : A') ⊗ₜ[A] b = Algebra.TensorProduct.includeRight b from rfl, aeval_algHom_apply,
      aeval_algHom_apply]
    exact hψB _ hpb
  obtain ⟨κ, hκ⟩ := hps.mem_range_of_isRoot (hmon.map _).ne_zero hroot
  obtain ⟨a', rfl⟩ := hφ κ
  refine ⟨a', ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  change ψ ((1 : A') ⊗ₜ b) = _
  rw [← hκ]
  change θ (φ a') = _
  rw [hθ, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rfl

/-- A finite extension `L/k` embeds into a finite extension `K/k` in which the minimal
polynomials of all elements of `L` split (a normal closure). -/
lemma exists_splits_minpoly (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] : ∃ (K : Type u) (_ : Field K) (_ : Algebra k K),
      FiniteDimensional k K ∧ ∀ x : L, ((minpoly k x).map (algebraMap k K)).Splits := by
  let K := IntermediateField.normalClosure k L (AlgebraicClosure L)
  refine ⟨K, inferInstance, inferInstance, inferInstance, fun x ↦ ?_⟩
  have hx : algebraMap L (AlgebraicClosure L) x ∈ K :=
    AlgHom.fieldRange_le_normalClosure (IsScalarTower.toAlgHom k L (AlgebraicClosure L)) ⟨x, rfl⟩
  have hsp := Normal.splits (inferInstance : Normal k K) ⟨_, hx⟩
  have hmin : minpoly k (⟨_, hx⟩ : K) = minpoly k x := by
    rw [← minpoly.algHom_eq (IsScalarTower.toAlgHom k L (AlgebraicClosure L))
      (algebraMap L _).injective x]
    exact (minpoly.algHom_eq K.val Subtype.val_injective _).symm
  rwa [hmin] at hsp

/-- The finite free local extension used in the proofs of III.1.6, III.1.7 and III.2.1: if the
residue extension `L/k` of `A → B` is finite, there is a finite free local `A`-algebra `A'` such
that all residue extensions of `A' ⊗[A] B` over `A'` are trivial, i.e. `A' → (A' ⊗ B) ⧸ P` is
surjective for every maximal ideal `P`. As in SGA, `A'` lifts a finite extension `k'` of `k` (here
a normal closure of `L/k`) such that the residue fields of `k' ⊗_k L` are `k'`. -/
theorem exists_finite_free_residue_trivial [Module.Finite A (ResidueField B)] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : IsLocalRing A'),
      Module.Free A A' ∧ Module.Finite A A' ∧ ∀ (P : Ideal (A' ⊗[A] B)), P.IsMaximal →
        ∀ x : A' ⊗[A] B, ∃ a' : A', x - algebraMap A' (A' ⊗[A] B) a' ∈ P := by
  set k := ResidueField A
  set L := ResidueField B
  have : FiniteDimensional k L := Module.Finite.of_restrictScalars_finite A k L
  obtain ⟨K, _, _, _, hKs⟩ := exists_splits_minpoly k L
  let : Algebra A K := ((algebraMap k K).comp (algebraMap A k)).toAlgebra
  have : IsScalarTower A k K := IsScalarTower.of_algebraMap_eq' rfl
  have hK : RingHom.ker (algebraMap A K) = maximalIdeal A := by
    rw [IsScalarTower.algebraMap_eq A k K, RingHom.ker_comp_of_injective _
      (algebraMap k K).injective, ResidueField.algebraMap_eq, ker_residue]
  have : Module.Finite A K := Module.Finite.trans k K
  obtain ⟨A', _, _, _, hfree, hfin, φ, hφ, hkerφ⟩ := exists_finite_free_residue_lift A K hK
  have hsplit : ∀ b : B, ∃ p : A[X], p.Monic ∧ aeval b p ∈ maximalIdeal B ∧
      (p.map (algebraMap A K)).Splits := by
    intro b
    set x : L := residue B b
    have hint : IsIntegral k x := Algebra.IsIntegral.isIntegral x
    obtain ⟨p, hpmap, -, hp⟩ := lifts_and_natDegree_eq_and_monic
      (map_surjective (residue A) residue_surjective (minpoly k x)) (minpoly.monic hint)
    refine ⟨p, hp, ?_, ?_⟩
    · rw [← residue_eq_zero_iff]
      have : residue B (aeval b p) = aeval x p :=
        (aeval_algHom_apply (IsScalarTower.toAlgHom A B L) b p).symm
      rw [this, ← aeval_map_algebraMap k, ResidueField.algebraMap_eq, hpmap, minpoly.aeval]
    · rw [IsScalarTower.algebraMap_eq A k K, ← Polynomial.map_map, ResidueField.algebraMap_eq,
        hpmap]
      exact hKs x
  exact ⟨A', inferInstance, inferInstance, inferInstance, hfree, hfin, fun P hP x ↦
    exists_sub_mem_of_forall_tmul A' P (fun b ↦
      exists_tmul_sub_mem_of_splits A' φ hφ hkerφ.le hsplit P
        (map_maximalIdeal_le_of_isMaximal A' P) b) x⟩

end ResidueTrivial

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section LocalComponent

variable (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalRing A'] [Module.Finite A A']
  (P : Ideal (A' ⊗[A] B)) [P.IsMaximal]

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] [IsLocalRing A'] in
/-- The local components `(A' ⊗[A] B)_P` of `A' ⊗ B` are complete local rings (for `B` complete
and `A'` finite over `A`): they are quotients of the complete ring `A' ⊗ B` by idempotents. -/
theorem isAdicComplete_maximalIdeal_localization :
    IsAdicComplete (maximalIdeal (Localization.AtPrime P)) (Localization.AtPrime P) := by
  have := finite_tensorProduct_right A A' B
  set I := (maximalIdeal B).map (algebraMap B (A' ⊗[A] B))
  have : IsAdicComplete I (A' ⊗[A] B) := isAdicComplete_map_of_finite (maximalIdeal B)
  have : IsArtinianRing ((A' ⊗[A] B) ⧸ I) := isArtinianRing_quotient_map_maximalIdeal
  obtain ⟨e, he, heP, hQ⟩ := exists_isIdempotentElem_notMem_forall_mem I P
  set S := (A' ⊗[A] B) ⧸ Ideal.span {1 - e}
  have := isLocalization_atPrime_quotient he heP hQ
  have := isLocalRing_quotient he heP hQ
  have hS : IsAdicComplete (maximalIdeal S) S := isAdicComplete_maximalIdeal_of_finite (A := B)
  let φ := (IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)).toRingEquiv
  have hmax : (maximalIdeal S).map φ = maximalIdeal (Localization.AtPrime P) := by
    rw [← Ideal.comap_symm]
    exact IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective)
  rw [← hmax]
  exact (IsAdicComplete.congr_ringEquiv _ φ).mpr hS

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] [IsLocalRing A'] in
/-- Formal smoothness of `A' ⊗ B` over `A'` (for the `𝔫`-adic topology) passes to the local
components, for their maximal-adic topologies. -/
theorem adicFormallySmooth_maximalIdeal_localization
    (h : AdicFormallySmooth A'
      ((maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B))) :
    AdicFormallySmooth A' (maximalIdeal (Localization.AtPrime P)) := by
  have := finite_tensorProduct_right A A' B
  set I := (maximalIdeal B).map (algebraMap B (A' ⊗[A] B))
  have : IsAdicComplete I (A' ⊗[A] B) := isAdicComplete_map_of_finite (maximalIdeal B)
  have : IsArtinianRing ((A' ⊗[A] B) ⧸ I) := isArtinianRing_quotient_map_maximalIdeal
  obtain ⟨e, he, heP, hQ⟩ := exists_isIdempotentElem_notMem_forall_mem I P
  set S := (A' ⊗[A] B) ⧸ Ideal.span {1 - e}
  have := isLocalization_atPrime_quotient he heP hQ
  have := isLocalRing_quotient he heP hQ
  have h₂ : AdicFormallySmooth A' (maximalIdeal S) := by
    refine (h.quotient_span_one_sub he).mono ?_
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P S, Ideal.Quotient.algebraMap_eq]
    exact Ideal.map_mono (map_maximalIdeal_le_of_isMaximal A' P)
  let φ : Localization.AtPrime P ≃ₐ[A'] S :=
    ((IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)).restrictScalars A').symm
  have := h₂.of_algEquiv φ
  rwa [IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ φ.surjective)] at this

omit [IsNoetherianRing B] [IsAdicComplete (maximalIdeal B) B] in
/-- The local components of `A' ⊗ B` are local over `A'`. -/
theorem isLocalHom_algebraMap_localization :
    IsLocalHom (algebraMap A' (Localization.AtPrime P)) :=
  ⟨fun a' ha' ↦ by
    by_contra h
    have hmem : algebraMap A' (A' ⊗[A] B) a' ∈ P := map_maximalIdeal_left_le A' P
      (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr h))
    have : algebraMap A' (Localization.AtPrime P) a' ∈ maximalIdeal _ := by
      rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P),
        IsScalarTower.algebraMap_apply A' (A' ⊗[A] B)]
      exact Ideal.mem_map_of_mem _ hmem
    exact (mem_maximalIdeal _).mp this ha'⟩

omit [IsLocalRing A] [IsLocalHom (algebraMap A B)] [IsLocalRing A'] [IsNoetherianRing B]
  [IsAdicComplete (maximalIdeal B) B] in
/-- The residue extensions of the local components of `A' ⊗ B` over `A'` are finite when that of
`B` over `A` is. -/
theorem finite_residueField_localization [Module.Finite A (ResidueField B)] :
    Module.Finite A' (ResidueField (Localization.AtPrime P)) := by
  set I := (maximalIdeal B).map (Algebra.TensorProduct.includeRight : B →ₐ[A] A' ⊗[A] B)
  have : Module.Finite A (B ⧸ maximalIdeal B) := ‹Module.Finite A (ResidueField B)›
  have : Module.Finite A ((A' ⊗[A] B) ⧸ I) := Module.Finite.equiv
    (Algebra.TensorProduct.tensorQuotientEquiv (R := A) A B A' (maximalIdeal B)).toLinearEquiv
  let r : A' ⊗[A] B →ₐ[A] ResidueField (Localization.AtPrime P) :=
    IsScalarTower.toAlgHom A _ _
  have hr (x : A' ⊗[A] B) : r x = residue _ (algebraMap _ (Localization.AtPrime P) x) := rfl
  have hrs : Function.Surjective r := by
    intro y
    obtain ⟨z, rfl⟩ :=
      (IsLocalization.AtPrime.equivQuotMaximalIdeal P (Localization.AtPrime P)).surjective y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨x, rfl⟩
  have hI : I ≤ RingHom.ker r := by
    intro x hx
    rw [RingHom.mem_ker, hr, residue_eq_zero_iff,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal P (Localization.AtPrime P)]
    exact Ideal.mem_map_of_mem _ (map_maximalIdeal_le_of_isMaximal A' P hx)
  let r' : ((A' ⊗[A] B) ⧸ I) →ₐ[A] ResidueField (Localization.AtPrime P) :=
    Ideal.Quotient.liftₐ I r hI
  have hr' : Function.Surjective r' := by
    intro y
    obtain ⟨x, rfl⟩ := hrs y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  have : Module.Finite A (ResidueField (Localization.AtPrime P)) :=
    Module.Finite.of_surjective r'.toLinearMap hr'
  exact Module.Finite.of_restrictScalars_finite A A' _

end LocalComponent

omit [IsLocalHom (algebraMap A B)] in
/-- III.2.1, (i) ⇒ (iii), for an arbitrary residue extension: if `B` is formally smooth over `A`
in the sense of Definition III.1.1 (`B` complete noetherian), then `B` is formally smooth for its
`𝔫`-adic topology. The local components of `A' ⊗ B` are power series rings, hence formally smooth
over `A'`; so is `A' ⊗ B`, the product of its local components
(`AdicFormallySmooth.of_localization`); and formal smoothness descends to `B`
(`AdicFormallySmooth.of_baseChange_of_free`, III.1.4 (ii)). -/
theorem adicFormallySmooth_of_formallySmoothLocal' (h : FormallySmoothLocal A B) :
    AdicFormallySmooth A (maximalIdeal B) := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := h
  have := finite_tensorProduct_right A A' B
  set I := (maximalIdeal B).map (algebraMap B (A' ⊗[A] B))
  have : IsAdicComplete I (A' ⊗[A] B) := isAdicComplete_map_of_finite (maximalIdeal B)
  have : IsArtinianRing ((A' ⊗[A] B) ⧸ I) := isArtinianRing_quotient_map_maximalIdeal
  have h' : AdicFormallySmooth A' I := AdicFormallySmooth.of_localization fun P _ ↦ by
    obtain ⟨n, ⟨e⟩⟩ := hA' P
    exact adicFormallySmooth_of_algEquiv_mvPowerSeries e
  exact AdicFormallySmooth.of_baseChange_of_free A' (I := maximalIdeal B) h'

variable [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A]

/-- III.2.1, (iii) ⇒ (i), for a finite residue extension: if `B` is formally smooth over `A` for
its `𝔫`-adic topology (`A`, `B` complete noetherian, `L/k` finite), then it is formally smooth in
the sense of Definition III.1.1. As in SGA (proof of III.2.1 (iv) ⇒ (i) and of III.1.6), one takes
`A'` finite free local making the residue extensions of `A' ⊗ B` trivial
(`exists_finite_free_residue_trivial`); the local components of `A' ⊗ B` are then formally smooth
over `A'` with trivial residue extension, hence power series rings (III.1.5). -/
theorem formallySmoothLocal_of_adicFormallySmooth' [Module.Finite A (ResidueField B)]
    (h : AdicFormallySmooth A (maximalIdeal B)) : FormallySmoothLocal A B := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := exists_finite_free_residue_trivial (A := A) (B := B)
  exact ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun P _ ↦ exists_algEquiv_localization_of_adicFormallySmooth A' (h.baseChange A') P
      (hA' P ‹_›)⟩

/-- III.2.1, (i) ⇔ (iii): a local homomorphism of complete noetherian local rings with finite
residue extension is formally smooth (Definition III.1.1) if and only if it has the lifting
property for continuous maps into nilpotent thickenings. -/
theorem formallySmoothLocal_iff_adicFormallySmooth' [Module.Finite A (ResidueField B)] :
    FormallySmoothLocal A B ↔ AdicFormallySmooth A (maximalIdeal B) :=
  ⟨adicFormallySmooth_of_formallySmoothLocal', formallySmoothLocal_of_adicFormallySmooth'⟩

/-- III.1.4 (i), in the form of Definition III.1.1: let `A → B` be a local homomorphism of complete
noetherian local rings with finite residue extension, and `A'` a finite local `A`-algebra. If `B`
is formally smooth over `A`, the localizations of `A' ⊗[A] B` at its maximal ideals (its local
components) are formally smooth over `A'`. -/
theorem FormallySmoothLocal.localization [Module.Finite A (ResidueField B)]
    (h : FormallySmoothLocal A B) (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalRing A']
    [Module.Finite A A'] (P : Ideal (A' ⊗[A] B)) [P.IsMaximal] :
    FormallySmoothLocal A' (Localization.AtPrime P) := by
  have := isAdicComplete_maximalIdeal_localization A' P
  have := isLocalHom_algebraMap_localization A' P
  have := finite_residueField_localization A' P
  have := finite_tensorProduct_right A A' B
  have : IsNoetherianRing (A' ⊗[A] B) := IsNoetherianRing.of_finite B _
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have : IsAdicComplete (maximalIdeal A') A' := isAdicComplete_maximalIdeal_of_finite (A := A)
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  exact formallySmoothLocal_of_adicFormallySmooth' (adicFormallySmooth_maximalIdeal_localization
    A' P ((adicFormallySmooth_of_formallySmoothLocal' h).baseChange A'))

/-- III.1.4 (ii), in the form of Definition III.1.1: let `A → B` be a local homomorphism of
complete noetherian local rings with finite residue extension, and `A'` a finite free local
`A`-algebra. If the local components of `A' ⊗[A] B` are formally smooth over `A'`, then `B` is
formally smooth over `A`. -/
theorem formallySmoothLocal_of_localization [Module.Finite A (ResidueField B)] (A' : Type u)
    [CommRing A'] [Algebra A A'] [IsLocalRing A'] [Module.Free A A'] [Module.Finite A A']
    (h : ∀ (P : Ideal (A' ⊗[A] B)) [P.IsMaximal], FormallySmoothLocal A' (Localization.AtPrime P)) :
    FormallySmoothLocal A B := by
  refine formallySmoothLocal_of_adicFormallySmooth'
    (AdicFormallySmooth.of_baseChange_of_free A' (I := maximalIdeal B) ?_)
  have := finite_tensorProduct_right A A' B
  have : IsNoetherianRing (A' ⊗[A] B) := IsNoetherianRing.of_finite B _
  set I := (maximalIdeal B).map (algebraMap B (A' ⊗[A] B))
  have : IsAdicComplete I (A' ⊗[A] B) := isAdicComplete_map_of_finite (maximalIdeal B)
  have : IsArtinianRing ((A' ⊗[A] B) ⧸ I) := isArtinianRing_quotient_map_maximalIdeal
  change AdicFormallySmooth A' I
  exact AdicFormallySmooth.of_localization fun P _ ↦ by
    have := isAdicComplete_maximalIdeal_localization A' P
    have : IsNoetherianRing (Localization.AtPrime P) :=
      IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
    exact adicFormallySmooth_of_formallySmoothLocal' (h P)

/-- III.1.6: if `B` is formally smooth over `A` (Definition III.1.1), then for every finite local
`A`-algebra `A'` such that the residue extensions of `A' ⊗[A] B` over `A'` are trivial, the local
components of `A' ⊗[A] B` are power series rings over `A'`. (SGA states it for `A'` finite over the
possibly non-complete `A`, with `Â ⊗ A'`; here `A`, `B` are complete.) -/
theorem exists_algEquiv_mvPowerSeries_of_formallySmoothLocal (h : FormallySmoothLocal A B)
    (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalRing A'] [Module.Finite A A']
    (hA' : ∀ P : Ideal (A' ⊗[A] B), P.IsMaximal →
      ∀ x : A' ⊗[A] B, ∃ a' : A', x - algebraMap A' (A' ⊗[A] B) a' ∈ P)
    (P : Ideal (A' ⊗[A] B)) [P.IsMaximal] :
    ∃ n, Nonempty (Localization.AtPrime P ≃ₐ[A'] MvPowerSeries (Fin n) A') :=
  exists_algEquiv_localization_of_adicFormallySmooth A'
    ((adicFormallySmooth_of_formallySmoothLocal' h).baseChange A') P (hA' P ‹_›)

/-- III.1.6, with the existence of `A'`: if `B` is formally smooth over `A` with finite residue
extension, there is a finite free local `A`-algebra `A'` making the residue extensions of
`A' ⊗[A] B` trivial, and for any such `A'` the local components of `A' ⊗ B` are power series
rings over `A'`. -/
theorem exists_residue_trivial_of_formallySmoothLocal [Module.Finite A (ResidueField B)]
    (h : FormallySmoothLocal A B) :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : IsLocalRing A'),
      Module.Free A A' ∧ Module.Finite A A' ∧
      (∀ P : Ideal (A' ⊗[A] B), P.IsMaximal →
        ∀ x : A' ⊗[A] B, ∃ a' : A', x - algebraMap A' (A' ⊗[A] B) a' ∈ P) ∧
      ∀ (P : Ideal (A' ⊗[A] B)) [P.IsMaximal],
        ∃ n, Nonempty (Localization.AtPrime P ≃ₐ[A'] MvPowerSeries (Fin n) A') := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := exists_finite_free_residue_trivial (A := A) (B := B)
  exact ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hA',
    fun P _ ↦ exists_algEquiv_mvPowerSeries_of_formallySmoothLocal h A' hA' P⟩

end Main

end SGA.SGA1.ExposeIII
