/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.HenselianFinite

/-!
# Maps from finite étale algebras to finite algebras over a strictly henselian ring

Let `A` be a strictly henselian local ring with residue field `k`, `B` a finite étale
`A`-algebra and `T` a finite `A`-algebra (not necessarily flat). Then the `A`-algebra maps
`B → T` are the `A`-algebra maps `B → k ⊗_A T`
(`IsStrictlyHenselian.bijective_comp_includeRight_of_finite`; Stacks 04GG, EGA IV 18.5.11). The
finite free case over a henselian ring is `HenselianLocalRing.bijective_comp_includeRight`.

Since `B ≅ A^n` (`IsStrictlyHenselian.exists_algEquiv_pi`), the maps `B → T` are the complete
families of `n` orthogonal idempotents of `T` (`CompleteOrthogonalIdempotents.piAlgHom`), and these
lift uniquely from `k ⊗_A T` to `T` (`HenselianLocalRing.exists_isIdempotentElem_lift_of_finite`;
idempotents in the Jacobson radical vanish).
-/

open IsLocalRing TensorProduct

universe u

namespace CompleteOrthogonalIdempotents

variable {R T ι : Type*} [CommRing R] [CommRing T] [Algebra R T] [Fintype ι] [DecidableEq ι]
  {e : ι → T} (he : CompleteOrthogonalIdempotents e)

/-- The `R`-algebra map `(ι → R) → T` sending the `i`-th standard idempotent to `e i`, for a
complete family `e` of orthogonal idempotents of `T`. -/
noncomputable def piAlgHom : (ι → R) →ₐ[R] T where
  toFun v := ∑ i, algebraMap R T (v i) * e i
  map_one' := by simp [he.complete]
  map_mul' v w := by
    simp only [Pi.mul_apply, map_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i]
    · rw [mul_mul_mul_comm, (he.idem i).eq]
    · intro j _ hji
      rw [mul_mul_mul_comm, he.ortho (Ne.symm hji), mul_zero]
    · simp
  map_zero' := by simp
  map_add' v w := by simp [add_mul, Finset.sum_add_distrib]
  commutes' r := by simp [← Finset.mul_sum, he.complete]

omit [DecidableEq ι] in
lemma piAlgHom_apply (v : ι → R) : he.piAlgHom v = ∑ i, algebraMap R T (v i) * e i := rfl

lemma piAlgHom_single (i : ι) : he.piAlgHom (Pi.single i (1 : R)) = e i := by
  rw [piAlgHom_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [hji]
  · simp

end CompleteOrthogonalIdempotents

/-- Two `R`-algebra maps out of `ι → R` which agree on the standard idempotents are equal. -/
lemma AlgHom.pi_ext {R T ι : Type*} [CommRing R] [Semiring T] [Algebra R T]
    [_root_.Finite ι] [DecidableEq ι] {f g : (ι → R) →ₐ[R] T}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  have : f.toLinearMap = g.toLinearMap := by
    refine LinearMap.pi_ext fun i r ↦ ?_
    have hr : (Pi.single i r : ι → R) = r • Pi.single i 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    simp only [AlgHom.toLinearMap_apply, hr, map_smul, h i]
  exact AlgHom.toLinearMap_injective this

namespace IsStrictlyHenselian

variable {A : Type u} [CommRing A] [IsStrictlyHenselian A]

set_option backward.isDefEq.respectTransparency false in
/-- Over a strictly henselian local ring `A` with residue field `k`, for `B` finite étale and `T`
finite over `A`, every `A`-algebra map `B → k ⊗_A T` lifts uniquely to an `A`-algebra map
`B → T` (Stacks 04GG; EGA IV 18.5.11). -/
theorem bijective_comp_includeRight_of_finite (B : Type u) [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] (T : Type*) [CommRing T] [Algebra A T]
    [Module.Finite A T] :
    Function.Bijective fun f : B →ₐ[A] T ↦
      (Algebra.TensorProduct.includeRight : T →ₐ[A] (A ⧸ maximalIdeal A) ⊗[A] T).comp f := by
  classical
  let π : T →ₐ[A] (A ⧸ maximalIdeal A) ⊗[A] T := Algebra.TensorProduct.includeRight
  -- the kernel of the reduction lies in the Jacobson radical
  have hker (t : T) (ht : π t = 0) : t ∈ (maximalIdeal A).map (algebraMap A T) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal A)).injective
    rw [map_zero]
    exact ht
  have hjac := IsLocalRing.map_maximalIdeal_le_jacobson (A := A) (C := T)
  have hidem0 {t : T} (ht : IsIdempotentElem t) (h0 : π t = 0) : t = 0 :=
    ht.eq_zero_of_mem_jacobson (hjac (hker t h0))
  refine ⟨fun f₁ f₂ h ↦ ?_, fun ψ ↦ ?_⟩
  · refine Algebra.FormallyUnramified.algHom_ext_of_sub_mem_jacobson hjac fun b ↦ hker _ ?_
    rw [map_sub, sub_eq_zero]
    exact DFunLike.congr_fun h b
  · obtain ⟨n, ⟨ε⟩⟩ := exists_algEquiv_pi A B
    let ψ' : (Fin n → A) →ₐ[A] (A ⧸ maximalIdeal A) ⊗[A] T := ψ.comp ε.symm.toAlgHom
    let ē : Fin n → (A ⧸ maximalIdeal A) ⊗[A] T := fun i ↦ ψ' (Pi.single i 1)
    have hē : CompleteOrthogonalIdempotents ē :=
      (CompleteOrthogonalIdempotents.single (fun _ : Fin n ↦ A)).map ψ'.toRingHom
    -- lift the idempotents
    have hlift (i : Fin n) : ∃ t : T, IsIdempotentElem t ∧ π t = ē i :=
      HenselianLocalRing.exists_isIdempotentElem_lift_of_finite (A := A) (B := T) (hē.idem i)
    choose e he hπe using hlift
    have hortho : OrthogonalIdempotents e := by
      refine ⟨he, fun i j hij ↦ hidem0 ((he i).mul (he j)) ?_⟩
      rw [map_mul, hπe, hπe]
      exact hē.ortho hij
    have hcompl : CompleteOrthogonalIdempotents e := by
      refine ⟨hortho, ?_⟩
      have hsum : IsIdempotentElem (∑ i, e i) := hortho.isIdempotentElem_sum
      have h1 : 1 - ∑ i, e i = 0 := hidem0 hsum.one_sub (by
        rw [map_sub, map_one, map_sum]
        simp only [hπe]
        rw [hē.complete, sub_self])
      exact (sub_eq_zero.mp h1).symm
    refine ⟨(hcompl.piAlgHom (R := A)).comp ε.toAlgHom, ?_⟩
    have hψ : π.comp (hcompl.piAlgHom (R := A)) = ψ' :=
      AlgHom.pi_ext fun i ↦ by
        rw [AlgHom.comp_apply, CompleteOrthogonalIdempotents.piAlgHom_single, hπe]
    refine AlgHom.ext fun b ↦ ?_
    have := DFunLike.congr_fun hψ (ε b)
    simpa [ψ', π] using this

end IsStrictlyHenselian
