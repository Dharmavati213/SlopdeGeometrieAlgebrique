/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Lifting étale algebras along surjections

Let `A` be a ring and `I` an ideal. Every étale `A ⧸ I`-algebra `B₀` is the reduction
`(A ⧸ I) ⊗[A] C` of an étale `A`-algebra `C`; for nilpotent `I` this is the affine case of
the lifting of étale schemes along nilpotent thickenings (EGA IV, §18.1; SGA 1 I.8.1). We lift
a submersive presentation `B₀ = A₀[x₁, …, xₙ]/(f₁, …, fₙ)`
(`Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero`) to
`B = A[x₁, …, xₙ]/(F₁, …, Fₙ)` and invert the Jacobian determinant of the `Fᵢ`, which is a unit
modulo `I`.

No finiteness is claimed: `C` is in general not finite over `A` even if `B₀` is finite over
`A ⧸ I`. When `A` is `I`-adically complete and noetherian, completing `C` along `I` produces a
finite étale lift (`SGA.Foundations.Formal.FiniteEtale`).

## Main results

* `Algebra.tensorQuotientEquivOfSurjective`: `(A ⧸ I) ⊗[A] C ≅ B₀` for a surjection `C → B₀`
  with kernel `I C`.
* `Algebra.Etale.exists_etale_tensorQuotient_equiv`: étale algebras lift along `A → A ⧸ I`.
-/

universe u

open TensorProduct

namespace Algebra

section Surjective

variable {R : Type u} [CommRing R] {S : Type*} [CommRing S] [Algebra R S]
  (hS : Function.Surjective (algebraMap R S))

/-- For `R → S` surjective, `R ⧸ ker ≅ S` as `R`-algebras. -/
noncomputable def quotientKerAlgEquivOfSurjective :
    (R ⧸ RingHom.ker (algebraMap R S)) ≃ₐ[R] S :=
  AlgEquiv.ofRingEquiv (f := RingHom.quotientKerEquivOfSurjective hS) fun _ ↦ rfl

/-- For `R → S` surjective with kernel `K`, `S ⊗[R] C ≅ C ⧸ K C`, as `R`-algebras. -/
noncomputable def tensorEquivQuotientOfSurjective (C : Type*) [CommRing C] [Algebra R C] :
    S ⊗[R] C ≃ₐ[R] C ⧸ (RingHom.ker (algebraMap R S)).map (algebraMap R C) :=
  (Algebra.TensorProduct.congr (quotientKerAlgEquivOfSurjective hS).symm AlgEquiv.refl).trans
    ((Algebra.TensorProduct.comm R _ C).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C
        (RingHom.ker (algebraMap R S))).restrictScalars R).symm)

lemma tensorEquivQuotientOfSurjective_one_tmul {C : Type*} [CommRing C] [Algebra R C] (c : C) :
    tensorEquivQuotientOfSurjective hS C (1 ⊗ₜ c) = Ideal.Quotient.mk _ c := by
  simp only [tensorEquivQuotientOfSurjective, AlgEquiv.trans_apply,
    Algebra.TensorProduct.congr_apply, map_one, AlgEquiv.refl_toAlgHom, AlgHom.coe_id, id_eq,
    Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
  rw [AlgEquiv.symm_apply_eq]
  rfl

/-- Let `R → S` be surjective with kernel `K`, `C` an `R`-algebra and `φ : C → B₀` a surjective
ring map to an `S`-algebra, compatible with the structure maps, with kernel `K C`. Then
`S ⊗[R] C ≅ B₀`. -/
noncomputable def tensorEquivOfSurjective {C B₀ : Type*} [CommRing C] [Algebra R C]
    [CommRing B₀] [Algebra S B₀] (φ : C →+* B₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = (RingHom.ker (algebraMap R S)).map (algebraMap R C))
    (hcomp : ∀ a, φ (algebraMap R C a) = algebraMap S B₀ (algebraMap R S a)) :
    S ⊗[R] C ≃ₐ[S] B₀ := by
  let e₁ := tensorEquivQuotientOfSurjective hS C
  let e : S ⊗[R] C ≃+* B₀ :=
    e₁.toRingEquiv.trans ((Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hφ))
  refine AlgEquiv.ofRingEquiv (f := e) fun x ↦ ?_
  obtain ⟨a, rfl⟩ := hS x
  have h1 : e₁ (algebraMap R S a ⊗ₜ[R] (1 : C)) = Ideal.Quotient.mk _ (algebraMap R C a) := by
    have : (algebraMap R S a ⊗ₜ[R] (1 : C) : S ⊗[R] C) = algebraMap R (S ⊗[R] C) a := rfl
    rw [this, e₁.commutes]
    rfl
  change e (algebraMap R S a ⊗ₜ[R] (1 : C)) = _
  simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, h1, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  exact hcomp a

end Surjective

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- Let `C` be an `A`-algebra and `φ : C → B₀` a surjective ring map to an `A ⧸ I`-algebra,
compatible with the structure maps, whose kernel is `I C`. Then `(A ⧸ I) ⊗[A] C ≅ B₀`. -/
noncomputable def tensorQuotientEquivOfSurjective {C B₀ : Type*} [CommRing C] [Algebra A C]
    [CommRing B₀] [Algebra (A ⧸ I) B₀] (φ : C →+* B₀) (hφ : Function.Surjective φ)
    (hker : RingHom.ker φ = I.map (algebraMap A C))
    (hcomp : ∀ a, φ (algebraMap A C a) = algebraMap (A ⧸ I) B₀ (Ideal.Quotient.mk I a)) :
    (A ⧸ I) ⊗[A] C ≃ₐ[A ⧸ I] B₀ := by
  let e₁ : (A ⧸ I) ⊗[A] C ≃ₐ[A] C ⧸ I.map (algebraMap A C) :=
    ((Algebra.TensorProduct.comm A (A ⧸ I) C).trans
      ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).restrictScalars A).symm)
  let e : (A ⧸ I) ⊗[A] C ≃+* B₀ :=
    e₁.toRingEquiv.trans ((Ideal.quotEquivOfEq hker.symm).trans
      (RingHom.quotientKerEquivOfSurjective hφ))
  refine AlgEquiv.ofRingEquiv (f := e) fun x ↦ ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have h1 : e₁ (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : C)) =
      Ideal.Quotient.mk _ (algebraMap A C a) := by
    have : (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : C) : (A ⧸ I) ⊗[A] C) =
        algebraMap A ((A ⧸ I) ⊗[A] C) a := rfl
    rw [this, e₁.commutes]
    rfl
  change e (Ideal.Quotient.mk I a ⊗ₜ[A] (1 : C)) = _
  simp only [e, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, h1, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]
  exact hcomp a


/-- Étale algebras lift along surjections (for nilpotent kernel, EGA IV, §18.1): if `A → S` is
surjective, every étale `S`-algebra `B₀` is `S ⊗[A] C` for an étale `A`-algebra `C`. One lifts a
submersive presentation `B₀ = S[x]/(f)` to `B = A[x]/(F)` and inverts the Jacobian of `F`. -/
theorem Etale.exists_etale_tensor_equiv {S : Type*} [CommRing S] [Algebra A S]
    (hS : Function.Surjective (algebraMap A S)) (B₀ : Type u) [CommRing B₀]
    [Algebra S B₀] [Algebra.Etale S B₀] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), Algebra.Etale A C ∧
      Nonempty (S ⊗[A] C ≃ₐ[S] B₀) := by
  classical
  obtain ⟨ι, σ, _, _, P₀, hP₀⟩ :=
    (Algebra.Etale.iff_isStandardSmoothOfRelativeDimension_zero.mp ‹_›).out
  let π : A →+* S := algebraMap A S
  have hπ : Function.Surjective (MvPolynomial.map π : MvPolynomial ι A → _) :=
    MvPolynomial.map_surjective π hS
  let rel : σ → MvPolynomial ι A := fun j ↦ Function.surjInv hπ (P₀.relation j)
  have hrel (j : σ) : MvPolynomial.map π (rel j) = P₀.relation j := Function.surjInv_eq hπ _
  let J : Ideal (MvPolynomial ι A) := Ideal.span (Set.range rel)
  let B := MvPolynomial ι A ⧸ J
  let P := PreSubmersivePresentation.naive (v := rel) P₀.map P₀.map_inj
  -- the comparison map `B → B₀`
  let ψ : MvPolynomial ι A →+* B₀ :=
    (MvPolynomial.aeval P₀.val).toRingHom.comp (MvPolynomial.map π)
  have hψ : J ≤ RingHom.ker ψ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    simp [ψ, hrel]
  let φ : B →+* B₀ := Ideal.Quotient.lift J ψ hψ
  have hφ (p : MvPolynomial ι A) : φ (Ideal.Quotient.mk J p) = ψ p := rfl
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨p₀, rfl⟩ := P₀.aeval_val_surjective y
    obtain ⟨p, rfl⟩ := hπ p₀
    exact ⟨Ideal.Quotient.mk J p, rfl⟩
  have hφa (a : A) : φ (algebraMap A B a) = algebraMap S B₀ (π a) := by
    change φ (Ideal.Quotient.mk J (MvPolynomial.C a)) = _
    rw [hφ]
    simp [ψ, π]
  -- the kernel of `B → B₀` is `I B`
  have hker : RingHom.ker φ = (RingHom.ker π).map (algebraMap A B) := by
    refine le_antisymm (fun b hb ↦ ?_) ?_
    · obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [RingHom.mem_ker, hφ] at hb
      have h1 : MvPolynomial.map π p ∈ J.map (MvPolynomial.map π) := by
        rw [Ideal.map_span, ← Set.range_comp]
        have : (MvPolynomial.map π ∘ rel) = P₀.relation := funext hrel
        rw [this, P₀.span_range_relation_eq_ker, P₀.ker_eq_ker_aeval_val]
        exact hb
      obtain ⟨q, hq, hpq⟩ := (Ideal.mem_map_iff_of_surjective _ hπ).mp h1
      have h2 : p - q ∈ Ideal.map (MvPolynomial.C : A →+* MvPolynomial ι A) (RingHom.ker π) := by
        rw [← MvPolynomial.ker_map, RingHom.mem_ker, map_sub, hpq, sub_self]
      have : Ideal.Quotient.mk J p = Ideal.Quotient.mk J (p - q) := by
        rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr hq, sub_zero]
      rw [this]
      have h3 := Ideal.mem_map_of_mem (Ideal.Quotient.mk J) h2
      rwa [Ideal.map_map] at h3
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hφa, RingHom.mem_ker.mp ha, map_zero]
  -- the Jacobian of the lifted presentation maps to that of `P₀`
  have := Fintype.ofFinite σ
  have hjac : φ P.jacobian = P₀.jacobian := by
    rw [P.jacobian_eq_jacobiMatrix_det, P₀.jacobian_eq_jacobiMatrix_det,
      Generators.algebraMap_apply P₀.toGenerators]
    change φ (Ideal.Quotient.mk J _) = _
    rw [hφ]
    simp only [ψ, RingHom.map_det]
    rw [← AlgHom.coe_toRingHom, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, RingHom.coe_comp, Function.comp_apply,
      PreSubmersivePresentation.jacobiMatrix_apply]
    rw [← MvPolynomial.pderiv_map]
    change MvPolynomial.aeval P₀.val
      (MvPolynomial.pderiv (P₀.map i) (MvPolynomial.map π (rel j))) = _
    rw [hrel]
    rfl
  have hunit : IsUnit (φ P.jacobian) := hjac ▸ P₀.jacobian_isUnit
  -- invert the Jacobian
  let C := Localization.Away P.jacobian
  let Q := (PreSubmersivePresentation.localizationAway C P.jacobian).comp P
  have hQ : IsUnit Q.jacobian := by
    rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def,
      PreSubmersivePresentation.localizationAway_jacobian, IsUnit.mul_iff, and_self]
    exact IsLocalization.map_units C (⟨P.jacobian, 1, by simp⟩ : Submonoid.powers P.jacobian)
  let Q' : SubmersivePresentation A C (Unit ⊕ ι) (Unit ⊕ σ) := ⟨Q, hQ⟩
  have : IsStandardSmoothOfRelativeDimension 0 A C := by
    refine Q'.isStandardSmoothOfRelativeDimension ?_
    change Q.dimension = 0
    rw [PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, ← hP₀]
    simp [Presentation.dimension]
  refine ⟨C, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  -- the reduction of `C` is still `B₀`
  let φ' : C →+* B₀ := IsLocalization.Away.lift P.jacobian hunit
  have hφ' (b : B) : φ' (algebraMap B C b) = φ b := IsLocalization.Away.lift_eq _ _ b
  refine tensorEquivOfSurjective hS φ' ?_ ?_ ?_
  · intro y
    obtain ⟨b, rfl⟩ := hφsurj y
    exact ⟨algebraMap B C b, hφ' b⟩
  · refine le_antisymm (fun c hc ↦ ?_) ?_
    · obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers P.jacobian) c
      have hb : b ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, ← hφ', ← IsLocalization.mk'_spec C b s, map_mul,
          RingHom.mem_ker.mp hc, zero_mul]
      rw [hker] at hb
      change IsLocalization.mk' C b s ∈ _
      rw [IsLocalization.mk'_eq_mul_mk'_one]
      refine Ideal.mul_mem_right _ _ ?_
      have := Ideal.mem_map_of_mem (algebraMap B C) hb
      rwa [Ideal.map_map, ← IsScalarTower.algebraMap_eq] at this
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, IsScalarTower.algebraMap_apply A B C, hφ', hφa,
        RingHom.mem_ker.mp ha, map_zero]
  · intro a
    rw [IsScalarTower.algebraMap_apply A B C, hφ', hφa]

/-- Étale algebras lift along `A → A ⧸ I` (for nilpotent `I`, EGA IV, §18.1): every étale
`A ⧸ I`-algebra `B₀` is `(A ⧸ I) ⊗[A] C` for an étale `A`-algebra `C`. -/
theorem Etale.exists_etale_tensorQuotient_equiv (B₀ : Type u) [CommRing B₀]
    [Algebra (A ⧸ I) B₀] [Algebra.Etale (A ⧸ I) B₀] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C), Algebra.Etale A C ∧
      Nonempty ((A ⧸ I) ⊗[A] C ≃ₐ[A ⧸ I] B₀) :=
  Etale.exists_etale_tensor_equiv Ideal.Quotient.mk_surjective B₀

end Algebra
