/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Smooth.AdicCompletion
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.RingTheory.TensorProduct.Quotient
import SGA.SGA1.ExposeI.StandardEtale

/-!
# SGA 1, Exposé I, §6: étale extensions of complete local rings

Theorem I.6.1: for a complete noetherian local ring `A` with residue field `k`,
`B ↦ k ⊗_A B` is an equivalence from finite étale `A`-algebras to finite étale
(= separable) `k`-algebras (`isEquivalence_finiteEtale_baseChange_residueField`).

Full faithfulness is I.6.2 (`bijective_map_residueField`): a finite `A`-module is
`m`-adically complete, and maps out of a formally étale algebra lift uniquely through
the `m`-adic filtration. SGA reduces to the artinian case `A/mⁿ` and I.5.5; the
artinian step is `hom_equiv_residue` below. Existence follows SGA: a separable
extension of `k` is `k[t]/(f)`, and `A[t]/(F)` for a monic lift `F` of `f` is finite
étale (I.7.4); this part holds over any local ring.
-/

universe u

namespace SGA.SGA1.ExposeI

open Algebra IsLocalRing TensorProduct Polynomial

variable {A : Type u} [CommRing A]

/-- A finite module over an `I`-adically complete noetherian ring is `I`-adically
complete. -/
theorem isAdicComplete_of_finite (I : Ideal A) [IsNoetherianRing A] [IsAdicComplete I A]
    (M : Type*) [AddCommGroup M] [Module A M] [Module.Finite A M] : IsAdicComplete I M := by
  have : IsHausdorff I M := .of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  have hA : Function.Surjective (AdicCompletion.of I A) :=
    (AdicCompletion.of_bijective_iff (I := I) (M := A)).mpr inferInstance |>.2
  have hM : Function.Surjective (AdicCompletion.of I M) := by
    intro x
    obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M x
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul r m =>
      obtain ⟨a, rfl⟩ := hA r
      exact ⟨a • m, by rw [AdicCompletion.ofTensorProduct_tmul, map_smul]; rfl⟩
    | add s t hs ht =>
      obtain ⟨a, ha⟩ := hs
      obtain ⟨b, hb⟩ := ht
      exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  exact (AdicCompletion.of_bijective_iff (I := I) (M := M)).mp
    ⟨AdicCompletion.of_injective I M, hM⟩


section

variable (I : Ideal A) {B B' : Type u} [CommRing B] [CommRing B'] [Algebra A B] [Algebra A B']

/-- I.6.2 and the full faithfulness in I.8.4, for an adic ring: let `A` be noetherian and
`I`-adically complete, `B` formally étale over `A` and `B'` finite over `A`. Then
`Hom_A(B, B') → Hom_{A/I}(B/IB, B'/IB')` is bijective. -/
theorem bijective_map_quotient [IsNoetherianRing A] [IsAdicComplete I A] [FormallyEtale A B]
    [Module.Finite A B'] :
    Function.Bijective fun f : B →ₐ[A] B' ↦
      Algebra.TensorProduct.map (AlgHom.id (A ⧸ I) (A ⧸ I)) f := by
  have : IsAdicComplete I B' := isAdicComplete_of_finite I B'
  have hI : IsAdicComplete (I.map (algebraMap A B')) B' :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  let e := quotientEquivQuotientTensor I (B' := B')
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · apply FormallyUnramified.ext_of_iInf (I := I.map (algebraMap A B'))
    · have := hI.toIsHausdorff.iInf_pow_smul
      simpa [smul_eq_mul, Ideal.mul_top] using this
    · intro b
      apply e.injective
      have := congr($hfg (1 ⊗ₜ b))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this
      rw [quotientEquivQuotientTensor_mk, quotientEquivQuotientTensor_mk]
      exact this
  · obtain ⟨f, hf⟩ := FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (R := A)
      (I := I.map (algebraMap A B'))
      ((e.symm.toAlgHom).comp ((φ.restrictScalars A).comp Algebra.TensorProduct.includeRight))
    refine ⟨f, Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_⟩
    ext b
    have := congr(e ($hf b))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [quotientEquivQuotientTensor_mk] at this
    simpa using this

/-- I.6.2: let `A` be a complete noetherian local ring with residue field `k`, `B` an
étale `A`-algebra and `B'` a finite `A`-algebra. Then
`Hom_A(B, B') → Hom_k(k ⊗_A B, k ⊗_A B')` is bijective. (SGA assumes `B` finite as
well; only formal étaleness of `B` is used.) -/
theorem bijective_map_residueField [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] [FormallyEtale A B] [Module.Finite A B'] :
    Function.Bijective fun f : B →ₐ[A] B' ↦
      Algebra.TensorProduct.map (AlgHom.id (ResidueField A) (ResidueField A)) f :=
  bijective_map_quotient (maximalIdeal A)

omit I in
/-- I.6.2 for any quotient `T` of `A` (e.g. a field quotient isomorphic to the residue
field): if `A` is noetherian and complete for the kernel of `A → T`, then
`Hom_A(B, B') → Hom_T(T ⊗_A B, T ⊗_A B')` is bijective. -/
theorem bijective_map_of_surjective {T : Type u} [CommRing T] [Algebra A T]
    (hT : Function.Surjective (algebraMap A T)) [IsNoetherianRing A]
    [IsAdicComplete (RingHom.ker (algebraMap A T)) A] [FormallyEtale A B] [Module.Finite A B'] :
    Function.Bijective fun f : B →ₐ[A] B' ↦ Algebra.TensorProduct.map (AlgHom.id T T) f := by
  set I := RingHom.ker (algebraMap A T)
  have : IsAdicComplete I B' := isAdicComplete_of_finite I B'
  have hI : IsAdicComplete (I.map (algebraMap A B')) B' :=
    (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  let eT : (A ⧸ I) ≃ₐ[A] T := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A T) hT
  let e : (B' ⧸ I.map (algebraMap A B')) ≃ₐ[A] T ⊗[A] B' :=
    (quotientEquivQuotientTensor I).trans (Algebra.TensorProduct.congr eT AlgEquiv.refl)
  have he (b : B') : e (Ideal.Quotient.mk _ b) = 1 ⊗ₜ b := by
    simp [e, quotientEquivQuotientTensor_mk]
  refine ⟨fun f g hfg ↦ ?_, fun φ ↦ ?_⟩
  · apply FormallyUnramified.ext_of_iInf (I := I.map (algebraMap A B'))
    · have := hI.toIsHausdorff.iInf_pow_smul
      simpa [smul_eq_mul, Ideal.mul_top] using this
    · intro b
      apply e.injective
      have := congr($hfg (1 ⊗ₜ b))
      simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at this
      rw [he, he]
      exact this
  · obtain ⟨f, hf⟩ := FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete (R := A)
      (I := I.map (algebraMap A B'))
      ((e.symm.toAlgHom).comp ((φ.restrictScalars A).comp Algebra.TensorProduct.includeRight))
    refine ⟨f, Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_⟩
    ext b
    have := congr(e ($hf b))
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [he] at this
    simpa using this

end

section Artinian

variable {B : Type u} [CommRing B] [Algebra A B] [IsLocalRing A] [IsArtinianRing A]

lemma isNilpotent_map_maximalIdeal {C : Type u} [CommRing C] [Algebra A C] :
    IsNilpotent ((maximalIdeal A).map (algebraMap A C)) := by
  have hnil : IsNilpotent (maximalIdeal A) := by
    rw [← jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsArtinianRing.isNilpotent_jacobson_bot
  obtain ⟨n, hn⟩ := hnil
  exact ⟨n, by simpa [Ideal.map_pow] using congr_arg (Ideal.map (algebraMap A C)) hn⟩

/-- I.6.2, the artinian step (a special case of I.5.5): if `A` is artinian local and
`B` formally étale over `A`, maps `B → C` into any `A`-algebra correspond bijectively
to maps into `C ⧸ m C`. -/
theorem hom_equiv_residue [FormallyEtale A B] {C : Type u} [CommRing C] [Algebra A C] :
    Function.Bijective fun f : B →ₐ[A] C ↦
      (Ideal.Quotient.mkₐ A ((maximalIdeal A).map (algebraMap A C))).comp f :=
  ⟨fun _ _ h ↦ FormallyUnramified.ext (I := (maximalIdeal A).map (algebraMap A C))
      isNilpotent_map_maximalIdeal fun x ↦ congr($(h) x),
    fun φ ↦ ⟨FormallySmooth.lift _ isNilpotent_map_maximalIdeal φ,
      FormallySmooth.comp_lift _ _ φ⟩⟩

end Artinian

/-- If `A → k` is a surjection onto a field, a polynomial over `A` whose image in `k[t]` is
separable has separable reduction modulo the maximal ideal. -/
lemma separable_map_residue_of_surjective [IsLocalRing A] {k : Type u} [Field k] [Algebra A k]
    (hk : Function.Surjective (algebraMap A k)) {P : A[X]}
    (h : (P.map (algebraMap A k)).Separable) : (P.map (residue A)).Separable := by
  have hker : RingHom.ker (algebraMap A k) = maximalIdeal A :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hk)
  let ψ : ResidueField A →+* k := Ideal.Quotient.lift _ (algebraMap A k) fun a ha ↦ by
    rwa [← RingHom.mem_ker, hker]
  have hψ : ψ.comp (residue A) = algebraMap A k := by ext; rfl
  rw [← hψ, ← Polynomial.map_map, Polynomial.separable_map] at h
  exact h

/-- I.6.1, existence, for a separable field extension: let `A` be local and `k` a field
quotient of `A` (its residue field). If `L/k` is finite separable, there is a finite étale
`A`-algebra `B` with `k ⊗_A B ≅ L`, namely `A[t]/(F)` for a monic lift `F` of the minimal
polynomial of a primitive element of `L`. No completeness is needed. -/
theorem exists_finite_etale_tensor_equiv_field [IsLocalRing A] {k : Type u} [Field k]
    [Algebra A k] (hk : Function.Surjective (algebraMap A k)) (L : Type u) [Field L]
    [Algebra k L] [Module.Finite k L] [Algebra.IsSeparable k L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty (k ⊗[A] B ≃ₐ[k] L) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  obtain ⟨P, hPmap, -, hPmonic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.map_surjective _ hk (minpoly k α)) (minpoly.monic hint)
  have hsep : (P.map (algebraMap A k)).Separable := hPmap ▸ Algebra.IsSeparable.isSeparable _ α
  have hPs : P.Separable :=
    separable_of_separable_map_residue hPmonic (separable_map_residue_of_surjective hk hsep)
  have := etale_adjoinRoot_of_separable hPmonic hPs
  have : Module.Finite A (AdjoinRoot P) := (AdjoinRoot.powerBasis' hPmonic).finite
  refine ⟨AdjoinRoot P, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  have e₁ : AdjoinRoot (P.map (algebraMap A k)) ≃ₐ[k] AdjoinRoot (minpoly k α) := by
    rw [show P.map (algebraMap A k) = minpoly k α from hPmap]
  exact (tensorAdjoinRootEquiv _ P).trans (e₁.trans
    ((IntermediateField.adjoinRootEquivAdjoin _ hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)))

/-- I.6.1, existence: over a local ring `A` with residue field `k` (any field quotient of
`A`), every finite étale `k`-algebra is `k ⊗_A B` for a finite étale `A`-algebra `B`. -/
theorem exists_finite_etale_tensor_equiv [IsLocalRing A] {k : Type u} [Field k] [Algebra A k]
    (hk : Function.Surjective (algebraMap A k)) (L : Type u) [CommRing L] [Algebra k L]
    [Module.Finite k L] [Algebra.Etale k L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty (k ⊗[A] B ≃ₐ[k] L) := by
  obtain ⟨I, _, Li, _, _, e, hLi⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (K := k) (A := L)).mp inferInstance
  have H (i : I) := by
    have := (hLi i).1
    have := (hLi i).2
    exact exists_finite_etale_tensor_equiv_field hk (Li i)
  choose B _ _ hfin het e' using H
  have := fun i ↦ hfin i
  have := fun i ↦ het i
  refine ⟨Π i, B i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  classical
  have := Fintype.ofFinite I
  exact (Algebra.TensorProduct.piRight A k k B).trans
    ((AlgEquiv.piCongrRight fun i ↦ (e' i).some).trans e.symm)

/-- I.6.1, existence, with the residue field: every finite étale `k`-algebra lifts. -/
theorem exists_finite_etale_residueField_tensor_equiv [IsLocalRing A] (L : Type u) [CommRing L]
    [Algebra (ResidueField A) L] [Module.Finite (ResidueField A) L]
    [Algebra.Etale (ResidueField A) L] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty (ResidueField A ⊗[A] B ≃ₐ[ResidueField A] L) :=
  exists_finite_etale_tensor_equiv residue_surjective L

open CategoryTheory in
/-- I.6.1: if `A` is a complete noetherian local ring with residue field `k`, then
`B ↦ k ⊗_A B` is an equivalence from finite étale `A`-algebras to finite étale
(i.e. separable) `k`-algebras. -/
theorem isEquivalence_finiteEtale_baseChange_residueField [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] :
    (CommAlgCat.FiniteEtale.baseChange.{u} A (ResidueField A)).IsEquivalence where
  faithful := ⟨fun {X Y} f g h ↦ by
    have h' : Algebra.TensorProduct.map (AlgHom.id (ResidueField A) (ResidueField A)) f.hom.hom =
        Algebra.TensorProduct.map (AlgHom.id (ResidueField A) (ResidueField A)) g.hom.hom :=
      congr($(h).hom.hom)
    have := (bijective_map_residueField (A := A) (B := X.obj) (B' := Y.obj)).1 h'
    ext : 2
    exact this⟩
  full := ⟨fun {X Y} φ ↦ by
    obtain ⟨f, hf⟩ := (bijective_map_residueField (A := A) (B := X.obj) (B' := Y.obj)).2 φ.hom.hom
    refine ⟨⟨CommAlgCat.ofHom f⟩, ?_⟩
    ext : 2
    exact hf⟩
  essSurj := ⟨fun L ↦ by
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := exists_finite_etale_residueField_tensor_equiv (A := A) L.obj
    exact ⟨CommAlgCat.FiniteEtale.of A B, ⟨CommAlgCat.FiniteEtale.isoMk e⟩⟩⟩

open CategoryTheory in
/-- I.6.1 with any field quotient `k` of `A` in place of the residue field: if `A` is a
noetherian local ring, complete for the kernel of `A → k`, then `B ↦ k ⊗_A B` is an
equivalence between finite étale algebras. -/
theorem isEquivalence_finiteEtale_baseChange_of_surjective [IsLocalRing A] [IsNoetherianRing A]
    {k : Type u} [Field k] [Algebra A k] (hk : Function.Surjective (algebraMap A k))
    [IsAdicComplete (RingHom.ker (algebraMap A k)) A] :
    (CommAlgCat.FiniteEtale.baseChange.{u} A k).IsEquivalence where
  faithful := ⟨fun {X Y} f g h ↦ by
    have h' : Algebra.TensorProduct.map (AlgHom.id k k) f.hom.hom =
        Algebra.TensorProduct.map (AlgHom.id k k) g.hom.hom :=
      congr($(h).hom.hom)
    have := (bijective_map_of_surjective hk (B := X.obj) (B' := Y.obj)).1 h'
    ext : 2
    exact this⟩
  full := ⟨fun {X Y} φ ↦ by
    obtain ⟨f, hf⟩ := (bijective_map_of_surjective hk (B := X.obj) (B' := Y.obj)).2 φ.hom.hom
    refine ⟨⟨CommAlgCat.ofHom f⟩, ?_⟩
    ext : 2
    exact hf⟩
  essSurj := ⟨fun L ↦ by
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := exists_finite_etale_tensor_equiv hk L.obj
    exact ⟨CommAlgCat.FiniteEtale.of A B, ⟨CommAlgCat.FiniteEtale.isoMk e⟩⟩⟩

/-- I.6.1, over a separably closed field (mathlib): finite étale algebras are
anti-equivalent to finite sets. -/
noncomputable def finiteEtaleEquivOfIsSepClosed (Ω : Type u) [Field Ω] [IsSepClosed Ω] :
    (CommAlgCat.FiniteEtale.{u} Ω)ᵒᵖ ≌ FintypeCat.{u} :=
  CommAlgCat.FiniteEtale.equivOfIsSepClosed Ω

end SGA.SGA1.ExposeI
