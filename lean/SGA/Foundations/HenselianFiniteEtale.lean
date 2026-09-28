/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.HenselianLifting
import SGA.Foundations.StrictHenselization
import SGA.Foundations.WeilRestriction
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Finite étale algebras over a henselian local ring

Let `A` be a henselian local ring with residue field `k`.

* `HenselianLocalRing.bijective_comp_includeRight`: for `T` a finite free `A`-algebra and `B` an
  étale `A`-algebra, the `A`-algebra maps `B → T` are the `A`-algebra maps `B → k ⊗_A T`
  (Stacks 04GG, in the finite free case; EGA IV 18.5). The proof applies the case
  `T = A` (`HenselianLocalRing.algHomEquivResidueField`) to the Weil restriction of `T ⊗_A B`
  along `A → T`, which is étale over `A` (`Algebra.WeilRestriction`).
* `HenselianLocalRing.existsUnique_isIdempotentElem_lift`: idempotents of `k ⊗_A T` lift uniquely
  to `T`.
* `HenselianLocalRing.isEquivalence_baseChange_residueField`: `B ↦ k ⊗_A B` is an equivalence
  from finite étale `A`-algebras to finite étale `k`-algebras (EGA IV 18.5; used in SGA 1 X).
  Faithfulness and essential surjectivity hold over any local ring
  (`IsLocalRing.faithful_baseChange_residueField`, `IsLocalRing.essSurj_baseChange_residueField`,
  `IsLocalRing.exists_finite_etale_lift`); fullness is
  `HenselianLocalRing.full_baseChange_residueField`.
* `HenselianLocalRing.exists_algEquiv_pi_isLocalRing`: a finite étale `A`-algebra is a finite
  product of local finite étale `A`-algebras, which are henselian
  (`HenselianLocalRing.of_finite_etale`).
* `IsStrictlyHenselian.exists_algEquiv_pi`: over a strictly henselian local ring every finite
  étale algebra is isomorphic to `Fin n → A`.
-/

open IsLocalRing TensorProduct CategoryTheory Polynomial

noncomputable section

universe u v w

namespace HenselianLocalRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A]

section Presented

variable {σ τ : Type*} [Finite σ] [Finite τ] (r : τ → MvPolynomial σ A)
  [Algebra.FormallyEtale A (MvPolynomial σ A ⧸ Ideal.span (Set.range r))]
  {T : Type v} [CommRing T] [Algebra A T] {ι : Type*} [Finite ι] (b : Module.Basis ι A T)

include b in
theorem bijective_comp_includeRight_of_presentation :
    Function.Bijective (fun φ : MvPolynomial σ A ⧸ Ideal.span (Set.range r) →ₐ[A] T ↦
      (Algebra.TensorProduct.includeRight : T →ₐ[A] ResidueField A ⊗[A] T).comp φ) := by
  have := Fintype.ofFinite ι
  set k := ResidueField A
  let B₀ := MvPolynomial σ A ⧸ Ideal.span (Set.range r)
  let W := Algebra.WeilRestriction b r
  let res : A →ₐ[A] k := IsScalarTower.toAlgHom A A k
  let ρ : A ⊗[A] T →ₐ[A] k ⊗[A] T := Algebra.TensorProduct.map res (AlgHom.id A T)
  -- reduction modulo `𝔪`, on `A ⊗[A] T`, is bijective on `B₀`-points
  have hG : Function.Bijective (fun χ : B₀ →ₐ[A] A ⊗[A] T ↦ ρ.comp χ) := by
    have hL := (algHomEquivResidueField A W A).bijective
    have H : (fun χ : B₀ →ₐ[A] A ⊗[A] T ↦ ρ.comp χ) =
        (Algebra.WeilRestriction.homEquiv b r k) ∘ (algHomEquivResidueField A W A) ∘
          (Algebra.WeilRestriction.homEquiv b r A).symm := by
      funext χ
      simp only [Function.comp_apply]
      rw [show (algHomEquivResidueField A W A) ((Algebra.WeilRestriction.homEquiv b r A).symm χ)
          = res.comp ((Algebra.WeilRestriction.homEquiv b r A).symm χ) from rfl,
        Algebra.WeilRestriction.homEquiv_comp, Equiv.apply_symm_apply]
    rw [H]
    exact (Algebra.WeilRestriction.homEquiv b r k).bijective.comp
      (hL.comp (Algebra.WeilRestriction.homEquiv b r A).symm.bijective)
  have hρ : ρ.comp (Algebra.TensorProduct.lid A T).symm.toAlgHom =
      Algebra.TensorProduct.includeRight := by
    ext t
    simp [ρ, res]
  have hlid : Function.Bijective (fun φ : B₀ →ₐ[A] T ↦
      ((Algebra.TensorProduct.lid A T).symm : T →ₐ[A] A ⊗[A] T).comp φ) :=
    ⟨fun φ ψ h ↦ AlgHom.ext fun x ↦ (Algebra.TensorProduct.lid A T).symm.injective
      (DFunLike.congr_fun h x), fun χ ↦ ⟨(Algebra.TensorProduct.lid A T : A ⊗[A] T →ₐ[A] T).comp χ,
        AlgHom.ext fun x ↦ by simp⟩⟩
  convert hG.comp hlid using 1
  funext φ
  simp only [Function.comp_apply, ← AlgHom.comp_assoc]
  rw [← hρ]

end Presented

variable (T : Type v) [CommRing T] [Algebra A T] [Module.Free A T] [Module.Finite A T]
  (B : Type w) [CommRing B] [Algebra A B] [Algebra.Etale A B]

/-- Stacks 04GG (finite free case), EGA IV 18.5: over a henselian local ring `A` with
residue field `k`, for `T` a finite free `A`-algebra and `B` an étale `A`-algebra, every
`A`-algebra map `B → k ⊗_A T` lifts uniquely to an `A`-algebra map `B → T`. -/
theorem bijective_comp_includeRight :
    Function.Bijective (fun φ : B →ₐ[A] T ↦
      (Algebra.TensorProduct.includeRight : T →ₐ[A] ResidueField A ⊗[A] T).comp φ) := by
  classical
  obtain ⟨n, f, hf, s, hs⟩ := (inferInstance : Algebra.FinitePresentation A B).out
  let r : s → MvPolynomial (Fin n) A := Subtype.val
  have hr : Ideal.span (Set.range r) = RingHom.ker f.toRingHom := by
    simpa [r] using hs
  let e : (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range r)) ≃ₐ[A] B :=
    (Ideal.quotientEquivAlgOfEq A hr).trans (Ideal.quotientKerAlgEquivOfSurjective hf)
  have : Algebra.FormallyEtale A (MvPolynomial (Fin n) A ⧸ Ideal.span (Set.range r)) :=
    .of_equiv e.symm
  have H := bijective_comp_includeRight_of_presentation r (Module.Free.chooseBasis A T)
  have h₁ := (e.symm.arrowCongr (AlgEquiv.refl : T ≃ₐ[A] T)).bijective
  have h₂ := (e.arrowCongr
    (AlgEquiv.refl : ResidueField A ⊗[A] T ≃ₐ[A] ResidueField A ⊗[A] T)).bijective
  convert h₂.comp (H.comp h₁) using 1
  funext φ
  refine AlgHom.ext fun x ↦ ?_
  simp [AlgEquiv.arrowCongr_apply]

/-- Stacks 04GG (finite free case): the bijection
`(B →ₐ[A] T) ≃ (B →ₐ[A] k ⊗_A T)` for `B` étale and `T` finite free over a henselian local
ring `A` with residue field `k`. -/
def algHomEquivOfFinite : (B →ₐ[A] T) ≃ (B →ₐ[A] ResidueField A ⊗[A] T) :=
  Equiv.ofBijective _ (bijective_comp_includeRight T B)

@[simp]
lemma algHomEquivOfFinite_apply (φ : B →ₐ[A] T) (x : B) :
    algHomEquivOfFinite T B φ x = 1 ⊗ₜ φ x := rfl

lemma algHomEquivOfFinite_symm_apply (ψ : B →ₐ[A] ResidueField A ⊗[A] T) (x : B) :
    1 ⊗ₜ (algHomEquivOfFinite T B).symm ψ x = ψ x :=
  DFunLike.congr_fun ((algHomEquivOfFinite T B).apply_symm_apply ψ) x

/-- The standard étale pair `(X² - X, 1)`: its points are the idempotents. -/
def idempotentPair (R : Type*) [CommRing R] : StandardEtalePair R where
  f := X ^ 2 - X
  monic_f := monic_X_pow_sub (degree_X_le.trans_lt (by exact_mod_cast one_lt_two))
  g := 1
  cond := ⟨derivative (X ^ 2 - X), C (-4), 0, by
    rw [derivative_sub, derivative_X_pow, derivative_X]
    simp only [map_neg, pow_zero]
    ring_nf
    simp [map_ofNat]
    ring⟩

lemma idempotentPair_hasMap_iff {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (x : S) :
    (idempotentPair R).HasMap x ↔ IsIdempotentElem x := by
  simp [StandardEtalePair.HasMap, idempotentPair, IsIdempotentElem, sub_eq_zero, sq]

/-- Idempotents lift uniquely from `k ⊗_A T` to a finite free algebra `T` over a henselian local
ring `A` with residue field `k` (Stacks 04GG). -/
theorem existsUnique_isIdempotentElem_lift {e₀ : ResidueField A ⊗[A] T}
    (he₀ : IsIdempotentElem e₀) : ∃! e : T, IsIdempotentElem e ∧ 1 ⊗ₜ e = e₀ := by
  let P := idempotentPair A
  have hbij := bijective_comp_includeRight (A := A) T P.Ring
  obtain ⟨φ, hφ⟩ := hbij.2 (P.lift e₀ ((idempotentPair_hasMap_iff e₀).mpr he₀))
  beta_reduce at hφ
  refine ⟨φ P.X, ⟨(idempotentPair_hasMap_iff _).mp (StandardEtalePair.hasMap_X.map φ), ?_⟩, ?_⟩
  · simpa using DFunLike.congr_fun hφ P.X
  · rintro e ⟨he, rfl⟩
    have h := hbij.1 (a₁ := P.lift e ((idempotentPair_hasMap_iff e).mpr he)) (a₂ := φ) (by
      simp only
      rw [hφ]
      apply P.hom_ext
      simp)
    simpa using DFunLike.congr_fun h P.X

end HenselianLocalRing

namespace IsLocalRing

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- For `C` finite over a local ring `A`, the ideal `𝔪_A C` lies in the Jacobson radical. -/
lemma map_maximalIdeal_le_jacobson {C : Type*} [CommRing C] [Algebra A C] [Module.Finite A C] :
    (maximalIdeal A).map (algebraMap A C) ≤ Ideal.jacobson ⊥ := by
  rw [Ideal.jacobson, le_sInf_iff]
  rintro M ⟨-, hM⟩
  rw [Ideal.map_le_iff_le_comap]
  exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)).ge

/-- The structure map of a local ring finite over a local ring is local. -/
lemma isLocalHom_of_finite (B : Type*) [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Finite A B] : IsLocalHom (algebraMap A B) :=
  ((local_hom_TFAE (algebraMap A B)).out 1 5).mpr
    (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B)))

/-- For `T` finite over a local ring `A` with residue field `k`, the map `T → k ⊗_A T` is local:
it is the reduction modulo `𝔪_A T`, which lies in the Jacobson radical. -/
lemma isLocalHom_includeRight (T : Type*) [CommRing T] [Algebra A T] [Module.Finite A T] :
    IsLocalHom (Algebra.TensorProduct.includeRight : T →ₐ[A] ResidueField A ⊗[A] T) := by
  have := isLocalHom_of_le_jacobson_bot _ (map_maximalIdeal_le_jacobson (A := A) (C := T))
  refine ⟨fun t ht ↦ ?_⟩
  have ht' : IsUnit (Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A T)) t) :=
    (isUnit_map_iff (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (maximalIdeal A)) _).mp ht
  exact isUnit_of_map_unit _ t ht'

variable (A) in
/-- Every finite separable extension `k'` of the residue field `k` of a local ring `A` is
`k ⊗_A A[x]/(g)` for a finite étale `A`-algebra `A[x]/(g)`, `g` a monic lift of the minimal
polynomial of a primitive element of `k'` (the construction of unramified extensions of local
rings, EGA IV 18.4). -/
theorem exists_finite_etale_lift_of_isSeparable (k' : Type u) [Field k']
    [Algebra (ResidueField A) k'] [FiniteDimensional (ResidueField A) k']
    [Algebra.IsSeparable (ResidueField A) k'] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty (ResidueField A ⊗[A] B ≃ₐ[ResidueField A] k') := by
  set k := ResidueField A
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k k'
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  have hmon : (minpoly k α).Monic := minpoly.monic hint
  have hsep : (minpoly k α).Separable := Algebra.IsSeparable.isSeparable k α
  obtain ⟨g, hg, -, hgmon⟩ := lifts_and_degree_eq_and_monic
    (map_surjective (residue A) residue_surjective (minpoly k α)) hmon
  obtain ⟨u₀, v₀, huv⟩ := hsep
  obtain ⟨u, rfl⟩ := map_surjective (residue A) residue_surjective u₀
  obtain ⟨v, rfl⟩ := map_surjective (residue A) residue_surjective v₀
  set h := u * g + v * derivative g with hh
  let P : StandardEtalePair A := ⟨g, hgmon, h, ⟨v, u, 1, by rw [hh]; ring⟩⟩
  have hmap : map (residue A) (h - 1) = 0 := by
    rw [Polynomial.map_sub, hh, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
      ← Polynomial.derivative_map, hg, huv, Polynomial.map_one, sub_self]
  let B := AdjoinRoot g
  have : Module.Finite A B := hgmon.finite_adjoinRoot
  have hmem : AdjoinRoot.mk g (h - 1) ∈ (maximalIdeal A).map (algebraMap A B) := by
    have h1 : h - 1 ∈ (maximalIdeal A).map (C : A →+* A[X]) := by
      rw [Ideal.mem_map_C_iff]
      intro n
      rw [← ker_residue, RingHom.mem_ker, ← Polynomial.coeff_map, hmap, coeff_zero]
    have := Ideal.mem_map_of_mem (AdjoinRoot.mk g) h1
    rwa [Ideal.map_map] at this
  have hunit : IsUnit (AdjoinRoot.mk P.f P.g) := by
    have := Ideal.mem_jacobson_bot.mp (map_maximalIdeal_le_jacobson hmem) 1
    rw [mul_one, map_sub, map_one, sub_add_cancel] at this
    exact this
  have : Algebra.Etale A B := Algebra.Etale.of_equiv (P.equivAwayAdjoinRoot.trans
    ((IsLocalization.atUnit _ _ (AdjoinRoot.mk P.f P.g) hunit).symm.restrictScalars A))
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  letI : Algebra A k' := ((algebraMap k k').comp (algebraMap A k)).toAlgebra
  haveI : IsScalarTower A k k' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let e₁ : k ⊗[A] B ≃ₐ[A] (B ⧸ ((maximalIdeal A).map (algebraMap A B) : Ideal B)) :=
    ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).symm).restrictScalars A
  let e₂ : (B ⧸ ((maximalIdeal A).map (algebraMap A B) : Ideal B)) ≃ₐ[A]
      AdjoinRoot (g.map (Ideal.Quotient.mk (maximalIdeal A))) :=
    AdjoinRoot.quotEquivQuotMap g (maximalIdeal A)
  let e₃ : AdjoinRoot (minpoly k α) ≃ₐ[k] k' :=
    (IntermediateField.adjoinRootEquivAdjoin k hint).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  let e₃' : AdjoinRoot (g.map (residue A)) ≃ₐ[k] k' := by
    rw [hg]
    exact e₃
  exact AlgEquiv.extendScalarsOfSurjective residue_surjective
    (e₁.trans (e₂.trans (e₃'.restrictScalars A)))

variable (A) in
/-- Every finite étale algebra over the residue field `k` of a local ring `A` is `k ⊗_A B` for a
finite étale `A`-algebra `B`. -/
theorem exists_finite_etale_lift (C : Type u) [CommRing C] [Algebra (ResidueField A) C]
    [Algebra.Etale (ResidueField A) C] :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B), Module.Finite A B ∧ Algebra.Etale A B ∧
      Nonempty (ResidueField A ⊗[A] B ≃ₐ[ResidueField A] C) := by
  classical
  obtain ⟨I, _, K, _, _, e, hK⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod (ResidueField A) C).mp inferInstance
  have := Fintype.ofFinite I
  have hlift (i : I) := by
    have := (hK i).1
    have := (hK i).2
    exact exists_finite_etale_lift_of_isSeparable A (K i)
  choose B _ _ hBf hBe hBiso using hlift
  refine ⟨Π i, B i, inferInstance, inferInstance, inferInstance, inferInstance, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.piRight A (ResidueField A) (ResidueField A) B).trans
    ((AlgEquiv.piCongrRight fun i ↦ (hBiso i).some).trans e.symm)

variable (A) in
/-- Reduction modulo the maximal ideal, from finite étale `A`-algebras to finite étale algebras
over the residue field, is essentially surjective for any local ring `A`. -/
instance essSurj_baseChange_residueField :
    (CommAlgCat.FiniteEtale.baseChange.{u, u} A (ResidueField A)).EssSurj where
  mem_essImage C := by
    obtain ⟨B, _, _, _, _, ⟨e⟩⟩ := exists_finite_etale_lift A C.obj
    exact ⟨CommAlgCat.FiniteEtale.of A B, ⟨CommAlgCat.FiniteEtale.isoMk e⟩⟩

instance (B : CommAlgCat.FiniteEtale.{v} A) : Module.Free A B :=
  Module.free_of_flat_of_isLocalRing

variable (A) in
/-- Reduction modulo the maximal ideal, `B ↦ k ⊗_A B`, is faithful on finite étale algebras over
any local ring `A`: two maps from an unramified algebra to a finite algebra which agree modulo
`𝔪_A` are equal. -/
instance faithful_baseChange_residueField :
    (CommAlgCat.FiniteEtale.baseChange.{u, u} A (ResidueField A)).Faithful where
  map_injective {B C} f g hfg := by
    apply ObjectProperty.hom_ext
    ext : 1
    refine Algebra.FormallyUnramified.algHom_ext_of_sub_mem_jacobson
      (map_maximalIdeal_le_jacobson (A := A) (C := C.obj)) fun b ↦ ?_
    have h : Algebra.TensorProduct.map (AlgHom.id (ResidueField A) (ResidueField A)) f.hom.hom
        (1 ⊗ₜ b) = Algebra.TensorProduct.map (AlgHom.id (ResidueField A) (ResidueField A))
          g.hom.hom (1 ⊗ₜ b) :=
      DFunLike.congr_fun (congrArg (fun φ ↦ φ.hom.hom) hfg) (1 ⊗ₜ b)
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul] at h
    rw [← Ideal.Quotient.eq]
    apply (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C.obj (maximalIdeal A)).injective
    exact h

end IsLocalRing

namespace HenselianLocalRing

open CommAlgCat

variable (A : Type u) [CommRing A] [HenselianLocalRing A]

/-- Reduction modulo the maximal ideal is full on finite étale algebras over a henselian local
ring (Stacks 04GG). -/
instance full_baseChange_residueField :
    (FiniteEtale.baseChange.{u, u} A (ResidueField A)).Full where
  map_surjective {B C} F := by
    let F' : ResidueField A ⊗[A] B.obj →ₐ[ResidueField A] ResidueField A ⊗[A] C.obj := F.hom.hom
    obtain ⟨φ, hφ⟩ := (bijective_comp_includeRight C.obj B.obj).2
      ((F'.restrictScalars A).comp Algebra.TensorProduct.includeRight)
    refine ⟨ObjectProperty.homMk (CommAlgCat.ofHom φ), ?_⟩
    apply ObjectProperty.hom_ext
    ext : 1
    change Algebra.TensorProduct.map (AlgHom.id (ResidueField A) (ResidueField A)) φ = F'
    apply Algebra.TensorProduct.ext
    · ext
    · refine AlgHom.ext fun b ↦ ?_
      simpa using DFunLike.congr_fun hφ b

/-- Over a henselian local ring `A` with residue field `k`, reduction `B ↦ k ⊗_A B` is an
equivalence from finite étale `A`-algebras to finite étale `k`-algebras (Stacks 04GG;
EGA IV 18.5; SGA 1 X uses this for complete local rings). -/
instance isEquivalence_baseChange_residueField :
    (FiniteEtale.baseChange.{u, u} A (ResidueField A)).IsEquivalence where

end HenselianLocalRing

namespace IsStrictlyHenselian

open CommAlgCat

variable (A : Type u) [CommRing A] [IsStrictlyHenselian A]

/-- Over a strictly henselian local ring `A`, every finite étale `A`-algebra is isomorphic to a
finite product of copies of `A` (Stacks, Section 04GE; EGA IV 18.8): its reduction is split
since the residue field is separably closed, and reduction is an equivalence on finite étale
algebras. In the language of Galois categories: the fundamental group of `Spec A` is trivial. -/
theorem exists_algEquiv_pi (B : Type u) [CommRing B] [Algebra A B] [Module.Finite A B]
    [Algebra.Etale A B] : ∃ n : ℕ, Nonempty (B ≃ₐ[A] (Fin n → A)) := by
  classical
  set k := ResidueField A
  let P := PrimeSpectrum (k ⊗[A] B)
  have : Finite P := by
    have := Algebra.FormallyUnramified.finite_of_free k (k ⊗[A] B)
    have : IsArtinianRing (k ⊗[A] B) := isArtinian_of_tower k inferInstance
    infer_instance
  let n := Nat.card P
  let eP : P ≃ Fin n := Finite.equivFin P
  let e₁ : k ⊗[A] B ≃ₐ[k] (P → k) := Algebra.FormallyEtale.equivPiOfIsSepClosed k (k ⊗[A] B)
  let e₂ : (P → k) ≃ₐ[k] (Fin n → k) := AlgEquiv.piCongrLeft' k (fun _ ↦ k) eP
  let e₃ : k ⊗[A] (Fin n → A) ≃ₐ[k] (Fin n → k) :=
    (Algebra.TensorProduct.piRight A k k (fun _ : Fin n ↦ A)).trans
      (AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.rid A k k)
  let F := FiniteEtale.baseChange.{u, u} A k
  let i : F.obj (FiniteEtale.of A B) ≅ F.obj (FiniteEtale.of A (Fin n → A)) :=
    FiniteEtale.isoMk ((e₁.trans e₂).trans e₃.symm)
  let j := (Functor.FullyFaithful.ofFullyFaithful F).preimageIso i
  refine ⟨n, ⟨AlgEquiv.ofAlgHom j.hom.hom.hom j.inv.hom.hom ?_ ?_⟩⟩
  · exact congrArg (fun f ↦ f.hom.hom) j.inv_hom_id
  · exact congrArg (fun f ↦ f.hom.hom) j.hom_inv_id

end IsStrictlyHenselian

namespace HenselianLocalRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A]

/-- A local ring which is finite étale over a henselian local ring is henselian (Stacks,
Section 04GE). -/
theorem of_finite_etale (B : Type v) [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] : HenselianLocalRing B where
  is_henselian f hf a₀ h₁ h₂ := by
    have := IsLocalRing.isLocalHom_of_finite (A := A) B
    have : Module.Free A B := Module.free_of_flat_of_isLocalRing
    -- `k ⊗_A B` is the residue field of `B`
    have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B :=
      Algebra.FormallyUnramified.map_maximalIdeal
    let θ : ResidueField B ≃ₐ[A] ResidueField A ⊗[A] B :=
      (Ideal.quotientEquivAlgOfEq A hm.symm).trans
        ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).restrictScalars A)
    have hθ (b : B) : θ (residue B b) = 1 ⊗ₜ b := rfl
    -- the standard étale `B`-algebra adjoining a root of `f`
    let Q : StandardEtalePair B := ⟨f, hf, derivative f, 1, 0, 1, by ring⟩
    let : Algebra A Q.Ring := ((algebraMap B Q.Ring).comp (algebraMap A B)).toAlgebra
    have : IsScalarTower A B Q.Ring := IsScalarTower.of_algebraMap_eq' rfl
    have : Algebra.Etale A Q.Ring := Algebra.Etale.comp A B Q.Ring
    have hx : Q.HasMap (residue B a₀) := by
      refine ⟨?_, ?_⟩
      · change aeval (residue B a₀) f = 0
        rw [← residue_aeval, coe_aeval_eq_eval, residue_eq_zero_iff]
        exact h₁
      · change IsUnit (aeval (residue B a₀) (derivative f))
        rw [← residue_aeval, coe_aeval_eq_eval]
        exact h₂.map _
    let τ : Q.Ring →ₐ[A] ResidueField A ⊗[A] B :=
      (θ : ResidueField B →ₐ[A] _).comp ((Q.lift _ hx).restrictScalars A)
    obtain ⟨φ, hφ⟩ := (bijective_comp_includeRight B Q.Ring).2 τ
    have hφ' (y : Q.Ring) : 1 ⊗ₜ φ y = τ y := DFunLike.congr_fun hφ y
    -- `φ` is `B`-linear
    have hφB (b : B) : φ (algebraMap B Q.Ring b) = b := by
      have H := Algebra.FormallyUnramified.algHom_ext_of_residue (R := A)
        (f := φ.comp (IsScalarTower.toAlgHom A B Q.Ring)) (g := AlgHom.id A B) fun b ↦ by
          apply θ.injective
          rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', hθ, hφ', AlgHom.id_apply, hθ]
          simp [τ, hθ]
      exact DFunLike.congr_fun H b
    refine ⟨φ Q.X, ?_, ?_⟩
    · have hcomp : (φ : Q.Ring →+* B).comp (algebraMap B Q.Ring) = RingHom.id B :=
        RingHom.ext hφB
      change eval (φ Q.X) f = 0
      rw [← eval₂_id, ← hcomp]
      change eval₂ ((φ : Q.Ring →+* B).comp (algebraMap B Q.Ring))
        ((φ : Q.Ring →+* B) Q.X) f = 0
      rw [← hom_eval₂, ← aeval_def]
      change φ (aeval Q.X Q.f) = 0
      rw [StandardEtalePair.hasMap_X.1, map_zero]
    · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero]
      apply θ.injective
      rw [hθ, hφ']
      simp [τ]

end HenselianLocalRing

namespace HenselianLocalRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A]

/-- A finite étale algebra over a henselian local ring is a finite product of local rings, which
are finite étale, hence henselian (`HenselianLocalRing.of_finite_etale`) (Stacks 04GG). The
factors correspond to the points of the closed fibre. -/
theorem exists_algEquiv_pi_isLocalRing (B : Type u) [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] :
    ∃ (ι : Type u) (_ : Fintype ι) (Bi : ι → Type u) (_ : ∀ i, CommRing (Bi i))
      (_ : ∀ i, Algebra A (Bi i)),
      (∀ i, IsLocalRing (Bi i) ∧ Module.Finite A (Bi i) ∧ Algebra.Etale A (Bi i)) ∧
        Nonempty (B ≃ₐ[A] ∀ i, Bi i) := by
  classical
  set k := ResidueField A
  have : Module.Free A B := Module.free_of_flat_of_isLocalRing
  have : IsArtinianRing (k ⊗[A] B) := isArtinian_of_tower k inferInstance
  have : IsReduced (k ⊗[A] B) := Algebra.FormallyUnramified.isReduced_of_field k (k ⊗[A] B)
  let ι := MaximalSpectrum (k ⊗[A] B)
  let _ : Fintype ι := Fintype.ofFinite ι
  let E := IsArtinianRing.equivPi (k ⊗[A] B)
  let ē : ι → k ⊗[A] B := fun i ↦ E.symm (Pi.single i 1)
  have hē : CompleteOrthogonalIdempotents ē :=
    (CompleteOrthogonalIdempotents.single _).map E.symm.toRingEquiv.toRingHom
  have hEē (i j : ι) : E (ē i) j = if j = i then 1 else 0 := by
    rw [show E (ē i) = Pi.single i 1 from E.apply_symm_apply _]
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  -- the lifted idempotents
  choose e he he' using fun i ↦ (existsUnique_isIdempotentElem_lift (A := A) B (hē.idem i)).exists
  have hortho (i j : ι) (hij : i ≠ j) : e i * e j = 0 := by
    refine (existsUnique_isIdempotentElem_lift (A := A) B (e₀ := 0) .zero).unique
      ⟨(he i).mul (he j), ?_⟩ ⟨.zero, by simp⟩
    rw [← mul_one (1 : k), ← Algebra.TensorProduct.tmul_mul_tmul, he', he', hē.ortho hij]
  have he_c : CompleteOrthogonalIdempotents e := by
    refine ⟨⟨he, hortho⟩, ?_⟩
    refine (existsUnique_isIdempotentElem_lift (A := A) B (e₀ := 1) .one).unique
      ⟨OrthogonalIdempotents.isIdempotentElem_sum ⟨he, hortho⟩, ?_⟩ ⟨.one, rfl⟩
    rw [TensorProduct.tmul_sum]
    simp only [he']
    exact hē.complete
  let Bi : ι → Type u := fun i ↦ B ⧸ Ideal.span {1 - e i}
  refine ⟨ι, inferInstance, Bi, inferInstance, inferInstance, fun i ↦ ⟨?_, inferInstance, ?_⟩,
    ⟨AlgEquiv.ofBijective (AlgHom.pi fun i ↦ Ideal.Quotient.mkₐ A (Ideal.span {1 - e i}))
      he_c.bijective_pi⟩⟩
  · -- the closed fibre of `Bi i` is the field `(k ⊗ B)/𝔪ᵢ`
    have hspan : Ideal.span {1 - ē i} = i.asIdeal := by
      apply le_antisymm
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
          ← Ideal.Quotient.eq_zero_iff_mem]
        have := hEē i i
        simp only [↓reduceIte] at this
        change E (1 - ē i) i = 0
        rw [map_sub, map_one, Pi.sub_apply, Pi.one_apply, this, sub_self]
      · intro x hx
        have hx0 : x * ē i = 0 := by
          apply E.injective
          ext j
          rw [map_mul, Pi.mul_apply, hEē, map_zero, Pi.zero_apply]
          split_ifs with hji
          · subst hji
            rw [mul_one]
            exact Ideal.Quotient.eq_zero_iff_mem.mpr hx
          · rw [mul_zero]
        rw [Ideal.mem_span_singleton']
        exact ⟨x, by rw [mul_sub, mul_one, hx0, sub_zero]⟩
    have hmax : (Ideal.span {1 - ē i}).IsMaximal := hspan ▸ i.isMaximal
    have hmap : (Ideal.span {1 - e i}).map
        (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B) = Ideal.span {1 - ē i} := by
      rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
      simp [he']
    let F : k ⊗[A] Bi i ≃ₐ[k] (k ⊗[A] B) ⧸ Ideal.span {1 - ē i} :=
      (Algebra.TensorProduct.tensorQuotientEquiv (R := A) k B k (Ideal.span {1 - e i})).trans
        (Ideal.quotientEquivAlgOfEq k hmap)
    have hfield : IsField (k ⊗[A] Bi i) :=
      F.toMulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
    let := hfield.toField
    have := IsLocalRing.isLocalHom_includeRight (A := A) (Bi i)
    have : Nontrivial (Bi i) :=
      (Algebra.TensorProduct.includeRight : Bi i →ₐ[A] k ⊗[A] Bi i).domain_nontrivial
    refine .of_isUnit_or_isUnit_one_sub_self fun x ↦ ?_
    by_cases hx : (Algebra.TensorProduct.includeRight : Bi i →ₐ[A] k ⊗[A] Bi i) x = 0
    · right
      apply isUnit_of_map_unit (Algebra.TensorProduct.includeRight : Bi i →ₐ[A] k ⊗[A] Bi i)
      rw [map_sub, map_one, hx, sub_zero]
      exact isUnit_one
    · left
      exact isUnit_of_map_unit (Algebra.TensorProduct.includeRight : Bi i →ₐ[A] k ⊗[A] Bi i) x
        (isUnit_iff_ne_zero.mpr hx)
  · have : IsLocalization.Away (e i) (Bi i) :=
      IsLocalization.away_of_isIdempotentElem (he i)
        (by rw [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]) Ideal.Quotient.mk_surjective
    have : Algebra.Etale B (Bi i) := Algebra.Etale.of_isLocalizationAway (e i)
    exact Algebra.Etale.comp A B (Bi i)

end HenselianLocalRing
