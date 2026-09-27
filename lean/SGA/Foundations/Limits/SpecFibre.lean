/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Limits.GeometricFiberCard

/-!
# The fibres of `Spec B ⟶ Spec A`

For an `A`-algebra `B` we express the invariants of the fibres of `Spec B ⟶ Spec A` in terms of
`B`:

* `AlgebraicGeometry.Scheme.geometricFiberCard_specMap`: the geometric number of points of the
  fibre at the image of `Spec Ω ⟶ Spec A` (`Ω` algebraically closed) is the number of `A`-algebra
  maps `B → Ω`;
* `AlgebraicGeometry.Scheme.residueDegree_specMap`: the residue field extensions are those of
  the primes of `B` over the primes of `A`;
* `AlgebraicGeometry.Scheme.fiberDegree_specMap_bot`: for `A` a domain with fraction field `K`
  and `K ⊗_A B` reduced and finite over `K`, the degree of the generic fibre is `[K ⊗_A B : K]`.
-/

universe u

open CategoryTheory Limits IsLocalRing
open scoped TensorProduct

noncomputable section

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

set_option backward.isDefEq.respectTransparency false in
/-- The `Ω`-points of `Spec B` over the `Ω`-point of `Spec A` given by `A → Ω` are the
`A`-algebra maps `B → Ω`. -/
def Scheme.pointsOverSpecEquiv (Ω : Type u) [Field Ω] [Algebra A Ω] :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).PointsOver
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω))) ≃ (B →ₐ[A] Ω) where
  toFun a :=
    { (Spec.preimage a.1).hom with
      commutes' r := by
        have h : Spec.map (CommRingCat.ofHom (algebraMap A B) ≫ Spec.preimage a.1) =
            Spec.map (CommRingCat.ofHom (algebraMap A Ω)) := by
          rw [Spec.map_comp, Spec.map_preimage]
          exact a.2
        exact congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of Ω ↦ φ r)
          (Spec.map_injective h) }
  invFun ψ := ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom), by
    rw [← Spec.map_comp]
    congr 1
    ext r
    exact ψ.commutes r⟩
  left_inv a := Subtype.ext (Spec.map_preimage a.1)
  right_inv ψ := by
    ext b
    change (Spec.preimage (Spec.map (CommRingCat.ofHom ψ.toRingHom))).hom b = ψ b
    rw [Spec.preimage_map]
    rfl

/-- The geometric number of points of the fibre of `Spec B ⟶ Spec A` at the image of
`Spec Ω ⟶ Spec A` (`Ω` algebraically closed) is the number of `A`-algebra maps `B → Ω`. -/
theorem Scheme.geometricFiberCard_specMap (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra A Ω]
    [LocallyQuasiFinite (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (hfin : (Spec.map (CommRingCat.ofHom (algebraMap A B)) ⁻¹'
      {Spec.map (CommRingCat.ofHom (algebraMap A Ω)) (closedPoint Ω)}).Finite) :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).geometricFiberCard
        (Spec.map (CommRingCat.ofHom (algebraMap A Ω)) (closedPoint Ω)) =
      Nat.card (B →ₐ[A] Ω) := by
  rw [← Scheme.Hom.natCard_pointsOver' _ _ hfin]
  exact Nat.card_congr (Scheme.pointsOverSpecEquiv Ω)

set_option backward.isDefEq.respectTransparency false in
/-- The residue field extensions of `Spec S ⟶ Spec R` at `P` is `κ(P ∩ R) → κ(P)`. -/
theorem Scheme.residueDegree_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S) (P : Spec S) :
    (Spec.map φ).residueDegree P =
      letI := (Ideal.ResidueField.map ((Spec.map φ) P).asIdeal P.asIdeal φ.hom rfl).toAlgebra
      Module.finrank ((Spec.map φ) P).asIdeal.ResidueField P.asIdeal.ResidueField := by
  let Q := (Spec.map φ) P
  let ρ := Ideal.ResidueField.map Q.asIdeal P.asIdeal φ.hom rfl
  have hsq : (Spec.map φ).residueFieldMap P ≫ (Scheme.Spec.residueFieldIso S P).hom =
      (Scheme.Spec.residueFieldIso R Q).hom ≫ CommRingCat.ofHom ρ := by
    rw [← Iso.inv_comp_eq]
    ext1
    refine Ideal.ResidueField.ringHom_ext ?_
    have h₁ := Scheme.Spec.algebraMap_residueFieldIso_inv R Q
    have h₂ := Scheme.Spec.algebraMap_residueFieldIso_inv S P
    rw [Scheme.germ_residue] at h₁ h₂
    have h₃ := Scheme.Γevaluation_naturality (Spec.map φ) P
    have h₄ : (Scheme.ΓSpecIso R).inv ≫ (Spec.map φ).appTop = φ ≫ (Scheme.ΓSpecIso S).inv := by
      rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Scheme.ΓSpecIso_naturality]
    have key : CommRingCat.ofHom (algebraMap R Q.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso R Q).inv ≫ (Spec.map φ).residueFieldMap P ≫
          (Scheme.Spec.residueFieldIso S P).hom =
        φ ≫ CommRingCat.ofHom (algebraMap S P.asIdeal.ResidueField) := by
      rw [reassoc_of% h₁, reassoc_of% h₃, reassoc_of% h₄, ← reassoc_of% h₂, Iso.inv_hom_id,
        Category.comp_id]
    change CommRingCat.Hom.hom (CommRingCat.ofHom (algebraMap R Q.asIdeal.ResidueField) ≫
      (Scheme.Spec.residueFieldIso R Q).inv ≫ (Spec.map φ).residueFieldMap P ≫
        (Scheme.Spec.residueFieldIso S P).hom) = ρ.comp (algebraMap R Q.asIdeal.ResidueField)
    rw [key]
    ext r
    exact (Ideal.ResidueField.map_algebraMap Q.asIdeal P.asIdeal φ.hom rfl r).symm
  exact finrank_eq_of_isIso _ _ _ _ hsq

set_option backward.isDefEq.respectTransparency false in
/-- For a finite reduced algebra `R` over a field `K`, the degree of the fibre of
`Spec R ⟶ Spec K` is `[R : K]`: `R` is the product of its residue fields. -/
theorem Scheme.fiberDegree_specMap_of_field {K R : Type u} [Field K] [CommRing R] [Algebra K R]
    [Module.Finite K R] [_root_.IsReduced R] (pt : Spec (.of K)) :
    (Spec.map (CommRingCat.ofHom (algebraMap K R))).fiberDegree pt = Module.finrank K R := by
  classical
  let f := Spec.map (CommRingCat.ofHom (algebraMap K R))
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  have : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  have hall (P : Spec (.of R)) : f P = pt := Subsingleton.elim _ _
  -- the residue degree at `P` is `[R ⧸ P : K]`
  have hdeg (P : Spec (.of R)) : f.residueDegree P = Module.finrank K (R ⧸ P.asIdeal) := by
    have : P.asIdeal.IsMaximal := (IsArtinianRing.isPrime_iff_isMaximal _).mp P.2
    rw [Scheme.residueDegree_specMap]
    let Q := f P
    let ρ := Ideal.ResidueField.map Q.asIdeal P.asIdeal (algebraMap K R) rfl
    let : Algebra Q.asIdeal.ResidueField P.asIdeal.ResidueField := ρ.toAlgebra
    let i : K ≃+* Q.asIdeal.ResidueField :=
      (Ideal.algEquivResidueFieldOfField Q.asIdeal).toRingEquiv
    let j : R ⧸ P.asIdeal ≃+* P.asIdeal.ResidueField := RingEquiv.ofBijective
      (algebraMap (R ⧸ P.asIdeal) P.asIdeal.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)
    refine (Algebra.finrank_eq_of_equiv_equiv i j ?_).symm
    ext k
    change ρ (algebraMap K Q.asIdeal.ResidueField k) =
      algebraMap (R ⧸ P.asIdeal) P.asIdeal.ResidueField
        (Ideal.Quotient.mk _ (algebraMap K R k))
    rw [Ideal.ResidueField.map_algebraMap, Ideal.algebraMap_quotient_residueField_mk]
  -- reindex by the maximal ideals
  let e : f ⁻¹' {pt} ≃ MaximalSpectrum R :=
    (Equiv.subtypeUnivEquiv fun P ↦ hall P).trans
      (IsArtinianRing.primeSpectrumEquivMaximalSpectrum (R := R))
  rw [Scheme.Hom.fiberDegree, ← finsum_comp_equiv e.symm, finsum_eq_sum_of_fintype]
  have hsum : ∑ I : MaximalSpectrum R, f.residueDegree (e.symm I).1 =
      ∑ I : MaximalSpectrum R, Module.finrank K (R ⧸ I.asIdeal) :=
    Finset.sum_congr rfl fun I _ ↦ hdeg _
  rw [hsum, ← Module.finrank_pi_fintype]
  exact ((IsArtinianRing.equivPi R).restrictScalars K).toLinearEquiv.finrank_eq.symm

set_option backward.isDefEq.respectTransparency false in
/-- Let `A` be a domain with fraction field `K` and `B` an `A`-algebra with `K ⊗_A B` finite and
reduced over `K`. The degree of the generic fibre of `Spec B ⟶ Spec A` is `[K ⊗_A B : K]`. -/
theorem Scheme.fiberDegree_specMap_bot [IsDomain A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] [Module.Finite K (K ⊗[A] B)] [_root_.IsReduced (K ⊗[A] B)] :
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).fiberDegree ⟨⊥, Ideal.isPrime_bot⟩ =
      Module.finrank K (K ⊗[A] B) := by
  have hpo := CommRingCat.isPushout_tensorProduct A K B
  have hpb := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  have : IsPreimmersion (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors A)
  let pt : Spec (.of K) := ⟨⊥, Ideal.isPrime_bot⟩
  have hpt : Spec.map (CommRingCat.ofHom (algebraMap A K)) pt = ⟨⊥, Ideal.isPrime_bot⟩ := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (algebraMap A K) ⊥ = ⊥
    rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).mp
      (IsFractionRing.injective A K)]
  rw [← hpt, ← Scheme.Hom.fiberDegree_of_isPullback _ hpb pt]
  exact Scheme.fiberDegree_specMap_of_field (K := K) (R := K ⊗[A] B) pt

omit [CommRing B] [Algebra A B] in
/-- For a reduced torsion-free algebra `B` over a domain `A` with fraction field `K`, the
algebra `K ⊗_A B` (a localization of `B`) is reduced. -/
lemma isReduced_tensorProduct_of_isTorsionFree {B : Type*} [CommRing B] [Algebra A B] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K] [_root_.IsReduced B]
    [Module.IsTorsionFree A B] : _root_.IsReduced (K ⊗[A] B) := by
  refine ⟨fun t ⟨n, hn⟩ ↦ ?_⟩
  obtain ⟨⟨b, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors A) (TensorProduct.mk A K B 1) t
  have hs' : algebraMap A K s • t = 1 ⊗ₜ b := by
    rw [algebraMap_smul]
    exact hs
  have hs0 : algebraMap A K s ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero s.2)
  have hbn : (1 : K) ⊗ₜ[A] (b ^ n) = 0 := by
    rw [← one_pow n, ← Algebra.TensorProduct.tmul_pow, ← hs', smul_pow, hn, smul_zero]
  have hb : b ^ n = 0 := by
    have h' : TensorProduct.mk A K B 1 (b ^ n) = 0 := hbn
    rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors A)] at h'
    obtain ⟨⟨s', hs''⟩, h''⟩ := h'
    exact (smul_eq_zero.mp h'').resolve_left (nonZeroDivisors.ne_zero hs'')
  have hb0 : b = 0 := IsReduced.eq_zero b ⟨n, hb⟩
  rw [hb0, TensorProduct.tmul_zero] at hs'
  rw [← inv_smul_smul₀ hs0 t, hs', smul_zero]

end AlgebraicGeometry
