/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.HenselianFiniteEtale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Finite and integral algebras over a henselian local ring

Let `A` be a henselian local ring with residue field `k` and `B` an integral `A`-algebra.

* `HenselianLocalRing.exists_isIdempotentElem_lift`: every idempotent of `k ⊗_A B` lifts to an
  idempotent of `B` (Stacks 04GG (6)). A lift `b` of the idempotent is a root of a monic `p`; in
  `k[X]/(p̄)` the idempotent `ε̄ ≡ 1 mod (X - 1)^m`, `ε̄ ≡ 0` modulo the rest of `p̄`, lifts to the
  finite free algebra `A[X]/(p)` (`existsUnique_isIdempotentElem_lift`), whose image in `B` is the
  required idempotent.
* `HenselianLocalRing.exists_isIdempotentElem_notMem_iff` (`B` finite) and
  `HenselianLocalRing.exists_isIdempotentElem_notMem_iff_of_isOpen` (`B` integral, the prime
  isolated in the closed fibre): for a prime `𝔮` of `B` over the maximal ideal of `A` there is an
  idempotent of `B` lying outside `𝔮` and in every other prime over the maximal ideal. Hence a
  finite `B` is a finite product of local rings (Stacks 04GG (10)).
* `AlgebraicGeometry.exists_isClopen_of_isFinite`,
  `AlgebraicGeometry.exists_isClopen_of_isIntegralHom`: the scheme versions: a point of the
  closed fibre has a clopen neighbourhood meeting the closed fibre only in that point.
* `AlgebraicGeometry.exists_isClopen_of_locallyQuasiFinite`: the same for a separated,
  quasi-compact, locally quasi-finite morphism of finite type (Stacks 04GJ), through its relative
  normalization, in which it is an open subscheme (Zariski's main theorem).
-/

universe u v

open CategoryTheory Polynomial IsLocalRing TensorProduct

noncomputable section

namespace IsIdempotentElem

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R] {e : R}

/-- A polynomial at an idempotent `e`: `q(e) = q(1) e + q(0) (1 - e)`. -/
lemma aeval_eq (he : IsIdempotentElem e) (q : k[X]) :
    aeval e q = q.eval 1 • e + q.eval 0 • (1 - e) := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, hp, hq, eval_add, eval_add, add_smul, add_smul]
    abel
  | monomial n c =>
    cases n with
    | zero =>
      rw [aeval_monomial, pow_zero, mul_one, eval_monomial, eval_monomial, pow_zero, pow_zero,
        mul_one, ← smul_add, add_sub_cancel, Algebra.algebraMap_eq_smul_one]
    | succ n =>
      rw [aeval_monomial, he.pow_succ_eq, eval_monomial, eval_monomial, one_pow, mul_one,
        zero_pow n.succ_ne_zero, mul_zero, zero_smul, add_zero, Algebra.smul_def]

end IsIdempotentElem

namespace HenselianLocalRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A] {B : Type v} [CommRing B] [Algebra A B]

/-- A polynomial over `A` whose reduction vanishes has `1 ⊗ h(t) = 0` in `k ⊗_A C`. -/
lemma one_tmul_aeval_eq_zero {C : Type*} [CommRing C] [Algebra A C] (t : C) (h : A[X])
    (hh : h.map (algebraMap A (ResidueField A)) = 0) :
    (1 : ResidueField A) ⊗ₜ[A] aeval t h = 0 := by
  rw [← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply,
    ← aeval_map_algebraMap (ResidueField A), hh, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- Idempotents lift from `k ⊗_A B` to an integral (for instance finite) algebra `B` over a
henselian local ring `A` with residue field `k` (Stacks 04GG (6)). -/
theorem exists_isIdempotentElem_lift [Algebra.IsIntegral A B]
    {e₀ : ResidueField A ⊗[A] B} (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧ 1 ⊗ₜ e = e₀ := by
  classical
  let k := ResidueField A
  by_cases h0 : e₀ = 0
  · exact ⟨0, .zero, by rw [h0, TensorProduct.tmul_zero]⟩
  by_cases h1 : e₀ = 1
  · exact ⟨1, .one, by rw [h1]; rfl⟩
  -- a lift `b` of `e₀`, a root of a monic `p`
  obtain ⟨b, hb⟩ := Algebra.TensorProduct.includeRight_surjective (T := B)
    (residue_surjective (R := A)) e₀
  obtain ⟨p, hpm, hpb⟩ : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  let pbar := p.map (algebraMap A k)
  have hpbar : aeval e₀ pbar = 0 := by
    rw [aeval_map_algebraMap, ← hb, aeval_algHom_apply]
    change Algebra.TensorProduct.includeRight (eval₂ (algebraMap A B) b p) = 0
    rw [hpb, map_zero]
  have hev := he₀.aeval_eq pbar
  rw [hpbar] at hev
  have h01 : e₀ * (1 - e₀) = 0 := by rw [mul_sub, mul_one, he₀.eq, sub_self]
  have hp1 : pbar.eval 1 = 0 := by
    have h := congrArg (e₀ * ·) hev
    simp only [mul_zero, mul_add, mul_smul_comm, he₀.eq, h01, smul_zero, add_zero] at h
    exact (smul_eq_zero.mp h.symm).resolve_right h0
  have hp0 : pbar.eval 0 = 0 := by
    have h := congrArg ((1 - e₀) * ·) hev
    have h10 : (1 - e₀) * e₀ = 0 := by rw [mul_comm, h01]
    have h11 : (1 - e₀) * (1 - e₀) = 1 - e₀ := (he₀.one_sub).eq
    simp only [mul_zero, mul_add, mul_smul_comm, h10, h11, smul_zero, zero_add] at h
    exact (smul_eq_zero.mp h.symm).resolve_right (sub_ne_zero.mpr (Ne.symm h1))
  -- `pbar = (X - 1)^m r` with `r(1) ≠ 0`, `r(0) = 0`
  have hpbar0 : pbar ≠ 0 := (hpm.map _).ne_zero
  obtain ⟨r, hpr, hr⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd pbar hpbar0 1
  have hm : 0 < rootMultiplicity 1 pbar := (rootMultiplicity_pos hpbar0).mpr hp1
  have hcop : IsCoprime ((X - C 1) ^ rootMultiplicity 1 pbar) r :=
    ((irreducible_X_sub_C (1 : k)).coprime_iff_not_dvd.mpr hr).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hr0 : r.eval 0 = 0 := by
    have h := congrArg (eval 0) hpr
    rw [hp0, eval_mul, eval_pow, eval_sub, eval_X, eval_C] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (pow_ne_zero _ (by simp))
  -- the idempotent `εbar = v r` of `k[X]/(pbar)`, with `εbar(1) = 1`, `εbar(0) = 0`
  let εbar : k[X] := v * r
  have hε1 : εbar.eval 1 = 1 := by
    have h := congrArg (eval 1) huv
    rw [eval_add, eval_mul, eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_self,
      zero_pow hm.ne', mul_zero, zero_add, eval_one] at h
    rw [eval_mul, h]
  have hε0 : εbar.eval 0 = 0 := by rw [eval_mul, hr0, mul_zero]
  have hεidem : εbar * εbar - εbar = -(u * v) * pbar := by
    rw [hpr]
    linear_combination (v * r) * huv
  -- lifts to `A[X]`
  obtain ⟨ε, hε⟩ := map_surjective (algebraMap A k) residue_surjective εbar
  obtain ⟨w, hw⟩ := map_surjective (algebraMap A k) residue_surjective (-(u * v))
  -- the finite free algebra `T = A[X]/(p)`
  let T := AdjoinRoot p
  let pb := AdjoinRoot.powerBasis' hpm
  have : Module.Free A T := .of_basis pb.basis
  have : Module.Finite A T := pb.finite
  let t := AdjoinRoot.root p
  let ε₀ : k ⊗[A] T := 1 ⊗ₜ aeval t ε
  have hε₀ : IsIdempotentElem ε₀ := by
    have h := one_tmul_aeval_eq_zero t (ε * ε - ε - w * p) (by
      rw [Polynomial.map_sub, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, hε, hw,
        hεidem, sub_self])
    rw [map_sub, map_sub, map_mul, map_mul, AdjoinRoot.aeval_eq p, AdjoinRoot.mk_self, mul_zero,
      sub_zero] at h
    change (1 ⊗ₜ[A] aeval t ε) * (1 ⊗ₜ[A] aeval t ε) = 1 ⊗ₜ[A] aeval t ε
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← sub_eq_zero, ← TensorProduct.tmul_sub]
    exact h
  obtain ⟨eT, heT, heT'⟩ := (existsUnique_isIdempotentElem_lift (A := A) T hε₀).exists
  let φ : T →ₐ[A] B := AdjoinRoot.liftAlgHom p (Algebra.ofId A B) b hpb
  refine ⟨φ eT, heT.map φ, ?_⟩
  have h := congrArg (Algebra.TensorProduct.map (AlgHom.id A k) φ) heT'
  rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply] at h
  rw [h, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ← aeval_algHom_apply,
    AdjoinRoot.liftAlgHom_root, ← Algebra.TensorProduct.includeRight_apply, ← aeval_algHom_apply,
    Algebra.TensorProduct.includeRight_apply, show (1 : k) ⊗ₜ[A] b = e₀ from hb,
    ← aeval_map_algebraMap k, hε, he₀.aeval_eq,
    hε1, hε0, one_smul, zero_smul, add_zero]

/-- Idempotents lift from `k ⊗_A B` to a finite algebra `B` over a henselian local ring `A`
(the finite case of `HenselianLocalRing.exists_isIdempotentElem_lift`). -/
theorem exists_isIdempotentElem_lift_of_finite [Module.Finite A B]
    {e₀ : ResidueField A ⊗[A] B} (he₀ : IsIdempotentElem e₀) :
    ∃ e : B, IsIdempotentElem e ∧ 1 ⊗ₜ e = e₀ :=
  exists_isIdempotentElem_lift he₀

set_option backward.isDefEq.respectTransparency false in
/-- Over a henselian local ring `A`, let `B` be a finite `A`-algebra and `𝔮` a prime of `B` over
the maximal ideal. There is an idempotent of `B` outside `𝔮` and inside every other prime of `B`
over the maximal ideal (Stacks 04GG (10): `B` is a finite product of local rings). -/
theorem exists_isIdempotentElem_notMem_iff [Module.Finite A B] (q : PrimeSpectrum B)
    (hq : q.asIdeal.comap (algebraMap A B) = maximalIdeal A) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ q' : PrimeSpectrum B,
      q'.asIdeal.comap (algebraMap A B) = maximalIdeal A → (e ∉ q'.asIdeal ↔ q' = q) := by
  classical
  let I := (maximalIdeal A).map (algebraMap A B)
  let E : (B ⧸ I) ≃+* ResidueField A ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).toRingEquiv
  have : IsArtinianRing (ResidueField A ⊗[A] B) :=
    isArtinian_of_tower (ResidueField A) inferInstance
  have : IsArtinianRing (B ⧸ I) := E.symm.isArtinianRing
  -- points of `Spec (B ⧸ I)` are the primes of `B` over the maximal ideal
  have hI (q' : PrimeSpectrum B) (hq' : q'.asIdeal.comap (algebraMap A B) = maximalIdeal A) :
      I ≤ q'.asIdeal := Ideal.map_le_iff_le_comap.mpr hq'.ge
  let bar (q' : PrimeSpectrum B) (hq' : q'.asIdeal.comap (algebraMap A B) = maximalIdeal A) :
      PrimeSpectrum (B ⧸ I) :=
    ⟨q'.asIdeal.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI q' hq')⟩
  -- the idempotent of `B ⧸ I` cutting out the point over `q`
  let s : TopologicalSpace.Clopens (PrimeSpectrum (B ⧸ I)) := ⟨{bar q hq}, isClopen_discrete _⟩
  let ebar := PrimeSpectrum.isIdempotentElemEquivClopens.symm s
  have hebar (P : PrimeSpectrum (B ⧸ I)) : ebar.1 ∉ P.asIdeal ↔ P = bar q hq := by
    have h := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum (B ⧸ I)) ↦ P ∈ U)
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s)
    exact h.to_iff
  obtain ⟨e, he, he'⟩ := exists_isIdempotentElem_lift (A := A) (B := B)
    (e₀ := E ebar.1) (ebar.2.map E)
  have hmk : Ideal.Quotient.mk I e = ebar.1 := E.injective (by
    rw [← he']
    rfl)
  refine ⟨e, he, fun q' hq' ↦ ?_⟩
  have h₁ : e ∉ q'.asIdeal ↔ ebar.1 ∉ (bar q' hq').asIdeal := by
    rw [← hmk]
    exact not_congr (Ideal.mem_quotient_iff_mem (hI q' hq')).symm
  rw [h₁, hebar]
  refine ⟨fun h ↦ PrimeSpectrum.ext ?_, fun h ↦ by subst h; rfl⟩
  have h₂ := congrArg (fun P : PrimeSpectrum (B ⧸ I) ↦ P.asIdeal.comap (Ideal.Quotient.mk I)) h
  simp only [bar, Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
    sup_eq_left.mpr (hI q' hq'), sup_eq_left.mpr (hI q hq)] at h₂
  exact h₂

set_option backward.isDefEq.respectTransparency false in
/-- Over a henselian local ring `A`, let `B` be an integral `A`-algebra and `𝔮` a prime of `B`
over the maximal ideal which is isolated among these primes (it has an open neighbourhood
containing no other prime over the maximal ideal). There is an idempotent of `B` outside `𝔮` and
inside every other prime of `B` over the maximal ideal. -/
theorem exists_isIdempotentElem_notMem_iff_of_isOpen [Algebra.IsIntegral A B]
    (q : PrimeSpectrum B) (hq : q.asIdeal.comap (algebraMap A B) = maximalIdeal A)
    (O : Set (PrimeSpectrum B)) (hO : IsOpen O) (hqO : q ∈ O)
    (hO' : ∀ q' ∈ O, q'.asIdeal.comap (algebraMap A B) = maximalIdeal A → q' = q) :
    ∃ e : B, IsIdempotentElem e ∧ ∀ q' : PrimeSpectrum B,
      q'.asIdeal.comap (algebraMap A B) = maximalIdeal A → (e ∉ q'.asIdeal ↔ q' = q) := by
  classical
  let I := (maximalIdeal A).map (algebraMap A B)
  let E : (B ⧸ I) ≃+* ResidueField A ⊗[A] B :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B (maximalIdeal A)).toRingEquiv
  have hI (q' : PrimeSpectrum B) (hq' : q'.asIdeal.comap (algebraMap A B) = maximalIdeal A) :
      I ≤ q'.asIdeal := Ideal.map_le_iff_le_comap.mpr hq'.ge
  let bar (q' : PrimeSpectrum B) (hq' : q'.asIdeal.comap (algebraMap A B) = maximalIdeal A) :
      PrimeSpectrum (B ⧸ I) :=
    ⟨q'.asIdeal.map (Ideal.Quotient.mk I), Ideal.map_isPrime_of_surjective
      Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hI q' hq')⟩
  have hcomap (q' : PrimeSpectrum B) (hq' : q'.asIdeal.comap (algebraMap A B) = maximalIdeal A) :
      PrimeSpectrum.comap (Ideal.Quotient.mk I) (bar q' hq') = q' := by
    ext1
    simp only [PrimeSpectrum.comap_asIdeal, bar]
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_eq_left.mpr (hI q' hq')]
  -- every point of `Spec (B ⧸ I)` lies over the maximal ideal
  have hover (P : PrimeSpectrum (B ⧸ I)) :
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).asIdeal.comap (algebraMap A B) =
        maximalIdeal A := by
    refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.comap_ne_top _
      (PrimeSpectrum.comap (Ideal.Quotient.mk I) P).2.ne_top)) ?_
    refine Ideal.map_le_iff_le_comap.mp (le_trans ?_ (Ideal.ker_le_comap (Ideal.Quotient.mk I)))
    rw [Ideal.mk_ker]
  -- the point over `q` is isolated and closed in `Spec (B ⧸ I)`
  have hsingle : ({bar q hq} : Set (PrimeSpectrum (B ⧸ I))) =
      PrimeSpectrum.comap (Ideal.Quotient.mk I) ⁻¹' O := by
    ext P
    constructor
    · rintro rfl
      change PrimeSpectrum.comap (Ideal.Quotient.mk I) (bar q hq) ∈ O
      rw [hcomap q hq]
      exact hqO
    · intro hP
      have h := hO' _ hP (hover P)
      rw [← hcomap q hq] at h
      exact PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h
  have hmax : (bar q hq).asIdeal.IsMaximal := by
    have : (bar q hq).asIdeal.IsPrime := (bar q hq).2
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A) _ ?_
    change ((bar q hq).asIdeal.comap (algebraMap A (B ⧸ I))).IsMaximal
    rw [IsScalarTower.algebraMap_eq A B (B ⧸ I), ← Ideal.comap_comap]
    change ((PrimeSpectrum.comap (Ideal.Quotient.mk I) (bar q hq)).asIdeal.comap
      (algebraMap A B)).IsMaximal
    rw [hcomap q hq, hq]
    infer_instance
  let s : TopologicalSpace.Clopens (PrimeSpectrum (B ⧸ I)) :=
    ⟨{bar q hq}, ⟨(PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hmax,
      hsingle ▸ hO.preimage (PrimeSpectrum.continuous_comap (Ideal.Quotient.mk I))⟩⟩
  let ebar := PrimeSpectrum.isIdempotentElemEquivClopens.symm s
  have hebar (P : PrimeSpectrum (B ⧸ I)) : ebar.1 ∉ P.asIdeal ↔ P = bar q hq := by
    have h := congrArg (fun U : TopologicalSpace.Opens (PrimeSpectrum (B ⧸ I)) ↦ P ∈ U)
      (PrimeSpectrum.basicOpen_isIdempotentElemEquivClopens_symm s)
    exact h.to_iff
  obtain ⟨e, he, he'⟩ := exists_isIdempotentElem_lift (A := A) (B := B)
    (e₀ := E ebar.1) (ebar.2.map E)
  have hmk : Ideal.Quotient.mk I e = ebar.1 := E.injective (by
    rw [← he']
    rfl)
  refine ⟨e, he, fun q' hq' ↦ ?_⟩
  have h₁ : e ∉ q'.asIdeal ↔ ebar.1 ∉ (bar q' hq').asIdeal := by
    rw [← hmk]
    exact not_congr (Ideal.mem_quotient_iff_mem (hI q' hq')).symm
  rw [h₁, hebar]
  refine ⟨fun h ↦ ?_, fun h ↦ by subst h; rfl⟩
  rw [← hcomap q' hq', ← hcomap q hq, h]

end HenselianLocalRing

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Let `A` be a henselian local ring and `p : X ⟶ Spec A` finite. Every point `x` of the closed
fibre has a clopen neighbourhood which meets the closed fibre only in `x` (Stacks 04GG (10)). -/
theorem exists_isClopen_of_isFinite {A : CommRingCat.{u}} [HenselianLocalRing A] {X : Scheme.{u}}
    (p : X ⟶ Spec A) [IsFinite p] (x : X) (hx : p x = closedPoint A) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ x' ∈ U, p x' = closedPoint A → x' = x := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let φ : A ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso A).inv ≫ p.appTop
  have hp : p = X.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let _ : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have : Module.Finite A Γ(X, ⊤) := by
    have : IsFinite (Spec.map φ) := by
      have : Spec.map φ = X.isoSpec.inv ≫ p := by rw [hp, Iso.inv_hom_id_assoc]
      rw [this]
      infer_instance
    exact (IsFinite.SpecMap_iff _).mp this
  have hpt (z : X) : p z = PrimeSpectrum.comap φ.hom (X.isoSpec.hom z) := by
    rw [hp]
    rfl
  have hover (z : X) (hz : p z = closedPoint A) :
      (X.isoSpec.hom z).asIdeal.comap (algebraMap A Γ(X, ⊤)) = maximalIdeal A := by
    rw [hpt] at hz
    exact congrArg PrimeSpectrum.asIdeal hz
  obtain ⟨e, he, hq⟩ := HenselianLocalRing.exists_isIdempotentElem_notMem_iff
    (X.isoSpec.hom x) (hover x hx)
  let V : Set (PrimeSpectrum Γ(X, ⊤)) := PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩
  let U : Set X := X.isoSpec.hom ⁻¹' V
  refine ⟨U, (PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen.preimage
    X.isoSpec.hom.continuous, (hq _ (hover x hx)).mpr rfl, fun x' hx' h ↦ ?_⟩
  have h' := (hq _ (hover x' h)).mp hx'
  have := congrArg X.isoSpec.inv h'
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at this
  simpa using this

set_option backward.isDefEq.respectTransparency false in
/-- Let `A` be a henselian local ring and `p : X ⟶ Spec A` integral. Every point `x` of the closed
fibre which is isolated in it (some open neighbourhood of `x` contains no other point of the
closed fibre) has a clopen neighbourhood which meets the closed fibre only in `x`
(Stacks 04GG (6)). -/
theorem exists_isClopen_of_isIntegralHom {A : CommRingCat.{u}} [HenselianLocalRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec A) [IsIntegralHom p] (x : X) (hx : p x = closedPoint A)
    (O : Set X) (hO : IsOpen O) (hxO : x ∈ O) (hO' : ∀ x' ∈ O, p x' = closedPoint A → x' = x) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ ∀ x' ∈ U, p x' = closedPoint A → x' = x := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let φ : A ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso A).inv ≫ p.appTop
  have hp : p = X.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let _ : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have : Algebra.IsIntegral A Γ(X, ⊤) := by
    have : IsIntegralHom (Spec.map φ) := by
      have : Spec.map φ = X.isoSpec.inv ≫ p := by rw [hp, Iso.inv_hom_id_assoc]
      rw [this]
      infer_instance
    exact ⟨IsIntegralHom.SpecMap_iff.mp this⟩
  have hpt (z : X) : p z = PrimeSpectrum.comap φ.hom (X.isoSpec.hom z) := by
    rw [hp]
    rfl
  have hover (z : X) (hz : p z = closedPoint A) :
      (X.isoSpec.hom z).asIdeal.comap (algebraMap A Γ(X, ⊤)) = maximalIdeal A := by
    rw [hpt] at hz
    exact congrArg PrimeSpectrum.asIdeal hz
  have hinv (z : X) : X.isoSpec.inv (X.isoSpec.hom z) = z := by
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    rfl
  have hinv' (q : Spec Γ(X, ⊤)) : X.isoSpec.hom (X.isoSpec.inv q) = q := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  obtain ⟨e, he, hq⟩ := HenselianLocalRing.exists_isIdempotentElem_notMem_iff_of_isOpen
    (X.isoSpec.hom x) (hover x hx) (X.isoSpec.inv ⁻¹' O)
    (hO.preimage X.isoSpec.inv.continuous) (by rw [Set.mem_preimage, hinv]; exact hxO)
    (fun q' hq'O hq' ↦ by
      have h := hO' _ hq'O (by rw [hpt, hinv']; exact PrimeSpectrum.ext hq')
      rw [← hinv' q', h])
  let V : Set (PrimeSpectrum Γ(X, ⊤)) := PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩
  let U : Set X := X.isoSpec.hom ⁻¹' V
  refine ⟨U, (PrimeSpectrum.isIdempotentElemEquivClopens ⟨e, he⟩).isClopen.preimage
    X.isoSpec.hom.continuous, (hq _ (hover x hx)).mpr rfl, fun x' hx' h ↦ ?_⟩
  have h' := (hq _ (hover x' h)).mp hx'
  rw [← hinv x', h', hinv]

set_option backward.isDefEq.respectTransparency false in
/-- A point over the closed point of an integral scheme over the spectrum of a local ring is
closed (a prime over a maximal ideal in an integral extension is maximal). -/
lemma isClosed_singleton_of_isIntegralHom {A : CommRingCat.{u}} [IsLocalRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec A) [IsIntegralHom p] (x : X) (hx : p x = closedPoint A) :
    IsClosed ({x} : Set X) := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let φ : A ⟶ Γ(X, ⊤) := (Scheme.ΓSpecIso A).inv ≫ p.appTop
  have hp : p = X.isoSpec.hom ≫ Spec.map φ := by
    rw [Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
      Scheme.isoSpec_Spec_hom, Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
      Category.comp_id]
  let _ : Algebra A Γ(X, ⊤) := φ.hom.toAlgebra
  have : Algebra.IsIntegral A Γ(X, ⊤) := by
    have : IsIntegralHom (Spec.map φ) := by
      have : Spec.map φ = X.isoSpec.inv ≫ p := by rw [hp, Iso.inv_hom_id_assoc]
      rw [this]
      infer_instance
    exact ⟨IsIntegralHom.SpecMap_iff.mp this⟩
  have hq : (X.isoSpec.hom x).asIdeal.comap (algebraMap A Γ(X, ⊤)) = maximalIdeal A := by
    have h : p x = PrimeSpectrum.comap φ.hom (X.isoSpec.hom x) := by rw [hp]; rfl
    rw [hx] at h
    exact (congrArg PrimeSpectrum.asIdeal h).symm
  have : (X.isoSpec.hom x).asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (by rw [hq]; infer_instance)
  have hc : IsClosed ({X.isoSpec.hom x} : Set (PrimeSpectrum Γ(X, ⊤))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr this
  convert hc.preimage X.isoSpec.hom.continuous using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  refine ⟨fun h ↦ h ▸ rfl, fun h ↦ ?_⟩
  have h' := congrArg X.isoSpec.inv h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Iso.hom_inv_id] at h'
  simpa using h'

set_option backward.isDefEq.respectTransparency false in
/-- **Quasi-finite schemes over a henselian local ring** (Stacks 04GJ, in the form of the
decomposition into pieces around the closed fibre). Let `A` be a henselian local ring and
`p : X ⟶ Spec A` separated, quasi-compact, locally quasi-finite and locally of finite type.
Every point `x` of the closed fibre has a clopen neighbourhood `U` meeting the closed fibre only in
`x`, whose image in the relative normalization of `Spec A` in `X` (in which `X` is open, by
Zariski's main theorem) is closed. -/
theorem exists_isClopen_of_locallyQuasiFinite {A : CommRingCat.{u}} [HenselianLocalRing A]
    {X : Scheme.{u}} (p : X ⟶ Spec A) [LocallyOfFiniteType p] [QuasiCompact p]
    [LocallyQuasiFinite p] [IsSeparated p] (x : X) (hx : p x = closedPoint A) :
    ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ (∀ x' ∈ U, p x' = closedPoint A → x' = x) ∧
      IsClosed (p.toNormalization '' U) := by
  classical
  let ι := p.toNormalization
  let π := p.fromNormalization
  have hιπ : ι ≫ π = p := p.toNormalization_fromNormalization
  have hπ (z : X) : π (ι z) = p z := by rw [← Scheme.Hom.comp_apply, hιπ]
  let F := p ⁻¹' {closedPoint A}
  have hF : F.Finite := p.finite_preimage_singleton _
  -- the other points of the closed fibre, as closed points of the normalization
  let G := ⋃ z ∈ F \ {x}, ({ι z} : Set p.normalization)
  have hG : IsClosed G := (hF.sdiff).isClosed_biUnion fun z hz ↦
    isClosed_singleton_of_isIntegralHom π (ι z) (by rw [hπ]; exact hz.1)
  let O := Set.range ι \ G
  have hO : IsOpen O := ι.isOpenEmbedding.isOpen_range.sdiff hG
  have hxO : ι x ∈ O := by
    refine ⟨⟨x, rfl⟩, fun h ↦ ?_⟩
    simp only [G, Set.mem_iUnion, Set.mem_singleton_iff] at h
    obtain ⟨z, hz, hzx⟩ := h
    exact hz.2 (ι.isOpenEmbedding.injective hzx).symm
  have hO' : ∀ z' ∈ O, π z' = closedPoint A → z' = ι x := by
    rintro _ ⟨⟨u, rfl⟩, huG⟩ hu
    by_contra hne
    refine huG ?_
    simp only [G, Set.mem_iUnion, Set.mem_singleton_iff]
    have huF : u ∈ F := by
      change p u = closedPoint A
      rw [← hπ]
      exact hu
    exact ⟨u, ⟨huF, fun h ↦ hne (by rw [Set.mem_singleton_iff.mp h])⟩, rfl⟩
  obtain ⟨V, hVc, hxV, hV⟩ :=
    exists_isClopen_of_isIntegralHom π (ι x) (by rw [hπ, hx]) O hO hxO hO'
  have hVsub : V ⊆ Set.range ι := by
    intro v hvV
    by_contra hvr
    have hC : IsClosed (V \ Set.range ι) := hVc.1.sdiff ι.isOpenEmbedding.isOpen_range
    obtain ⟨c, ⟨hcV, hcr⟩, hc⟩ : closedPoint A ∈ π '' (V \ Set.range ι) :=
      (specializes_closedPoint (π v)).mem_closed (π.isClosedMap _ hC) ⟨v, ⟨hvV, hvr⟩, rfl⟩
    exact hcr (hV c hcV hc ▸ ⟨x, rfl⟩)
  refine ⟨ι ⁻¹' V, hVc.preimage ι.continuous, hxV, fun x' hx' h ↦
    ι.isOpenEmbedding.injective (hV _ hx' (by rw [hπ, h])), ?_⟩
  rw [Set.image_preimage_eq_of_subset hVsub]
  exact hVc.1

end AlgebraicGeometry
