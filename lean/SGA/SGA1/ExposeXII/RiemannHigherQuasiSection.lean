/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.BranchedCover
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite étale quasi-sections of dominant morphisms in characteristic `0`

`RiemannHigher.exists_finite_etale_quasiSection`: let `A ⊆ B` be domains, `A` integrally closed
of characteristic `0` and `B` of finite type over `A`. Then there are `t ≠ 0` in `A`, a domain `A'`
finite étale over `A[1/t]`, and an `A`-algebra map `B → A'`. Geometrically: a dominant morphism
`Spec B → Spec A` has a section after a finite étale surjective base change of a dense open
subset of `Spec A` (EGA IV 17.16.3 (ii) in characteristic `0`, for integral schemes).

Proof: a closed point of the generic fibre `Spec (B ⊗_A K)`, `K = Frac A`, has a residue field `L`
finite over `K` (Zariski's lemma), separable since the characteristic is `0`; a primitive element
of `L`, made integral over `A`, generates a finite `A`-subalgebra `S ⊆ L` with `L = S ⊗_A K`, so
that `S[1/H]` is standard étale over `A` for some `H ≠ 0` (generic étaleness,
`exists_isStandardEtale_localizationAway`), and the finitely many generators of `B` land in
`S[1/t]` for a suitable multiple `t` of `H`.

This is the quasi-section used in the induction step of XII.5.1 in higher dimension
(`SGA.SGA1.ExposeXII.RiemannHigher`, step 1).
-/

noncomputable section

open nonZeroDivisors Polynomial IntermediateField

namespace SGA.SGA1.ExposeXII.RiemannHigher

variable {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CharZero A]
  [CommRing B] [IsDomain B] [Algebra A B]

/-- The generic fibre `B ⊗_A K` of `A → B`, as the localization of `B` at the nonzero elements of
`A`. -/
abbrev GenericFibre (A B : Type) [CommRing A] [CommRing B] [Algebra A B] : Type :=
  Localization (Algebra.algebraMapSubmonoid B A⁰)

omit [IsIntegrallyClosed A] [CharZero A] in
lemma algebraMapSubmonoid_le_nonZeroDivisors (hinj : Function.Injective (algebraMap A B)) :
    Algebra.algebraMapSubmonoid B A⁰ ≤ B⁰ := by
  rintro _ ⟨a, ha, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  rw [ne_eq, ← map_zero (algebraMap A B)]
  exact hinj.ne (nonZeroDivisors.ne_zero ha)

omit [IsIntegrallyClosed A] [CharZero A] [IsDomain A] [IsDomain B] in
/-- The generic fibre of a finite type algebra is of finite type over the fraction field. -/
lemma finiteType_genericFibre [Algebra.FiniteType A B] :
    Algebra.FiniteType (FractionRing A) (GenericFibre A B) := by
  have : IsLocalization (A⁰.map (algebraMap A B)) (GenericFibre A B) :=
    inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid B A⁰) _)
  have := RingHom.finiteType_localizationPreserves (algebraMap A B) A⁰ (FractionRing A)
    (GenericFibre A B) (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact RingHom.finiteType_algebraMap.mp this

/-- **Finite étale quasi-sections** (EGA IV 17.16.3 (ii) for integral schemes in characteristic
`0`): let `A ⊆ B` be domains (`algebraMap A B` injective), `A` integrally closed of characteristic
`0` and `B` of finite type over `A`. There are `t ≠ 0` in `A`, a domain `A'` which is finite and
étale over `A[1/t]`, and an `A`-algebra map `B → A'`. -/
theorem exists_finite_etale_quasiSection [Algebra.FiniteType A B]
    (hinj : Function.Injective (algebraMap A B)) :
    ∃ t : A, t ≠ 0 ∧ ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A')
      (_ : Algebra (Localization.Away t) A') (_ : IsScalarTower A (Localization.Away t) A'),
      Module.Finite (Localization.Away t) A' ∧ Algebra.Etale (Localization.Away t) A' ∧
      Nonempty (B →ₐ[A] A') := by
  classical
  let K := FractionRing A
  let BK := GenericFibre A B
  have : IsDomain BK := IsLocalization.isDomain_of_le_nonZeroDivisors BK
    (algebraMapSubmonoid_le_nonZeroDivisors hinj)
  have := finiteType_genericFibre (A := A) (B := B)
  -- a closed point of the generic fibre and its residue field `L`, finite over `K`
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal BK
  let L := BK ⧸ 𝔪
  let : Field L := Ideal.Quotient.field 𝔪
  have : Algebra.FiniteType K L :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K 𝔪) Ideal.Quotient.mk_surjective
  have : Module.Finite K L := finite_of_finite_type_of_isJacobsonRing K L
  have : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective A K)
  have hAK : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  -- a primitive element, made integral over `A`
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element K L
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K A⁰
  have : Algebra.IsAlgebraic A L := Algebra.IsAlgebraic.trans A K L
  obtain ⟨a, ha, hint⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := A) θ).exists_integral_multiple
  set θ' := a • θ with hθ'
  have hKθ' : Algebra.adjoin K {θ'} = ⊤ := by
    have hθθ' : θ ∈ K⟮θ'⟯ := by
      have hane : algebraMap A L a ≠ 0 := by
        rw [ne_eq, ← map_zero (algebraMap A L)]
        exact hAK.ne ha
      have : θ = (algebraMap A L a)⁻¹ * θ' := by
        rw [hθ', Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ hane, one_mul]
      rw [this, IsScalarTower.algebraMap_apply A K L, ← map_inv₀]
      exact mul_mem (IntermediateField.algebraMap_mem _ _)
        (IntermediateField.mem_adjoin_simple_self K θ')
    have htop : K⟮θ'⟯ = ⊤ := eq_top_iff.mpr (hθ ▸ IntermediateField.adjoin_simple_le_iff.mpr hθθ')
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic θ'), htop, IntermediateField.top_toSubalgebra]
  -- the finite `A`-algebra `S = A[θ'] ⊆ L`, through which the generators of `B` factor up to
  -- denominators
  obtain ⟨gens, hgens⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A B).FG)
  let φ : B →ₐ[A] L := (Ideal.Quotient.mkₐ A 𝔪).comp (IsScalarTower.toAlgHom A B BK)
  obtain ⟨S, _, _, _, j, hj, _, hden⟩ : ∃ (S : Type) (_ : CommRing S) (_ : IsDomain S)
      (_ : Algebra A S) (j : S →ₐ[A] L), Function.Injective j ∧ Module.Finite A S ∧
      ∀ b : B, ∃ c : A⁰, ∃ y : S, j y = (c : A) • φ b := by
    refine ⟨Algebra.adjoin A {θ'}, inferInstance, inferInstance, inferInstance,
      (Algebra.adjoin A {θ'}).val, Subtype.val_injective,
      Algebra.finite_adjoin_simple_of_isIntegral hint, fun b ↦ ?_⟩
    obtain ⟨c, hc⟩ :=
      multiple_mem_adjoin_of_mem_localization_adjoin A⁰ K {θ'} (φ b) (hKθ' ▸ Algebra.mem_top)
    exact ⟨c, ⟨_, hc⟩, rfl⟩
  have hAS : Function.Injective (algebraMap A S) := fun x y h ↦
    hAK (by rw [← AlgHom.commutes j, ← AlgHom.commutes j, h])
  have : FaithfulSMul A S := (faithfulSMul_iff_algebraMap_injective A S).mpr hAS
  have : CharZero (FractionRing A) := ‹CharZero K›
  obtain ⟨H, hH, hst⟩ := exists_isStandardEtale_localizationAway A S
  choose c y hy using hden
  set t₀ : A := ∏ b ∈ gens, (c b : A) with ht₀
  have ht₀0 : t₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun b _ ↦ nonZeroDivisors.ne_zero (c b).2
  -- the finite étale algebra `A' = S[1/(t₀ H)]`
  let Sₕ := Localization.Away (algebraMap A S H)
  let A' := Localization.Away (algebraMap S Sₕ (algebraMap A S t₀))
  have hst' : Algebra.IsStandardEtale A A' :=
    Algebra.IsStandardEtale.of_isLocalizationAway (S := Sₕ) (algebraMap S Sₕ (algebraMap A S t₀))
  set t : A := t₀ * H with ht
  have ht0 : t ≠ 0 := mul_ne_zero ht₀0 hH
  have hAway : IsLocalization.Away (algebraMap A S t) A' := by
    rw [ht, map_mul]
    exact IsLocalization.Away.mul Sₕ A' (algebraMap A S H) (algebraMap A S t₀)
  have hSt : algebraMap A S t ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap A S)]
    exact hAS.ne ht0
  have : IsDomain A' := IsLocalization.isDomain_of_le_nonZeroDivisors A'
    (M := Submonoid.powers (algebraMap A S t)) (powers_le_nonZeroDivisors_of_noZeroDivisors hSt)
  have hu : IsUnit (algebraMap A A' t) := by
    rw [IsScalarTower.algebraMap_apply A S A']
    exact IsLocalization.Away.algebraMap_isUnit _
  let : Algebra (Localization.Away t) A' := (IsLocalization.Away.lift t hu).toAlgebra
  have : IsScalarTower A (Localization.Away t) A' := .of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq t hu x).symm
  have : Algebra.Etale A (Localization.Away t) := .of_isLocalizationAway t
  have : Algebra.Etale A A' := inferInstance
  have : Algebra.Etale (Localization.Away t) A' := .of_restrictScalars A (Localization.Away t) A'
  have : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers t)) A' := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    exact hAway
  have : Module.Finite (Localization.Away t) A' := .of_isLocalization A S (Submonoid.powers t)
  refine ⟨t, ht0, A', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, ⟨?_⟩⟩
  -- the map `B → A'`: `B → L` lands in the image of `A' ↪ L`
  have hunit (z : Submonoid.powers (algebraMap A S t)) : IsUnit (j z) := by
    obtain ⟨_, n, rfl⟩ := z
    change IsUnit (j ((algebraMap A S t) ^ n))
    rw [map_pow, AlgHom.commutes]
    refine (Ne.isUnit (G₀ := L) ?_).pow n
    rw [ne_eq, ← map_zero (algebraMap A L)]
    exact hAK.ne ht0
  let ι : A' →ₐ[A] L := IsLocalization.liftAlgHom (M := Submonoid.powers (algebraMap A S t))
    (f := j) hunit
  have hι : Function.Injective ι := by
    refine (IsLocalization.lift_injective_iff hunit).mpr fun x y ↦ ?_
    rw [(IsLocalization.injective A' (powers_le_nonZeroDivisors_of_noZeroDivisors hSt)).eq_iff]
    exact hj.eq_iff.symm
  have hrange (b : B) (hb : b ∈ gens) : φ b ∈ ι.range := by
    have hcu : IsUnit (algebraMap A A' (c b)) := isUnit_of_dvd_unit
      (map_dvd _ (Dvd.dvd.mul_right (Finset.dvd_prod_of_mem _ hb) H)) hu
    obtain ⟨v, hv⟩ := hcu
    refine ⟨↑v⁻¹ * algebraMap S A' (y b), ?_⟩
    have hιv : ι ↑v = algebraMap A L (c b) := by rw [hv, AlgHom.commutes]
    have hιv' : ι ↑v⁻¹ = (algebraMap A L (c b))⁻¹ := by
      rw [← hιv]
      exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    have hcb : algebraMap A L (c b) ≠ 0 := by
      rw [ne_eq, ← map_zero (algebraMap A L)]
      exact hAK.ne (nonZeroDivisors.ne_zero (c b).2)
    calc ι (↑v⁻¹ * algebraMap S A' (y b)) = ι ↑v⁻¹ * ι (algebraMap S A' (y b)) := map_mul ι _ _
      _ = (algebraMap A L (c b))⁻¹ * j (y b) := by
        rw [hιv']
        exact congrArg _ (IsLocalization.lift_eq hunit (y b))
      _ = φ b := by rw [hy, Algebra.smul_def, ← mul_assoc, inv_mul_cancel₀ hcb, one_mul]
  have hle : ⊤ ≤ ι.range.comap φ := by
    rw [← hgens, Algebra.adjoin_le_iff]
    exact fun b hb ↦ hrange b hb
  exact (AlgEquiv.ofInjective ι hι).symm.toAlgHom.comp
    (φ.codRestrict ι.range fun b ↦ hle Algebra.mem_top)

end SGA.SGA1.ExposeXII.RiemannHigher
