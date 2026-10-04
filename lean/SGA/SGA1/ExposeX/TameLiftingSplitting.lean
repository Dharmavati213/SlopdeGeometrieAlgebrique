/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import SGA.SGA1.ExposeX.TameLiftingUnramified

/-!
# An integral closure is étale if the extension splits over an unramified complete extension

Let `B` be a discrete valuation ring with fraction field `K`, `L` a finite separable extension of
`K` and `C` the integral closure of `B` in `L`. Let `B → R` be a local injective homomorphism to a
discrete valuation ring with `𝔪_B R = 𝔪_R` and `κ(R)/κ(B)` separable (in the application `R` is the
completion of the strict henselization of `B`), and `F` the fraction field of `R`. If every
`K`-embedding of `L` into an algebraically closed extension of `F` takes values in `F`
(`EmbeddingsFactorThrough K L F`, i.e. `L ⊗_K F` is a product of copies of `F`), then `C` is étale
over `B` (`etale_integralClosure_of_embeddingsFactorThrough`).

This is the classical criterion "a finite separable extension is unramified at `B` iff it splits
over the completion of the strict henselization of `B`", in the direction needed for the second part
of SGA 1 XIII.4.4 over a regular base: there `L` is the function field of an étale covering of the
generic fibre, and the splitting comes from the extension of the covering over `X ×_S R` given by
the core of X.3.8.

* `exists_ringHom_comap_eq_of_embeddingsFactorThrough`: every nonzero prime `Q` of `C` is
  `φ⁻¹(𝔪_R)` for a `K`-embedding `ι : L → F` with `ι(C) ⊆ R`, `φ = ι|_C`. A prime of `C ⊗_B R`
  over `Q` (faithful flatness) contains a minimal prime `𝔭` meeting `R` in `0` (the uniformizer is
  a non-zero-divisor of the flat `R`-module `C ⊗_B R`); the embedding of `L` into an algebraic
  closure of `Frac((C ⊗_B R)/𝔭)` factors through `F` by hypothesis.
* `etale_integralClosure_of_embeddingsFactorThrough`: the criterion, from
  `isUnramifiedAt_integralClosure_of_isUnramifiedAt` applied with `L' = F` (through `ι`).

## References

* J.-P. Serre, *Local fields*, I §4 and III §5.
-/

universe u

open IsLocalRing TensorProduct

namespace SGA.SGA1.ExposeX

/-- Every `K`-embedding of `L` into an algebraically closed field over `F` takes values in `F`
(for `L/K` finite separable: `L ⊗_K F` is a product of copies of `F`). -/
def EmbeddingsFactorThrough (K L F : Type u) [Field K] [Field L] [Field F] [Algebra K L]
    [Algebra K F] : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (j : F →+* Ω) (ψ : L →+* Ω),
    ψ.comp (algebraMap K L) = j.comp (algebraMap K F) →
      ∃ ι : L →ₐ[K] F, ψ = j.comp (ι : L →+* F)

variable {B : Type u} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  {K : Type u} [Field K] [Algebra B K] [IsFractionRing B K]
  {L : Type u} [Field L] [Algebra K L] [Algebra B L] [IsScalarTower B K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]
  {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Algebra B R]
  [IsLocalHom (algebraMap B R)]
  {F : Type u} [Field F] [Algebra R F] [IsFractionRing R F] [Algebra K F] [Algebra B F]
  [IsScalarTower B R F] [IsScalarTower B K F]

local notation "𝒞" => integralClosure B L

include K in
/-- Every nonzero prime `Q` of the integral closure `C` of `B` in `L` is the contraction of `𝔪_R`
along a `K`-embedding `ι : L → F` (restricted to `C`, with values in `R`), if every `K`-embedding
of `L` into an algebraically closed extension of `F` factors through `F`. -/
theorem exists_ringHom_comap_eq_of_embeddingsFactorThrough
    (hinj : Function.Injective (algebraMap B R))
    (hm : (maximalIdeal B).map (algebraMap B R) = maximalIdeal R)
    (H : EmbeddingsFactorThrough K L F) (Q : Ideal (integralClosure B L)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) :
    ∃ (ι : L →ₐ[K] F) (φ : integralClosure B L →+* R),
      (∀ c, algebraMap R F (φ c) = ι c) ∧ (maximalIdeal R).comap φ = Q := by
  classical
  have : IsDedekindDomain 𝒞 := integralClosure.isDedekindDomain B K L
  have : Module.IsTorsionFree B L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  have : Module.IsTorsionFree B 𝒞 := IsIntegralClosure.isTorsionFree B L
  have : Module.Flat B 𝒞 := inferInstance
  have : Module.IsTorsionFree B R := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Module.Flat B R := inferInstance
  have : Module.FaithfullyFlat B R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  -- a prime of `𝒞 ⊗_B R` over `Q`
  obtain ⟨⟨𝔮, h𝔮p⟩, h𝔮⟩ :=
    PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := 𝒞) (B := 𝒞 ⊗[B] R) ⟨Q, inferInstance⟩
  have hQ' : 𝔮.comap (algebraMap 𝒞 (𝒞 ⊗[B] R)) = Q := congrArg PrimeSpectrum.asIdeal h𝔮
  -- a minimal prime `𝔭 ⊆ 𝔮`
  obtain ⟨𝔭, h𝔭min, h𝔭𝔮⟩ := Ideal.exists_minimalPrimes_le (show (⊥ : Ideal _) ≤ 𝔮 from bot_le)
  have h𝔭 : 𝔭.IsPrime := h𝔭min.1.1
  let incR : R →+* 𝒞 ⊗[B] R := Algebra.TensorProduct.includeRight.toRingHom
  -- the uniformizer of `R` is a non-zero-divisor of `𝒞 ⊗_B R`
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hreg : incR π ∈ nonZeroDivisors (𝒞 ⊗[B] R) := by
    have hmul : Function.Injective ((LinearMap.lsmul R R π).restrictScalars B) := fun x y hxy ↦ by
      simpa [hπ0] using hxy
    have hinj' := Module.Flat.lTensor_preserves_injective_linearMap (M := 𝒞)
      ((LinearMap.lsmul R R π).restrictScalars B) hmul
    have hlt : ∀ x : 𝒞 ⊗[B] R,
        ((LinearMap.lsmul R R π).restrictScalars B).lTensor 𝒞 x = x * incR π := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul c r => simp [incR, mul_comm r π]
      | add x y hx hy => rw [map_add, hx, hy, add_mul]
    refine mem_nonZeroDivisors_iff.mpr
      ⟨fun x hx ↦ hinj' (by rw [map_zero]; exact (hlt x).trans ((mul_comm _ _).trans hx)),
        fun x hx ↦ hinj' (by rw [map_zero]; exact (hlt x).trans hx)⟩
  have hπ𝔭 : incR π ∉ 𝔭 := fun h ↦
    Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭min) h hreg
  -- `D = (𝒞 ⊗_B R)/𝔭` is a domain containing `R`
  let D := (𝒞 ⊗[B] R) ⧸ 𝔭
  let r : R →+* D := (Ideal.Quotient.mk 𝔭).comp incR
  have hr : Function.Injective r := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0 hπ
    obtain ⟨v, hv⟩ := hn.symm
    have hpow : r (π ^ n) = 0 := by
      have : r x = r (π ^ n) * r v := by rw [← map_mul, hv]
      rw [hx] at this
      exact (mul_eq_zero.mp this.symm).resolve_right (fun h ↦ by
        have := (v.isUnit.map r).ne_zero
        exact this h)
    rcases n with _ | n
    · rw [pow_zero, map_one] at hpow
      exact one_ne_zero hpow
    · rw [map_pow] at hpow
      exact hπ𝔭 (Ideal.Quotient.eq_zero_iff_mem.mp
        ((pow_eq_zero_iff (Nat.succ_ne_zero n)).mp hpow))
  let cD : 𝒞 →+* D := (Ideal.Quotient.mk 𝔭).comp Algebra.TensorProduct.includeLeftRingHom
  have hcomm : cD.comp (algebraMap B 𝒞) = r.comp (algebraMap B R) := by
    ext b
    simp only [cD, r, incR, RingHom.comp_apply]
    congr 1
    change algebraMap B 𝒞 b ⊗ₜ[B] (1 : R) = (1 : 𝒞) ⊗ₜ[B] algebraMap B R b
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  -- an algebraically closed field `Ω` containing `D`
  let FD := FractionRing D
  let Ω := AlgebraicClosure FD
  let jD : D →+* Ω := (algebraMap FD Ω).comp (algebraMap D FD)
  have hjD : Function.Injective jD :=
    (algebraMap FD Ω).injective.comp (IsFractionRing.injective D FD)
  have hjr : Function.Injective (jD.comp r) := hjD.comp hr
  let jF : F →+* Ω := IsFractionRing.lift hjr
  -- `𝒞 → D` is injective
  have : Algebra.IsIntegral B 𝒞 := inferInstance
  have hcD : Function.Injective cD := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hker : RingHom.ker cD = ⊥ := by
      have : (RingHom.ker cD).IsPrime := RingHom.ker_isPrime cD
      refine Ideal.eq_bot_of_comap_eq_bot (R := B) ?_
      rw [eq_bot_iff]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker, ← RingHom.comp_apply, hcomm, RingHom.comp_apply] at hb
      rw [Ideal.mem_bot]
      have h0 := hr (hb.trans (map_zero r).symm)
      exact hinj (h0.trans (map_zero _).symm)
    exact (RingHom.injective_iff_ker_eq_bot _).mpr hker |>.eq_iff.mp (by rw [hc, map_zero])
  have hC : Function.Injective (jD.comp cD) := hjD.comp hcD
  have : IsFractionRing 𝒞 L := integralClosure.isFractionRing_of_finite_extension K L
  let ψ₀ : L →+* Ω := IsFractionRing.lift hC
  have hψK : ψ₀.comp (algebraMap K L) = jF.comp (algebraMap K F) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors B)
    ext b
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply B K L, IsScalarTower.algebraMap_apply B 𝒞 L,
      IsFractionRing.lift_algebraMap]
    change jD (cD (algebraMap B 𝒞 b)) = jF (algebraMap K F (algebraMap B K b))
    rw [← IsScalarTower.algebraMap_apply B K F, IsScalarTower.algebraMap_apply B R F,
      IsFractionRing.lift_algebraMap, ← RingHom.comp_apply cD, hcomm]
    rfl
  obtain ⟨ι, hι⟩ := H Ω jF ψ₀ hψK
  -- `ι` maps `𝒞` into `R`
  have hmemR (c : 𝒞) : ι c ∈ (algebraMap R F).range := by
    have hB : IsIntegral B (ι (c : L)) := c.2.map (ι.restrictScalars B)
    exact IsIntegrallyClosed.isIntegral_iff.mp (hB.tower_top (A := R))
  let eR : R ≃+* (algebraMap R F).range :=
    RingEquiv.ofBijective (algebraMap R F).rangeRestrict
      ⟨fun x y h ↦ IsFractionRing.injective R F (congrArg Subtype.val h),
        (algebraMap R F).rangeRestrict_surjective⟩
  let φ : 𝒞 →+* R := eR.symm.toRingHom.comp
    (((ι : L →+* F).comp (algebraMap 𝒞 L)).codRestrict (algebraMap R F).range hmemR)
  have hφ (c : 𝒞) : algebraMap R F (φ c) = ι c := by
    have := congrArg Subtype.val (eR.apply_symm_apply
      ⟨ι c, hmemR c⟩)
    exact this
  refine ⟨ι, φ, hφ, ?_⟩
  -- `c ⊗ 1` and `1 ⊗ φ(c)` agree modulo `𝔭`
  have hdiff (c : 𝒞) : cD c = r (φ c) := by
    apply hjD
    have h1 : jD (cD c) = ψ₀ (algebraMap 𝒞 L c) := (IsFractionRing.lift_algebraMap hC c).symm
    have h2 : jD (r (φ c)) = jF (algebraMap R F (φ c)) :=
      (IsFractionRing.lift_algebraMap hjr (φ c)).symm
    rw [h1, h2, hφ, hι]
    rfl
  -- `𝔮 ∩ R = 𝔪_R`
  have hQB : Q.comap (algebraMap B 𝒞) = maximalIdeal B := comap_eq_maximalIdeal_of_ne_bot K Q hQ
  have hLR (c : 𝒞) : algebraMap 𝒞 (𝒞 ⊗[B] R) c = c ⊗ₜ[B] (1 : R) := rfl
  have h𝔮R : 𝔮.comap incR = maximalIdeal R := by
    have hle : maximalIdeal R ≤ 𝔮.comap incR := by
      rw [← hm, Ideal.map_le_iff_le_comap, Ideal.comap_comap]
      intro b hb
      have hb' : algebraMap B 𝒞 b ∈ Q := by
        rw [← Ideal.mem_comap, hQB]
        exact hb
      rw [← hQ', Ideal.mem_comap, hLR] at hb'
      rw [Ideal.mem_comap, RingHom.comp_apply]
      convert hb' using 1
      change (1 : 𝒞) ⊗ₜ[B] algebraMap B R b = algebraMap B 𝒞 b ⊗ₜ[B] (1 : R)
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    have : (𝔮.comap incR).IsPrime := Ideal.comap_isPrime _ _
    exact ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le this.ne_top hle).symm
  ext c
  rw [Ideal.mem_comap, ← h𝔮R, Ideal.mem_comap, ← hQ', Ideal.mem_comap]
  have hd : algebraMap 𝒞 (𝒞 ⊗[B] R) c - incR (φ c) ∈ 𝔭 := by
    rw [← Ideal.Quotient.eq]
    exact hdiff c
  constructor
  · intro h
    simpa using 𝔮.add_mem (h𝔭𝔮 hd) h
  · intro h
    simpa using 𝔮.sub_mem h (h𝔭𝔮 hd)

include K in
/-- **Étaleness of an integral closure from a splitting** (Serre, *Local fields*, I §4, III §5).
Let `B` be a discrete valuation ring with fraction field `K`, `L/K` finite separable, and `B → R`
an injective local homomorphism to a discrete valuation ring with `𝔪_B R = 𝔪_R` and `κ(R)/κ(B)`
separable, `F = Frac R`. If every `K`-embedding of `L` into an algebraically closed extension of
`F` takes values in `F`, the integral closure of `B` in `L` is étale over `B`. Each nonzero prime
`Q` of the integral closure is `ι⁻¹(𝔪_R)` for a `K`-embedding `ι : L → F`
(`exists_ringHom_comap_eq_of_embeddingsFactorThrough`), and unramifiedness descends along `ι`
(`isUnramifiedAt_integralClosure_of_isUnramifiedAt` with `L' = F`). -/
theorem etale_integralClosure_of_embeddingsFactorThrough
    (hinj : Function.Injective (algebraMap B R))
    (hm : (maximalIdeal B).map (algebraMap B R) = maximalIdeal R)
    [Algebra.IsSeparable (ResidueField B) (ResidueField R)]
    (H : EmbeddingsFactorThrough K L F) :
    Algebra.Etale B 𝒞 := by
  have : IsDedekindDomain 𝒞 := integralClosure.isDedekindDomain B K L
  have : Module.Finite B 𝒞 := IsIntegralClosure.finite B K L _
  have : Module.IsTorsionFree B L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq B K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective B K)
  have : Module.IsTorsionFree B 𝒞 := IsIntegralClosure.isTorsionFree B L
  have : Algebra.FinitePresentation B 𝒞 :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  -- the integral closure of `R` in `F` is `R`
  have hbot : integralClosure R F = ⊥ := IsIntegrallyClosed.integralClosure_eq_bot R F
  let e : R ≃ₐ[R] integralClosure R F := AlgEquiv.ofBijective (Algebra.ofId R _)
    ⟨fun x y h ↦ IsFractionRing.injective R F (congrArg Subtype.val h), fun z ↦ by
      have hz : (z : F) ∈ (⊥ : Subalgebra R F) := hbot ▸ z.2
      obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hz
      exact ⟨x, Subtype.ext hx⟩⟩
  have : Algebra.FiniteType R (integralClosure R F) :=
    Algebra.FiniteType.of_surjective e.toAlgHom e.surjective
  have : Algebra.FormallyUnramified R (integralClosure R F) :=
    Algebra.FormallyUnramified.of_surjective e.toAlgHom e.surjective
  have : Algebra.FormallyUnramified B 𝒞 := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    by_cases hq : q.asIdeal = ⊥
    · have : q = ⟨⊥, Ideal.isPrime_bot⟩ := PrimeSpectrum.ext hq
      subst this
      exact isUnramifiedAt_integralClosure_bot K
    · obtain ⟨ι, φ, hφ, hQ⟩ :=
        exists_ringHom_comap_eq_of_embeddingsFactorThrough hinj hm H q.asIdeal hq
      let : Algebra L F := ι.toRingHom.toAlgebra
      have : IsScalarTower B L F := IsScalarTower.of_algebraMap_eq fun b ↦ by
        change algebraMap B F b = ι (algebraMap B L b)
        rw [IsScalarTower.algebraMap_apply B K L, ι.commutes,
          ← IsScalarTower.algebraMap_apply B K F]
      let Q' : Ideal (integralClosure R F) := (maximalIdeal R).comap e.symm.toRingHom
      have : Q'.IsPrime := Ideal.comap_isPrime _ _
      have : Algebra.IsUnramifiedAt R Q' :=
        Algebra.FormallyUnramified.comp R (integralClosure R F) (Localization.AtPrime Q')
      have hQQ' : Q'.comap (integralClosureMap (B := B) (B' := R) L F).toRingHom = q.asIdeal := by
        rw [← hQ]
        ext c
        have hc : integralClosureMap (B := B) (B' := R) L F c = e (φ c) := Subtype.ext (hφ c).symm
        simp only [Q', Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hc]
        simp
      exact isUnramifiedAt_integralClosure_of_isUnramifiedAt K hm q.asIdeal hq Q' hQQ'
  exact Algebra.Etale.of_formallyUnramified_of_flat

end SGA.SGA1.ExposeX
