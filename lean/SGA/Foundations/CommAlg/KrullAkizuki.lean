/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.QuotSMulTop

/-!
# The theorem of Krull–Akizuki (rings between a one-dimensional domain and its fraction field)

Let `A` be a noetherian domain of Krull dimension `≤ 1` with fraction field `K`, and let `C` be a
ring with `A ⊆ C ⊆ K`. Then `C` is noetherian of dimension `≤ 1`
(Matsumura, *Commutative ring theory*, Theorem 11.7, case `L = K`; Stacks, Tag 00PG;
Bourbaki, *Algèbre commutative* VII §2 no. 5). As a corollary, a valuation ring of `K` that
contains `A` and is not `K` is a discrete valuation ring.

The proof is Matsumura's. For `0 ≠ a ∈ A` and a nonzero finitely generated `A`-submodule
`F ⊆ K`, `F ≅ I` for a nonzero ideal `I` of `A`, and the exact sequences
`0 → I/aI → A/aI → A/I → 0` and `0 → A/I → A/aI → A/aA → 0` give `ℓ(F/aF) = ℓ(A/aA)`. Hence every
finitely generated submodule of `C/aC` has length `≤ ℓ(A/aA)`, so `C/aC` has finite length.
A nonzero ideal `J` of `C` contains some `0 ≠ a ∈ A`, so `J/aC` is finitely generated, and so is
`J`; a nonzero prime `P` of `C` contains such an `a`, so `C/P` is an artinian domain, i.e. a field.

## Main results

* `Module.length_le_of_forall_fg`: a module whose finitely generated submodules have length
  `≤ n` has length `≤ n`.
* `KrullAkizuki.length_quotient_smul_top_of_fg`: `ℓ_A(F/aF) = ℓ_A(A/aA)` for a nonzero finitely
  generated `A`-submodule `F` of `K`.
* `KrullAkizuki.isNoetherianRing`, `KrullAkizuki.krullDimLE_one`: Krull–Akizuki for an
  `A`-algebra `C` with an injective `A`-algebra map `C → K` compatible with `A → K`.
* `ValuationSubring.isDiscreteValuationRing_of_krullDimLE_one`: a valuation subring `V ≠ K` of
  `K` containing `A` is a discrete valuation ring.
* `ValuationSubring.isDiscreteValuationRing_of_finiteDimensional`: the same for a valuation
  subring `V ≠ L` of a finite extension `L` of `K` containing `A` (valuation-ring form of
  Matsumura 11.7 for finite `L`).

For a finite extension `L` of `K`, the ring form (every ring `B` with `A ⊆ B ⊆ L` is noetherian
of dimension `≤ 1`) is `KrullAkizuki.isNoetherianRing_of_finiteDimensional` and
`KrullAkizuki.krullDimLE_one_of_finiteDimensional` in `SGA.Foundations.CommAlg.KrullAkizukiFinite`,
deduced from the length estimate proved here.
-/

open scoped Pointwise
open Module

section Generic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- A module whose finitely generated submodules all have length at most `n` has length at
most `n`. -/
theorem Module.length_le_of_forall_fg {n : ℕ}
    (h : ∀ N : Submodule R M, N.FG → Module.length R N ≤ n) : Module.length R M ≤ n := by
  classical
  simp_rw [Module.length_submodule] at h
  set S : Set ℕ := {k | ∃ N : Submodule R M, N.FG ∧ Order.height N = k}
  have hS0 : (0 : ℕ) ∈ S := ⟨⊥, Submodule.fg_bot, by simp⟩
  have hSb : BddAbove S := ⟨n, by
    rintro k ⟨N, hN, hk⟩
    exact_mod_cast hk ▸ h N hN⟩
  obtain ⟨N, hN, hNk⟩ := Nat.sSup_mem ⟨0, hS0⟩ hSb
  have hmax : ∀ N' : Submodule R M, N'.FG → Order.height N' ≤ Order.height N := by
    intro N' hN'
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Order.height N' = k :=
      (ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top n) (h N' hN'))).imp
        fun _ h ↦ h.symm
    rw [hk, hNk]
    exact_mod_cast le_csSup hSb ⟨N', hN', hk⟩
  have hNtop : N = ⊤ := by
    rw [eq_top_iff]
    intro m _
    by_contra hm
    have hlt : N < N ⊔ Submodule.span R {m} :=
      lt_of_le_of_ne le_sup_left fun he ↦
        hm (he ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self m))
    have hfin : Order.height N < ⊤ := lt_of_le_of_lt (h N hN) (ENat.natCast_lt_top n)
    exact (Order.height_strictMono hlt hfin).not_ge
      (hmax _ (hN.sup (Submodule.fg_span_singleton m)))
  rw [Module.length_eq_height, ← hNtop]
  exact h N hN

/-- If for every finitely generated submodule `P` of `M` the quotient `P/aP` has length at most
`n`, so has `M/aM`. -/
theorem Module.length_quotient_smul_top_le_of_forall_fg {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (a : R) {n : ℕ}
    (h : ∀ P : Submodule R M, P.FG → Module.length R (P ⧸ (a • ⊤ : Submodule R P)) ≤ n) :
    Module.length R (M ⧸ (a • ⊤ : Submodule R M)) ≤ n := by
  classical
  apply Module.length_le_of_forall_fg
  rintro N ⟨s, rfl⟩
  have hsurj : Function.Surjective (a • ⊤ : Submodule R M).mkQ := Submodule.mkQ_surjective _
  let P : Submodule R M := Submodule.span R (Function.surjInv hsurj '' s)
  let φ : P →ₗ[R] M ⧸ (a • ⊤ : Submodule R M) := (a • ⊤ : Submodule R M).mkQ ∘ₗ P.subtype
  have hker : (a • ⊤ : Submodule R P) ≤ LinearMap.ker φ := by
    intro y hy
    obtain ⟨z, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    simp only [LinearMap.mem_ker, φ, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_pointwise_smul _ a ⊤ trivial
  let φ' := (a • ⊤ : Submodule R P).liftQ φ hker
  have hle : Submodule.span R (s : Set (M ⧸ (a • ⊤ : Submodule R M))) ≤ LinearMap.range φ' := by
    rw [Submodule.span_le]
    intro q hq
    refine ⟨Submodule.Quotient.mk ⟨Function.surjInv hsurj q,
      Submodule.subset_span ⟨q, hq, rfl⟩⟩, ?_⟩
    simp [φ', φ, Function.surjInv_eq hsurj q]
  refine le_trans (Module.length_le_of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)) (le_trans ?_ (h P (Submodule.fg_span
      (s.finite_toSet.image _))))
  exact Module.length_le_of_surjective φ'.rangeRestrict φ'.surjective_rangeRestrict

end Generic

namespace KrullAkizuki

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

/-- In a noetherian domain of dimension `≤ 1`, the quotient by a nonzero ideal has finite
length. -/
theorem isFiniteLength_quotient (I : Ideal A) (hI : I ≠ ⊥) : IsFiniteLength A (A ⧸ I) := by
  have : Ring.KrullDimLE 0 (A ⧸ I) := by
    rw [Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal]
    intro J hJ
    exact hJ.1.1.isMaximal_of_ne_bot fun h ↦ hI (le_bot_iff.mp (h ▸ hJ.1.2))
  have : IsArtinianRing (A ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  exact ⟨isNoetherian_quotient I,
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))⟩

/-- For a nonzero ideal `I` and `a ≠ 0` in a noetherian domain of dimension `≤ 1`,
`ℓ(I/aI) = ℓ(A/aA)`. -/
theorem length_ideal_quotient_smul_top {a : A} (ha : a ≠ 0) {I : Ideal A} (hI : I ≠ ⊥) :
    Module.length A (I ⧸ (a • ⊤ : Submodule A I)) = Ring.ord A a := by
  set T : Submodule A A := a • I
  have hTI : T ≤ I := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
    exact I.smul_mem a hz
  let f₀ : I →ₗ[A] A ⧸ T := T.mkQ ∘ₗ I.subtype
  have hker : (a • ⊤ : Submodule A I) = LinearMap.ker f₀ := by
    ext y
    simp only [LinearMap.mem_ker, f₀, LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, T,
      Submodule.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, -, rfl⟩
      exact ⟨z, z.2, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      exact ⟨⟨z, hz⟩, trivial, Subtype.ext hzy⟩
  let f : (I ⧸ (a • ⊤ : Submodule A I)) →ₗ[A] A ⧸ T := (a • ⊤ : Submodule A I).liftQ f₀ hker.le
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hker
  let g : (A ⧸ T) →ₗ[A] A ⧸ I := Submodule.factor hTI
  have hg : Function.Surjective g := Submodule.factor_surjective hTI
  have hfg : Function.Exact f g := by
    intro y
    induction y using Submodule.Quotient.induction_on with | _ x
    rw [show g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x from rfl,
      Submodule.Quotient.mk_eq_zero, Set.mem_range]
    constructor
    · intro hx
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    · rintro ⟨y, hy⟩
      induction y using Submodule.Quotient.induction_on with | _ z
      have hz : (z : A) - x ∈ T := by
        rw [← Submodule.Quotient.eq]
        exact hy
      have := I.sub_mem z.2 (hTI hz)
      simpa using this
  have h₁ := Module.length_eq_add_of_exact f g hf hg hfg
  have h₂ := Module.length_eq_add_of_exact (Ideal.mulQuot a I) (Ideal.quotOfMul a I)
    (Ideal.mulQuot_injective I (mem_nonZeroDivisors_of_ne_zero ha))
    (Ideal.quotOfMul_surjective I) (Ideal.exact_mulQuot_quotOfMul I)
  have hfin : Module.length A (A ⧸ I) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (isFiniteLength_quotient I hI)
  rw [h₁, add_comm] at h₂
  exact (WithTop.add_left_cancel hfin h₂).trans rfl

variable {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- For a nonzero finitely generated `A`-submodule `F` of the fraction field and `a ≠ 0`,
`ℓ(F/aF) = ℓ(A/aA)`. -/
theorem length_quotient_smul_top_of_fg {a : A} (ha : a ≠ 0) {F : Submodule A K} (hF : F.FG)
    (hF0 : F ≠ ⊥) : Module.length A (F ⧸ (a • ⊤ : Submodule A F)) = Ring.ord A a := by
  obtain ⟨d, hd, hdF⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A) hF
  have hd0 : algebraMap A K d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd
  let ψ : A →ₗ[A] K := LinearMap.mulLeft A ((algebraMap A K d)⁻¹) ∘ₗ Algebra.linearMap A K
  have hψ : Function.Injective ψ := by
    intro x y hxy
    simp only [ψ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      Algebra.linearMap_apply, mul_eq_mul_left_iff, inv_eq_zero, hd0, or_false] at hxy
    exact IsFractionRing.injective A K hxy
  have hFψ : F ≤ LinearMap.range ψ := by
    intro b hb
    obtain ⟨y, hy⟩ := hdF b hb
    refine ⟨y, ?_⟩
    simp only [ψ, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
      Algebra.linearMap_apply, hy, Algebra.smul_def]
    field_simp
  set I : Ideal A := Submodule.comap ψ F
  have hmap : Submodule.map ψ I = F := Submodule.map_comap_eq_of_le hFψ
  have hI : I ≠ ⊥ := by
    rintro hI
    rw [hI, Submodule.map_bot] at hmap
    exact hF0 hmap.symm
  let e : I ≃ₗ[A] F := (Submodule.equivMapOfInjective ψ hψ I).trans (LinearEquiv.ofEq _ _ hmap)
  rw [← (QuotSMulTop.congr a e).length_eq]
  exact length_ideal_quotient_smul_top ha hI

variable {C : Type*} [CommRing C] [Algebra A C] [Algebra C K] [IsScalarTower A C K]

/-- If `A ⊆ C ⊆ K`, then `ℓ_A(C/aC) ≤ ℓ_A(A/aA)` for `a ≠ 0` (the key estimate of
Krull–Akizuki). -/
theorem length_quotient_smul_top_le (hC : Function.Injective (algebraMap C K)) {a : A}
    (ha : a ≠ 0) : Module.length A (C ⧸ (a • ⊤ : Submodule A C)) ≤ Ring.ord A a := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))
  rw [← hn]
  apply Module.length_quotient_smul_top_le_of_forall_fg
  intro P hP
  let ι : C →ₗ[A] K := (IsScalarTower.toAlgHom A C K).toLinearMap
  have hι : Function.Injective ι := hC
  by_cases hP0 : P = ⊥
  · subst hP0
    have : Subsingleton ((⊥ : Submodule A C) ⧸ (a • ⊤ : Submodule A (⊥ : Submodule A C))) :=
      (Submodule.mkQ_surjective _).subsingleton
    simp [Module.length_eq_zero]
  have hP0' : P.map ι ≠ ⊥ := by
    intro h
    apply hP0
    apply Submodule.map_injective_of_injective hι
    rw [h, Submodule.map_bot]
  rw [(QuotSMulTop.congr a (Submodule.equivMapOfInjective ι hι P)).length_eq,
    length_quotient_smul_top_of_fg ha (hP.map ι) hP0', hn]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- A nonzero ideal of `C` (`A ⊆ C ⊆ K`) contains the image of a nonzero element of `A`. -/
theorem exists_algebraMap_mem_of_ne_bot (hC : Function.Injective (algebraMap C K))
    {J : Ideal C} (hJ : J ≠ ⊥) : ∃ a : A, a ≠ 0 ∧ algebraMap A C a ∈ J := by
  obtain ⟨c, hcJ, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := A) (algebraMap C K c)
  have hy0 : algebraMap A K y ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
  have hx : algebraMap A C x = c * algebraMap A C y := by
    apply hC
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hxy,
      div_mul_cancel₀ _ hy0]
  refine ⟨x, ?_, hx ▸ J.mul_mem_right _ hcJ⟩
  rintro rfl
  rw [map_zero, zero_div, eq_comm] at hxy
  exact hc0 (hC (by rw [hxy, map_zero]))

/-- The `A`-module `C ⧸ aC` has finite length for `0 ≠ a ∈ A` (`A ⊆ C ⊆ K`). -/
theorem isFiniteLength_quotient_span_algebraMap (hC : Function.Injective (algebraMap C K))
    {a : A} (ha : a ≠ 0) : IsFiniteLength A (C ⧸ Ideal.span {algebraMap A C a}) := by
  have heq : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C) := by
    ext c
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, Algebra.smul_def,
      mul_comm]
  rw [← Module.length_ne_top_iff]
  have e := Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})
  rw [← e.length_eq, heq]
  exact ne_top_of_le_ne_top (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))
    (length_quotient_smul_top_le hC ha)

variable (A) in
include A in
/-- **Krull–Akizuki** (Matsumura 11.7, case `L = K`; Stacks 00PG): a ring `C` between a
noetherian domain `A` of dimension `≤ 1` and its fraction field `K` is noetherian. Here `C` is an
`A`-algebra with an injective map `C → K` compatible with `A → K`. -/
theorem isNoetherianRing (hC : Function.Injective (algebraMap C K)) : IsNoetherianRing C := by
  refine ⟨fun J ↦ ?_⟩
  by_cases hJ : J = ⊥
  · rw [hJ]; exact Submodule.fg_bot
  obtain ⟨a, ha, haJ⟩ := exists_algebraMap_mem_of_ne_bot (A := A) (K := K) hC hJ
  set Q := Ideal.span {algebraMap A C a}
  have hfl := isFiniteLength_quotient_span_algebraMap (K := K) hC ha
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsNoetherian C (C ⧸ Q) := isNoetherian_of_tower A hfl.1
  refine Submodule.fg_of_fg_map_of_fg_inf_ker Q.mkQ (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)]
  exact Submodule.fg_span_singleton _

variable (A) in
include A in
/-- **Krull–Akizuki** (Matsumura 11.7, case `L = K`; Stacks 00PG): a ring `C` between a
noetherian domain `A` of dimension `≤ 1` and its fraction field `K` has dimension `≤ 1`. -/
theorem krullDimLE_one (hC : Function.Injective (algebraMap C K)) : Ring.KrullDimLE 1 C := by
  have : IsDomain C := hC.isDomain
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
  intro P hP0 hP
  obtain ⟨a, ha, haP⟩ := exists_algebraMap_mem_of_ne_bot (A := A) (K := K) hC hP0
  have hle : Ideal.span {algebraMap A C a} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr haP
  have hfl : IsFiniteLength A (C ⧸ P) :=
    (isFiniteLength_quotient_span_algebraMap (K := K) hC ha).of_surjective
      (f := (Submodule.factor hle).restrictScalars A) (Submodule.factor_surjective hle)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsArtinian C (C ⧸ P) := isArtinian_of_tower A hfl.2
  have : IsArtinianRing (C ⧸ P) := isArtinian_of_tower C this
  exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)

end KrullAkizuki

/-- A valuation subring `V ≠ K` of the fraction field `K` of a noetherian domain `A` of dimension
`≤ 1`, containing `A`, is a discrete valuation ring (a consequence of Krull–Akizuki). -/
theorem ValuationSubring.isDiscreteValuationRing_of_krullDimLE_one {A K : Type*} [CommRing A]
    [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Field K] [Algebra A K]
    [IsFractionRing A K] (V : ValuationSubring K) (hV : ∀ a : A, algebraMap A K a ∈ V)
    (hne : V ≠ ⊤) : IsDiscreteValuationRing V := by
  let : Algebra A V := ((algebraMap A K).codRestrict V hV).toAlgebra
  have : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsNoetherianRing V := KrullAkizuki.isNoetherianRing A (K := K)
    (C := V) Subtype.val_injective
  have hnf : ¬ IsField V := by
    obtain ⟨z, hz⟩ : ∃ z : K, z ∉ V := by
      by_contra! h
      apply hne
      ext z
      simp [h z]
    have hz0 : z ≠ 0 := fun h ↦ hz (h ▸ V.zero_mem)
    have hzi : z⁻¹ ∈ V := (V.mem_or_inv_mem z).resolve_left hz
    intro hF
    obtain ⟨w, hw⟩ := hF.mul_inv_cancel (a := ⟨z⁻¹, hzi⟩) (by
      intro h
      exact hz0 (inv_eq_zero.mp (congrArg Subtype.val h)))
    have : (w : K) = z := by
      have := congrArg Subtype.val hw
      simp only [MulMemClass.coe_mul, OneMemClass.coe_one] at this
      field_simp at this
      exact this
    exact hz (this ▸ w.2)
  exact ((IsDiscreteValuationRing.TFAE V hnf).out 2 1).mp (inferInstance : ValuationRing V)

/-- **Krull–Akizuki** for a finite extension (Matsumura 11.7; Stacks 00PG), valuation-ring form:
let `A` be a noetherian domain of dimension `≤ 1` with fraction field `K`, and `L` a finite
extension of `K`. A valuation subring `V ≠ L` of `L` containing `A` is a discrete valuation ring.
(Proof: `V` contains a `K`-basis of `L` integral over `A`; the `A`-algebra `B'` it generates is
finite over `A`, hence a noetherian domain of dimension `≤ 1` with fraction field `L`, and
`B' ⊆ V ⊆ L`.) -/
theorem ValuationSubring.isDiscreteValuationRing_of_finiteDimensional {A K L : Type*}
    [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [Field K] [Algebra A K]
    [IsFractionRing A K] [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] (V : ValuationSubring L) (hV : ∀ a : A, algebraMap A L a ∈ V)
    (hne : V ≠ ⊤) : IsDiscreteValuationRing V := by
  classical
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let B' : Subalgebra A L := Algebra.adjoin A (Set.range b)
  have hfg : (Subalgebra.toSubmodule B').FG :=
    fg_adjoin_of_finite (Set.finite_range b) (by rintro _ ⟨i, rfl⟩; exact hb i)
  have : Module.Finite A B' := Module.Finite.iff_fg.mpr hfg
  have : IsNoetherianRing B' := IsNoetherianRing.of_finite A B'
  have : Algebra.IsIntegral A B' := Algebra.IsIntegral.of_finite A B'
  have : Ring.KrullDimLE 1 B' := by
    rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
    intro P hP0 hP
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := A)
    refine (Ideal.comap_isPrime (algebraMap A B') P).isMaximal_of_ne_bot fun h ↦ hP0 ?_
    exact Ideal.eq_bot_of_comap_eq_bot h
  have hsub : ∀ z : L, ∃ x y : B', z = algebraMap B' L x / algebraMap B' L y := by
    intro z
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors A) (Finset.univ.image (b.repr z))
    have hc : ∀ i, ∃ a : A, algebraMap A K a = d • b.repr z i := fun i ↦
      hint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))
    choose a ha using hc
    have hd0 : algebraMap A L d ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A K L]
      exact (map_ne_zero _).mpr (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
    have hmem : ∑ i, algebraMap A L (a i) * b i ∈ B' :=
      Subalgebra.sum_mem _ fun i _ ↦ Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
        (Algebra.subset_adjoin ⟨i, rfl⟩)
    refine ⟨⟨_, hmem⟩, algebraMap A B' d, ?_⟩
    rw [eq_div_iff (by simpa using hd0)]
    simp only [← IsScalarTower.algebraMap_apply]
    conv_lhs => rw [← b.sum_repr z]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [IsScalarTower.algebraMap_apply A K L (a i), ha i, Algebra.smul_def d,
      Algebra.smul_def (b.repr z i), map_mul, IsScalarTower.algebraMap_apply A K L d]
    ring
  have : IsFractionRing B' L := IsFractionRing.of_field B' L hsub
  have hle : ∀ x ∈ B', x ∈ V := by
    let : Algebra A V := ((algebraMap A L).codRestrict V hV).toAlgebra
    have : IsScalarTower A V L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    let V' : Subalgebra A L := { V.toSubring with algebraMap_mem' := hV }
    have : B' ≤ V' := Algebra.adjoin_le (by
      rintro _ ⟨i, rfl⟩
      obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp ((hb i).tower_top (A := V))
      exact hy ▸ y.2)
    exact fun x hx ↦ this hx
  exact V.isDiscreteValuationRing_of_krullDimLE_one (A := B') (fun x ↦ hle x x.2) hne
