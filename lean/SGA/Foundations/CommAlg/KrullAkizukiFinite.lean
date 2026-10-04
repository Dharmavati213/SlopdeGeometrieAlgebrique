/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.CommAlg.KrullAkizuki
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Localization.Integral

/-!
# The theorem of Krull–Akizuki for finite extensions of the fraction field

Let `A` be a noetherian domain of Krull dimension `≤ 1` with fraction field `K`, `L` a finite
extension of `K`, and `C` a ring with `A ⊆ C ⊆ L`. Then `C` is noetherian of dimension `≤ 1`
(Matsumura, *Commutative ring theory*, Theorem 11.7; Stacks, Tags 00PF, 00PG; Bourbaki,
*Algèbre commutative* VII §2 no. 5). `SGA.Foundations.CommAlg.KrullAkizuki` proves the case
`L = K`; this file deduces the general case.

## Main results

* `KrullAkizuki.length_quotSMulTop_le_finrank_mul`: for a finitely generated `A`-submodule `F`
  of a finite-dimensional `K`-vector space `V` and `0 ≠ a ∈ A`, `ℓ(F/aF) ≤ dim_K V · ℓ(A/aA)`
  (Stacks 00PF).
* `KrullAkizuki.isNoetherianRing_of_finiteDimensional`,
  `KrullAkizuki.krullDimLE_one_of_finiteDimensional`: Krull–Akizuki for an `A`-algebra `C` with an
  injective `A`-algebra map `C → L`.

## Proof

The bound on `ℓ(F/aF)` is by induction on `dim_K V`. A nonzero linear form `φ : V → K` gives an
exact sequence `0 → F ∩ ker φ → F → φ(F) → 0` whose last term is torsion free, so it stays exact
after applying `M ↦ M/aM` (`QuotSMulTop.map_exact`,
`QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`), and
`ℓ(φ(F)/aφ(F)) ≤ ℓ(A/aA)` is the case `L = K`. The rest is as for `L = K`: every finitely
generated `A`-submodule of `C/aC` has length `≤ [L : K] ℓ(A/aA)`, so `C/aC` has finite length, and
every nonzero ideal of `C` contains a nonzero element of `A` (elements of `C` are algebraic over
`A`).
-/

open Module
open scoped Pointwise

namespace KrullAkizuki

section Additivity

variable {R : Type*} [CommRing R] {M₁ M₂ M₃ : Type*} [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]

/-- For a short exact sequence `0 → M₁ → M₂ → M₃ → 0` with `r` a nonzerodivisor on `M₃`,
`ℓ(M₂/rM₂) = ℓ(M₁/rM₁) + ℓ(M₃/rM₃)`. -/
theorem length_quotSMulTop_eq_add {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) {r : R}
    (hr : IsSMulRegular M₃ r) :
    Module.length R (QuotSMulTop r M₂) =
      Module.length R (QuotSMulTop r M₁) + Module.length R (QuotSMulTop r M₃) := by
  have h₀ : Function.Exact (0 : (⊥ : Submodule R M₁) →ₗ[R] M₁) f := by
    intro x
    simp only [Set.mem_range, LinearMap.zero_apply]
    constructor
    · intro hx
      exact ⟨0, (hf (hx.trans f.map_zero.symm)).symm⟩
    · rintro ⟨-, rfl⟩
      exact f.map_zero
  have hex := QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last h₀ hfg hr
  have hinj : Function.Injective (QuotSMulTop.map r f) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨y, rfl⟩ := (hex x).mp hx
    induction y using Submodule.Quotient.induction_on with | _ y
    rw [QuotSMulTop.map_apply_mk]
    simp
  exact Module.length_eq_add_of_exact _ _ hinj (QuotSMulTop.map_surjective r hg)
    (QuotSMulTop.map_exact r hfg hg)

end Additivity

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

omit [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
/-- A nonzero element of `A` is a nonzerodivisor on any `K`-vector space. -/
theorem isSMulRegular_of_ne_zero {V : Type*} [AddCommGroup V] [Module K V] [Module A V]
    [IsScalarTower A K V] {a : A} (ha : a ≠ 0) : IsSMulRegular V a := by
  intro x y hxy
  have h0 : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  simp only [← algebraMap_smul K a x, ← algebraMap_smul K a y] at hxy
  exact smul_right_injective V h0 hxy

/-- **The key estimate of Krull–Akizuki** (Stacks 00PF): let `F` be a finitely generated
`A`-submodule of a finite-dimensional `K`-vector space `V`, and `0 ≠ a ∈ A`. Then
`ℓ_A(F/aF) ≤ dim_K V · ℓ_A(A/aA)`. -/
theorem length_quotSMulTop_le_finrank_mul {a : A} (ha : a ≠ 0) :
    ∀ (n : ℕ) {V : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
      [FiniteDimensional K V], finrank K V = n → ∀ F : Submodule A V, F.FG →
        Module.length A (QuotSMulTop a F) ≤ n * Ring.ord A a := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ _ _ hV F _
    have : Subsingleton V := Module.finrank_zero_iff.mp hV
    have : Subsingleton (QuotSMulTop a F) := (Submodule.mkQ_surjective _).subsingleton
    simp [Module.length_eq_zero]
  | succ n ih =>
    intro V _ _ _ _ _ hV F hF
    -- A nonzero linear form `φ : V → K`, and `W = ker φ` of dimension `n`.
    let b := Module.finBasisOfFinrankEq K V hV
    let φ : V →ₗ[K] K := b.coord 0
    let W := LinearMap.ker φ
    have hφ : Function.Surjective φ := by
      intro c
      refine ⟨c • b 0, ?_⟩
      simp [φ]
    have hW : finrank K W = n := by
      have := LinearMap.finrank_range_add_finrank_ker φ
      rw [LinearMap.range_eq_top.mpr hφ, finrank_top, Module.finrank_self, hV] at this
      change finrank K (LinearMap.ker φ) = n
      omega
    -- The pieces `F' = F ∩ W` and `F'' = φ(F)` of the exact sequence.
    let ιW : W →ₗ[A] V := W.subtype.restrictScalars A
    let φA : V →ₗ[A] K := φ.restrictScalars A
    let F' : Submodule A W := F.comap ιW
    let F'' : Submodule A K := F.map φA
    have : IsNoetherian A F := isNoetherian_of_fg_of_noetherian F hF
    have hF'fg : F'.FG := by
      have hfg : ((F'.map ιW).comap F.subtype).FG := IsNoetherian.noetherian _
      have hmap : ((F'.map ιW).comap F.subtype).map F.subtype = F'.map ιW := by
        rw [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr (Submodule.map_comap_le _ _)
      have : (F'.map ιW).FG := hmap ▸ hfg.map F.subtype
      exact Submodule.fg_of_fg_map_injective ιW W.injective_subtype this
    have hF''fg : F''.FG := hF.map φA
    -- The exact sequence `0 → F' → F → F'' → 0`.
    let f : F' →ₗ[A] F := (ιW.restrict fun x hx ↦ hx)
    let g : F →ₗ[A] F'' := φA.restrict fun x hx ↦ Submodule.mem_map_of_mem hx
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : F ↦ (z : V)) hxy
    have hg : Function.Surjective g := by
      rintro ⟨y, x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
    have hfg : Function.Exact f g := by
      intro x
      constructor
      · intro hx
        have hx' : φ x = 0 := congrArg Subtype.val hx
        exact ⟨⟨⟨x, hx'⟩, x.2⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        apply Subtype.ext
        exact y.1.2
    have hreg : IsSMulRegular F'' a := by
      intro x y hxy
      apply Subtype.ext
      exact isSMulRegular_of_ne_zero (K := K) (V := K) ha (congrArg Subtype.val hxy)
    rw [length_quotSMulTop_eq_add hf hg hfg hreg]
    have h₁ : Module.length A (QuotSMulTop a F') ≤ n * Ring.ord A a := ih hW F' hF'fg
    have h₂ : Module.length A (QuotSMulTop a F'') ≤ Ring.ord A a := by
      by_cases h0 : F'' = ⊥
      · have : Subsingleton F'' := by rw [h0]; infer_instance
        have : Subsingleton (QuotSMulTop a F'') := (Submodule.mkQ_surjective _).subsingleton
        simp [Module.length_eq_zero]
      · exact (length_quotient_smul_top_of_fg ha hF''fg h0).le
    calc _ ≤ (n : ℕ∞) * Ring.ord A a + Ring.ord A a := add_le_add h₁ h₂
      _ = ((n + 1 : ℕ) : ℕ∞) * Ring.ord A a := by push_cast; ring

variable {L : Type*} [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
  [FiniteDimensional K L] {C : Type*} [CommRing C] [Algebra A C] [Algebra C L]
  [IsScalarTower A C L]

/-- If `A ⊆ C ⊆ L` with `L` finite over `K`, then `ℓ_A(C/aC) ≤ [L : K] ℓ_A(A/aA)` for
`0 ≠ a ∈ A`. -/
theorem length_quotient_smul_top_le_finrank_mul (hC : Function.Injective (algebraMap C L))
    {a : A} (ha : a ≠ 0) :
    Module.length A (C ⧸ (a • ⊤ : Submodule A C)) ≤ finrank K L * Ring.ord A a := by
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))
  rw [← hm]
  have hbound : ((finrank K L * m : ℕ) : ℕ∞) = finrank K L * (m : ℕ∞) := by push_cast; ring
  rw [← hbound]
  apply Module.length_quotient_smul_top_le_of_forall_fg
  intro P hP
  let ι : C →ₗ[A] L := (IsScalarTower.toAlgHom A C L).toLinearMap
  have hι : Function.Injective ι := hC
  rw [(QuotSMulTop.congr a (Submodule.equivMapOfInjective ι hι P)).length_eq, hbound, hm]
  exact length_quotSMulTop_le_finrank_mul (K := K) ha _ rfl _ (hP.map ι)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
include K in
/-- If `A ⊆ C ⊆ L` with `L` finite over `K`, a nonzero ideal of `C` contains the image of a
nonzero element of `A`. -/
theorem exists_algebraMap_mem_of_ne_bot_of_finiteDimensional
    (hC : Function.Injective (algebraMap C L)) {J : Ideal C} (hJ : J ≠ ⊥) :
    ∃ a : A, a ≠ 0 ∧ algebraMap A C a ∈ J := by
  have : IsDomain C := hC.isDomain
  obtain ⟨c, hcJ, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hJ
  have hcL : IsAlgebraic A (algebraMap C L c) :=
    (IsFractionRing.isAlgebraic_iff A K L).mpr (.of_finite K _)
  have hc : IsAlgebraic A c := by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom A C L) hC]
    exact hcL
  obtain ⟨a, haJ, ha0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (Ideal.comap_ne_bot_of_algebraic_mem hc0 hcJ hc)
  exact ⟨a, ha0, haJ⟩

include K in
/-- The `A`-module `C ⧸ aC` has finite length for `0 ≠ a ∈ A` (`A ⊆ C ⊆ L`, `L` finite over
`K`). -/
theorem isFiniteLength_quotient_span_algebraMap_of_finiteDimensional
    (hC : Function.Injective (algebraMap C L)) {a : A} (ha : a ≠ 0) :
    IsFiniteLength A (C ⧸ Ideal.span {algebraMap A C a}) := by
  have heq : (Ideal.span {algebraMap A C a}).restrictScalars A = (a • ⊤ : Submodule A C) := by
    ext c
    simp only [Submodule.restrictScalars_mem, Ideal.mem_span_singleton',
      Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top, true_and, Algebra.smul_def,
      mul_comm]
  rw [← Module.length_ne_top_iff]
  have e := Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A C a})
  rw [← e.length_eq, heq]
  refine ne_top_of_le_ne_top ?_ (length_quotient_smul_top_le_finrank_mul (K := K) hC ha)
  exact WithTop.mul_ne_top (ENat.natCast_ne_top _)
    (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero ha))

variable (A K) in
include A K in
/-- **Krull–Akizuki** (Matsumura 11.7; Stacks 00PG): let `A` be a noetherian domain of dimension
`≤ 1` with fraction field `K` and `L` a finite extension of `K`. A ring `C` between `A` and `L`
is noetherian. Here `C` is an `A`-algebra with an injective map `C → L` compatible with
`A → L`. -/
theorem isNoetherianRing_of_finiteDimensional (hC : Function.Injective (algebraMap C L)) :
    IsNoetherianRing C := by
  refine ⟨fun J ↦ ?_⟩
  by_cases hJ : J = ⊥
  · rw [hJ]; exact Submodule.fg_bot
  obtain ⟨a, ha, haJ⟩ :=
    exists_algebraMap_mem_of_ne_bot_of_finiteDimensional (A := A) (K := K) hC hJ
  set Q := Ideal.span {algebraMap A C a}
  have hfl := isFiniteLength_quotient_span_algebraMap_of_finiteDimensional (K := K) hC ha
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsNoetherian C (C ⧸ Q) := isNoetherian_of_tower A hfl.1
  refine Submodule.fg_of_fg_map_of_fg_inf_ker Q.mkQ (IsNoetherian.noetherian _) ?_
  rw [Submodule.ker_mkQ, inf_eq_right.mpr ((Ideal.span_singleton_le_iff_mem _).mpr haJ)]
  exact Submodule.fg_span_singleton _

variable (A K) in
include A K in
/-- **Krull–Akizuki** (Matsumura 11.7; Stacks 00PG): let `A` be a noetherian domain of dimension
`≤ 1` with fraction field `K` and `L` a finite extension of `K`. A ring `C` between `A` and `L`
has dimension `≤ 1`. -/
theorem krullDimLE_one_of_finiteDimensional (hC : Function.Injective (algebraMap C L)) :
    Ring.KrullDimLE 1 C := by
  have : IsDomain C := hC.isDomain
  rw [Ring.krullDimLE_one_iff_of_noZeroDivisors]
  intro P hP0 hP
  obtain ⟨a, ha, haP⟩ :=
    exists_algebraMap_mem_of_ne_bot_of_finiteDimensional (A := A) (K := K) hC hP0
  have hle : Ideal.span {algebraMap A C a} ≤ P := (Ideal.span_singleton_le_iff_mem _).mpr haP
  have hfl : IsFiniteLength A (C ⧸ P) :=
    (isFiniteLength_quotient_span_algebraMap_of_finiteDimensional (K := K) hC ha).of_surjective
      (f := (Submodule.factor hle).restrictScalars A) (Submodule.factor_surjective hle)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at hfl
  have : IsArtinian C (C ⧸ P) := isArtinian_of_tower A hfl.2
  have : IsArtinianRing (C ⧸ P) := isArtinian_of_tower C this
  exact Ideal.Quotient.maximal_of_isField P (IsArtinianRing.isField_of_isDomain _)

end KrullAkizuki
