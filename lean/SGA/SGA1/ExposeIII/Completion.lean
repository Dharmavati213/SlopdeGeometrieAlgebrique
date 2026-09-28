/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.LiftingCriteria
import SGA.SGA1.ExposeIII.SmoothLocal
import SGA.SGA1.ExposeIV.CompletionCriterion
import SGA.Foundations.Formal.CompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing

/-!
# SGA 1, Exposé III, 1.2 and 1.9: formal smoothness only depends on the completions

SGA defines formal smoothness of a local homomorphism `A → B` of noetherian local rings
(Definition III.1.1) through the completions `Â → B̂`, and observes (Remark III.1.2) that it only
depends on them. Proposition III.1.9 compares it with smoothness when `B` is a localization of an
`A`-algebra of finite type.

We prove that the lifting property III.2.1 (iii) (`AdicFormallySmooth`) of `B` over `A` is
equivalent to that of `B̂` over `Â` (`adicFormallySmooth_completion_iff`); with III.2.1 for complete
rings this gives:

* `formallySmoothLocal_completion_iff`: `Â → B̂` is formally smooth (Definition III.1.1) if and only
  if `B` has the lifting property III.2.1 (iii) over `A` (Remark III.1.2, and III.2.1 for
  non-complete rings);
* `flat_of_formallySmoothLocal_completion`: Lemma III.1.3 for local rings which need not be
  complete;
* `formallySmooth_iff_formallySmoothLocal_completion`: Proposition III.1.9 in the form of
  Definition III.1.1: a localization `B` of an algebra of finite type over a noetherian local ring
  `A`, with finite residue extension, is smooth over `A` if and only if `B̂` is formally smooth over
  `Â`.

The map `Â → B̂` is `completionRingHom`; it is characterized by its compatibility with the
evaluations `Â → A ⧸ 𝔪ⁿ`, `B̂ → B ⧸ 𝔫ⁿ`.
-/

universe u v

open IsLocalRing

namespace SGA.SGA1.ExposeIII

section Abstract

variable {R : Type*} {B B' : Type v} [CommRing R] [CommRing B] [CommRing B'] [Algebra R B]
  [Algebra R B'] (φ : B →ₐ[R] B') {I : Ideal B} {I' : Ideal B'}
  (hsurj : ∀ n, Function.Surjective ((Ideal.Quotient.mk (I' ^ n)).comp (φ : B →+* B')))
  (hker : ∀ n, (I' ^ n).comap φ = I ^ n)
include hsurj hker

/-- The isomorphism `B ⧸ Iⁿ ≅ B' ⧸ I'ⁿ` induced by `φ`. -/
noncomputable def quotientPowAlgEquiv (n : ℕ) : (B ⧸ I ^ n) ≃ₐ[R] B' ⧸ I' ^ n :=
  (Ideal.quotientEquivAlgOfEq R (by
    rw [← hker n]
    ext b
    simp [Ideal.Quotient.eq_zero_iff_mem])).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := (Ideal.Quotient.mkₐ R (I' ^ n)).comp φ)
      (hsurj n))

lemma quotientPowAlgEquiv_mk (n : ℕ) (b : B) :
    quotientPowAlgEquiv φ hsurj hker n (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (φ b) := rfl

/-- Formal smoothness for adic topologies transfers along a map `φ : B → B'` inducing isomorphisms
`B ⧸ Iⁿ ≅ B' ⧸ I'ⁿ` (e.g. from `B` to its completion): from `B'` to `B`. -/
theorem AdicFormallySmooth.of_quotientPowEquiv (h : AdicFormallySmooth R I') :
    AdicFormallySmooth R I := by
  intro C _ _ J hJ f ⟨n, hn⟩
  let e := quotientPowAlgEquiv φ hsurj hker n
  let f' : B' →ₐ[R] C ⧸ J := ((Ideal.Quotient.liftₐ (I ^ n) f hn).comp e.symm.toAlgHom).comp
    (Ideal.Quotient.mkₐ R (I' ^ n))
  have hf' (b : B) : f' (φ b) = f b := by
    change Ideal.Quotient.liftₐ (I ^ n) f hn (e.symm (Ideal.Quotient.mk _ (φ b))) = f b
    rw [← quotientPowAlgEquiv_mk φ hsurj hker, AlgEquiv.symm_apply_apply]
    rfl
  obtain ⟨g', hg'⟩ := h J hJ f' ⟨n, fun x hx ↦ by
    rw [RingHom.mem_ker]
    change Ideal.Quotient.liftₐ (I ^ n) f hn (e.symm (Ideal.Quotient.mk _ x)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero, map_zero]⟩
  refine ⟨g'.comp φ, AlgHom.ext fun b ↦ ?_⟩
  have := congr($hg' (φ b))
  simp only [AlgHom.comp_apply] at this ⊢
  rw [this, hf']

/-- Formal smoothness for adic topologies transfers along a map `φ : B → B'` inducing isomorphisms
`B ⧸ Iⁿ ≅ B' ⧸ I'ⁿ`: from `B` to `B'`. A lift `B → C` kills a power of `I` since `J` is
nilpotent, hence factors through `B ⧸ Iᴺ ≅ B' ⧸ I'ᴺ`. -/
theorem AdicFormallySmooth.of_quotientPowEquiv' (h : AdicFormallySmooth R I) :
    AdicFormallySmooth R I' := by
  intro C _ _ J hJ f' ⟨n, hn⟩
  obtain ⟨m, hm⟩ := hJ
  have hφ (k : ℕ) : (I ^ k).map φ ≤ I' ^ k := by
    rw [Ideal.map_le_iff_le_comap, hker]
  obtain ⟨g, hg⟩ := h J ⟨m, hm⟩ (f'.comp φ) ⟨n, fun x hx ↦ by
    rw [RingHom.mem_ker, AlgHom.comp_apply]
    exact hn (hφ n (Ideal.mem_map_of_mem _ hx))⟩
  have hgJ : (I ^ n).map g ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
    have := congr($hg x)
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
    rw [this]
    exact hn (hφ n (Ideal.mem_map_of_mem _ hx))
  set N := n * (m + 1)
  have hgN : I ^ N ≤ RingHom.ker g := by
    rw [← Ideal.map_eq_bot_iff_le_ker, pow_mul, Ideal.map_pow, eq_bot_iff]
    refine (Ideal.pow_right_mono hgJ (m + 1)).trans ?_
    rw [pow_succ, hm, Ideal.zero_eq_bot, Ideal.bot_mul]
  let e := quotientPowAlgEquiv φ hsurj hker N
  let g' : B' →ₐ[R] C := ((Ideal.Quotient.liftₐ (I ^ N) g hgN).comp e.symm.toAlgHom).comp
    (Ideal.Quotient.mkₐ R (I' ^ N))
  refine ⟨g', AlgHom.ext fun y ↦ ?_⟩
  obtain ⟨b, hb⟩ := hsurj N (Ideal.Quotient.mk _ y)
  change Ideal.Quotient.mk (I' ^ N) (φ b) = Ideal.Quotient.mk _ y at hb
  have hgy : g' y = g b := by
    change Ideal.Quotient.liftₐ (I ^ N) g hgN (e.symm (Ideal.Quotient.mk _ y)) = g b
    rw [← hb, ← quotientPowAlgEquiv_mk φ hsurj hker, AlgEquiv.symm_apply_apply]
    rfl
  have hle : I' ^ N ≤ I' ^ n := Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n m.succ_pos)
  rw [AlgHom.comp_apply, hgy]
  have := congr($hg b)
  simp only [AlgHom.comp_apply] at this
  rw [this, ← sub_eq_zero, ← map_sub]
  exact hn (hle (Ideal.Quotient.eq.mp hb))

end Abstract

section Completion

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]

/-- The completion of `A` for its maximal ideal. -/
local notation "Â" => AdicCompletion (maximalIdeal A) A

omit [IsNoetherianRing A] in
/-- The evaluations of the completion are compatible. -/
lemma factor_evalₐ {m n : ℕ} (hmn : m ≤ n) (x : Â) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)
      (AdicCompletion.evalₐ (maximalIdeal A) n x) = AdicCompletion.evalₐ (maximalIdeal A) m x := by
  obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective (maximalIdeal A) A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk,
    Ideal.Quotient.eq]
  have := f.2 hmn
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  rw [← neg_mem_iff, neg_sub]
  exact this

/-- `A → Â ⧸ 𝔪̂ⁿ` is surjective with kernel `𝔪ⁿ`. -/
lemma surjective_algebraMap_completion (n : ℕ) :
    Function.Surjective ((Ideal.Quotient.mk (maximalIdeal Â ^ n)).comp (algebraMap A Â)) := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact SGA.SGA1.ExposeIV.algebraMap_quotient_pow_surjective _
    (maximalIdeal A).fg_of_isNoetherianRing n

lemma comap_maximalIdeal_pow_completion (n : ℕ) :
    (maximalIdeal Â ^ n).comap (algebraMap A Â) = maximalIdeal A ^ n := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← SGA.SGA1.ExposeIV.ker_evalₐ_eq_pow _
    (maximalIdeal A).fg_of_isNoetherianRing n]
  ext a
  rw [Ideal.mem_comap, RingHom.mem_ker, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of, Ideal.Quotient.eq_zero_iff_mem]

/-- Two ring maps from `Â` which agree on `A` and kill a power of `𝔪̂` are equal. -/
lemma ringHom_ext_completion {C : Type*} [CommRing C] {α β : Â →+* C}
    (h : α.comp (algebraMap A Â) = β.comp (algebraMap A Â)) {K : ℕ}
    (hα : maximalIdeal Â ^ K ≤ RingHom.ker α) (hβ : maximalIdeal Â ^ K ≤ RingHom.ker β) :
    α = β := by
  ext x
  obtain ⟨a, ha⟩ := surjective_algebraMap_completion A K (Ideal.Quotient.mk _ x)
  rw [RingHom.comp_apply, Ideal.Quotient.eq] at ha
  have h1 : α x = α (algebraMap A Â a) := by
    rw [← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, RingHom.mem_ker.mp (hα ha), neg_zero]
  have h2 : β x = β (algebraMap A Â a) := by
    rw [← sub_eq_zero, ← map_sub, ← neg_sub, map_neg, RingHom.mem_ker.mp (hβ ha), neg_zero]
  rw [h1, h2]
  exact congr($h a)

variable (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

local notation "B̂" => AdicCompletion (maximalIdeal B) B

omit [IsNoetherianRing A] [IsNoetherianRing B] in
lemma pow_maximalIdeal_le_comap (n : ℕ) :
    maximalIdeal A ^ n ≤ (maximalIdeal B ^ n).comap (algebraMap A B) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha ↦ map_nonunit _ a ha) n

/-- The maps `Â → A ⧸ 𝔪ⁿ → B ⧸ 𝔫ⁿ`. -/
noncomputable def completionFamily (n : ℕ) : Â →+* B ⧸ maximalIdeal B ^ n :=
  (Ideal.quotientMap (maximalIdeal B ^ n) (algebraMap A B)
    (pow_maximalIdeal_le_comap A B n)).comp
    (AdicCompletion.evalₐ (maximalIdeal A) n : Â →+* A ⧸ maximalIdeal A ^ n)

omit [IsNoetherianRing A] [IsNoetherianRing B] in
lemma completionFamily_compat {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) hle).comp (completionFamily A B n) =
      completionFamily A B m := by
  ext x
  simp only [completionFamily, RingHom.comp_apply, RingHom.coe_coe]
  rw [← factor_evalₐ A hle x]
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
  rw [← ha]
  rfl

/-- The canonical ring map `Â → B̂` between completions. -/
noncomputable def completionRingHom : Â →+* B̂ :=
  AdicCompletion.liftRingHom (maximalIdeal B) (completionFamily A B)
    fun hle ↦ completionFamily_compat A B hle

omit [IsNoetherianRing A] [IsNoetherianRing B] in
lemma evalₐ_completionRingHom (n : ℕ) (x : Â) :
    AdicCompletion.evalₐ (maximalIdeal B) n (completionRingHom A B x) =
      Ideal.quotientMap (maximalIdeal B ^ n) (algebraMap A B) (pow_maximalIdeal_le_comap A B n)
        (AdicCompletion.evalₐ (maximalIdeal A) n x) :=
  AdicCompletion.evalₐ_liftRingHom _ _ (fun hle ↦ completionFamily_compat A B hle) n x

/-- `B̂` as an `Â`-algebra. -/
noncomputable abbrev completionAlgebra : Algebra Â B̂ := (completionRingHom A B).toAlgebra

attribute [local instance] completionAlgebra

omit [IsNoetherianRing A] [IsNoetherianRing B] in
lemma algebraMap_completion_eq : algebraMap Â B̂ = completionRingHom A B := rfl

instance : IsScalarTower A Â B̂ := IsScalarTower.of_algebraMap_eq fun a ↦ by
  rw [algebraMap_completion_eq]
  refine AdicCompletion.ext_evalₐ fun n ↦ ?_
  simp only [evalₐ_completionRingHom, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

omit [IsNoetherianRing A] in
lemma mem_maximalIdeal_completion_iff {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] (x : AdicCompletion (maximalIdeal R) R) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal R) R) ↔
      AdicCompletion.evalₐ (maximalIdeal R) 1 x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← pow_one (Ideal.map _ _),
    ← SGA.SGA1.ExposeIV.ker_evalₐ_eq_pow _ (maximalIdeal R).fg_of_isNoetherianRing 1,
    RingHom.mem_ker]

lemma map_maximalIdeal_completion_le :
    (maximalIdeal Â).map (algebraMap Â B̂) ≤ maximalIdeal B̂ := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_maximalIdeal_completion_iff, algebraMap_completion_eq,
    evalₐ_completionRingHom, (mem_maximalIdeal_completion_iff x).mp hx, map_zero]

instance : IsLocalHom (algebraMap Â B̂) :=
  ⟨fun x hx ↦ by
    by_contra h
    exact (mem_maximalIdeal _).mp (map_maximalIdeal_completion_le A B
      (Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr h))) hx⟩

omit [IsLocalRing A] [IsNoetherianRing A] [IsLocalHom (algebraMap A B)] in
/-- Remark III.1.2, first half: `B` and its completion `B̂` have the same lifting property
III.2.1 (iii) over `A`, since `B ⧸ 𝔫ⁿ ≅ B̂ ⧸ 𝔫̂ⁿ`. -/
theorem adicFormallySmooth_completion_iff_self :
    AdicFormallySmooth A (maximalIdeal B̂) ↔ AdicFormallySmooth A (maximalIdeal B) := by
  have hsurj : ∀ n, Function.Surjective ((Ideal.Quotient.mk (maximalIdeal B̂ ^ n)).comp
      ((IsScalarTower.toAlgHom A B B̂ : B →ₐ[A] B̂) : B →+* B̂)) :=
    surjective_algebraMap_completion B
  have hker : ∀ n, (maximalIdeal B̂ ^ n).comap (IsScalarTower.toAlgHom A B B̂) =
      maximalIdeal B ^ n :=
    comap_maximalIdeal_pow_completion B
  exact ⟨AdicFormallySmooth.of_quotientPowEquiv _ hsurj hker,
    AdicFormallySmooth.of_quotientPowEquiv' _ hsurj hker⟩

/-- Remark III.1.2, second half: over the completion `Â`, the lifting property III.2.1 (iii) of
`B̂` for `Â`-algebras is equivalent to that for `A`-algebras. A test algebra over `A` receiving a
continuous map from `B̂` is automatically an `Â`-algebra, and an `A`-linear continuous map from
`B̂` is automatically `Â`-linear. -/
theorem adicFormallySmooth_completion_base_iff :
    AdicFormallySmooth Â (maximalIdeal B̂) ↔ AdicFormallySmooth A (maximalIdeal B̂) := by
  have hmap : (maximalIdeal Â).map (algebraMap Â B̂) ≤ maximalIdeal B̂ :=
    map_maximalIdeal_completion_le A B
  -- powers of an ideal mapped into a nilpotent ideal
  have hpow {C : Type u} [CommRing C] {J : Ideal C} {m : ℕ} (hm : J ^ m = 0) {n : ℕ}
      {α : Â →+* C} (hα : (maximalIdeal Â ^ n).map α ≤ J) :
      maximalIdeal Â ^ (n * (m + 1)) ≤ RingHom.ker α := by
    rw [← Ideal.map_eq_bot_iff_le_ker, pow_mul, Ideal.map_pow, eq_bot_iff]
    refine (Ideal.pow_right_mono hα (m + 1)).trans ?_
    rw [pow_succ, hm, Ideal.zero_eq_bot, Ideal.bot_mul]
  have hmapn (n : ℕ) : (maximalIdeal Â ^ n).map (algebraMap Â B̂) ≤ maximalIdeal B̂ ^ n := by
    rw [Ideal.map_pow]; exact Ideal.pow_right_mono hmap n
  constructor
  · -- an `A`-algebra test ring is an `Â`-algebra
    intro h C _ _ J hJ f ⟨n, hn⟩
    obtain ⟨m, hm⟩ := hJ
    set K := n * (m + 1)
    have : IsLocalHom (algebraMap A B̂) := by
      rw [IsScalarTower.algebraMap_eq A B B̂]; infer_instance
    have hA : (maximalIdeal A ^ n).map (algebraMap A C) ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply, ← f.commutes]
      refine hn ?_
      have : (maximalIdeal A ^ n).map (algebraMap A B̂) ≤ maximalIdeal B̂ ^ n := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha ↦
          Ideal.mem_comap.mpr (map_nonunit (algebraMap A B̂) a ha)) n
      exact this (Ideal.mem_map_of_mem _ ha)
    have hAK : maximalIdeal A ^ K ≤ RingHom.ker (algebraMap A C) := by
      rw [← Ideal.map_eq_bot_iff_le_ker, pow_mul, Ideal.map_pow, eq_bot_iff]
      refine (Ideal.pow_right_mono hA (m + 1)).trans ?_
      rw [pow_succ, hm, Ideal.zero_eq_bot, Ideal.bot_mul]
    let θ : Â →+* C := (Ideal.Quotient.lift (maximalIdeal A ^ K) (algebraMap A C)
      fun a ha ↦ hAK ha).comp
        (AdicCompletion.evalₐ (maximalIdeal A) K : Â →+* A ⧸ maximalIdeal A ^ K)
    have hθK : maximalIdeal Â ^ K ≤ RingHom.ker θ := by
      intro x hx
      rw [AdicCompletion.maximalIdeal_eq_map, ← SGA.SGA1.ExposeIV.ker_evalₐ_eq_pow _
        (maximalIdeal A).fg_of_isNoetherianRing K] at hx
      rw [RingHom.mem_ker, RingHom.comp_apply]
      change Ideal.Quotient.lift _ _ _ (AdicCompletion.evalₐ (maximalIdeal A) K x) = 0
      rw [RingHom.mem_ker.mp hx, map_zero]
    let : Algebra Â C := θ.toAlgebra
    have : IsScalarTower A Â C := IsScalarTower.of_algebraMap_eq fun a ↦ by
      have hθa : θ (algebraMap A Â a) = algebraMap A C a := by
        simp only [θ, RingHom.comp_apply, RingHom.coe_coe, AdicCompletion.algebraMap_apply,
          Algebra.algebraMap_self, RingHom.id_apply, AdicCompletion.evalₐ_of]
        rfl
      exact hθa.symm
    -- `f` is `Â`-linear
    have key : (f : B̂ →+* C ⧸ J).comp (algebraMap Â B̂) = algebraMap Â (C ⧸ J) := by
      refine ringHom_ext_completion A ?_ (K := K) ?_ ?_
      · ext a
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply, f.commutes, ← IsScalarTower.algebraMap_apply]
      · refine (Ideal.pow_le_pow_right (Nat.le_mul_of_pos_right n m.succ_pos)).trans ?_
        rw [← Ideal.map_eq_bot_iff_le_ker, eq_bot_iff, ← Ideal.map_map]
        refine (Ideal.map_mono (hmapn n)).trans ?_
        rw [Ideal.map_le_iff_le_comap]
        intro y hy
        exact hn hy
      · refine hθK.trans ?_
        intro x hx
        rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply Â C (C ⧸ J)]
        change Ideal.Quotient.mk J (θ x) = 0
        rw [RingHom.mem_ker.mp hx, map_zero]
    let f' : B̂ →ₐ[Â] C ⧸ J := { (f : B̂ →+* C ⧸ J) with commutes' := fun x ↦ congr($key x) }
    obtain ⟨g, hg⟩ := h J ⟨m, hm⟩ f' ⟨n, hn⟩
    exact ⟨g.restrictScalars A, AlgHom.ext fun y ↦ congr($hg y)⟩
  · -- an `A`-linear lift is `Â`-linear
    intro h C _ _ J hJ f ⟨n, hn⟩
    let : Algebra A C := ((algebraMap Â C).comp (algebraMap A Â)).toAlgebra
    have : IsScalarTower A Â C := IsScalarTower.of_algebraMap_eq' rfl
    obtain ⟨g, hg⟩ := h J hJ (f.restrictScalars A) ⟨n, hn⟩
    obtain ⟨m, hm⟩ := hJ
    have hgJ : (maximalIdeal B̂ ^ n).map g ≤ J := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      have := congr($hg y)
      simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at this
      rw [this]
      exact hn hy
    have key : (g : B̂ →+* C).comp (algebraMap Â B̂) = algebraMap Â C := by
      refine ringHom_ext_completion A ?_ (hpow hm (n := n) ?_) (hpow hm (n := n) ?_)
      · ext a
        simp only [RingHom.comp_apply, RingHom.coe_coe]
        rw [← IsScalarTower.algebraMap_apply, g.commutes, IsScalarTower.algebraMap_apply A Â C]
      · rw [← Ideal.map_map]
        exact (Ideal.map_mono (hmapn n)).trans hgJ
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.algebraMap_eq,
          ← IsScalarTower.algebraMap_apply, ← f.commutes]
        exact hn (hmapn n (Ideal.mem_map_of_mem _ hx))
    exact ⟨{ (g : B̂ →+* C) with commutes' := fun x ↦ congr($key x) },
      AlgHom.ext fun y ↦ congr($hg y)⟩

omit [IsNoetherianRing A] in
/-- The residue extension of `Â → B̂` is finite when that of `A → B` is (they are the same). -/
theorem finite_residueField_completion [Module.Finite A (ResidueField B)] :
    Module.Finite Â (ResidueField B̂) := by
  have : IsLocalHom (IsScalarTower.toAlgHom A B B̂) :=
    ⟨fun b hb ↦ isUnit_of_map_unit (algebraMap B B̂) b hb⟩
  let φ := ResidueField.mapAlgHom (IsScalarTower.toAlgHom A B B̂)
  have hφ : Function.Bijective φ := AdicCompletion.residueField_map_bijective (R := B)
  have : Module.Finite A (ResidueField B̂) :=
    Module.Finite.equiv (AlgEquiv.ofBijective φ hφ).toLinearEquiv
  exact Module.Finite.of_restrictScalars_finite A Â _

/-- Remark III.1.2 and Theorem III.2.1, (i) ⇔ (iii), for local homomorphisms of noetherian local
rings which need not be complete: SGA's Definition III.1.1 applies to the completions `Â → B̂`
(`completionAlgebra`), and `B̂` is formally smooth over `Â` in this sense if and only if `B` has
the lifting property III.2.1 (iii) over `A`. -/
theorem formallySmoothLocal_completion_iff [Module.Finite A (ResidueField B)] :
    FormallySmoothLocal Â B̂ ↔ AdicFormallySmooth A (maximalIdeal B) := by
  have := finite_residueField_completion A B
  rw [formallySmoothLocal_iff_adicFormallySmooth', adicFormallySmooth_completion_base_iff,
    adicFormallySmooth_completion_iff_self]

/-- Proposition III.1.9, in the form of Definition III.1.1: let `B` be a local ring which is a
localization of an algebra of finite type over a noetherian local ring `A`, with `A → B` local
and the residue extension finite. Then `B` is smooth over `A` (formally smooth, as in Exposé II
for such rings) if and only if it is formally smooth in the sense of Definition III.1.1, i.e.
`B̂` is formally smooth over `Â`. -/
theorem formallySmooth_iff_formallySmoothLocal_completion [Module.Finite A (ResidueField B)]
    {P₀ : Type u} [CommRing P₀] [Algebra A P₀] [Algebra P₀ B] [IsScalarTower A P₀ B]
    [Algebra.FiniteType A P₀] (M : Submonoid P₀) [IsLocalization M B] :
    Algebra.FormallySmooth A B ↔ FormallySmoothLocal Â B̂ := by
  rw [formallySmoothLocal_completion_iff, formallySmooth_iff_adicFormallySmooth M]

/-- Lemma III.1.3 for local rings which need not be complete: if `B` is formally smooth over `A`
in the sense of Definition III.1.1 (i.e. `B̂` over `Â`), then `B` is flat over `A`. As in SGA,
`B̂` is flat over `Â` and flatness is invariant under completion (IV.5.8,
`SGA.SGA1.ExposeIV.flat_of_flat_completion`). -/
theorem flat_of_formallySmoothLocal_completion (h : FormallySmoothLocal Â B̂) :
    Module.Flat A B := by
  have hflat : Module.Flat Â B̂ := h.flat
  have hle : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ Ideal.mem_comap.mpr (map_nonunit _ a ha)
  exact SGA.SGA1.ExposeIV.flat_of_flat_completion (M := B) (maximalIdeal A) (maximalIdeal B) hle
    (maximalIdeal_le_jacobson _) (completionRingHom A B) (evalₐ_completionRingHom A B) hflat

end Completion

end SGA.SGA1.ExposeIII
