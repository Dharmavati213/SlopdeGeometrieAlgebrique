/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.TensorProduct.Basic
import SGA.SGA1.ExposeIV.TorOne

/-!
# SGA 1, Exposé IV: the canonical map `gr⁰_I(M) ⊗ gr_I(A) → gr_I(M)`

IV.4.2 and §5 use the canonical surjection `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`. In degree `n`
its source is `M/IM ⊗_{A/I} I^n/I^{n+1} = I^n/I^{n+1} ⊗_A M`, so it is the map
`I^n/I^{n+1} ⊗_A M → I^nM/I^{n+1}M` induced by `a ⊗ m ↦ a m`. We define `grMap I M n` with
target `M/I^{n+1}M` (this does not change injectivity) and the predicate `GrMapInjective I M`
saying that the canonical map is an isomorphism in every degree.

We prove IV.5.1: if `Tor₁^A(M, A/I^n) = 0` for all `n > 0` then the canonical map is an
isomorphism, with the converse when `I` is nilpotent. The converse is deduced from a more general
statement (`torOneVanishes_of_grMapInjective`): if the canonical map is an isomorphism, the
kernel of `I^n ⊗ M → M` lies in `⋂ₖ Iᵏ (I^n ⊗ M)`; this also serves in the noetherian case
(IV.4.2 (b), IV.5.6).
-/

universe u v

namespace SGA.SGA1.ExposeIV

open TensorProduct LinearMap Function

variable {A : Type u} [CommRing A] (I : Ideal A) (M : Type v) [AddCommGroup M] [Module A M]

/-- `I^n/I^{n+1}`, the degree `n` part of `gr_I(A)`. -/
abbrev GrPiece (n : ℕ) : Type u := ↥(I ^ n) ⧸ Submodule.comap (I ^ n).subtype (I ^ (n + 1))

/-- The inclusion `I^{n+1} → I^n`. -/
abbrev powSucc (n : ℕ) : ↥(I ^ (n + 1)) →ₗ[A] ↥(I ^ n) :=
  Submodule.inclusion (Ideal.pow_le_pow_right n.le_succ)

/-- The degree `n` part `I^n/I^{n+1} ⊗_A M → M/I^{n+1}M` of the canonical map
`gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)`, sending `a ⊗ m` to `a m`. -/
noncomputable def grMap (n : ℕ) : GrPiece I n ⊗[A] M →ₗ[A] M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M) :=
  TensorProduct.lift <| (Submodule.comap (I ^ n).subtype (I ^ (n + 1))).liftQ
    (((LinearMap.lsmul A M).compr₂ (Submodule.mkQ _)).comp (I ^ n).subtype) fun a ha ↦ by
      ext m
      change Submodule.Quotient.mk ((a : A) • m) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul (Submodule.mem_comap.1 ha) Submodule.mem_top

/-- The canonical map `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism: it is surjective,
so this means that each `grMap I M n` is injective. -/
def GrMapInjective : Prop := ∀ n, Injective (grMap I M n)

variable {I M}

@[simp]
lemma grMap_tmul (n : ℕ) (a : ↥(I ^ n)) (m : M) :
    grMap I M n (Submodule.Quotient.mk a ⊗ₜ m) = Submodule.Quotient.mk ((a : A) • m) := rfl

/-- `grMap` composed with `I^n ⊗ M → I^n/I^{n+1} ⊗ M` is `I^n ⊗ M → M → M/I^{n+1}M`. -/
lemma grMap_rTensor_mkQ (n : ℕ) (y : ↥(I ^ n) ⊗[A] M) :
    grMap I M n ((Submodule.mkQ _).rTensor M y) =
      Submodule.Quotient.mk (TensorProduct.lid A M ((I ^ n).subtype.rTensor M y)) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy => simp only [map_add, hx, hy, Submodule.Quotient.mk_add]

/-- Right exactness: `I^{n+1} ⊗ M → I^n ⊗ M → I^n/I^{n+1} ⊗ M → 0`. -/
lemma exact_rTensor_powSucc (n : ℕ) :
    Exact ((powSucc I n).rTensor M)
      ((Submodule.mkQ (Submodule.comap (I ^ n).subtype (I ^ (n + 1)))).rTensor M) := by
  refine _root_.rTensor_exact M ?_ (Submodule.mkQ_surjective _)
  rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_inclusion]

lemma rTensor_powSucc_comp (n : ℕ) :
    (I ^ n).subtype ∘ₗ powSucc I n = (I ^ (n + 1)).subtype := rfl

/-- The image of `I^n ⊗ M → M` is `I^n M`. -/
lemma range_lid_rTensor (J : Ideal A) :
    (LinearMap.range (J.subtype.rTensor M)).map (TensorProduct.lid A M : A ⊗[A] M →ₗ[A] M) =
      J • ⊤ :=
  Submodule.map_range_rTensor_subtype_lid

/-- `Tor₁^A(M, A/J) = 0` if and only if `J ⊗ M → M` is injective. -/
lemma torOneVanishes_quotient_iff_rTensor (J : Ideal A) :
    TorOneVanishes A M (A ⧸ J) ↔ Injective (J.subtype.rTensor M) := by
  rw [torOneVanishes_quotient_iff, LinearMap.lTensor_inj_iff_rTensor_inj]

/-- IV.5.1: if `Tor₁^A(M, A/I^n) = 0` for all `n > 0`, the canonical map
`gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism. -/
theorem grMapInjective_of_torOneVanishes (h : ∀ n, 0 < n → TorOneVanishes A M (A ⧸ I ^ n)) :
    GrMapInjective I M := by
  intro n
  have hφ : Injective ((I ^ n).subtype.rTensor M) := by
    rcases n.eq_zero_or_pos with rfl | hn
    · have : Bijective (I ^ 0).subtype := ⟨Subtype.val_injective, fun a ↦ ⟨⟨a, by simp⟩, rfl⟩⟩
      exact (LinearEquiv.rTensor M (LinearEquiv.ofBijective _ this)).injective
    · exact (torOneVanishes_quotient_iff_rTensor _).1 (h n hn)
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.rTensor_surjective M (Submodule.mkQ_surjective _) x
  rw [grMap_rTensor_mkQ, Submodule.Quotient.mk_eq_zero, ← range_lid_rTensor] at hx
  obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hx
  have : (powSucc I n).rTensor M z = y := by
    apply hφ
    apply (TensorProduct.lid A M).injective
    rw [← hz, ← LinearMap.comp_apply, ← LinearMap.rTensor_comp, rTensor_powSucc_comp]
    rfl
  rw [← this]
  exact (exact_rTensor_powSucc n).apply_apply_eq_zero z

/-- The image of `I^{n+1} ⊗ M → I^n ⊗ M` lies in `I (I^n ⊗ M)`. -/
lemma range_rTensor_powSucc_le (n : ℕ) :
    LinearMap.range ((powSucc I n).rTensor M) ≤ I • (⊤ : Submodule A (↥(I ^ n) ⊗[A] M)) := by
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    obtain ⟨a, ha⟩ := a
    have key : ∀ (x : A) (hx : x ∈ I * I ^ n),
        (⟨x, Ideal.mul_le_right hx⟩ : ↥(I ^ n)) ⊗ₜ[A] m ∈
          I • (⊤ : Submodule A (↥(I ^ n) ⊗[A] M)) := by
      intro x hx
      induction hx using Submodule.mul_induction_on' with
      | mem_mul_mem b hb c hc =>
        have : (⟨b * c, Ideal.mul_le_right (Submodule.mul_mem_mul hb hc)⟩ : ↥(I ^ n)) =
            b • ⟨c, hc⟩ := rfl
        rw [this, ← smul_tmul']
        exact Submodule.smul_mem_smul hb trivial
      | add x hx y hy hx' hy' =>
        have : (⟨x + y, Ideal.mul_le_right (add_mem hx hy)⟩ : ↥(I ^ n)) =
            ⟨x, Ideal.mul_le_right hx⟩ + ⟨y, Ideal.mul_le_right hy⟩ := rfl
        rw [this, add_tmul]
        exact add_mem hx' hy'
    exact key a (by rwa [← pow_succ'])
  | add x y hx hy => rw [map_add]; exact add_mem hx hy

/-- If the canonical map `gr⁰_I(M) ⊗ gr_I(A) → gr_I(M)` is an isomorphism, the kernel of
`I^n ⊗ M → M` is contained in `Iᵏ (I^n ⊗ M)` for every `k`. -/
theorem mem_smul_top_of_rTensor_eq_zero (h : GrMapInjective I M) (k : ℕ) :
    ∀ (n : ℕ) (y : ↥(I ^ n) ⊗[A] M), (I ^ n).subtype.rTensor M y = 0 →
      y ∈ I ^ k • (⊤ : Submodule A (↥(I ^ n) ⊗[A] M)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    intro n y hy
    -- `y` comes from `I^{n+1} ⊗ M`, from an element `z` killed in `M`
    have hy' :
        (Submodule.mkQ (Submodule.comap (I ^ n).subtype (I ^ (n + 1)))).rTensor M y = 0 := by
      apply h n
      rw [grMap_rTensor_mkQ, hy, map_zero, Submodule.Quotient.mk_zero, map_zero]
    obtain ⟨z, rfl⟩ := (exact_rTensor_powSucc n y).1 hy'
    have hz : (I ^ (n + 1)).subtype.rTensor M z = 0 := by
      rw [← rTensor_powSucc_comp, LinearMap.rTensor_comp, LinearMap.comp_apply, hy]
    have := Submodule.mem_map_of_mem (f := (powSucc I n).rTensor M) (ih (n + 1) z hz)
    rw [Submodule.map_smul'', Submodule.map_top] at this
    rw [pow_succ, mul_smul]
    exact Submodule.smul_mono le_rfl (range_rTensor_powSucc_le n) this

/-- If the canonical map `gr⁰_I(M) ⊗ gr_I(A) → gr_I(M)` is an isomorphism and `I^n ⊗ M` is
`I`-adically separated, then `Tor₁^A(M, A/I^n) = 0`. -/
theorem torOneVanishes_of_grMapInjective (h : GrMapInjective I M) (n : ℕ)
    (hsep : ∀ y : ↥(I ^ n) ⊗[A] M, (∀ k, y ∈ I ^ k • (⊤ : Submodule A (↥(I ^ n) ⊗[A] M))) →
      y = 0) :
    TorOneVanishes A M (A ⧸ I ^ n) := by
  rw [torOneVanishes_quotient_iff_rTensor, injective_iff_map_eq_zero]
  exact fun y hy ↦ hsep y fun k ↦ mem_smul_top_of_rTensor_eq_zero h k n y hy

/-- IV.5.1, converse: if `I` is nilpotent and the canonical map
`gr⁰_I(M) ⊗ gr_I(A) → gr_I(M)` is an isomorphism, then `Tor₁^A(M, A/I^n) = 0` for all `n`. -/
theorem torOneVanishes_of_grMapInjective_of_isNilpotent (hI : IsNilpotent I)
    (h : GrMapInjective I M) (n : ℕ) : TorOneVanishes A M (A ⧸ I ^ n) := by
  obtain ⟨N, hN⟩ := hI
  refine torOneVanishes_of_grMapInjective h n fun y hy ↦ ?_
  simpa [hN] using hy N

/-- IV.5.1: for a nilpotent ideal `I`, `Tor₁^A(M, A/I^n) = 0` for all `n > 0` if and only if the
canonical map `gr⁰_I(M) ⊗_{A/I} gr_I(A) → gr_I(M)` is an isomorphism. -/
theorem grMapInjective_iff_of_isNilpotent (hI : IsNilpotent I) :
    GrMapInjective I M ↔ ∀ n, 0 < n → TorOneVanishes A M (A ⧸ I ^ n) :=
  ⟨fun h n _ ↦ torOneVanishes_of_grMapInjective_of_isNilpotent hI h n,
    grMapInjective_of_torOneVanishes⟩

end SGA.SGA1.ExposeIV
