/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Tactic.LinearCombination

/-!
# Lifting a morphism to `ℙ¹` along a square-zero thickening: the chart algebra

Let `X` be a scheme covered by two affine opens `U₀ = Spec R`, `U₁ = Spec S` with affine
intersection `W = Spec T`. A morphism `X ⟶ ℙ¹` with `U₀`, `U₁` the inverse images of the two
standard charts is the datum of `t ∈ R` and `s ∈ S` with `t s = 1` in `T`. This file contains the
commutative algebra behind lifting such a morphism along a square-zero thickening of `X`. This is
the deformation theory of morphisms (the obstruction lies in `H¹(X₀, g^* T_{ℙ¹})`); SGA 1 III.5–6
treats the deformations of the scheme itself, not of a morphism to `ℙ¹`, and SGA 1 III.7 lifts a
projective curve through an ample line bundle instead:

* `exists_forall_eq_add_pow_mul`: the Čech computation of the vanishing of `H¹` of a sufficiently
  positive twist on two charts. If `R` is generated as a module over `k[τ]` by finitely many
  elements, `T = R[1/τ] = S[1/σ]` and `τ σ = 1` in `T`, then `T = R + τᵉ S` for all `e ≫ 0`
  (for a finite morphism `g : X₀ ⟶ ℙ¹_k` with `τ`, `σ` the pulled back coordinates, this is
  `H¹(ℙ¹, g_* 𝒪(e)) = 0` for `e ≫ 0`, Serre's vanishing theorem on `ℙ¹`, Hartshorne III.5.2).
* `exists_lift_mul_eq_one`: the lifting step. Let `R' → R`, `S' → S`, `T' → T` be surjections
  with kernel `J R'`, … for an ideal `J` of a base ring `Λ` with `J² T' = 0` and `J 𝔪 T' = 0`,
  and let `R₀ = R' / 𝔪 R'`, … be the reductions. If `t s = 1` in `T` and the reductions `t₀`, `s₀`
  satisfy `T₀ = t₀ S₀ + s₀ R₀` (vanishing of `H¹(X₀, g₀^* 𝒪(2))` for the morphism
  `g₀ = (t₀ : s₀)`), then `t`, `s` lift to `t' ∈ R'`, `s' ∈ S'` with `t' s' = 1` in `T'`.

## References

* [SGA 1, III.5–III.7][SGA1]; [Hartshorne, *Algebraic Geometry*, III.5.2]; for the obstruction
  theory of morphisms, [Hartshorne, *Deformation theory*, Theorem 6.2].
-/

open Ideal

namespace AlgebraicGeometry.AmpleLift

section Vanishing

variable {k R S T : Type*} [CommRing k] [CommRing R] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra k S] [Algebra k T]

/-- The elements `ρ a + ρ(τ)ᵉ ρ'(b)` of `T`, as a `k`-submodule. -/
def sumPowMul (ρ : R →ₐ[k] T) (ρ' : S →ₐ[k] T) (τ : R) (e : ℕ) : Submodule k T where
  carrier := {w | ∃ (a : R) (b : S), w = ρ a + ρ τ ^ e * ρ' b}
  add_mem' := by
    rintro _ _ ⟨a, b, rfl⟩ ⟨a', b', rfl⟩
    exact ⟨a + a', b + b', by rw [map_add, map_add]; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  smul_mem' := by
    rintro c _ ⟨a, b, rfl⟩
    refine ⟨c • a, c • b, ?_⟩
    rw [map_smul, map_smul]
    simp only [Algebra.smul_def]
    ring

lemma mem_sumPowMul {ρ : R →ₐ[k] T} {ρ' : S →ₐ[k] T} {τ : R} {e : ℕ} {w : T} :
    w ∈ sumPowMul ρ ρ' τ e ↔ ∃ (a : R) (b : S), w = ρ a + ρ τ ^ e * ρ' b :=
  Iff.rfl

/-- **Vanishing of `H¹` of a positive twist on two charts** (the Čech computation behind Serre's
vanishing theorem on `ℙ¹`, Hartshorne III.5.2): let `ρ : R → T`, `ρ' : S → T` be `k`-algebra
maps, `τ ∈ R`, `σ ∈ S` with `ρ(τ) ρ'(σ) = 1`, such that every element of `T` is of the form
`ρ(r) / ρ(τ)ⁿ` and of the form `ρ'(b) / ρ'(σ)ⁿ`, and `R` is spanned over `k` by the `τʲ e` for `e`
in a finite set (`R` is finite over `k[τ]`). Then `T = ρ(R) + ρ(τ)ᵉ ρ'(S)` for all large `e`. -/
theorem exists_forall_eq_add_pow_mul (ρ : R →ₐ[k] T) (ρ' : S →ₐ[k] T) (τ : R) (σ : S)
    (hτσ : ρ τ * ρ' σ = 1)
    (hR : ∀ w : T, ∃ (r : R) (n : ℕ), w * ρ τ ^ n = ρ r)
    (hS : ∀ w : T, ∃ (b : S) (n : ℕ), w * ρ' σ ^ n = ρ' b)
    (s : Finset R) (hs : Submodule.span k {x | ∃ (j : ℕ) (e : R), e ∈ s ∧ x = τ ^ j * e} = ⊤) :
    ∃ N : ℕ, ∀ e, N ≤ e → ∀ w : T, ∃ (a : R) (b : S), w = ρ a + ρ τ ^ e * ρ' b := by
  choose b n hbn using fun x : R ↦ hS (ρ x)
  refine ⟨s.sup n, fun e he w ↦ ?_⟩
  -- `ρ(x) ρ'(σ)ᴺ ∈ ρ'(S)` for `x ∈ s`
  have hN : ∀ x ∈ s, ρ x * ρ' σ ^ s.sup n = ρ' (b x * σ ^ (s.sup n - n x)) := by
    intro x hx
    have hle : n x ≤ s.sup n := Finset.le_sup hx
    rw [map_mul, map_pow, ← hbn x, mul_assoc, ← pow_add, Nat.add_sub_cancel' hle]
  have hστ : ∀ m : ℕ, ρ τ ^ m * ρ' σ ^ m = 1 := fun m ↦ by rw [← mul_pow, hτσ, one_pow]
  -- every `ρ(r) ρ'(σ)ᵐ` lies in `ρ(R) + ρ(τ)ᵉ ρ'(S)`
  have key : ∀ (r : R) (m : ℕ), ρ r * ρ' σ ^ m ∈ sumPowMul ρ ρ' τ e := by
    intro r m
    have hr : r ∈ Submodule.span k {x | ∃ (j : ℕ) (e : R), e ∈ s ∧ x = τ ^ j * e} := hs ▸ trivial
    induction hr using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, x, hx, rfl⟩ := hx
      rcases le_or_gt m j with hmj | hmj
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmj
        refine ⟨τ ^ d * x, 0, ?_⟩
        rw [map_zero, mul_zero, add_zero, map_mul, map_mul, map_pow, map_pow, pow_add]
        calc ρ τ ^ m * ρ τ ^ d * ρ x * ρ' σ ^ m = (ρ τ ^ m * ρ' σ ^ m) * (ρ τ ^ d * ρ x) := by
              ring
          _ = _ := by rw [hστ, one_mul]
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hmj
        refine ⟨0, b x * σ ^ (s.sup n - n x) * σ ^ (e - s.sup n + d + 1), ?_⟩
        rw [map_zero, zero_add, map_mul, map_mul, ← hN x hx, map_pow, map_pow]
        calc ρ τ ^ j * ρ x * ρ' σ ^ (j + d + 1)
            = (ρ τ ^ j * ρ' σ ^ j) * (ρ x * ρ' σ ^ (d + 1)) := by ring
          _ = ρ x * ρ' σ ^ (d + 1) := by rw [hστ, one_mul]
          _ = (ρ τ ^ e * ρ' σ ^ e) * (ρ x * ρ' σ ^ (d + 1)) := by rw [hστ, one_mul]
          _ = ρ τ ^ e * (ρ x * ρ' σ ^ s.sup n * ρ' σ ^ (e - s.sup n + d + 1)) := by
              have h2 : ρ' σ ^ e = ρ' σ ^ s.sup n * ρ' σ ^ (e - s.sup n) := by
                rw [← pow_add, Nat.add_sub_cancel' he]
              rw [h2]
              ring
    | zero => simp [(sumPowMul ρ ρ' τ e).zero_mem]
    | add x y _ _ hx hy => simpa [add_mul] using (sumPowMul ρ ρ' τ e).add_mem hx hy
    | smul c x _ hx =>
      have := (sumPowMul ρ ρ' τ e).smul_mem c hx
      rwa [map_smul, smul_mul_assoc]
  obtain ⟨r, m, hrm⟩ := hR w
  have hw : w = ρ r * ρ' σ ^ m := by
    rw [← hrm, mul_assoc, ← mul_pow, hτσ, one_pow, mul_one]
  exact hw ▸ key r m

end Vanishing

section Lift

variable {Λ R' S' T' R S T R₀ S₀ T₀ : Type*} [CommRing Λ] [CommRing R'] [CommRing S']
  [CommRing T'] [CommRing R] [CommRing S] [CommRing T] [CommRing R₀] [CommRing S₀] [CommRing T₀]
  [Algebra Λ R'] [Algebra Λ S'] [Algebra Λ T']

/-- **Lifting the coordinates of a morphism to `ℙ¹` along a square-zero thickening** (deformation
of a morphism `X₀ ⟶ ℙ¹` on two charts, with obstruction in `H¹(X₀, g^* T_{ℙ¹})`; this is not in
SGA 1, which lifts an ample line bundle instead, III.7.1). Let `J`, `𝔪` be ideals of `Λ` with `J²`
and `J 𝔪` acting as zero on `T'`.
Let `ρ' : R' → T'`, `σ' : S' → T'` be `Λ`-algebra maps (the restrictions from the two charts to
their intersection), with reductions `πR : R' → R`, `πS : S' → S`, `πT : T' → T`, surjective onto
`R` and `S`, with kernels `J R'`, `J S'`, `J T'`, and with reductions `R' → R₀ = R' / 𝔪 R'`, … that
factor through `R`, `S` (the kernel of `T' → T₀` is contained in `𝔪 T'`). Let `t ∈ R`, `s ∈ S`
with `t s = 1` in `T`, and assume that their images `t₀`, `s₀` satisfy `T₀ = t₀ S₀ + s₀ R₀`. Then
`t`, `s` lift to `t' ∈ R'`, `s' ∈ S'` with `t' s' = 1` in `T'`. -/
theorem exists_lift_mul_eq_one (J 𝔪 : Ideal Λ) (hJJ : J * J ≤ RingHom.ker (algebraMap Λ T'))
    (hJ𝔪 : J * 𝔪 ≤ RingHom.ker (algebraMap Λ T'))
    (ρ' : R' →ₐ[Λ] T') (σ' : S' →ₐ[Λ] T')
    (πR : R' →+* R) (πS : S' →+* S) (πT : T' →+* T) (ρ : R →+* T) (σm : S →+* T)
    (hπR : Function.Surjective πR) (hπS : Function.Surjective πS)
    (hρ : ∀ x, πT (ρ' x) = ρ (πR x)) (hσ : ∀ x, πT (σ' x) = σm (πS x))
    (hkR : RingHom.ker πR = J.map (algebraMap Λ R'))
    (hkS : RingHom.ker πS = J.map (algebraMap Λ S'))
    (hkT : RingHom.ker πT = J.map (algebraMap Λ T'))
    (ψR : R →+* R₀) (ψS : S →+* S₀) (π₀T : T' →+* T₀) (ρ₀ : R₀ →+* T₀) (σ₀ : S₀ →+* T₀)
    (hψR : Function.Surjective (ψR.comp πR)) (hψS : Function.Surjective (ψS.comp πS))
    (hρ₀ : ∀ x, π₀T (ρ' x) = ρ₀ (ψR (πR x))) (hσ₀ : ∀ x, π₀T (σ' x) = σ₀ (ψS (πS x)))
    (hk₀T : RingHom.ker π₀T ≤ 𝔪.map (algebraMap Λ T'))
    (t : R) (s : S) (hts : ρ t * σm s = 1)
    (H : ∀ w₀ : T₀, ∃ (r₀ : R₀) (u₀ : S₀), w₀ = ρ₀ (ψR t) * σ₀ u₀ + σ₀ (ψS s) * ρ₀ r₀) :
    ∃ (t' : R') (s' : S'), πR t' = t ∧ πS s' = s ∧ ρ' t' * σ' s' = 1 := by
  obtain ⟨t₁, rfl⟩ := hπR t
  obtain ⟨s₁, rfl⟩ := hπS s
  -- the elements `ρ'(t₁) σ'(β) + ρ'(α) σ'(s₁)`, `α ∈ J R'`, `β ∈ J S'`
  let P : T' → Prop := fun x ↦ ∃ α ∈ J.map (algebraMap Λ R'), ∃ β ∈ J.map (algebraMap Λ S'),
    ρ' t₁ * σ' β + ρ' α * σ' s₁ = x
  have hPadd : ∀ x y, P x → P y → P (x + y) := by
    rintro x y ⟨α, hα, β, hβ, rfl⟩ ⟨α', hα', β', hβ', rfl⟩
    exact ⟨α + α', add_mem hα hα', β + β', add_mem hβ hβ', by rw [map_add, map_add]; ring⟩
  -- the generators `w a`, `a ∈ J`
  have hgen : ∀ (a : Λ), a ∈ J → ∀ w : T', P (w * algebraMap Λ T' a) := by
    intro a ha w
    obtain ⟨r₀, u₀, hw⟩ := H (π₀T w)
    obtain ⟨r, hr⟩ := hψR r₀
    obtain ⟨u, hu⟩ := hψS u₀
    have hdiff : w - (ρ' t₁ * σ' u + σ' s₁ * ρ' r) ∈ RingHom.ker π₀T := by
      rw [RingHom.mem_ker, map_sub, map_add, map_mul, map_mul, hρ₀, hσ₀, hρ₀, hσ₀]
      simp only [RingHom.comp_apply] at hr hu
      rw [hr, hu, ← hw, sub_self]
    have hzero : ∀ y ∈ 𝔪.map (algebraMap Λ T'), y * algebraMap Λ T' a = 0 := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨b, hb, rfl⟩ := hx
        rw [← map_mul, mul_comm]
        exact RingHom.mem_ker.mp (hJ𝔪 (Ideal.mul_mem_mul ha hb))
      | zero => simp
      | add x y _ _ hx hy => rw [add_mul, hx, hy, add_zero]
      | smul c x _ hx => rw [smul_eq_mul, mul_assoc, hx, mul_zero]
    have h := hzero _ (hk₀T hdiff)
    refine ⟨algebraMap Λ R' a * r, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha),
      algebraMap Λ S' a * u, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha), ?_⟩
    rw [map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
    rw [sub_mul, sub_eq_zero] at h
    rw [h]
    ring
  have hP : ∀ x ∈ J.map (algebraMap Λ T'), ∀ w : T', P (w * x) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact hgen a ha
    | zero => intro w; exact ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
    | add x y _ _ hx hy => intro w; rw [mul_add]; exact hPadd _ _ (hx w) (hy w)
    | smul c x _ hx => intro w; rw [smul_eq_mul, ← mul_assoc]; exact hx (w * c)
  -- the error `ρ'(t₁) σ'(s₁) - 1` lies in `J T'`
  have hε : ρ' t₁ * σ' s₁ - 1 ∈ J.map (algebraMap Λ T') := by
    rw [← hkT, RingHom.mem_ker, map_sub, map_mul, hρ, hσ, map_one, hts, sub_self]
  obtain ⟨α, hα, β, hβ, hαβ⟩ := hP _ hε (-1)
  -- the product of two elements of `J T'` vanishes
  have hJ2 : ∀ x ∈ J.map (algebraMap Λ R'), ∀ y ∈ J.map (algebraMap Λ S'), ρ' x * σ' y = 0 := by
    intro x hx y hy
    have hx' : ρ' x ∈ J.map (algebraMap Λ T') := by
      have := Ideal.mem_map_of_mem ρ'.toRingHom hx
      rwa [Ideal.map_map, show ρ'.toRingHom.comp (algebraMap Λ R') = algebraMap Λ T' from
        ρ'.comp_algebraMap] at this
    have hy' : σ' y ∈ J.map (algebraMap Λ T') := by
      have := Ideal.mem_map_of_mem σ'.toRingHom hy
      rwa [Ideal.map_map, show σ'.toRingHom.comp (algebraMap Λ S') = algebraMap Λ T' from
        σ'.comp_algebraMap] at this
    have := Ideal.mul_mem_mul hx' hy'
    rwa [← Ideal.map_mul, (Ideal.map_eq_bot_iff_le_ker _).mpr hJJ, Ideal.mem_bot] at this
  refine ⟨t₁ + α, s₁ + β, ?_, ?_, ?_⟩
  · have hα0 : πR α = 0 := by rw [← RingHom.mem_ker, hkR]; exact hα
    rw [map_add, hα0, add_zero]
  · have hβ0 : πS β = 0 := by rw [← RingHom.mem_ker, hkS]; exact hβ
    rw [map_add, hβ0, add_zero]
  · rw [map_add, map_add]
    linear_combination hαβ + hJ2 α hα β hβ

end Lift

end AlgebraicGeometry.AmpleLift
