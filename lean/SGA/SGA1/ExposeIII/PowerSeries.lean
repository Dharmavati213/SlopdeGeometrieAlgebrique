/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.FormallySmooth
import Mathlib.RingTheory.AdicCompletion.Functoriality
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Nakayama

/-!
# SGA 1, Exposé III, 2.2–2.3: recognising power series rings

Corollary III.2.3: let `A → B` be a local homomorphism of noetherian local rings with `B`
complete, and `u : B → A⟦t₁, …, tₙ⟧` a local `A`-homomorphism inducing an isomorphism of
relative cotangent spaces `𝔫/(𝔫² + 𝔪B) ≅ 𝔫₁/(𝔫₁² + 𝔪B₁)`. Then `u` is an isomorphism. This is
the implication (v) ⇒ (i) of Corollary III.2.2 (and it recovers III.1.5).

SGA proves surjectivity by completeness and constructs an inverse. We prove surjectivity with
mathlib's complete Nakayama lemma (`surjective_of_mk_map_comp_surjective`), and injectivity by
splitting `u` with the lifting property of the power series ring (III.2.1 (iii) ⇒ (ii),
`AdicFormallySmooth.exists_lift_of_isLocalRing`): the kernel `K` then satisfies `K = 𝔫 K`.

The implication (iv ter) ⇒ (v) (constructing `u`) is in `PowerSeriesStructure.lean`.
-/

universe u

open IsLocalRing

namespace SGA.SGA1.ExposeIII

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A]
  [IsNoetherianRing A] [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)]
  [IsAdicComplete (maximalIdeal B) B] {n : ℕ}


/-- III.2.3: a local `A`-homomorphism `u : B → A⟦t₁, …, tₙ⟧`, with `B` complete, which induces a
bijection `𝔫/(𝔫² + 𝔪B) → 𝔫₁/(𝔫₁² + 𝔪B₁)` of relative cotangent spaces, is an isomorphism.
The bijectivity of the induced map is stated as `hsurj` and `hinj`. -/
theorem bijective_of_cotangent (u : B →ₐ[A] MvPowerSeries (Fin n) A) [IsLocalHom u]
    (hsurj : ∀ y ∈ maximalIdeal (MvPowerSeries (Fin n) A), ∃ x ∈ maximalIdeal B,
      u x - y ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)))
    (hinj : ∀ x ∈ maximalIdeal B, u x ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)) →
      x ∈ maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)) :
    Function.Bijective u := by
  set B₁ := MvPowerSeries (Fin n) A
  set 𝔫₁ := maximalIdeal B₁
  set 𝔫 := maximalIdeal B
  have hloc : ∀ x, u x ∈ 𝔫₁ ↔ x ∈ 𝔫 := fun x ↦ by
    simp only [𝔫₁, 𝔫, mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun h hx ↦ h (hx.map u), fun h hx ↦ h (isUnit_of_map_unit u x hx)⟩
  -- the images of `𝔪` lie in `u(𝔫)`
  have h𝔪 : (maximalIdeal A).map (algebraMap A B₁) ≤ 𝔫.map u := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ← u.commutes]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr
      (map_nonunit (algebraMap A B) a ((mem_maximalIdeal _).mp ha)))
  -- (a) `u(𝔫)` generates `𝔫₁`
  have hgen : 𝔫.map u = 𝔫₁ := by
    refine le_antisymm (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ (hloc x).mpr hx) ?_
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) fun y hy ↦ ?_
    obtain ⟨x, hx, hxy⟩ := hsurj y hy
    have : y = u x - (u x - y) := by ring
    rw [this]
    refine Submodule.sub_mem _ (Submodule.mem_sup_left (Ideal.mem_map_of_mem _ hx)) ?_
    obtain ⟨p, hp, q, hq, hpq⟩ := Submodule.mem_sup.mp hxy
    rw [← hpq]
    refine Submodule.add_mem _ (Submodule.mem_sup_right ?_) (Submodule.mem_sup_left (h𝔪 hq))
    rwa [smul_eq_mul, ← pow_two]
  -- (b) `u` is surjective, by completeness of `B`
  have hsurj' : Function.Surjective u := by
    have : IsHausdorff (𝔫.map u.toRingHom) B₁ := by
      rw [show 𝔫.map u.toRingHom = 𝔫₁ from hgen]
      infer_instance
    refine surjective_of_mk_map_comp_surjective (I := 𝔫) u.toRingHom fun y ↦ ?_
    obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨algebraMap A B (MvPowerSeries.constantCoeff F), ?_⟩
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, u.commutes,
      show Ideal.map (u : B →+* B₁) 𝔫 = 𝔫₁ from hgen, Ideal.Quotient.eq]
    rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp [MvPowerSeries.algebraMap_apply]
  -- (c) `u` has a section `s`, by formal smoothness of `B₁` and completeness of `B`
  refine ⟨?_, hsurj'⟩
  set K := RingHom.ker (u : B →+* B₁)
  let e : (B ⧸ K) ≃ₐ[A] B₁ := Ideal.quotientKerAlgEquivOfSurjective hsurj'
  have hFS : AdicFormallySmooth A 𝔫₁ :=
    adicFormallySmooth_mvPowerSeries.mono (Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i ↦
      (mem_maximalIdeal _).mpr (by
        rw [mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
          MvPowerSeries.constantCoeff_X]
        exact not_isUnit_zero)))
  have hK : K ≠ ⊤ := fun h ↦ by
    have : (1 : B) ∈ K := h ▸ Submodule.mem_top
    simp [K] at this
  have : IsLocalHom (e.symm.toAlgHom : B₁ →ₐ[A] B ⧸ K) :=
    ⟨fun y hy ↦ by simpa using hy.map e⟩
  obtain ⟨s, hs⟩ := hFS.exists_lift_of_isLocalRing (C := B) hK e.symm.toAlgHom
  have hus (y : B₁) : u (s y) = y := by
    have h1 : Ideal.Quotient.mk K (s y) = e.symm y := congr($hs y)
    have h2 : e (Ideal.Quotient.mk K (s y)) = u (s y) :=
      Ideal.quotientKerAlgEquivOfSurjective_mk hsurj' _
    rw [← h2, h1, AlgEquiv.apply_symm_apply]
  have hπK (b : B) : b - s (u b) ∈ K := by
    rw [RingHom.mem_ker]; simp [hus]
  have hπ𝔫 {b : B} (hb : b ∈ 𝔫) : s (u b) ∈ 𝔫 := (hloc _).mp (by rw [hus]; exact (hloc b).mpr hb)
  have hsub (x y : B) : x + y - s (u (x + y)) = (x - s (u x)) + (y - s (u y)) := by
    rw [map_add, map_add]; ring
  have hsq : ∀ p ∈ 𝔫 * 𝔫, p - s (u p) ∈ 𝔫 * K := fun p hp ↦
    Submodule.mul_induction_on (C := fun p ↦ p - s (u p) ∈ 𝔫 * K) hp
      (fun a ha b hb ↦ by
        rw [show a * b - s (u (a * b)) = b * (a - s (u a)) + s (u a) * (b - s (u b)) by
          simp only [map_mul]; ring]
        exact add_mem (Ideal.mul_mem_mul hb (hπK a)) (Ideal.mul_mem_mul (hπ𝔫 ha) (hπK b)))
      (fun x y hx hy ↦ by rw [hsub]; exact add_mem hx hy)
  have hq𝔫 : (maximalIdeal A).map (algebraMap A B) ≤ 𝔫 :=
    Ideal.map_le_iff_le_comap.mpr fun a ha ↦ (mem_maximalIdeal _).mpr
      (map_nonunit (algebraMap A B) a ((mem_maximalIdeal _).mp ha))
  have hmB : ∀ q ∈ (maximalIdeal A).map (algebraMap A B), q - s (u q) ∈ 𝔫 * K := by
    intro q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, -, rfl⟩ := hx
      rw [u.commutes, s.commutes, sub_self]
      exact zero_mem _
    | zero => simp
    | add x y _ _ hx hy => rw [hsub]; exact add_mem hx hy
    | smul c x hx' hx =>
      rw [smul_eq_mul, show c * x - s (u (c * x)) =
          c * (x - s (u x)) + s (u x) * (c - s (u c)) by simp only [map_mul]; ring]
      exact add_mem (Ideal.mul_mem_left _ c hx) (Ideal.mul_mem_mul (hπ𝔫 (hq𝔫 hx')) (hπK c))
  have hkey : ∀ z ∈ 𝔫 ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B), z - s (u z) ∈ 𝔫 * K := by
    intro z hz
    obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hz
    rw [hsub]
    exact add_mem (hsq p (by rwa [pow_two] at hp)) (hmB q hq)
  have hle : K ≤ 𝔫 • K := by
    intro k hk
    have hk0 : u k = 0 := hk
    have hk𝔫 : k ∈ 𝔫 := (hloc k).mp (by rw [hk0]; exact zero_mem _)
    have := hkey k (hinj k hk𝔫 (by rw [hk0]; exact zero_mem _))
    rwa [hk0, map_zero, sub_zero] at this
  have hbot : K = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔫 K
    (IsNoetherian.noetherian _) hle (maximalIdeal_le_jacobson _)
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hbot

/-- III.2.2, (v) ⇒ (i): under the hypotheses of III.2.3, `B` is `A`-isomorphic to a power series
ring over `A`, hence formally smooth over `A` (III.1.5, `formallySmoothLocal_mvPowerSeries`). -/
noncomputable def algEquivOfCotangent (u : B →ₐ[A] MvPowerSeries (Fin n) A) [IsLocalHom u]
    (hsurj : ∀ y ∈ maximalIdeal (MvPowerSeries (Fin n) A), ∃ x ∈ maximalIdeal B,
      u x - y ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)))
    (hinj : ∀ x ∈ maximalIdeal B, u x ∈ maximalIdeal (MvPowerSeries (Fin n) A) ^ 2 ⊔
        (maximalIdeal A).map (algebraMap A (MvPowerSeries (Fin n) A)) →
      x ∈ maximalIdeal B ^ 2 ⊔ (maximalIdeal A).map (algebraMap A B)) :
    B ≃ₐ[A] MvPowerSeries (Fin n) A :=
  AlgEquiv.ofBijective u (bijective_of_cotangent u hsurj hinj)

end SGA.SGA1.ExposeIII
