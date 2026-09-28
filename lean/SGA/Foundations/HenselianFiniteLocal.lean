/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Unramified.LocalStructure
import SGA.Foundations.HenselianLifting
import SGA.Foundations.HenselianQuasiFinite
import SGA.Foundations.StrictHenselization

/-!
# Local rings finite over a henselian local ring

Let `A` be a henselian local ring and `B` a local ring which is a finite `A`-algebra.

* `IsLocalRing.bijective_algebraMap_of_finite_of_etale`: a finite étale local algebra `E` over a
  local ring `B` with a `B`-point `E → κ(B)` is `B` itself (Nakayama, and faithful flatness).
* `HenselianLocalRing.exists_algHom_lift_of_finite`: an étale `B`-algebra with a point in `κ(B)`
  has a `B`-point lifting it. The étale algebra is quasi-finite over `A`, so its localization
  at the point is finite over `A` (Stacks 04GJ,
  `HenselianLocalRing.exists_notMem_forall_le_and_finite`),
  hence finite étale and local over `B`.
* `HenselianLocalRing.of_finite`: `B` is henselian (Stacks 04GH).
* `IsStrictlyHenselian.of_finite`: if `A` is strictly henselian, so is `B`.
-/

open IsLocalRing Polynomial

universe u

namespace IsLocalRing

/-- A finite étale local algebra `E` over a local ring `B` with a `B`-algebra map `E → κ(B)` is
`B` itself: `B → E` is surjective by Nakayama (`E / 𝔪_B E = κ(E) = κ(B)`) and injective by
faithful flatness. -/
theorem bijective_algebraMap_of_finite_of_etale {B E : Type*} [CommRing B] [IsLocalRing B]
    [CommRing E] [IsLocalRing E] [Algebra B E] [Module.Finite B E] [Algebra.Etale B E]
    (ψ : E →ₐ[B] ResidueField B) : Function.Bijective (algebraMap B E) := by
  have : IsLocalHom (algebraMap B E) := isLocalHom_of_finite (A := B) E
  have hm : (maximalIdeal B).map (algebraMap B E) = maximalIdeal E :=
    Algebra.FormallyUnramified.map_maximalIdeal
  refine ⟨?_, ?_⟩
  · have : Module.FaithfullyFlat B E := .of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective B E
  · -- the kernel of `ψ` is the maximal ideal of `E`
    have hker (e : E) (he : ψ e = 0) : e ∈ maximalIdeal E := by
      by_contra h
      have hu : IsUnit e := by simpa [mem_maximalIdeal, mem_nonunits_iff] using h
      exact (hu.map ψ).ne_zero he
    let N : Submodule B E := LinearMap.range (Algebra.linearMap B E)
    have hN : (⊤ : Submodule B E) ≤ N ⊔ maximalIdeal B • ⊤ := by
      intro e _
      obtain ⟨b, hb⟩ := residue_surjective (ψ e)
      have hmem : e - algebraMap B E b ∈ maximalIdeal E := hker _ (by
        rw [map_sub, AlgHom.commutes]
        change ψ e - residue B b = 0
        rw [hb, sub_self])
      rw [← hm, ← Submodule.restrictScalars_mem B, ← Ideal.smul_top_eq_map] at hmem
      have : e = algebraMap B E b + (e - algebraMap B E b) := by ring
      rw [this]
      exact Submodule.add_mem_sup ⟨b, rfl⟩ hmem
    have htop : (⊤ : Submodule B E) ≤ N :=
      Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
        (maximalIdeal_le_jacobson _) (by simpa using hN)
    intro e
    obtain ⟨b, hb⟩ := htop (Submodule.mem_top (x := e))
    exact ⟨b, hb⟩

end IsLocalRing

namespace HenselianLocalRing

variable {A : Type u} [CommRing A] [HenselianLocalRing A]

set_option backward.isDefEq.respectTransparency false in
/-- Let `B` be a local ring finite over a henselian local ring `A`. Every `B`-algebra map from an
étale `B`-algebra `D` to the residue field of `B` lifts to a `B`-algebra map `D → B`. The
localization of `D` at the kernel is finite over `A` (Stacks 04GJ), hence a finite étale local
`B`-algebra with a `B`-point, which is `B`
(`IsLocalRing.bijective_algebraMap_of_finite_of_etale`). -/
theorem exists_algHom_lift_of_finite {B : Type u} [CommRing B] [IsLocalRing B] [Algebra A B]
    [Module.Finite A B] {D : Type u} [CommRing D] [Algebra B D] [Algebra.Etale B D]
    (τ : D →ₐ[B] ResidueField B) :
    ∃ φ : D →ₐ[B] B, (IsScalarTower.toAlgHom B B (ResidueField B)).comp φ = τ := by
  classical
  have : IsLocalHom (algebraMap A B) := IsLocalRing.isLocalHom_of_finite (A := A) B
  let q : Ideal D := RingHom.ker τ
  have : q.IsPrime := RingHom.ker_isPrime _
  let _ : Algebra A D := ((algebraMap B D).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B D := .of_algebraMap_eq' rfl
  have : Algebra.FiniteType A D := .trans (S := B) inferInstance inferInstance
  have hqB : q.comap (algebraMap B D) = maximalIdeal B := by
    ext b
    simp only [Ideal.mem_comap, q, RingHom.mem_ker, AlgHom.commutes]
    exact residue_eq_zero_iff b
  have : q.LiesOver (maximalIdeal A) := by
    refine ⟨?_⟩
    rw [Ideal.under, IsScalarTower.algebraMap_eq A B D, ← Ideal.comap_comap, hqB]
    exact (eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal B))).symm
  have : Algebra.QuasiFinite B (Localization.AtPrime q) := inferInstance
  have : Algebra.QuasiFiniteAt A q := Algebra.QuasiFinite.trans A B (Localization.AtPrime q)
  obtain ⟨e, heq, hle, hfin⟩ := exists_notMem_forall_le_and_finite (A := A) q
  let E := Localization.Away e
  have : Module.Finite A E := hfin E
  have : Module.Finite B E := .of_restrictScalars_finite A B E
  -- `E` is local, with maximal ideal `q E`
  have hdisj : Disjoint (Submonoid.powers e : Set D) q := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact heq
  let qE : Ideal E := q.map (algebraMap D E)
  have hqE : qE.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint (.powers e) E q
    inferInstance hdisj
  have hle' (M : Ideal E) (hM : M.IsMaximal) : M ≤ qE := by
    have hP : (M.comap (algebraMap D E)).IsPrime := Ideal.comap_isPrime _ _
    have heP : e ∉ M.comap (algebraMap D E) := fun h ↦
      hM.ne_top (M.eq_top_of_isUnit_mem h (IsLocalization.Away.algebraMap_isUnit e))
    rw [← IsLocalization.map_under (.powers e) E M]
    exact Ideal.map_mono (hle _ hP heP)
  have : IsLocalRing E := by
    have : Nontrivial E := ⟨⟨0, 1, fun h ↦ hqE.ne_top (qE.eq_top_iff_one.mpr (h ▸ qE.zero_mem))⟩⟩
    obtain ⟨M, hM⟩ := Ideal.exists_maximal E
    have hMq : M = qE := hM.eq_of_le hqE.ne_top (hle' M hM)
    refine .of_unique_max_ideal ⟨M, hM, fun M' hM' ↦ ?_⟩
    rw [hMq]
    exact hM'.eq_of_le hqE.ne_top (hle' M' hM')
  -- the point `E → κ(B)` extending `τ`
  have hτe : IsUnit (τ e) := isUnit_iff_ne_zero.mpr fun h ↦ heq (RingHom.mem_ker.mpr h)
  let ψ : E →ₐ[B] ResidueField B := IsLocalization.Away.liftAlgHom e hτe
  have hψ (d : D) : ψ (algebraMap D E d) = τ d := IsLocalization.Away.lift_eq e hτe d
  have hbij := IsLocalRing.bijective_algebraMap_of_finite_of_etale ψ
  let iso : B ≃ₐ[B] E := AlgEquiv.ofBijective (Algebra.ofId B E) hbij
  refine ⟨iso.symm.toAlgHom.comp (IsScalarTower.toAlgHom B D E), ?_⟩
  ext d
  have h₁ : algebraMap B E (iso.symm (algebraMap D E d)) = algebraMap D E d :=
    iso.apply_symm_apply _
  have h₂ := congrArg ψ h₁
  rw [AlgHom.commutes, hψ] at h₂
  simpa using h₂

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 04GH**: a local ring which is finite over a henselian local ring is henselian. -/
theorem of_finite (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] [Module.Finite A B] :
    HenselianLocalRing B where
  is_henselian f hf a₀ h₁ h₂ := by
    -- the standard étale `B`-algebra adjoining a root of `f`
    let Q : StandardEtalePair B := ⟨f, hf, derivative f, 1, 0, 1, by ring⟩
    have hx : Q.HasMap (residue B a₀) := by
      refine ⟨?_, ?_⟩
      · change aeval (residue B a₀) f = 0
        rw [← residue_aeval, coe_aeval_eq_eval, residue_eq_zero_iff]
        exact h₁
      · change IsUnit (aeval (residue B a₀) (derivative f))
        rw [← residue_aeval, coe_aeval_eq_eval]
        exact h₂.map _
    obtain ⟨φ, hφ⟩ := exists_algHom_lift_of_finite (A := A) (Q.lift _ hx)
    have hφ' (y : Q.Ring) : residue B (φ y) = Q.lift _ hx y := DFunLike.congr_fun hφ y
    refine ⟨φ Q.X, ?_, ?_⟩
    · change eval (φ Q.X) f = 0
      rw [← eval₂_id, show (RingHom.id B) = (φ : Q.Ring →+* B).comp (algebraMap B Q.Ring) from
        RingHom.ext fun b ↦ (φ.commutes b).symm]
      change eval₂ ((φ : Q.Ring →+* B).comp (algebraMap B Q.Ring)) ((φ : Q.Ring →+* B) Q.X) f = 0
      rw [← hom_eval₂, ← aeval_def]
      change φ (aeval Q.X Q.f) = 0
      rw [StandardEtalePair.hasMap_X.1, map_zero]
    · rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, hφ']
      simp

end HenselianLocalRing

namespace IsStrictlyHenselian

/-- A local ring which is finite over a strictly henselian local ring is strictly henselian: it
is henselian (Stacks 04GH) and its residue field is algebraic over a separably closed field. -/
theorem of_finite {A : Type u} [CommRing A] [IsStrictlyHenselian A] (B : Type u) [CommRing B]
    [IsLocalRing B] [Algebra A B] [Module.Finite A B] : IsStrictlyHenselian B where
  __ := HenselianLocalRing.of_finite (A := A) B
  isSepClosed_residueField := by
    have : IsLocalHom (algebraMap A B) := IsLocalRing.isLocalHom_of_finite (A := A) B
    have : Algebra.IsIntegral (ResidueField A) (ResidueField B) := inferInstance
    exact Algebra.IsAlgebraic.isSepClosed (F := ResidueField A)

end IsStrictlyHenselian
