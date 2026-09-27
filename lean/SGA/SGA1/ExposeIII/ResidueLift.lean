/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Polynomial.Basic


/-!
# SGA 1, Exposé III, 1.6: lifting residue field extensions

The proof of Corollary III.1.6 uses that for a local ring `A` and a finite extension `k'` of its
residue field `k`, there is a finite free local `A`-algebra `A'` with `A'/𝔪A' = k'` ("reducing step
by step to the case where `k'/k` is monogenic, and then lifting to `A` the coefficients of the
minimal polynomial of a generator"). This is `exists_finite_free_residue_lift`.

The rest of III.1.6 (the local components of `B̂ ⊗ Â'` are power series rings once the residue
extensions become trivial) is `exists_algEquiv_mvPowerSeries_of_formallySmoothLocal` in
`LocalComponents.lean`.
-/

universe u v

namespace SGA.SGA1.ExposeIII

open IsLocalRing Polynomial

variable (A : Type u) [CommRing A] [IsLocalRing A] (K : Type v) [Field K] [Algebra A K]

/-- The monogenic step of the lemma in the proof of III.1.6: adjoining to `A` a root of a monic
lift of the minimal polynomial of `α ∈ K` over the residue field gives a finite free local
`A`-algebra `A₁` with a map `φ : A₁ → K` hitting `α`, whose kernel `𝔪A₁` is the maximal ideal. -/
lemma exists_adjoinRoot_lift (hK : RingHom.ker (algebraMap A K) = maximalIdeal A)
    [Module.Finite A K] (α : K) :
    ∃ (A₁ : Type u) (_ : CommRing A₁) (_ : Algebra A A₁) (_ : IsLocalRing A₁) (φ : A₁ →ₐ[A] K),
      Module.Free A A₁ ∧ Module.Finite A A₁ ∧ α ∈ φ.range ∧
        RingHom.ker φ = (maximalIdeal A).map (algebraMap A A₁) ∧
        RingHom.ker φ = maximalIdeal A₁ := by
  have : IsLocalHom (algebraMap A K) := ⟨fun a ha ↦ by
    by_contra h
    have : a ∈ RingHom.ker (algebraMap A K) := hK ▸ (mem_maximalIdeal _).2 h
    rw [RingHom.mem_ker.1 this] at ha
    exact not_isUnit_zero ha⟩
  let : Algebra (ResidueField A) K := (ResidueField.lift (algebraMap A K)).toAlgebra
  have : IsScalarTower A (ResidueField A) K :=
    IsScalarTower.of_algebraMap_eq fun a ↦ (ResidueField.lift_residue_apply _ a).symm
  have : Module.Finite (ResidueField A) K := Module.Finite.of_restrictScalars_finite A _ K
  set pbar := minpoly (ResidueField A) α
  have hmon : pbar.Monic := minpoly.monic (Algebra.IsIntegral.isIntegral α)
  obtain ⟨p, hpmap, -, hp⟩ := lifts_and_natDegree_eq_and_monic
    (map_surjective (residue A) residue_surjective pbar) hmon
  have hmap (q : A[X]) : aeval α q = aeval α (q.map (residue A)) := by
    rw [← aeval_map_algebraMap (ResidueField A)]
    rfl
  have hroot : p.eval₂ (Algebra.ofId A K : A →+* K) α = 0 := by
    change aeval α p = 0
    rw [hmap, hpmap]
    exact minpoly.aeval _ _
  let φ := AdjoinRoot.liftAlgHom p (Algebra.ofId A K) α hroot
  have hφmk (q : A[X]) : φ (AdjoinRoot.mk p q) = aeval α q := rfl
  -- the kernel of `φ` is `𝔪 A₁`
  have hker : RingHom.ker φ = (maximalIdeal A).map (algebraMap A (AdjoinRoot p)) := by
    refine le_antisymm (fun x hx ↦ ?_) (Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_)
    · obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
      rw [RingHom.mem_ker, hφmk, hmap] at hx
      obtain ⟨rbar, hr⟩ := minpoly.dvd _ _ hx
      obtain ⟨r, rfl⟩ := map_surjective (residue A) residue_surjective rbar
      have hmem : q - p * r ∈ (maximalIdeal A).map (C : A →+* A[X]) := by
        rw [← ker_residue, ← ker_mapRingHom, RingHom.mem_ker, coe_mapRingHom, Polynomial.map_sub,
          Polynomial.map_mul, hr, hpmap, sub_self]
      have : AdjoinRoot.mk p q = AdjoinRoot.mk p (q - p * r) := by
        rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
      rw [this, AdjoinRoot.algebraMap_eq, AdjoinRoot.of, ← Ideal.map_map]
      exact Ideal.mem_map_of_mem _ hmem
    · rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ← RingHom.mem_ker, hK]
      exact ha
  have hcomap : (RingHom.ker φ).comap (algebraMap A (AdjoinRoot p)) = maximalIdeal A := by
    ext a
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, ← RingHom.mem_ker, hK]
  have : Module.Free A (AdjoinRoot p) := .of_basis (AdjoinRoot.powerBasis' hp).basis
  have : Module.Finite A (AdjoinRoot p) := (AdjoinRoot.powerBasis' hp).finite
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have hmax : (RingHom.ker φ).IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap _ (hcomap ▸ maximalIdeal.isMaximal A)
  have huniq (M : Ideal (AdjoinRoot p)) (hM : M.IsMaximal) : M = RingHom.ker φ := by
    have hMc : M.comap (algebraMap A (AdjoinRoot p)) = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M)
    have hle : RingHom.ker φ ≤ M := by
      rw [hker, Ideal.map_le_iff_le_comap, hMc]
    exact (hmax.eq_of_le hM.ne_top hle).symm
  have : IsLocalRing (AdjoinRoot p) := .of_unique_max_ideal ⟨_, hmax, huniq⟩
  exact ⟨AdjoinRoot p, inferInstance, inferInstance, inferInstance, φ, inferInstance,
    inferInstance, ⟨AdjoinRoot.root p, AdjoinRoot.liftAlgHom_root _ _ _ _⟩, hker,
    IsLocalRing.eq_maximalIdeal hmax⟩

/-- III.1.6, the lemma used in its proof: let `A` be a local ring and `K` a finite extension
of its residue field (an `A`-algebra which is a field, finite over `A`, with kernel `𝔪`). There is
a finite free local `A`-algebra `A'` with an `A`-algebra surjection `A' → K` whose kernel is
`𝔪A'`, i.e. `A'/𝔪A' ≅ K`. As in SGA, one proceeds step by step through monogenic extensions and
lifts the minimal polynomial of a generator (`exists_adjoinRoot_lift`). -/
theorem exists_finite_free_residue_lift (hK : RingHom.ker (algebraMap A K) = maximalIdeal A)
    [Module.Finite A K] :
    ∃ (A' : Type u) (_ : CommRing A') (_ : Algebra A A') (_ : IsLocalRing A'),
      Module.Free A A' ∧ Module.Finite A A' ∧ ∃ φ : A' →ₐ[A] K, Function.Surjective φ ∧
        RingHom.ker φ = (maximalIdeal A).map (algebraMap A A') := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.of_restrictScalars_finiteType A A K :
    Algebra.FiniteType A K).out
  induction s using Finset.induction_on generalizing A with
  | empty =>
    have hsurj : Function.Surjective (algebraMap A K) := fun x ↦ by
      have : x ∈ (⊥ : Subalgebra A K) := by
        rw [Finset.coe_empty, Algebra.adjoin_empty] at hs
        rw [hs]; trivial
      exact Algebra.mem_bot.1 this
    refine ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      Algebra.ofId A K, hsurj, ?_⟩
    rw [Algebra.algebraMap_self, Ideal.map_id]
    exact hK
  | insert α s hαs ih =>
    obtain ⟨A₁, _, _, _, φ₁, _, _, ⟨r, hr⟩, hker₁, hmax₁⟩ := exists_adjoinRoot_lift A K hK α
    let : Algebra A₁ K := φ₁.toRingHom.toAlgebra
    have hφ₁ (y : A₁) : algebraMap A₁ K y = φ₁ y := rfl
    have : IsScalarTower A A₁ K := IsScalarTower.of_algebraMap_eq fun a ↦ (φ₁.commutes a).symm
    have : Module.Finite A₁ K := Module.Finite.of_restrictScalars_finite A A₁ K
    have hs₁ : Algebra.adjoin A₁ (s : Set K) = ⊤ := by
      have hle : Algebra.adjoin A ((insert α s : Finset K) : Set K) ≤
          (Algebra.adjoin A₁ (s : Set K)).restrictScalars A := by
        rw [Algebra.adjoin_le_iff, Finset.coe_insert]
        rintro x (rfl | hx)
        · rw [← hr]
          change algebraMap A₁ K r ∈ Algebra.adjoin A₁ (s : Set K)
          exact Subalgebra.algebraMap_mem _ r
        · change x ∈ Algebra.adjoin A₁ (s : Set K)
          exact Algebra.subset_adjoin hx
      refine eq_top_iff.2 fun x _ ↦ hle ?_
      rw [hs]
      trivial
    obtain ⟨A', _, _, _, _, _, ψ, hψ, hkerψ⟩ := ih A₁ (hmax₁ ▸ rfl) hs₁
    let : Algebra A A' := ((algebraMap A₁ A').comp (algebraMap A A₁)).toAlgebra
    have : IsScalarTower A A₁ A' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    refine ⟨A', inferInstance, inferInstance, inferInstance, Module.Free.trans (S := A₁),
      Module.Finite.trans A₁ A', ψ.restrictScalars A, hψ, ?_⟩
    rw [show RingHom.ker (ψ.restrictScalars A) = RingHom.ker ψ from rfl, hkerψ, ← hmax₁, hker₁,
      Ideal.map_map, ← IsScalarTower.algebraMap_eq]

end SGA.SGA1.ExposeIII
