/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.LiftingCriteria
import Mathlib.RingTheory.Smooth.Quotient
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# SGA 1, Exposé III, 1.7: formal smoothness is flatness plus smoothness of the closed fibre

Corollary III.1.7: a local homomorphism `A → B` (noetherian, finite residue extension) is formally
smooth if and only if `B` is flat over `A` and the closed fibre `B/𝔪B = k ⊗[A] B` is formally smooth
over the residue field `k` of `A`.

SGA reduces to a trivial residue extension by a finite free local extension `A'` (III.1.4) and
then observes that the proof of III.1.5 shows that `B` is a power series ring over `A`. We follow
this. With trivial residue extension (`exists_algEquiv_mvPowerSeries_of_flat`): a basis of the
relative cotangent space gives a surjection `v : A⟦t₁, …, tₙ⟧ → B` (complete Nakayama); formal
smoothness of the fibre gives a section of the reduction `A⟦t⟧ ⧸ 𝔪 → k ⊗ B`, which forces the
kernel `K` of `v` into `𝔪 A⟦t⟧`; flatness of `B` gives `K = 𝔪 K`, hence `K = 0`.

The fibre condition is formal smoothness of `k ⊗[A] B` over `k` for the `𝔫`-adic topology (the
lifting property III.2.1 (iii)).
-/

universe u

open IsLocalRing TensorProduct MvPowerSeries

namespace SGA.SGA1.ExposeIII

section Lemmas

/-- A surjective ring map between local rings maps the maximal ideal into the maximal ideal. -/
lemma map_maximalIdeal_le_of_surjective {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Surjective f) :
    (maximalIdeal R).map f ≤ maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  obtain ⟨y, hy⟩ := hf (hu.unit⁻¹ : Sˣ)
  have h1 : f (x * y - 1) = 0 := by rw [map_sub, map_mul, map_one, hy, hu.mul_val_inv, sub_self]
  have h2 : IsUnit (x * y - 1) := by
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (x * y)
      (Ideal.mul_mem_right _ _ hx)
    rw [show x * y - 1 = -(1 - x * y) by ring]
    exact this.neg
  exact not_isUnit_zero (h1 ▸ h2.map f)

/-- In a noetherian local ring, every ideal is closed for the maximal-adic topology (Krull). -/
lemma mem_of_forall_mem_sup_pow {C : Type*} [CommRing C] [IsLocalRing C] [IsNoetherianRing C]
    {J : Ideal C} {c : C} (hc : ∀ q, c ∈ J ⊔ maximalIdeal C ^ q) : c ∈ J := by
  have hK := (maximalIdeal C).iInf_pow_smul_eq_bot_of_isLocalRing (M := C ⧸ J)
    (maximalIdeal.isMaximal C).ne_top
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have : Ideal.Quotient.mk J c ∈ (⨅ i : ℕ, maximalIdeal C ^ i • ⊤ : Submodule C (C ⧸ J)) := by
    refine Submodule.mem_iInf _ |>.mpr fun q ↦ ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp (hc q)
    rw [map_add, Ideal.Quotient.eq_zero_iff_mem.mpr ha, zero_add]
    have := Submodule.smul_mem_smul hb (Submodule.mem_top (x := (1 : C ⧸ J)))
    simpa [Algebra.smul_def] using this
  rwa [hK] at this

/-- The splitting argument of III.2.3: in a noetherian local ring `P`, an ideal `J ⊆ 𝔫²` which is
the kernel of an idempotent-like endomorphism `σ` (`p ≡ σ p` modulo `J`, and `σ` kills `J`)
satisfies `J = 𝔫 J`, hence is zero. -/
lemma eq_bot_of_forall_sub_mem {P : Type*} [CommRing P] [IsLocalRing P] [IsNoetherianRing P]
    {J : Ideal P} (σ : P →+* P) (h1 : ∀ p, p - σ p ∈ J) (h2 : ∀ q ∈ J, σ q = 0)
    (hJ : J ≤ maximalIdeal P ^ 2) : J = ⊥ := by
  set 𝔫 := maximalIdeal P
  have hJ𝔫 : J ≤ 𝔫 := hJ.trans (Ideal.pow_le_self two_ne_zero)
  have hσ {p : P} (hp : p ∈ 𝔫) : σ p ∈ 𝔫 := by
    rw [show σ p = p - (p - σ p) by ring]
    exact sub_mem hp (hJ𝔫 (h1 p))
  have hsq : ∀ p ∈ 𝔫 * 𝔫, p - σ p ∈ 𝔫 * J := fun p hp ↦
    Submodule.mul_induction_on (C := fun p ↦ p - σ p ∈ 𝔫 * J) hp
      (fun a ha b hb ↦ by
        rw [show a * b - σ (a * b) = b * (a - σ a) + σ a * (b - σ b) by rw [map_mul]; ring]
        exact add_mem (Ideal.mul_mem_mul hb (h1 a)) (Ideal.mul_mem_mul (hσ ha) (h1 b)))
      (fun x y hx hy ↦ by
        rw [show x + y - σ (x + y) = (x - σ x) + (y - σ y) by rw [map_add]; ring]
        exact add_mem hx hy)
  have hle : J ≤ 𝔫 • J := by
    intro q hq
    have := hsq q (by rw [← pow_two]; exact hJ hq)
    rwa [h2 q hq, sub_zero] at this
  exact Submodule.eq_bot_of_le_smul_of_le_jacobson_bot 𝔫 J (IsNoetherian.noetherian _) hle
    (maximalIdeal_le_jacobson _)

end Lemmas

section Trivial

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] [IsNoetherianRing A] [IsNoetherianRing B]
  [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A] [IsNoetherianRing B]
  [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B] in
/-- The reduction `B → k ⊗[A] B` kills `𝔪 B`. -/
lemma map_maximalIdeal_le_ker_includeRight :
    (maximalIdeal A).map (algebraMap A B) ≤
      RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[A] ResidueField A ⊗[A] B) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes,
    IsScalarTower.algebraMap_apply A (ResidueField A), ResidueField.algebraMap_eq,
    (residue_eq_zero_iff a).mpr ha, map_zero]

/-- III.1.7 with trivial residue extension (and III.1.5 in its refined form): let `A → B` be a
local homomorphism of complete noetherian local rings with trivial residue extension. If `B` is
flat over `A` and the closed fibre `k ⊗[A] B` is formally smooth over `k` (for its `𝔫`-adic
topology), then `B` is `A`-isomorphic to a power series ring over `A`. -/
theorem exists_algEquiv_mvPowerSeries_of_flat
    (htriv : ∀ b : B, ∃ a : A, b - algebraMap A B a ∈ maximalIdeal B) [Module.Flat A B]
    (hfib : AdicFormallySmooth (ResidueField A)
      ((maximalIdeal B).map (Algebra.TensorProduct.includeRight :
        B →ₐ[A] ResidueField A ⊗[A] B))) :
    ∃ n, Nonempty (B ≃ₐ[A] MvPowerSeries (Fin n) A) := by
  classical
  obtain ⟨n, x, hx, hind⟩ := exists_isCotangentFamily (A := A) (B := B)
  set R := MvPowerSeries (Fin n) A
  set Q := relCotangentIdeal A B
  set w₀ := cotangentMap (A := A) x hx.1
  have hw₀ : Function.Surjective w₀ := cotangentMap_surjective hx htriv
  have hker₀ : RingHom.ker w₀ = relCotangentIdeal A R := ker_cotangentMap hx hind
  have : IsAdicComplete (maximalIdeal R) R := isAdicComplete_maximalIdeal
  have hQ : Q ≤ maximalIdeal B := relCotangentIdeal_le
  have hQtop : Q ≠ ⊤ := fun h ↦ (maximalIdeal.isMaximal B).ne_top (eq_top_iff.mpr (h ▸ hQ))
  -- `w₀` is local
  have hw₀loc : IsLocalHom w₀ := ⟨fun F hF ↦ by
    by_contra h
    have hF' : F ∈ maximalIdeal R := (mem_maximalIdeal _).mpr h
    have hmem : algebraMap A B (constantCoeff F) +
        ∑ i, algebraMap A B (coeff (Finsupp.single i 1) F) * x i ∈ maximalIdeal B :=
      (linear_mem_maximalIdeal_iff hx _ _).mpr (constantCoeff_mem_maximalIdeal_iff.mpr hF')
    have := isLocalHom_of_le_jacobson_bot Q (hQ.trans (maximalIdeal_le_jacobson _))
    rw [cotangentMap_apply] at hF
    exact (mem_maximalIdeal _).mp hmem (isUnit_of_map_unit _ _ hF)⟩
  obtain ⟨v, hv⟩ := (adicFormallySmooth_of_algEquiv_mvPowerSeries
    (AlgEquiv.refl : R ≃ₐ[A] R)).exists_lift_of_isLocalRing (C := B) hQtop w₀
  have hv' (F : R) : Ideal.Quotient.mk Q (v F) = w₀ F := congr($hv F)
  have hvloc : IsLocalHom v := ⟨fun F hF ↦ by
    have : IsUnit (w₀ F) := by rw [← hv']; exact hF.map _
    exact isUnit_of_map_unit w₀ F this⟩
  -- `v` is surjective, by complete Nakayama
  set N := (maximalIdeal R).map v
  have hN : N ≤ maximalIdeal B :=
    Ideal.map_le_iff_le_comap.mpr fun F hF ↦ Ideal.mem_comap.mpr ((mem_maximalIdeal _).mpr
      fun hu ↦ (mem_maximalIdeal _).mp hF (isUnit_of_map_unit v F hu))
  have h𝔪B : (maximalIdeal A).map (algebraMap A B) ≤ N := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, ← v.commutes]
    exact Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr
      (map_nonunit (algebraMap A R) a ((mem_maximalIdeal _).mp ha)))
  have hQN : Q ≤ N ⊔ maximalIdeal B • maximalIdeal B :=
    sup_le (by rw [pow_two, ← smul_eq_mul]; exact le_sup_right) (h𝔪B.trans le_sup_left)
  have hgen : maximalIdeal B ≤ N := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (maximalIdeal_le_jacobson _) ((hx.2.trans (sup_le ?_ hQN)))
    refine Ideal.span_le.mpr (Set.range_subset_iff.mpr fun i ↦ ?_)
    have hxi : x i - v (X i) ∈ Q := by
      rw [← Ideal.Quotient.eq, hv', cotangentMap_X]
    rw [show x i = v (X i) + (x i - v (X i)) by ring]
    exact add_mem (Submodule.mem_sup_left (Ideal.mem_map_of_mem _
      (span_X_le_maximalIdeal (Ideal.subset_span ⟨i, rfl⟩)))) (hQN hxi)
  have hsurj : Function.Surjective v := by
    have : IsHausdorff ((maximalIdeal R).map v.toRingHom) B :=
      IsHausdorff.of_isLocalRing _ _ fun h ↦ (maximalIdeal.isMaximal B).ne_top
        (eq_top_iff.mpr (h ▸ hN))
    refine surjective_of_mk_map_comp_surjective (I := maximalIdeal R) v.toRingHom fun y ↦ ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := htriv b
    refine ⟨algebraMap A R a, ?_⟩
    rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, v.commutes,
      Ideal.Quotient.eq]
    exact neg_mem_iff.mp (by rw [neg_sub]; exact hgen ha)
  -- the kernel of `v` lies in `𝔪 A⟦t⟧`: formal smoothness of the fibre gives a splitting
  set k := ResidueField A
  set M : Ideal R := (maximalIdeal A).map (algebraMap A R)
  set 𝔪B : Ideal B := (maximalIdeal A).map (algebraMap A B)
  let w' : R →ₐ[A] B ⧸ 𝔪B := (Ideal.Quotient.mkₐ A 𝔪B).comp v
  have hw' : Function.Surjective w' := Ideal.Quotient.mk_surjective.comp hsurj
  set K' := RingHom.ker w'
  have hMK : M ≤ K' := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, AlgHom.commutes, IsScalarTower.algebraMap_apply A B,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ ha
  set C := R ⧸ M
  let : Algebra k C := Ideal.Quotient.algebraQuotientMapQuotient
  have : IsScalarTower A k C := Ideal.Quotient.tower_quotient_map_quotient
  have hM : M ≤ maximalIdeal R := Ideal.map_le_iff_le_comap.mpr fun a ha ↦
    map_nonunit (algebraMap A R) a ha
  have : Nontrivial C := Ideal.Quotient.nontrivial_iff.mpr fun h ↦
    (maximalIdeal.isMaximal R).ne_top (eq_top_iff.mpr (h ▸ hM))
  have : IsLocalRing C := .of_surjective' (Ideal.Quotient.mk M) Ideal.Quotient.mk_surjective
  have : IsAdicComplete (maximalIdeal C) C := isAdicComplete_maximalIdeal_of_finite (A := R)
  set J : Ideal C := K'.map (Ideal.Quotient.mk M)
  let e : (C ⧸ J) ≃ₐ[A] B ⧸ 𝔪B :=
    (DoubleQuot.quotQuotEquivQuotOfLEₐ A hMK).trans (Ideal.quotientKerAlgEquivOfSurjective hw')
  have he (r : R) : e (Ideal.Quotient.mk J (Ideal.Quotient.mk M r)) = w' r := rfl
  let ψ : B →ₐ[A] C ⧸ J := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A 𝔪B)
  let u : k ⊗[A] B →ₐ[k] C ⧸ J :=
    Algebra.TensorProduct.lift (Algebra.ofId k _) ψ fun a b ↦ by
      rw [Commute, SemiconjBy]; exact mul_comm ((Algebra.ofId k (C ⧸ J)) a) (ψ b)
  have hu (b : B) : u ((1 : k) ⊗ₜ b) = ψ b := by simp [u]
  have hJtop : J ≠ ⊤ := fun h ↦ by
    have : Subsingleton (C ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr h
    have : Subsingleton (B ⧸ 𝔪B) := e.symm.toEquiv.subsingleton
    have h𝔪 : 𝔪B ≤ maximalIdeal B := Ideal.map_le_iff_le_comap.mpr fun a ha ↦
      map_nonunit _ a ha
    exact (maximalIdeal.isMaximal B).ne_top (eq_top_iff.mpr
      ((Ideal.Quotient.subsingleton_iff.mp this).symm ▸ h𝔪))
  have hu𝔫 : ((maximalIdeal B).map (Algebra.TensorProduct.includeRight :
      B →ₐ[A] k ⊗[A] B)).map u ≤ (maximalIdeal C).map (Ideal.Quotient.mk J) := by
    rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change u ((1 : k) ⊗ₜ b) ∈ _
    rw [hu]
    obtain ⟨c, hc⟩ := Ideal.Quotient.mk_surjective (ψ b)
    rw [← hc]
    refine Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr fun hcu ↦ ?_)
    have h𝔪 : 𝔪B ≤ Ideal.jacobson ⊥ := (Ideal.map_le_iff_le_comap.mpr fun a ha ↦
      map_nonunit _ a ha).trans (maximalIdeal_le_jacobson _)
    have := isLocalHom_of_le_jacobson_bot 𝔪B h𝔪
    have h1 : IsUnit (Ideal.Quotient.mk 𝔪B b) := by
      have := (hcu.map (Ideal.Quotient.mk J)).map e
      rwa [hc, show e (ψ b) = Ideal.Quotient.mk 𝔪B b by simp [ψ]] at this
    exact (mem_maximalIdeal _).mp hb (isUnit_of_map_unit _ _ h1)
  obtain ⟨s, hs⟩ := hfib.exists_lift_of_isAdicComplete (C := C) (maximalIdeal C)
    (le_maximalIdeal hJtop) (fun c hc ↦ mem_of_forall_mem_sup_pow hc) u hu𝔫
  have hs' (y : k ⊗[A] B) : Ideal.Quotient.mk J (s y) = u y := congr($hs y)
  have hkill : 𝔪B ≤ RingHom.ker (Algebra.TensorProduct.includeRight : B →ₐ[A] k ⊗[A] B) :=
    map_maximalIdeal_le_ker_includeRight
  let w : C →ₐ[A] k ⊗[A] B := Ideal.Quotient.liftₐ M
    ((Algebra.TensorProduct.includeRight).comp v) fun r hr ↦ by
      have : r ∈ K' := hMK hr
      rw [RingHom.mem_ker, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
        Ideal.Quotient.eq_zero_iff_mem] at this
      rw [AlgHom.comp_apply]
      exact hkill this
  have hw (r : R) : w (Ideal.Quotient.mk M r) = (1 : k) ⊗ₜ v r := rfl
  let σ : C →+* C := ((s.restrictScalars A).comp w : C →ₐ[A] C)
  have h1 : ∀ p, p - σ p ∈ J := by
    intro p
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective p
    rw [← Ideal.Quotient.eq]
    change _ = Ideal.Quotient.mk J (s (w (Ideal.Quotient.mk M r)))
    rw [hw, hs', hu]
    apply e.injective
    rw [he]
    simp [ψ, w']
  have h2 : ∀ q ∈ J, σ q = 0 := by
    intro q hq
    obtain ⟨r, hr, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hq
    change s (w (Ideal.Quotient.mk M r)) = 0
    rw [hw]
    have : v r ∈ 𝔪B := by
      rw [RingHom.mem_ker] at hr
      exact Ideal.Quotient.eq_zero_iff_mem.mp hr
    rw [show (1 : k) ⊗ₜ[A] v r = Algebra.TensorProduct.includeRight (v r) from rfl,
      RingHom.mem_ker.mp (hkill this), map_zero]
  have hJ2 : J ≤ maximalIdeal C ^ 2 := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have hr₀ : r ∈ RingHom.ker w₀ := by
      rw [RingHom.mem_ker, ← hv', Ideal.Quotient.eq_zero_iff_mem]
      rw [RingHom.mem_ker] at hr
      exact (le_sup_right : 𝔪B ≤ Q) (Ideal.Quotient.eq_zero_iff_mem.mp hr)
    rw [hker₀] at hr₀
    obtain ⟨a, ha, m, hm, rfl⟩ := Submodule.mem_sup.mp hr₀
    rw [Ideal.mem_comap, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hm, add_zero]
    have hle := map_maximalIdeal_le_of_surjective (Ideal.Quotient.mk M)
      Ideal.Quotient.mk_surjective
    have : Ideal.Quotient.mk M a ∈ ((maximalIdeal R) ^ 2).map (Ideal.Quotient.mk M) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hle 2 this
  have hJbot := eq_bot_of_forall_sub_mem σ h1 h2 hJ2
  have hKM : RingHom.ker v ≤ M := fun r hr ↦ by
    have : Ideal.Quotient.mk M r ∈ J := Ideal.mem_map_of_mem _ (by
      rw [RingHom.mem_ker, AlgHom.comp_apply, RingHom.mem_ker.mp hr, map_zero])
    rwa [hJbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this
  -- flatness: `ker v = 𝔪 ker v`, hence `ker v = 0`
  have hflat := LinearMap.ker_inf_smul_top_eq_smul_of_flat (maximalIdeal A) v.toLinearMap hsurj
  have hle : RingHom.ker v ≤ maximalIdeal R • RingHom.ker v := by
    intro r hr
    have hr' : r ∈ LinearMap.ker v.toLinearMap ⊓ (maximalIdeal A • ⊤ : Submodule A R) := by
      refine ⟨hr, ?_⟩
      rw [Ideal.smul_top_eq_map]
      exact hKM hr
    rw [hflat] at hr'
    refine Submodule.smul_induction_on hr' (fun a ha y hy ↦ ?_) fun _ _ ↦ add_mem
    have hy' : y ∈ RingHom.ker v := hy
    have ha' : algebraMap A R a ∈ maximalIdeal R :=
      (mem_maximalIdeal _).mpr (map_nonunit (algebraMap A R) a ((mem_maximalIdeal _).mp ha))
    rw [show a • y = algebraMap A R a • y from Algebra.smul_def a y]
    exact Submodule.smul_mem_smul ha' hy'
  have hbot : RingHom.ker v = ⊥ := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _
    (IsNoetherian.noetherian _) hle (maximalIdeal_le_jacobson _)
  have hinj : Function.Injective v := (RingHom.injective_iff_ker_eq_bot _).mpr hbot
  exact ⟨n, ⟨(AlgEquiv.ofBijective v ⟨hinj, hsurj⟩).symm⟩⟩

end Trivial

section Transport

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

omit [IsLocalRing B] [IsLocalHom (algebraMap A B)] in
/-- An idempotent of a ring which lies in a nilpotent ideal is zero. -/
lemma eq_zero_of_isIdempotentElem_of_mem_nilpotent {C : Type*} [CommRing C] {J : Ideal C}
    (hJ : IsNilpotent J) {x : C} (hx : IsIdempotentElem x) (hxJ : x ∈ J) : x = 0 := by
  obtain ⟨N, hN⟩ := hJ
  have : x ^ (N + 1) ∈ J ^ N :=
    Ideal.pow_le_pow_right N.le_succ (Ideal.pow_mem_pow hxJ (N + 1))
  rwa [hN, hx.pow_succ_eq, Ideal.zero_eq_bot, Ideal.mem_bot] at this

omit [IsLocalHom (algebraMap A B)] in
/-- The closed fibre of a local component of `A' ⊗[A] B` over `A'` is formally smooth over the
residue field `k'` of `A'` when the closed fibre `k ⊗[A] B` of `B` is formally smooth over `k`
("formal smoothness of the fibre is stable under base change and localization"). We argue with the
lifting property directly: a map from `k' ⊗ (A' ⊗ B) ⧸ (1 - e)` to `C ⧸ J` restricts to
`k ⊗ B`, whose lift to `C` extends back. -/
theorem adicFormallySmooth_fiber_quotient
    (hfib : AdicFormallySmooth (ResidueField A)
      ((maximalIdeal B).map (Algebra.TensorProduct.includeRight :
        B →ₐ[A] ResidueField A ⊗[A] B)))
    (A' : Type u) [CommRing A'] [Algebra A A'] [IsLocalRing A'] [Module.Finite A A']
    (e : A' ⊗[A] B) (he : IsIdempotentElem e) :
    AdicFormallySmooth (ResidueField A')
      ((((maximalIdeal B).map (algebraMap B (A' ⊗[A] B))).map
        (Ideal.Quotient.mk (Ideal.span {1 - e}))).map
          (Algebra.TensorProduct.includeRight :
            ((A' ⊗[A] B) ⧸ Ideal.span {1 - e}) →ₐ[A'] ResidueField A' ⊗[A']
              ((A' ⊗[A] B) ⧸ Ideal.span {1 - e}))) := by
  intro C _ _ J hJ f ⟨m, hm⟩
  set k := ResidueField A
  set k' := ResidueField A'
  set S := (A' ⊗[A] B) ⧸ Ideal.span {1 - e}
  have := isLocalHom_of_finite (A := A) (A' := A')
  -- the algebra structures on `C`
  let : Algebra A' C := ((algebraMap k' C).comp (residue A')).toAlgebra
  have : IsScalarTower A' k' C := .of_algebraMap_eq' rfl
  let : Algebra k C := ((algebraMap k' C).comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' C := .of_algebraMap_eq' rfl
  let : Algebra A C := ((algebraMap k C).comp (algebraMap A k)).toAlgebra
  have : IsScalarTower A k C := .of_algebraMap_eq' rfl
  have : IsScalarTower A A' C := .of_algebraMap_eq fun a ↦ by
    change algebraMap k' C (algebraMap k k' (algebraMap A k a)) =
      algebraMap k' C (residue A' (algebraMap A A' a))
    rw [ResidueField.algebraMap_eq]
    exact congrArg (algebraMap k' C) (ResidueField.map_residue _ a)
  -- the restriction of `f` to `B`
  let ι₃ : S →ₐ[A'] k' ⊗[A'] S := Algebra.TensorProduct.includeRight
  let g : B →ₐ[A] C ⧸ J :=
    (((f.restrictScalars A').comp (ι₃.comp (Ideal.Quotient.mkₐ A' _))).restrictScalars A).comp
      Algebra.TensorProduct.includeRight
  have hg (b : B) : g b = f ((1 : k') ⊗ₜ Ideal.Quotient.mk _ ((1 : A') ⊗ₜ b)) := rfl
  let f₀ : k ⊗[A] B →ₐ[k] C ⧸ J :=
    Algebra.TensorProduct.lift (Algebra.ofId k _) g fun a b ↦ by
      rw [Commute, SemiconjBy]; exact mul_comm ((Algebra.ofId k (C ⧸ J)) a) (g b)
  have hf₀ (b : B) : f₀ ((1 : k) ⊗ₜ b) = g b := by simp [f₀]
  have hcont : (maximalIdeal B).map g ≤ ((((maximalIdeal B).map (algebraMap B (A' ⊗[A] B))).map
      (Ideal.Quotient.mk (Ideal.span {1 - e}))).map ι₃).map f := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, hg]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _
      (Ideal.mem_map_of_mem _ hb)))
  obtain ⟨G₀, hG₀⟩ := hfib J hJ f₀ ⟨m, by
    rw [← Ideal.map_eq_bot_iff_le_ker, Ideal.map_pow, eq_bot_iff]
    have h1 : ((maximalIdeal B).map (Algebra.TensorProduct.includeRight :
        B →ₐ[A] k ⊗[A] B)).map f₀ ≤ (maximalIdeal B).map g := by
      rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change f₀ ((1 : k) ⊗ₜ b) ∈ _
      rw [hf₀]
      exact Ideal.mem_map_of_mem _ hb
    refine (Ideal.pow_right_mono (h1.trans hcont) m).trans ?_
    rw [← Ideal.map_pow f]
    exact ((Ideal.map_eq_bot_iff_le_ker f).mpr hm).le⟩
  have hG₀' (b : B) : Ideal.Quotient.mk J (G₀ ((1 : k) ⊗ₜ b)) = g b := by
    rw [← hf₀]; exact congr($hG₀ ((1 : k) ⊗ₜ b))
  -- extend to `A' ⊗ B`
  let g₀ : B →ₐ[A] C := (G₀.restrictScalars A).comp Algebra.TensorProduct.includeRight
  let G : A' ⊗[A] B →ₐ[A'] C :=
    Algebra.TensorProduct.lift (Algebra.ofId A' C) g₀ fun a b ↦ by
      rw [Commute, SemiconjBy]; exact mul_comm ((Algebra.ofId A' C) a) (g₀ b)
  have hG : (Ideal.Quotient.mkₐ A' J).comp G =
      (f.restrictScalars A').comp (ι₃.comp (Ideal.Quotient.mkₐ A' _)) := by
    refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun b ↦ ?_)
    change Ideal.Quotient.mk J (G ((1 : A') ⊗ₜ b)) = g b
    rw [← hG₀']
    simp [G, g₀]
  have hG1 : G (1 - e) = 0 := by
    refine eq_zero_of_isIdempotentElem_of_mem_nilpotent hJ (he.one_sub.map G) ?_
    have := congr($hG (1 - e))
    have h0 : (Ideal.Quotient.mkₐ A' (Ideal.span {1 - e})) (1 - e) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [AlgHom.comp_apply, h0, map_zero, Ideal.Quotient.mkₐ_eq_mk] at this
    exact Ideal.Quotient.eq_zero_iff_mem.mp this
  let G' : S →ₐ[A'] C := Ideal.Quotient.liftₐ _ G fun x hx ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hG1, mul_zero]
  let F : k' ⊗[A'] S →ₐ[k'] C :=
    Algebra.TensorProduct.lift (Algebra.ofId k' C) G' fun a b ↦ by
      rw [Commute, SemiconjBy]; exact mul_comm ((Algebra.ofId k' C) a) (G' b)
  refine ⟨F, Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_⟩
  refine Ideal.Quotient.algHom_ext _ (AlgHom.ext fun x ↦ ?_)
  change Ideal.Quotient.mk J (F ((1 : k') ⊗ₜ Ideal.Quotient.mk _ x)) =
    f ((1 : k') ⊗ₜ Ideal.Quotient.mk _ x)
  have hF : F ((1 : k') ⊗ₜ Ideal.Quotient.mk _ x) = G x := by
    simp only [F, G', Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  rw [hF]
  exact congr($hG x)

end Transport

section Main

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing A] [IsLocalRing B]
  [IsLocalHom (algebraMap A B)] [IsNoetherianRing A] [IsNoetherianRing B]
  [IsAdicComplete (maximalIdeal A) A] [IsAdicComplete (maximalIdeal B) B]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- III.1.7, sufficiency: let `A → B` be a local homomorphism of complete noetherian local rings
with finite residue extension. If `B` is flat over `A` and the closed fibre `k ⊗[A] B` is formally
smooth over `k`, then `B` is formally smooth over `A` (Definition III.1.1). As in SGA, after a
finite free local extension `A'` making the residue extensions trivial, the local components of
`A' ⊗ B` are flat over `A'` with formally smooth closed fibres
(`adicFormallySmooth_fiber_quotient`), hence power series rings over `A'`
(`exists_algEquiv_mvPowerSeries_of_flat`). -/
theorem formallySmoothLocal_of_flat_of_fiber [Module.Finite A (ResidueField B)] [Module.Flat A B]
    (hfib : AdicFormallySmooth (ResidueField A)
      ((maximalIdeal B).map (Algebra.TensorProduct.includeRight :
        B →ₐ[A] ResidueField A ⊗[A] B))) :
    FormallySmoothLocal A B := by
  obtain ⟨A', _, _, _, _, _, hA'⟩ := exists_finite_free_residue_trivial (A := A) (B := B)
  refine ⟨A', inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    fun P _ ↦ ?_⟩
  refine exists_algEquiv_localization_of_artinianLiftingProperty A' P (hA' P ‹_›)
    fun e he heP hQ _ _ _ _ _ _ htriv ↦ ?_
  set S := (A' ⊗[A] B) ⧸ Ideal.span {1 - e}
  have := isLocalization_atPrime_quotient he heP hQ
  have : IsLocalization.Away e S := IsLocalization.Away.quotient_of_isIdempotentElem he
  have : Module.Flat (A' ⊗[A] B) S := IsLocalization.flat S (Submonoid.powers e)
  have : Module.Flat A' S := Module.Flat.trans A' (A' ⊗[A] B) S
  have hfib' := (adicFormallySmooth_fiber_quotient hfib A' e he).mono (Ideal.map_mono (by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal P S, Ideal.Quotient.algebraMap_eq]
    exact Ideal.map_mono (map_maximalIdeal_le_of_isMaximal A' P) :
      ((maximalIdeal B).map (algebraMap B (A' ⊗[A] B))).map
        (Ideal.Quotient.mk (Ideal.span {1 - e})) ≤ maximalIdeal S))
  obtain ⟨n, ⟨φ⟩⟩ := exists_algEquiv_mvPowerSeries_of_flat htriv hfib'
  exact (adicFormallySmooth_of_algEquiv_mvPowerSeries φ).artinianLiftingProperty

/-- Corollary III.1.7: a local homomorphism `A → B` of complete noetherian local rings with finite
residue extension is formally smooth (Definition III.1.1) if and only if `B` is flat over `A` and
the closed fibre `B/𝔪B = k ⊗[A] B` is formally smooth over the residue field `k` of `A` (for its
`𝔫`-adic topology, i.e. the lifting property III.2.1 (iii)). -/
theorem formallySmoothLocal_iff_flat_and_fiber [Module.Finite A (ResidueField B)] :
    FormallySmoothLocal A B ↔ Module.Flat A B ∧ AdicFormallySmooth (ResidueField A)
      ((maximalIdeal B).map (Algebra.TensorProduct.includeRight :
        B →ₐ[A] ResidueField A ⊗[A] B)) :=
  ⟨fun h ↦ ⟨h.flat, (adicFormallySmooth_of_formallySmoothLocal' h).baseChange _⟩,
    fun ⟨_, h⟩ ↦ formallySmoothLocal_of_flat_of_fiber h⟩

end Main

end SGA.SGA1.ExposeIII
