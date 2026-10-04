/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.GAGAFiberSeparating
import SGA.SGA1.ExposeXII.BranchedCover
import SGA.SGA1.ExposeXII.RiemannReductionUniverse
import SGA.SGA1.ExposeXII.RiemannExtensionLocal
import SGA.SGA1.ExposeXII.RiemannHigherBase
import SGA.Foundations.Dimension.FiniteType

/-!
# SGA 1, Exposé XII, 5.1 for curves: a dense open subset finite étale over `ℂ ∖ S`

Let `B` be a domain of finite type and of dimension `1` over `ℂ` (an integral affine curve,
possibly singular). A Noether normalization `ℂ[t] ⊆ B` (`exists_finite_injective_polynomial`)
is generically étale in characteristic `0` (xii52's `exists_isStandardEtale_localizationAway`):
there is `H ∈ ℂ[t]`, `H ≠ 0`, with `B[1/H]` standard étale over `ℂ[t]`. With `S` the set of roots
of `H`, the ring `ℂ[t][1/H]` is `ℂ[t][1/∏_{a ∈ S} (t - a)]`, the coordinate ring of `ℂ ∖ S`
(`isLocalization_away_coordRing`), so `B[1/h]`, `h = H(t)`, is a finite étale `ℂ ∖ S`-algebra
(`finiteEtale_away`). XII.5.1 for `ℂ ∖ S` and its finite étale coverings
(`PuncturedPlane.riemannExistence_finiteEtale`) then gives XII.5.1 for `Spec B[1/h]`, the
complement of the finite set `{h = 0}` of `X(ℂ)`, `X = Spec B`
(`exists_isEquivalence_pointsFunctor_away`).

What remains for XII.5.1 on `X` is the extension across the finitely many points of `{h = 0}`
(`SGA.SGA1.ExposeXII.RiemannExtension`). This route through `ℂ ∖ S` is this project's, not SGA's.
It overlaps ret-hd's `exists_finiteEtale_hypersurfaceComplement` (`RiemannHigherSmooth.lean`,
any domain of finite type: `B_g` finite étale over a hypersurface complement in `𝔸^s`), which in
dimension `1`, together with `riemannExistence_polynomial_away` and
`isEquivalence_pointsFunctor_of_finiteEtale`, gives the same conclusion except the finiteness of
the zero set of `h` used by the extension step.
-/

noncomputable section

open Polynomial CategoryTheory

namespace SGA.SGA1.ExposeXII

namespace NoetherCurve

variable (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] [Algebra.FiniteType ℂ B]

/-- **Noether normalization of a curve**: a domain of finite type and dimension `1` over `ℂ` is
finite over a polynomial subring `ℂ[t]`. -/
theorem exists_finite_injective_polynomial (hdim : ringKrullDim B = 1) :
    ∃ g₀ : ℂ[X] →ₐ[ℂ] B, Function.Injective g₀ ∧ g₀.Finite := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ B
  have hs : ((s : ℕ∞) : WithBot ℕ∞) = 1 := by
    rw [← hdim, Algebra.FiniteType.ringKrullDim_eq_of_isIntegral_mvPolynomial ℂ hinj
      hfin.to_isIntegral]
    rfl
  have hs1 : s = 1 := by exact_mod_cast hs
  subst hs1
  let e : ℂ[X] ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ := (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm
  exact ⟨g.comp e.toAlgHom, hinj.comp e.injective,
    RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ e.surjective)⟩

/-- The polynomial `f_S = ∏_{a ∈ S} (t - a)`, `S` the set of roots of `H`, divides `H`. -/
lemma punctures_roots_dvd (H : ℂ[X]) : PuncturedPlane.punctures H.roots.toFinset ∣ H := by
  classical
  refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd H)
  rw [PuncturedPlane.punctures, Finset.prod_eq_multiset_prod, Multiset.toFinset_val]
  exact Multiset.prod_dvd_prod_of_le (Multiset.map_le_map (Multiset.dedup_le _))

/-- A nonzero `H` divides a power of `f_S = ∏_{a ∈ S} (t - a)`, `S` the set of roots of `H`. -/
lemma dvd_punctures_roots_pow {H : ℂ[X]} (hH : H ≠ 0) :
    H ∣ PuncturedPlane.punctures H.roots.toFinset ^ H.natDegree := by
  classical
  refine (IsAlgClosed.splits H).dvd_of_roots_le_roots hH ?_
  rw [roots_pow, PuncturedPlane.punctures, roots_prod_X_sub_C, Multiset.toFinset_val,
    Multiset.le_iff_count]
  intro a
  rw [Multiset.count_nsmul, Multiset.count_dedup]
  split_ifs with ha
  · rw [mul_one]
    exact (Multiset.count_le_card a _).trans (card_roots' H)
  · rw [Multiset.count_eq_zero.mpr ha]
    exact Nat.zero_le _

/-- `ℂ[t][1/H]` is the coordinate ring `ℂ[t][1/f_S]` of `ℂ ∖ S`, `S` the set of roots of `H ≠ 0`
(from ret-hd's `RiemannHigher.isLocalization_away_of_dvd_pow`: `f_S ∣ H` and `H ∣ f_S ^ deg H`). -/
lemma isLocalization_away_coordRing {H : ℂ[X]} (hH : H ≠ 0) :
    IsLocalization.Away H (PuncturedPlane.coordRing H.roots.toFinset) :=
  RiemannHigher.isLocalization_away_of_dvd_pow (m := 1) (n := H.natDegree)
    (by rw [pow_one]; exact punctures_roots_dvd H) (dvd_punctures_roots_pow hH)

open PuncturedPlane in
/-- **XII.5.1 on a dense open subset of an integral affine curve** (this project's route): for `B`
a domain of finite type and dimension `1` over `ℂ`, there is `h ≠ 0` in `B` such that the set of
zeros of `h` in `X(ℂ)`, `X = Spec B`, is finite and XII.5.1 holds for `B[1/h]`: `Spec B[1/h]` is
finite étale over some `ℂ ∖ S` (Noether normalization and generic étaleness), where XII.5.1 holds
(`PuncturedPlane.riemannExistence_finiteEtale`). -/
theorem exists_isEquivalence_pointsFunctor_away (hdim : ringKrullDim B = 1) :
    ∃ h : B, h ≠ 0 ∧ {φ : Points ℂ B | φ h = 0}.Finite ∧
      (pointsFunctor ℂ (Localization.Away h)).IsEquivalence := by
  obtain ⟨g₀, hinj, hfin⟩ := exists_finite_injective_polynomial B hdim
  algebraize [g₀.toRingHom]
  have : IsScalarTower ℂ ℂ[X] B := .of_algebraMap_eq fun c ↦ (g₀.commutes c).symm
  have : Module.Finite ℂ[X] B := hfin
  have : FaithfulSMul ℂ[X] B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : CharZero (FractionRing ℂ[X]) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing ℂ[X])).injective
  obtain ⟨H, hH, hstd⟩ := exists_isStandardEtale_localizationAway ℂ[X] B
  set S := H.roots.toFinset
  set h := algebraMap ℂ[X] B H
  let Bh := Localization.Away h
  have hh0 : h ≠ 0 := (map_ne_zero_iff _ hinj).mpr hH
  refine ⟨h, hh0, ?_, ?_⟩
  · -- the zeros of `h` lie over the finitely many roots of `H`
    refine (S.finite_toSet.biUnion fun z _ ↦ Points.finite_proj_preimage_of_finite (K := ℂ)
      (A := ℂ[X]) (B := B) (Points.polynomialHomeomorph.symm z)).subset fun φ hφ ↦ ?_
    have hz : H.eval (φ (algebraMap ℂ[X] B X)) = 0 := by
      have h1 : Points.proj ℂ[X] B φ H = 0 := hφ
      rwa [Points.apply_eq_eval_polynomial] at h1
    refine Set.mem_iUnion₂.mpr ⟨φ (algebraMap ℂ[X] B X), ?_, ?_⟩
    · simpa [S, Multiset.mem_toFinset, mem_roots hH] using hz
    · rw [Set.mem_preimage, Set.mem_singleton_iff, Homeomorph.eq_symm_apply]
      rfl
  · have := isLocalization_away_coordRing hH
    have : IsScalarTower ℂ ℂ[X] Bh := .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply ℂ[X] B Bh, ← IsScalarTower.algebraMap_apply ℂ ℂ[X] B,
        ← IsScalarTower.algebraMap_apply ℂ B Bh]
    have hunit : IsUnit (algebraMap ℂ[X] Bh H) := by
      rw [IsScalarTower.algebraMap_apply ℂ[X] B Bh]
      exact IsLocalization.Away.algebraMap_isUnit h
    let : Algebra (coordRing S) Bh := (IsLocalization.Away.lift H hunit).toAlgebra
    have : IsScalarTower ℂ[X] (coordRing S) Bh :=
      .of_algebraMap_eq fun p ↦ (IsLocalization.Away.lift_eq H hunit p).symm
    have : IsScalarTower ℂ (coordRing S) Bh := .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply ℂ ℂ[X] (coordRing S),
        ← IsScalarTower.algebraMap_apply ℂ[X] (coordRing S) Bh,
        ← IsScalarTower.algebraMap_apply ℂ ℂ[X] Bh]
    have : IsLocalization (Algebra.algebraMapSubmonoid B (.powers H)) Bh := by
      rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
      infer_instance
    have : Module.Finite (coordRing S) Bh := Module.Finite.of_isLocalization ℂ[X] B (.powers H)
    have : Algebra.Etale (coordRing S) Bh := Algebra.Etale.of_restrictScalars ℂ[X] _ _
    let T : CommAlgCat.FiniteEtale.{0} (coordRing S) := CommAlgCat.FiniteEtale.of (coordRing S) Bh
    have hT := riemannExistence_finiteEtale S T
    let e₀ : Bh ≃+* T.obj := RingEquiv.refl Bh
    let e : @AlgEquiv ℂ Bh T.obj _ _ _ _ (algebraOfFiniteEtale ℂ (coordRing S) T) :=
      @AlgEquiv.ofRingEquiv ℂ Bh T.obj _ _ _ _ (algebraOfFiniteEtale ℂ (coordRing S) T) e₀
        fun c ↦ IsScalarTower.algebraMap_apply ℂ (coordRing S) Bh c
    exact (@isEquivalence_pointsFunctor_iff_of_algEquiv Bh _ _ T.obj _
      (algebraOfFiniteEtale ℂ (coordRing S) T) e).mpr hT

end NoetherCurve

end SGA.SGA1.ExposeXII
