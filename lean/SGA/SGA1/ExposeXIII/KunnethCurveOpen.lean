/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Locus
import SGA.SGA1.ExposeVIII.FiniteSpreadingOut
import SGA.SGA1.ExposeXIII.KunnethCurve
import SGA.SGA1.ExposeXIII.KunnethFiniteEtale
import SGA.SGA1.ExposeXIII.KunnethInvariance

/-!
# SGA 1, XIII.4.6 in characteristic `0`: from open subsets of the affine line to all curves

The curve input of the resolution-free route to XIII.4.6 in characteristic `0` is the invariance
of `π₁` under algebraically closed base change for the open subsets `𝔸¹ ∖ V(g)` of the affine
line (`AffineLineOpenInvarianceStatement`; milestone C1 of the route, proved as
`affineLineOpenInvarianceStatement` in `SGA.SGA1.ExposeXIII.KunnethCurveInvariance`). Here we
show that it suffices for the step of the transcendence-degree induction
(`isEquivalence_pullback_fst_of_trdeg_le_one`): for `X` connected, normal, quasi-compact,
quasi-separated and locally of finite type over an algebraically closed field `k` of
characteristic `0`, and `k'` algebraically closed of transcendence degree at most `1`,
`FEt(X) ≌ FEt(X ⊗ₖ k')`.

* `exists_finite_etale_away` (generic finite étaleness): a domain `S` of finite type and
  algebraic over a noetherian domain `R` of characteristic `0` has a localization `S_f`, `f ≠ 0`,
  which is finite étale over `R_r` after inverting some `r ≠ 0` of `R` (generic étaleness,
  `Algebra.exists_etale_of_isEtaleAt`, and generic finiteness, EGA IV 8.10.5,
  `SGA.SGA1.ExposeVIII.exists_finite_away_of_finite_localization`);
* `exists_le_fg_invariance_of_trdeg_le_one`: every finitely generated `k`-subalgebra `A` of `k'`
  is contained in a finitely generated `B` such that `Spec B` is a connected étale covering of
  an open subset `𝔸¹ ∖ V(r)` of the affine line (choose `t ∈ k'` transcendental; `k'` is then
  algebraic over `k[t]`), hence smooth over `k`, and has the invariance property
  (`HasAlgClosedBaseChangeInvariance.of_isFinite_of_etale`);
* `isEquivalence_pullback_fst_of_trdeg_le_one`: hence the trdeg-`1` step, by the main lemma
  (`isEquivalence_pullback_fst_of_cofinal`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Polynomial

namespace SGA.SGA1.ExposeXIII

/-- XIII.4.6 (`Y = Spec k'`, `X = 𝔸¹ ∖ V(g)` an open subset of the affine line, characteristic
`0`; proved as `affineLineOpenInvarianceStatement` in `SGA.SGA1.ExposeXIII.KunnethCurveInvariance`):
for `k` algebraically closed of characteristic `0` and `g ≠ 0` in `k[X]`,
`Spec k[X]_g` has the invariance property of `π₁` under algebraically closed base change
(`HasAlgClosedBaseChangeInvariance`). The case `g` constant is `𝔸¹`
(`hasAlgClosedBaseChangeInvariance_localization_away_of_isUnit`). It is the special case
`X = Spec k[X]_g` of `InvarianceCharZeroStatement`
(`affineLineOpenInvarianceStatement_of_invarianceCharZeroStatement`). -/
def AffineLineOpenInvarianceStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k] (g : k[X]), g ≠ 0 →
    HasAlgClosedBaseChangeInvariance
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g))))

set_option backward.isDefEq.respectTransparency false in
/-- The case `g` a unit of `AffineLineOpenInvarianceStatement`: then `Spec k[X]_g = 𝔸¹`, whose
`π₁` is trivial in characteristic `0` (`hasAlgClosedBaseChangeInvariance_affineLine`). -/
theorem hasAlgClosedBaseChangeInvariance_localization_away_of_isUnit (k : Type u) [Field k]
    [IsAlgClosed k] [CharZero k] {g : k[X]} (hg : IsUnit g) :
    HasAlgClosedBaseChangeInvariance
      (Spec.map (CommRingCat.ofHom (algebraMap k (Localization.Away g)))) := by
  let e := IsLocalization.atUnit k[X] (Localization.Away g) g hg
  have : IsIso (CommRingCat.ofHom (algebraMap k[X] (Localization.Away g))) :=
    e.toRingEquiv.toCommRingCatIso.isIso_hom
  have : IsDomain (Localization.Away g) := e.toMulEquiv.isDomain_iff.mp inferInstance
  have : ConnectedSpace (Spec (.of (Localization.Away g))) := inferInstance
  refine (hasAlgClosedBaseChangeInvariance_affineLine k).of_isFinite_of_etale
    (Spec.map (CommRingCat.ofHom (algebraMap k[X] (Localization.Away g)))) ?_
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- `AffineLineOpenInvarianceStatement` is a special case of `InvarianceCharZeroStatement`. -/
theorem affineLineOpenInvarianceStatement_of_invarianceCharZeroStatement
    (h : InvarianceCharZeroStatement.{u}) : AffineLineOpenInvarianceStatement.{u} := by
  intro k _ _ _ g hg
  have : IsDomain (Localization.Away g) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hg)
  have : ConnectedSpace (Spec (.of (Localization.Away g))) := inferInstance
  exact h k _

open Algebra in
/-- Generic finite étaleness: let `S` be a domain of finite type and algebraic over a noetherian
domain `R` of characteristic `0`. There are `f ≠ 0` in `S` and `r ≠ 0` in `R` such that `(S_f)_r`
is finite étale over `R_r`. (Generic étaleness at the generic point of `Spec S`, which is
separable over `Frac R`, and generic finiteness, EGA IV 8.10.5.) -/
theorem exists_finite_etale_away {R S : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CharZero R] [CommRing S] [IsDomain S] [Algebra R S] [FaithfulSMul R S]
    [Algebra.FiniteType R S] [Algebra.IsAlgebraic R S] :
    ∃ f : S, f ≠ 0 ∧ ∃ r : R, r ≠ 0 ∧
      ∀ (Rr Sr : Type u) [CommRing Rr] [CommRing Sr] [Algebra R Rr]
        [Algebra (Localization.Away f) Sr] [Algebra Rr Sr] [Algebra R Sr]
        [IsScalarTower R (Localization.Away f) Sr] [IsScalarTower R Rr Sr]
        [IsLocalization.Away r Rr]
        [IsLocalization.Away (algebraMap R (Localization.Away f) r) Sr],
        Module.Finite Rr Sr ∧ Algebra.Etale Rr Sr := by
  classical
  have : FinitePresentation R S := FinitePresentation.of_finiteType.mp ‹_›
  -- `S` is étale over `R` at its generic point
  have hgen : IsEtaleAt R (⊥ : Ideal S) := by
    let _ := FractionRing.liftAlgebra R (FractionRing S)
    have : FormallyEtale (FractionRing R) (FractionRing S) := FormallyEtale.of_isSeparable _ _
    have : FormallyEtale R (FractionRing R) := FormallyEtale.of_isLocalization (nonZeroDivisors R)
    have : FormallyEtale R (FractionRing S) := FormallyEtale.comp R (FractionRing R) _
    have : IsLocalization (⊥ : Ideal S).primeCompl (FractionRing S) := by
      simpa [Ideal.primeCompl_bot] using (inferInstance : IsFractionRing S (FractionRing S))
    exact FormallyEtale.of_equiv ((IsLocalization.algEquiv (⊥ : Ideal S).primeCompl
      (FractionRing S) (Localization.AtPrime (⊥ : Ideal S))).restrictScalars R)
  obtain ⟨f, hf, hfet⟩ := exists_etale_of_isEtaleAt (R := R) (⊥ : Ideal S)
  have hf0 : f ≠ 0 := by simpa using hf
  -- generic finiteness for `T = S_f` (EGA IV 8.10.5 at the generic point)
  let T := Localization.Away f
  have : IsDomain T :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)
  have : FaithfulSMul R T := by
    rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq R S T]
    exact (IsLocalization.injective T (powers_le_nonZeroDivisors_of_noZeroDivisors hf0)).comp
      (FaithfulSMul.algebraMap_injective R S)
  have : Algebra.FiniteType S T := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) _
  have : Algebra.FiniteType R T := .trans (S := S) inferInstance inferInstance
  have : Algebra.IsAlgebraic S T := IsLocalization.isAlgebraic T (Submonoid.powers f)
  have : Algebra.IsAlgebraic R T := Algebra.IsAlgebraic.trans R S T
  let _ := FractionRing.liftAlgebra R (FractionRing T)
  have : IsLocalization.AtPrime (FractionRing R) (⊥ : Ideal R) := by
    change IsLocalization (⊥ : Ideal R).primeCompl (FractionRing R)
    simpa [Ideal.primeCompl_bot] using (inferInstance : IsFractionRing R (FractionRing R))
  have : IsLocalization (Algebra.algebraMapSubmonoid T (⊥ : Ideal R).primeCompl)
      (FractionRing T) := by
    simpa [Ideal.primeCompl_bot] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid T (nonZeroDivisors R))
        (FractionRing T))
  have : Algebra.FiniteType (FractionRing R) (FractionRing T) :=
    .equiv inferInstance (Algebra.IsPushout.equiv R (FractionRing R) T (FractionRing T))
  have : Module.Finite (FractionRing R) (FractionRing T) := Algebra.IsIntegral.finite
  obtain ⟨r, hr, hfin⟩ := ExposeVIII.exists_finite_away_of_finite_localization (A := T)
    (⊥ : Ideal R) (FractionRing R) (FractionRing T)
  refine ⟨f, hf0, r, by simpa using hr, fun Rr Sr _ _ _ _ _ _ _ _ _ _ ↦ ?_⟩
  have : IsScalarTower R T Sr := ‹_›
  have hfinr : Module.Finite Rr Sr := hfin Rr Sr
  refine ⟨hfinr, ?_⟩
  -- `Sr` is a localization of the étale `R`-algebra `T`
  have : FormallyEtale T Sr :=
    FormallyEtale.of_isLocalization (Submonoid.powers (algebraMap R T r))
  have : FormallyEtale R Sr := FormallyEtale.comp R T Sr
  have : IsLocalization ((Submonoid.powers r).map (algebraMap R T)) Sr := by
    rw [Submonoid.map_powers]
    infer_instance
  have : FormallyEtale Rr Sr := FormallyEtale.localization_base (Submonoid.powers r)
  have : IsNoetherianRing Rr := IsLocalization.isNoetherianRing (Submonoid.powers r) Rr ‹_›
  have : FinitePresentation Rr Sr := FinitePresentation.of_finiteType.mp inferInstance
  exact ⟨inferInstance, inferInstance⟩

/-- An element of a field `K` of transcendence degree at most `1` over `k` is algebraic over
`k[X]`, acting through `X ↦ t` for a transcendental `t`. -/
lemma isAlgebraic_polynomial_of_trdeg_le_one {k K : Type u} [Field k] [Field K] [Algebra k K]
    (hK : Algebra.trdeg k K ≤ 1) {t : K} (ht : Transcendental k t) (x : K) :
    letI := (Polynomial.aeval (R := k) t).toAlgebra
    IsAlgebraic k[X] x := by
  let _ := (Polynomial.aeval (R := k) t).toAlgebra
  let y : PUnit.{u + 1} → K := fun _ ↦ t
  have hy : AlgebraicIndependent k y := algebraicIndependent_unique_type_iff.mpr ht
  have hT : IsTranscendenceBasis k y :=
    hy.isTranscendenceBasis_of_trdeg_le_of_finite (by rwa [Cardinal.mk_punit])
  have halg := hT.isAlgebraic
  let e : Algebra.adjoin k (Set.range y) ≃+* k[X] :=
    (hy.aevalEquiv.symm.trans (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1})).toRingEquiv
  have he : (algebraMap k[X] K).comp (e : Algebra.adjoin k (Set.range y) →+* k[X]) =
      (RingHom.id K).comp (algebraMap (Algebra.adjoin k (Set.range y)) K) := by
    ext z
    obtain ⟨p, rfl⟩ := hy.aevalEquiv.surjective z
    change Polynomial.aeval t (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1} (hy.aevalEquiv.symm
      (hy.aevalEquiv p))) = (hy.aevalEquiv p : K)
    rw [AlgEquiv.symm_apply_apply, AlgebraicIndependent.aevalEquiv_apply_coe]
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
    | mul_X p i hp =>
      rw [map_mul, map_mul, map_mul, hp]
      simp [y]
  exact (isAlgebraic_ringHom_iff_of_comp_eq e (RingHom.id K) Function.injective_id he).mpr
    (halg.isAlgebraic x)

set_option backward.isDefEq.respectTransparency false in
/-- The cofinal family for the trdeg-`1` step, given `AffineLineOpenInvarianceStatement`: let `k`
be algebraically closed of characteristic `0` and `k'` an algebraically closed extension of
transcendence degree at most `1`. Every finitely generated `k`-subalgebra `A` of `k'` is
contained in a finitely generated `B` such that `Spec B` is smooth over `k` and has the invariance
property. If `k'` is algebraic over `k`, take `B = k`. Otherwise choose `t ∈ k'` transcendental;
`B = A[t][1/f][1/r(t)]` is finite étale over `k[t]_r ≅ k[X]_r` (`exists_finite_etale_away`), an
open subset of `𝔸¹`, so `HasAlgClosedBaseChangeInvariance.of_isFinite_of_etale` applies. -/
theorem exists_le_fg_invariance_of_trdeg_le_one (hC : AffineLineOpenInvarianceStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] (k' : Type u) [Field k'] [IsAlgClosed k']
    [Algebra k k'] (hk' : Algebra.trdeg k k' ≤ 1) (A : Subalgebra k k') (hA : A.FG) :
    ∃ B : Subalgebra k k', A ≤ B ∧ B.FG ∧
      (Smooth (Spec.map (CommRingCat.ofHom (algebraMap k B))) ∧
        HasAlgClosedBaseChangeInvariance (Spec.map (CommRingCat.ofHom (algebraMap k B)))) := by
  by_cases halg : Algebra.IsAlgebraic k k'
  · -- `k' = k`: take `B = k`
    have hbot : ∀ x : k', x ∈ (⊥ : Subalgebra k k') := fun x ↦ by
      have : Algebra.IsIntegral k k' := Algebra.IsAlgebraic.isIntegral
      obtain ⟨c, rfl⟩ := IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := k') |>.2 x
      exact Subalgebra.algebraMap_mem _ c
    refine ⟨⊥, fun x _ ↦ hbot x, Subalgebra.fg_bot, ?_⟩
    have hbij : Function.Bijective (algebraMap k (⊥ : Subalgebra k k')) := by
      convert (Algebra.botEquiv k k').symm.bijective
      ext c
      exact congrArg Subtype.val ((Algebra.botEquiv k k').symm.commutes c).symm
    have : IsIso (CommRingCat.ofHom (algebraMap k (⊥ : Subalgebra k k'))) :=
      (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
    have : ConnectedSpace (Spec (.of (⊥ : Subalgebra k k'))) := inferInstance
    exact ⟨inferInstance, hasAlgClosedBaseChangeInvariance_of_isProper _⟩
  obtain ⟨t, ht⟩ : ∃ t : k', Transcendental k t := by
    by_contra h
    exact halg ⟨fun x ↦ by_contra fun hx ↦ h ⟨x, hx⟩⟩
  let _ : Algebra k[X] k' := (Polynomial.aeval t).toAlgebra
  have : IsScalarTower k k[X] k' := IsScalarTower.of_algebraMap_eq fun c ↦ by
    change algebraMap k k' c = Polynomial.aeval t (Polynomial.C c)
    simp
  -- `S = k[t][A]`, of finite type and algebraic over `k[X]`
  obtain ⟨s₀, hs₀⟩ := hA
  let S : Subalgebra k[X] k' := Algebra.adjoin k[X] (s₀ : Set k')
  have hle : Algebra.adjoin k (s₀ : Set k') ≤ S.restrictScalars k :=
    Algebra.adjoin_le fun x hx ↦ (Algebra.subset_adjoin hx : x ∈ S)
  have hAS : ∀ a ∈ A, a ∈ S := fun a ha ↦ hle (hs₀ ▸ ha)
  have : Algebra.FiniteType k[X] S := (Subalgebra.fg_iff_finiteType S).mp ⟨s₀, rfl⟩
  have : FaithfulSMul k[X] S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b hab
    exact transcendental_iff_injective.mp ht (congrArg Subtype.val hab)
  have : Algebra.IsAlgebraic k[X] S := ⟨fun x ↦ (isAlgebraic_algHom_iff S.val
    Subtype.val_injective).mp (isAlgebraic_polynomial_of_trdeg_le_one hk' ht x)⟩
  obtain ⟨f, hf, r, hr, hfe⟩ := exists_finite_etale_away (R := k[X]) (S := S)
  -- `Sr = (S_f)_r` is finite étale over `Rr = k[X]_r`
  let T := Localization.Away f
  let Rr := Localization.Away r
  let Sr := Localization.Away (algebraMap k[X] T r)
  let _ : Algebra Rr Sr := (Localization.awayMap (algebraMap k[X] T) r).toAlgebra
  have : IsScalarTower k[X] Rr Sr := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply k[X] T Sr]
    change _ = Localization.awayMap (algebraMap k[X] T) r (algebraMap k[X] Rr a)
    exact (IsLocalization.map_eq _ _).symm
  obtain ⟨hfin, het⟩ := hfe Rr Sr
  -- the embedding `Sr ⟶ k'`
  have hfT : Submonoid.powers f ≤ nonZeroDivisors S :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : IsDomain T := IsLocalization.isDomain_localization hfT
  have hf' : IsUnit ((S.val : S →ₐ[k[X]] k') f) :=
    ((map_ne_zero_iff _ Subtype.val_injective).mpr hf).isUnit
  let ψ₁ : T →+* k' := IsLocalization.Away.lift f hf'
  have hψ₁ : ∀ x : S, ψ₁ (algebraMap S T x) = x := IsLocalization.Away.lift_eq f hf'
  have hψ₁i : Function.Injective ψ₁ := by
    refine (IsLocalization.lift_injective_iff _).mpr fun x y ↦ ?_
    rw [(IsLocalization.injective T hfT).eq_iff]
    exact Subtype.val_injective.eq_iff.symm
  have hr' : IsUnit (ψ₁ (algebraMap k[X] T r)) := by
    rw [IsScalarTower.algebraMap_apply k[X] S T, hψ₁]
    have : algebraMap k[X] k' r ≠ 0 := fun h ↦
      hr (transcendental_iff_injective.mp ht (h.trans (map_zero _).symm))
    exact Ne.isUnit this
  let ψ₂ : Sr →+* k' := IsLocalization.Away.lift (algebraMap k[X] T r) hr'
  have hψ₂ : ∀ x : T, ψ₂ (algebraMap T Sr x) = ψ₁ x := IsLocalization.Away.lift_eq _ hr'
  have hrT : Submonoid.powers (algebraMap k[X] T r) ≤ nonZeroDivisors T := by
    refine powers_le_nonZeroDivisors_of_noZeroDivisors fun h ↦ hr ?_
    rw [IsScalarTower.algebraMap_apply k[X] S T] at h
    exact (FaithfulSMul.algebraMap_injective k[X] S) ((IsLocalization.injective T hfT)
      (h.trans (map_zero _).symm) |>.trans (map_zero _).symm)
  have hψ₂i : Function.Injective ψ₂ := by
    refine (IsLocalization.lift_injective_iff _).mpr fun x y ↦ ?_
    rw [(IsLocalization.injective Sr hrT).eq_iff]
    exact hψ₁i.eq_iff.symm
  let ψ : Sr →ₐ[k] k' :=
    { ψ₂ with
      commutes' := fun c ↦ by
        change ψ₂ (algebraMap k Sr c) = _
        rw [IsScalarTower.algebraMap_apply k T Sr, hψ₂, IsScalarTower.algebraMap_apply k S T,
          hψ₁]
        rfl }
  have hψ : Function.Injective ψ := hψ₂i
  let B := ψ.range
  let e : Sr ≃ₐ[k] B := AlgEquiv.ofInjective ψ hψ
  -- `B` is finitely generated and contains `A`
  have : Algebra.FiniteType k S := .trans (S := k[X]) inferInstance inferInstance
  have : Algebra.FiniteType S T := IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) _
  have : Algebra.FiniteType k T := .trans (S := S) inferInstance inferInstance
  have : Algebra.FiniteType T Sr :=
    IsLocalization.finiteType_of_monoid_fg (Submonoid.powers (algebraMap k[X] T r)) _
  have : Algebra.FiniteType k Sr := .trans (S := T) inferInstance inferInstance
  have hBfg : B.FG := by
    change ψ.range.FG
    rw [← Algebra.map_top]
    exact (Algebra.FiniteType.out).map ψ
  have hAB : A ≤ B := fun a ha ↦
    ⟨algebraMap T Sr (algebraMap S T ⟨a, hAS a ha⟩), by
      change ψ₂ _ = _
      rw [hψ₂, hψ₁]⟩
  -- `B` is finite étale over `Rr`
  let _ : Algebra Rr B := ((e : Sr →+* B).comp (algebraMap Rr Sr)).toAlgebra
  let eR : Sr ≃ₐ[Rr] B := { e with commutes' := fun _ ↦ rfl }
  have : Module.Finite Rr B := Module.Finite.equiv eR.toLinearEquiv
  have : Algebra.Etale Rr B := Algebra.Etale.of_equiv eR
  -- `Spec B ⟶ Spec Rr ⟶ Spec k`
  let p := Spec.map (CommRingCat.ofHom (algebraMap Rr B))
  have : IsFinite p := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : Etale p := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hkRr : IsScalarTower k Rr Sr := IsScalarTower.of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply k k[X] Rr, ← IsScalarTower.algebraMap_apply k[X] Rr Sr,
      IsScalarTower.algebraMap_apply k k[X] Sr]
  have w : p ≫ Spec.map (CommRingCat.ofHom (algebraMap k Rr)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun c ↦ ?_
    change e (algebraMap Rr Sr (algebraMap k Rr c)) = algebraMap k B c
    rw [← IsScalarTower.algebraMap_apply k Rr Sr, AlgEquiv.commutes]
  have : ConnectedSpace (Spec (.of B)) := inferInstance
  refine ⟨B, hAB, hBfg, ?_, (hC k r hr).of_isFinite_of_etale p w⟩
  -- smoothness: `Spec k[X]_r ⟶ 𝔸¹` is an open immersion
  rw [← w]
  have : Spec.map (CommRingCat.ofHom (algebraMap k Rr)) =
      Spec.map (CommRingCat.ofHom (algebraMap k[X] Rr)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k k[X])) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rw [this]
  infer_instance

/-- The step of the transcendence-degree induction of the resolution-free route to XIII.4.6 in
characteristic `0`, given the case of the open subsets of the affine line
(`AffineLineOpenInvarianceStatement`): let `X` be connected, normal, quasi-compact,
quasi-separated and locally of finite type over an algebraically closed field `k` of
characteristic `0`, and `k'` an algebraically closed extension of transcendence degree at most
`1`. Then `X' ↦ X' ⊗ₖ k'` is an equivalence `FEt(X) ≌ FEt(X ⊗ₖ k')`
(`isEquivalence_pullback_fst_of_cofinal` with the cofinal family of
`exists_le_fg_invariance_of_trdeg_le_one`). -/
theorem isEquivalence_pullback_fst_of_trdeg_le_one (hC : AffineLineOpenInvarianceStatement.{u})
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k] {X : Scheme.{u}} (s : X ⟶ Spec (.of k))
    [QuasiCompact s] [QuasiSeparated s] [LocallyOfFiniteType s] [ConnectedSpace X]
    (hX : ExposeI.IsNormalScheme X) (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k']
    (hk' : Algebra.trdeg k k' ≤ 1) :
    (ExposeV.FEt.pullback
      (pullback.fst s (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).IsEquivalence :=
  isEquivalence_pullback_fst_of_cofinal s hX k'
    (exists_le_fg_invariance_of_trdeg_le_one hC k' hk')

end SGA.SGA1.ExposeXIII
