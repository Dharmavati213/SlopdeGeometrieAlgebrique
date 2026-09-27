/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.SGA1.ExposeI.Permanence
import SGA.SGA1.ExposeII.Criteria
import SGA.SGA1.ExposeII.Permanence

/-!
# SGA 1, Exposé II, II.3.1: permanence properties, pointwise

If `f : X → Y` is smooth at `x`, then `𝒪_x` is reduced (resp. regular, resp. normal) iff
`𝒪_{f(x)}` is (`permanence_of_mem_smoothLocus`). As in SGA, the proof reduces to étale morphisms
(I.9) and to affine spaces:

* the local ring `𝒪_x` is a local ring of an algebra smooth over `𝒪_{f(x)}`, at a point over the
  closed point (`IsSmoothAt.of_smooth_localizationAtPrime`);
* ascent: over a reduced (resp. regular) noetherian base this is §3 of
  `SGA.SGA1.ExposeII.Permanence`; over a normal domain, a smooth algebra is locally étale over a
  polynomial ring, which is normal, and I.9.5 (i) applies;
* descent: reducedness and normality descend along the faithfully flat `𝒪_{f(x)} → 𝒪_x`; for
  regularity, the local ring of `A[t₁,…,tₙ]` at the image of `x` is regular by I.9.1, hence so is
  its localization at `𝔪_A[t]`, which is flat over `A` with maximal ideal `𝔪_A A[t]`, and I.9.1
  applies again.
-/

universe u

open IsLocalRing Algebra

namespace SGA.SGA1.ExposeII

/-- The localization of `Localization M` at a prime `P` is the localization at `P ∩ R`. -/
lemma nonempty_ringEquiv_localization_atPrime {R : Type*} [CommRing R] (M : Submonoid R)
    (P : Ideal (Localization M)) [P.IsPrime] (Q : Ideal R) [Q.IsPrime]
    (h : P.comap (algebraMap R _) = Q) :
    Nonempty (Localization.AtPrime Q ≃ₐ[R] Localization.AtPrime P) := by
  subst h
  exact ⟨IsLocalization.localizationLocalizationAtPrimeIsoLocalization M P⟩

/-- A polynomial ring in finitely many variables over an integrally closed domain is an
integrally closed domain. -/
theorem isIntegrallyClosed_mvPolynomial (A : Type u) [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] (n : ℕ) : IsIntegrallyClosed (MvPolynomial (Fin n) A) := by
  induction n with
  | zero =>
    exact (SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
      (MvPolynomial.isEmptyAlgEquiv A (Fin 0)).symm.toRingEquiv ⟨inferInstance, inferInstance⟩).2
  | succ n ih =>
    exact (SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
      (MvPolynomial.finSuccEquiv A n).symm.toRingEquiv ⟨inferInstance, inferInstance⟩).2

/-- Reduction for II.3.1: if `S` (finitely presented over `R`) is smooth over `R` at `Q`, with
`p = Q ∩ R`, then `S_Q` is isomorphic to a local ring `S'_{Q'}` of an `R_p`-algebra `S'` smooth over
`R_p`, at a prime `Q'` over the maximal ideal of `R_p`. We state it as a transfer principle for
properties of rings invariant under isomorphism. -/
theorem IsSmoothAt.of_smooth_localizationAtPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] [FinitePresentation R S] (Q : Ideal S) [Q.IsPrime] [IsSmoothAt R Q]
    (P : ∀ (T : Type u) [CommRing T], Prop)
    (hP : ∀ (T T' : Type u) [CommRing T] [CommRing T'], (T ≃+* T') → P T → P T')
    (h : ∀ (S' : Type u) [CommRing S'] [Algebra (Localization.AtPrime (Q.under R)) S']
      [Smooth (Localization.AtPrime (Q.under R)) S'] (Q' : Ideal S') [Q'.IsPrime],
      Q'.under (Localization.AtPrime (Q.under R)) = maximalIdeal _ →
        P (Localization.AtPrime Q')) :
    P (Localization.AtPrime Q) := by
  obtain ⟨g, hg, hsm⟩ := IsSmoothAt.exists_notMem_smooth R Q
  have hdisj : Disjoint (Submonoid.powers g : Set S) Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hg
  have hQg := IsLocalization.isPrime_of_isPrime_disjoint (.powers g) (Localization.Away g) Q ‹_›
    hdisj
  have hQgc : (Q.map (algebraMap S (Localization.Away g))).comap (algebraMap S _) = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers g) _ ‹_› hdisj
  -- `S' = R_p ⊗_R S_g`, a localization of `S_g`
  let M := algebraMapSubmonoid (Localization.Away g) (Q.under R).primeCompl
  have hMdisj : Disjoint (M : Set (Localization.Away g))
      (Q.map (algebraMap S (Localization.Away g)) : Set (Localization.Away g)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨r, hr, rfl⟩ hrQ
    apply hr
    change algebraMap R S r ∈ Q
    rw [← hQgc, Ideal.mem_comap, ← IsScalarTower.algebraMap_apply]
    exact hrQ
  have hQ' := IsLocalization.isPrime_of_isPrime_disjoint M (Localization M)
    (Q.map (algebraMap S (Localization.Away g))) hQg hMdisj
  have hQ'c : ((Q.map (algebraMap S (Localization.Away g))).map
      (algebraMap _ (Localization M))).comap (algebraMap _ _) =
        Q.map (algebraMap S (Localization.Away g)) :=
    IsLocalization.under_map_of_isPrime_disjoint M _ hQg hMdisj
  have : Smooth (Localization.AtPrime (Q.under R)) (Localization M) := by
    have : Algebra.IsPushout R (Localization.AtPrime (Q.under R)) (Localization.Away g)
        (Localization M) :=
      .symm <| Algebra.isPushout_of_isLocalization (Q.under R).primeCompl _ _ _
    exact .of_equiv (Algebra.IsPushout.equiv R (Localization.AtPrime (Q.under R))
      (Localization.Away g) (Localization M))
  obtain ⟨e₁⟩ := nonempty_ringEquiv_localization_atPrime (.powers g) _ Q hQgc
  obtain ⟨e₂⟩ := nonempty_ringEquiv_localization_atPrime M _ _ hQ'c
  refine hP _ _ (e₁.toRingEquiv.trans e₂.toRingEquiv).symm (h (Localization M)
    ((Q.map (algebraMap S (Localization.Away g))).map (algebraMap _ (Localization M))) ?_)
  -- `Q'` lies over the maximal ideal of `R_p`
  refine le_antisymm (IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)) ?_
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
  intro r hr
  change algebraMap _ (Localization M) (algebraMap R (Localization.AtPrime (Q.under R)) r) ∈
    (Q.map (algebraMap S (Localization.Away g))).map (algebraMap _ (Localization M))
  rw [← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply R (Localization.Away g) (Localization M),
    ← Ideal.mem_comap, hQ'c, IsScalarTower.algebraMap_apply R S (Localization.Away g),
    ← Ideal.mem_comap, hQgc]
  exact hr

/-- Let `A` be a noetherian local ring and `q` a prime of `A[t₁,…,tₙ]` over the maximal ideal. If
the local ring at `q` is regular, so is `A`: localize further at the prime `𝔪_A[t]`, whose local
ring is flat over `A` with maximal ideal generated by `𝔪_A`, and apply I.9.1. -/
theorem isRegularLocalRing_of_localization_mvPolynomial {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] {n : ℕ} (q : Ideal (MvPolynomial (Fin n) A)) [q.IsPrime]
    (hq : q.comap (algebraMap A _) = maximalIdeal A) [IsRegularLocalRing (Localization.AtPrime q)] :
    IsRegularLocalRing A := by
  set P₀ := (maximalIdeal A).map (algebraMap A (MvPolynomial (Fin n) A))
  have hP₀ : P₀ = RingHom.ker (MvPolynomial.map (residue A) : MvPolynomial (Fin n) A →+* _) := by
    rw [MvPolynomial.ker_map, ker_residue]
    exact congrArg (Ideal.map · (maximalIdeal A)) (MvPolynomial.algebraMap_eq ..)
  have : P₀.IsPrime := hP₀ ▸ RingHom.ker_isPrime _
  have hP₀q : P₀ ≤ q := Ideal.map_le_iff_le_comap.mpr hq.ge
  -- the local ring at `P₀` is regular
  have hdisj : Disjoint (q.primeCompl : Set (MvPolynomial (Fin n) A)) P₀ := by
    rw [Set.disjoint_left]
    exact fun x hx hxP ↦ hx (hP₀q hxP)
  have := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q) P₀
    ‹_› hdisj
  have hc := IsLocalization.under_map_of_isPrime_disjoint q.primeCompl (Localization.AtPrime q)
    ‹P₀.IsPrime› hdisj
  obtain ⟨e⟩ := nonempty_ringEquiv_localization_atPrime q.primeCompl _ P₀ hc
  have : IsRegularLocalRing (Localization.AtPrime P₀) :=
    IsRegularLocalRing.of_ringEquiv
      (R := Localization.AtPrime (P₀.map (algebraMap _ (Localization.AtPrime q))))
      e.toRingEquiv.symm
  -- `A → A[t]_{P₀}` is flat and local, with `𝔪_A A[t]_{P₀}` maximal
  have hmax : (maximalIdeal A).map (algebraMap A (Localization.AtPrime P₀)) =
      maximalIdeal (Localization.AtPrime P₀) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, IsScalarTower.algebraMap_eq A
      (MvPolynomial (Fin n) A), ← Ideal.map_map]
  have : IsLocalHom (algebraMap A (Localization.AtPrime P₀)) := by
    refine ⟨fun a ha ↦ ?_⟩
    by_contra h
    have : algebraMap A (Localization.AtPrime P₀) a ∈ maximalIdeal (Localization.AtPrime P₀) :=
      hmax ▸ Ideal.mem_map_of_mem _ ((mem_maximalIdeal _).mpr h)
    exact (mem_maximalIdeal _).mp this ha
  have : IsNoetherianRing (Localization.AtPrime P₀) :=
    IsLocalization.isNoetherianRing P₀.primeCompl _ inferInstance
  have : Module.Flat A (Localization.AtPrime P₀) := .trans A (MvPolynomial (Fin n) A) _
  exact (SGA.SGA1.ExposeI.isRegularLocalRing_iff_of_flat hmax).mpr inferInstance

/-- II.3.1, "normal", ascent for smooth algebras (via I.9.5 (i)): if `S` is smooth over an
integrally closed domain `A`, the local rings of `S` are integrally closed domains. -/
theorem isDomain_and_isIntegrallyClosed_localization_of_smooth {A S : Type u} [CommRing A]
    [CommRing S] [Algebra A S] [IsDomain A] [IsIntegrallyClosed A] [Smooth A S] (Q : Ideal S)
    [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  have : IsSmoothAt A Q := by
    have := smoothLocus_eq_univ (R := A) (A := S) ▸ Set.mem_univ (⟨Q, ‹_›⟩ : PrimeSpectrum S)
    exact this
  obtain ⟨f, hf, n, _, _, _⟩ := IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := Q)
  have hdisj : Disjoint (Submonoid.powers f : Set S) Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) Q ‹_› hdisj
  have hc := IsLocalization.under_map_of_isPrime_disjoint (.powers f) (Localization.Away f)
    ‹Q.IsPrime› hdisj
  have : IsIntegrallyClosed (MvPolynomial (Fin n) A) := isIntegrallyClosed_mvPolynomial A n
  have h := SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_localization_of_etale
    (A := MvPolynomial (Fin n) A) (B := Localization.Away f)
    (Q.map (algebraMap S (Localization.Away f)))
  obtain ⟨e⟩ := nonempty_ringEquiv_localization_atPrime (.powers f) _ Q hc
  exact SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv e.toRingEquiv.symm h

/-- II.3.1, "regular", descent for smooth algebras: let `S` be smooth over a noetherian local
ring `A` and `Q` a prime of `S` over the maximal ideal. If `S_Q` is regular, so is `A`. By
II.1.1 `S` is, near `Q`, étale over `A[t₁,…,tₙ]`, so the local ring of `A[t]` at the image of `Q`
is regular (I.9.1), and then so is `A`. -/
theorem isRegularLocalRing_of_smooth {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    [IsLocalRing A] [IsNoetherianRing A] [Smooth A S] (Q : Ideal S) [Q.IsPrime]
    (hQ : Q.under A = maximalIdeal A) [IsRegularLocalRing (Localization.AtPrime Q)] :
    IsRegularLocalRing A := by
  have : IsSmoothAt A Q := by
    have := smoothLocus_eq_univ (R := A) (A := S) ▸ Set.mem_univ (⟨Q, ‹_›⟩ : PrimeSpectrum S)
    exact this
  obtain ⟨f, hf, n, _, _, _⟩ := IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A) (p := Q)
  have hdisj : Disjoint (Submonoid.powers f : Set S) Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) Q ‹_› hdisj
  have hc := IsLocalization.under_map_of_isPrime_disjoint (.powers f) (Localization.Away f)
    ‹Q.IsPrime› hdisj
  obtain ⟨e⟩ := nonempty_ringEquiv_localization_atPrime (.powers f) _ Q hc
  have : IsRegularLocalRing
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    IsRegularLocalRing.of_ringEquiv (R := Localization.AtPrime Q) e.toRingEquiv
  -- the local ring of `A[t]` at the image `q` of `Q`
  let := Localization.AtPrime.algebraOfLiesOver
    ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A))
    (Q.map (algebraMap S (Localization.Away f)))
  have : IsNoetherianRing S := FiniteType.isNoetherianRing A S
  have : IsNoetherianRing (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    have : IsNoetherianRing (Localization.Away f) :=
      IsLocalization.isNoetherianRing (.powers f) _ inferInstance
    IsLocalization.isNoetherianRing (Q.map (algebraMap S (Localization.Away f))).primeCompl _
      inferInstance
  have : IsNoetherianRing (Localization.AtPrime
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A))) :=
    IsLocalization.isNoetherianRing
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)).primeCompl _
      inferInstance
  have : IsLocalHom (algebraMap (Localization.AtPrime
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)))
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f))))) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have : Module.Flat (MvPolynomial (Fin n) A)
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    .trans _ (Localization.Away f) _
  have : Module.Flat (Localization.AtPrime
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)))
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    (Module.flat_iff_of_isLocalization _
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)).primeCompl
      _).mpr ‹_›
  have : FormallyEtale (MvPolynomial (Fin n) A)
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    .comp _ (Localization.Away f) _
  have : FormallyEtale (Localization.AtPrime
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)))
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    .localization_base
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)).primeCompl
  have : EssFiniteType (MvPolynomial (Fin n) A)
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    .comp _ (Localization.Away f) _
  have : EssFiniteType (Localization.AtPrime
      ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)))
      (Localization.AtPrime (Q.map (algebraMap S (Localization.Away f)))) :=
    .of_comp (MvPolynomial (Fin n) A) _ _
  have hreg := (SGA.SGA1.ExposeI.isRegularLocalRing_iff_of_etale (A := Localization.AtPrime
    ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)))
    (B := Localization.AtPrime (Q.map (algebraMap S (Localization.Away f))))).mpr inferInstance
  refine isRegularLocalRing_of_localization_mvPolynomial
    ((Q.map (algebraMap S (Localization.Away f))).under (MvPolynomial (Fin n) A)) ?_
  rw [← hQ]
  change ((Q.map (algebraMap S (Localization.Away f))).comap
    (algebraMap (MvPolynomial (Fin n) A) (Localization.Away f))).comap (algebraMap A _) =
      Q.comap (algebraMap A S)
  rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq,
    IsScalarTower.algebraMap_eq A S (Localization.Away f), ← Ideal.comap_comap]
  exact congrArg (Ideal.comap (algebraMap A S)) hc

/-- II.3.1, affine pointwise form: let `S` be of finite presentation over a noetherian ring `R`
and smooth over `R` at the prime `Q`, over `p = Q ∩ R`. Then `S_Q` is reduced (resp. regular,
resp. an integrally closed domain) iff `R_p` is. -/
theorem isSmoothAt_permanence {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [FinitePresentation R S] (Q : Ideal S) [Q.IsPrime] [IsSmoothAt R Q] :
    (IsReduced (Localization.AtPrime Q) ↔ IsReduced (Localization.AtPrime (Q.under R))) ∧
    (IsRegularLocalRing (Localization.AtPrime Q) ↔
      IsRegularLocalRing (Localization.AtPrime (Q.under R))) ∧
    ((IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q)) ↔
      (IsDomain (Localization.AtPrime (Q.under R)) ∧
        IsIntegrallyClosed (Localization.AtPrime (Q.under R)))) := by
  have : IsNoetherianRing (Localization.AtPrime (Q.under R)) :=
    IsLocalization.isNoetherianRing (Q.under R).primeCompl _ inferInstance
  -- the flat local homomorphism `𝒪_y → 𝒪_x`
  let := Localization.AtPrime.algebraOfLiesOver (Q.under R) Q
  have : IsLocalHom (algebraMap (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom _ _ _ Ideal.LiesOver.over
  have : Module.Flat (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
    (Module.flat_iff_of_isLocalization _ (Q.under R).primeCompl _).mpr
      (IsSmoothAt.flat_localization Q)
  have : Module.FaithfullyFlat (Localization.AtPrime (Q.under R)) (Localization.AtPrime Q) :=
    .of_flat_of_isLocalHom
  refine ⟨⟨fun _ ↦ isReduced_of_flat_of_isLocalHom (B := Localization.AtPrime Q), fun _ ↦ ?_⟩,
    ⟨fun _ ↦ ?_, fun _ ↦ ?_⟩, ⟨fun ⟨_, _⟩ ↦ isIntegrallyClosed_of_faithfullyFlat
      (B := Localization.AtPrime Q), fun ⟨_, _⟩ ↦ ?_⟩⟩
  · -- reduced, ascent
    refine IsSmoothAt.of_smooth_localizationAtPrime (R := R) Q (fun T _ ↦ IsReduced T)
      (fun T T' _ _ e _ ↦ isReduced_of_injective e.symm.toRingHom e.symm.injective)
      fun S' _ _ _ Q' _ _ ↦ ?_
    have : IsReduced S' := isReduced_of_smooth (R := Localization.AtPrime (Q.under R))
    exact isReduced_localizationPreserves Q'.primeCompl _ ‹_›
  · -- regular, descent
    refine IsSmoothAt.of_smooth_localizationAtPrime (R := R) Q
      (fun T _ ↦ IsRegularLocalRing T → IsRegularLocalRing (Localization.AtPrime (Q.under R)))
      (fun T T' _ _ e h h' ↦ h (.of_ringEquiv e.symm)) (fun S' _ _ _ Q' _ hQ' _ ↦
        isRegularLocalRing_of_smooth Q' hQ') ‹_›
  · -- regular, ascent
    refine IsSmoothAt.of_smooth_localizationAtPrime (R := R) Q (fun T _ ↦ IsRegularLocalRing T)
      (fun T T' _ _ e _ ↦ .of_ringEquiv e) fun S' _ _ _ Q' _ _ ↦ ?_
    exact isRegularLocalRing_localization_of_smooth (R := Localization.AtPrime (Q.under R)) Q'
  · -- normal, ascent
    refine IsSmoothAt.of_smooth_localizationAtPrime (R := R) Q
      (fun T _ ↦ IsDomain T ∧ IsIntegrallyClosed T)
      (fun T T' _ _ e h ↦ SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv e h)
      fun S' _ _ _ Q' _ _ ↦ ?_
    exact isDomain_and_isIntegrallyClosed_localization_of_smooth
      (A := Localization.AtPrime (Q.under R)) Q'

/-- Reducedness, regularity and normality are invariant under ring isomorphisms. -/
lemma permanence_iff_of_ringEquiv {T T' : Type u} [CommRing T] [CommRing T'] (e : T ≃+* T') :
    (IsReduced T ↔ IsReduced T') ∧ (IsRegularLocalRing T ↔ IsRegularLocalRing T') ∧
      ((IsDomain T ∧ IsIntegrallyClosed T) ↔ (IsDomain T' ∧ IsIntegrallyClosed T')) :=
  ⟨⟨fun _ ↦ isReduced_of_injective e.symm.toRingHom e.symm.injective,
      fun _ ↦ isReduced_of_injective e.toRingHom e.injective⟩,
    ⟨fun _ ↦ .of_ringEquiv e, fun _ ↦ .of_ringEquiv e.symm⟩,
    ⟨SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv e,
      SGA.SGA1.ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv e.symm⟩⟩

open AlgebraicGeometry in
set_option backward.isDefEq.respectTransparency.types false in
/-- II.3.1: let `f : X ⟶ Y` be locally of finite presentation with `Y` locally noetherian, and
`x ∈ X` a point where `f` is smooth. Then `𝒪_x` is reduced (resp. regular, resp. an integrally
closed domain) iff `𝒪_{f(x)}` is. -/
theorem permanence_of_mem_smoothLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [IsLocallyNoetherian Y] (x : X) (hx : x ∈ f.smoothLocus) :
    (IsReduced (X.presheaf.stalk x) ↔ IsReduced (Y.presheaf.stalk (f x))) ∧
    (IsRegularLocalRing (X.presheaf.stalk x) ↔ IsRegularLocalRing (Y.presheaf.stalk (f x))) ∧
    ((IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)) ↔
      (IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x)))) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsSmoothAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (formallySmooth_stalkMap_iff U hU V hV hVU hxV).mp hx
  have hp : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.under Γ(Y, U) =
      (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal :=
    congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hxV).1)
  -- the stalks are the local rings of the rings of sections
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  let eX : X.presheaf.stalk x ≃+* Localization.AtPrime (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (IsLocalization.algEquiv (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl _ _).toRingEquiv
  let := Y.presheaf.algebra_section_stalk ⟨f x, hVU hxV⟩
  have := hU.isLocalization_stalk ⟨f x, hVU hxV⟩
  have key (I : Ideal Γ(Y, U)) [I.IsPrime] (hI : I = (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal) :
      Nonempty (Y.presheaf.stalk (f x) ≃+* Localization.AtPrime I) := by
    subst hI
    exact ⟨(IsLocalization.algEquiv
      (hU.primeIdealOf ⟨f x, hVU hxV⟩).asIdeal.primeCompl _ _).toRingEquiv⟩
  obtain ⟨eY⟩ := key _ hp
  obtain ⟨h₁, h₂, h₃⟩ := isSmoothAt_permanence (R := Γ(Y, U)) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  obtain ⟨hX₁, hX₂, hX₃⟩ := permanence_iff_of_ringEquiv eX
  obtain ⟨hY₁, hY₂, hY₃⟩ := permanence_iff_of_ringEquiv eY
  exact ⟨hX₁.trans (h₁.trans hY₁.symm), hX₂.trans (h₂.trans hY₂.symm),
    hX₃.trans (h₃.trans hY₃.symm)⟩

end SGA.SGA1.ExposeII
