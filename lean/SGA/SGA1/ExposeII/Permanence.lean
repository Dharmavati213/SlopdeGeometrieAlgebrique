/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.Field
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# SGA 1, Exposé II, §3: permanence properties

II.3.1 says that if `f : X ⟶ Y` is smooth at `x`, then `𝒪_x` is reduced (resp. regular, resp.
normal) iff `𝒪_{f(x)}` is. SGA reduces to étale morphisms (I.9) and to affine spaces. We prove:

* the regularity of étale extensions of regular local rings (the step of I.9.1 needed here),
  hence that an algebra smooth over a regular ring has regular local rings, and that a scheme
  smooth over a locally noetherian regular scheme is regular (II.3.1, "regular", ascent);
* that a smooth algebra over a reduced noetherian ring, and a scheme smooth over a reduced
  locally noetherian scheme, are reduced (II.3.1, "reduced", ascent; via the étale case I.9.2);
* the descent of reducedness and of normality along flat local homomorphisms (II.3.1,
  "reduced" and "normal", descent);
* the flat part of formula (3.1): `dim 𝒪_x = dim 𝒪_y + dim 𝒪_{x}(fibre)` (mathlib's height
  formula for going-down extensions).

The full pointwise statement of II.3.1 is `permanence_of_mem_smoothLocus` in
`SGA.SGA1.ExposeII.PermanenceSmooth`; the formulas (3.1)–(3.2) and the Cohen–Macaulay
consequence are in `SGA.SGA1.ExposeII.Depth`.
-/

universe u

open IsLocalRing Algebra

namespace SGA.SGA1.ExposeII

section Local

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

/-- II, formula (3.1), flat part (Matsumura 13.B; mathlib): for a flat extension and `Q` over `p`,
`ht Q = ht p + ht (Q / p B)`, i.e. `dim 𝒪_x = dim 𝒪_y + dim 𝒪_{f⁻¹(y), x}`. -/
theorem height_eq_height_add_of_flat [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]
    (p : Ideal A) [p.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] :
    Q.height = p.height + (Q.map (Ideal.Quotient.mk (p.map (algebraMap A B)))).height :=
  Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p Q

/-- A flat local homomorphism of noetherian local rings with `𝔪_A B = 𝔪_B` (e.g. a local
étale homomorphism) preserves the Krull dimension. -/
theorem ringKrullDim_eq_of_flat_of_map_maximalIdeal [IsLocalRing A] [IsNoetherianRing A]
    [IsLocalRing B] [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    ringKrullDim B = ringKrullDim A := by
  have := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal A) (maximalIdeal B)
  rw [h, Ideal.map_quotient_self, Ideal.height_bot, add_zero] at this
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim, this]

/-- A flat local homomorphism of noetherian local rings with `𝔪_A B = 𝔪_B` sends a regular
local ring to a regular local ring (I.9.1, one direction). -/
theorem isRegularLocalRing_of_flat_of_map_maximalIdeal [IsRegularLocalRing A] [IsLocalRing B]
    [IsNoetherianRing B] [IsLocalHom (algebraMap A B)] [Module.Flat A B]
    (h : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B) :
    IsRegularLocalRing B := by
  refine .of_spanFinrank_maximalIdeal_le _ ?_
  rw [ringKrullDim_eq_of_flat_of_map_maximalIdeal h, ← h,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := A)]
  exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

/-- An étale algebra over a regular ring has regular local rings. -/
theorem isRegularLocalRing_localization_of_etale [IsRegularRing A] [Etale A B] (Q : Ideal B)
    [Q.IsPrime] : IsRegularLocalRing (Localization.AtPrime Q) := by
  let p := Q.under A
  let := Localization.AtPrime.algebraOfLiesOver p Q
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime Q)) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact Localization.isLocalHom_localRingHom p Q (algebraMap A B) Ideal.LiesOver.over
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing A B
  have : Module.Flat A (Localization.AtPrime Q) := .trans A B _
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime Q) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime p) p.primeCompl _).mpr ‹_›
  have : FormallyEtale A (Localization.AtPrime Q) := .comp A B _
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime Q) :=
    .localization_base p.primeCompl
  have : EssFiniteType A (Localization.AtPrime Q) := .comp A B _
  have : EssFiniteType (Localization.AtPrime p) (Localization.AtPrime Q) := .of_comp A _ _
  exact isRegularLocalRing_of_flat_of_map_maximalIdeal (A := Localization.AtPrime p)
    FormallyUnramified.map_maximalIdeal

/-- II.3.1, "regular", ascent, affine form: if `S` is smooth over a regular ring `R`, then every
local ring of `S` is regular. (SGA assumes only that the local ring of the image point is
regular; that pointwise form is `isSmoothAt_permanence` in `PermanenceSmooth`.) -/
theorem isRegularLocalRing_localization_of_smooth {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsRegularRing R] [Smooth R S] (Q : Ideal S) [Q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime Q) := by
  have : IsSmoothAt R Q := by
    have := smoothLocus_eq_univ (R := R) (A := S) ▸ Set.mem_univ (⟨Q, ‹_›⟩ : PrimeSpectrum S)
    exact this
  obtain ⟨f, hf, n, _, _, _⟩ := IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := Q)
  have hdisj : Disjoint (Submonoid.powers f : Set S) Q :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime _).mpr hf
  have := IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) Q ‹_› hdisj
  have := isRegularLocalRing_localization_of_etale (A := MvPolynomial (Fin n) R)
    (Q.map (algebraMap S (Localization.Away f)))
  have hQ : (Q.map (algebraMap S (Localization.Away f))).under S = Q :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ ‹_› hdisj
  have key (I : Ideal S) [I.IsPrime] (hI : I = Q)
      (h : IsRegularLocalRing (Localization.AtPrime I)) :
      IsRegularLocalRing (Localization.AtPrime Q) := by
    subst hI; exact h
  exact key _ (by rwa [← Ideal.under_def]) (.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f)
      (Q.map (algebraMap S (Localization.Away f)))).toRingEquiv.symm)

/-- In a reduced noetherian ring, an ideal contained in no minimal prime contains a
nonzerodivisor. -/
private lemma exists_mem_nonZeroDivisors_of_forall_not_le [IsReduced A] [IsNoetherianRing A]
    (I : Ideal A) (hI : ∀ P ∈ minimalPrimes A, ¬ I ≤ P) : ∃ s ∈ I, s ∈ nonZeroDivisors A := by
  have hfin := minimalPrimes.finite_of_isNoetherianRing A
  have hnot : ¬ (I : Set A) ⊆ ⋃ P ∈ minimalPrimes A, ((_root_.id P : Ideal A) : Set A) := by
    rw [Ideal.subset_union_prime_finite hfin ⊥ ⊥ (f := _root_.id) fun P hP _ _ ↦ hP.isPrime]
    rintro ⟨P, hP, hle⟩
    exact hI P hP hle
  obtain ⟨s, hsI, hs⟩ := Set.not_subset.mp hnot
  simp only [_root_.id, Set.mem_iUnion, SetLike.mem_coe, not_exists] at hs
  refine ⟨s, hsI, mem_nonZeroDivisors_iff_right.mpr fun a ha ↦ ?_⟩
  have : a ∈ sInf (minimalPrimes A) := by
    refine Submodule.mem_sInf.mpr fun P hP ↦ ?_
    exact ((hP.isPrime.mem_or_mem (ha ▸ P.zero_mem : a * s ∈ P)).resolve_right (hs P hP))
  rw [minimalPrimes, Ideal.sInf_minimalPrimes, Ideal.radical_bot_of_isReduced] at this
  exact this

/-- A flat algebra over a reduced noetherian ring whose localizations at the minimal primes are
reduced is reduced. -/
lemma isReduced_of_flat_of_isReduced_localization [IsReduced A] [IsNoetherianRing A]
    [Module.Flat A B] (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
      IsReduced (Localization (algebraMapSubmonoid B P.primeCompl))) : IsReduced B := by
  refine ⟨fun b hb ↦ ?_⟩
  let I : Ideal A := (Submodule.span A {b}).annihilator
  have hI : ∀ P ∈ minimalPrimes A, ¬ I ≤ P := by
    intro P hP hIP
    have := hP.isPrime
    have := h P hP
    have hb' : IsNilpotent (algebraMap B (Localization (algebraMapSubmonoid B P.primeCompl)) b) :=
      hb.map _
    obtain ⟨⟨_, s, hs, rfl⟩, hsb⟩ := (IsLocalization.map_eq_zero_iff
      (algebraMapSubmonoid B P.primeCompl) _ _).mp hb'.eq_zero
    refine hs (hIP ?_)
    rw [Submodule.mem_annihilator_span_singleton, Algebra.smul_def]
    exact hsb
  obtain ⟨s, hsI, hs⟩ := exists_mem_nonZeroDivisors_of_forall_not_le I hI
  rw [Submodule.mem_annihilator_span_singleton] at hsI
  exact Module.Flat.isSMulRegular_of_nonZeroDivisors hs (hsI.trans (smul_zero s).symm)


/-- The localization of a reduced ring at a minimal prime is a field. -/
lemma isField_localization_of_mem_minimalPrimes [IsReduced A] (P : Ideal A) [P.IsPrime]
    (hP : P ∈ minimalPrimes A) : IsField (Localization.AtPrime P) := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
    ← IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := Localization.AtPrime P)
      (q := P) (I := ⊥) hP, Ideal.map_bot,
    Ideal.radical_bot_of_isReduced]

/-- I.9.2 (used in II.3.1): an étale algebra over a reduced noetherian ring is reduced. -/
lemma isReduced_of_etale [IsReduced A] [IsNoetherianRing A] [Etale A B] : IsReduced B := by
  refine isReduced_of_flat_of_isReduced_localization (A := A) fun P _ hP ↦ ?_
  let := (isField_localization_of_mem_minimalPrimes P hP).toField
  let Bp := Localization (algebraMapSubmonoid B P.primeCompl)
  have : FormallyEtale A Bp := .comp A B Bp
  have : FormallyEtale (Localization.AtPrime P) Bp := .localization_base P.primeCompl
  have : EssFiniteType A Bp := .comp A B Bp
  have : EssFiniteType (Localization.AtPrime P) Bp := .of_comp A _ _
  exact FormallyUnramified.isReduced_of_field (Localization.AtPrime P) Bp

/-- II.3.1, "reduced", ascent, affine form: an algebra smooth over a reduced noetherian ring is
reduced. -/
theorem isReduced_of_smooth {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsReduced R] [IsNoetherianRing R] [Smooth R S] : IsReduced S := by
  refine ⟨fun s hs ↦ ?_⟩
  suffices (Submodule.span S {s}).annihilator = ⊤ by
    simpa [Submodule.mem_annihilator_span_singleton] using
      (this ▸ Submodule.mem_top : (1 : S) ∈ (Submodule.span S {s}).annihilator)
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have : IsSmoothAt R Q := by
    have := smoothLocus_eq_univ (R := R) (A := S) ▸ Set.mem_univ (⟨Q, hQ.isPrime⟩ : PrimeSpectrum S)
    exact this
  obtain ⟨f, hf, n, _, _, _⟩ := IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := Q)
  have : IsReduced (Localization.Away f) := isReduced_of_etale (A := MvPolynomial (Fin n) R)
  have hs' : algebraMap S (Localization.Away f) s = 0 := (hs.map _).eq_zero
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalization.map_eq_zero_iff (.powers f) _ _).mp hs'
  exact hf (hQ.isPrime.mem_of_pow_mem k (hle (by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]; exact hk)))

/-- II.3.1, "reduced", descent: along a flat local homomorphism of local rings (e.g. the local
homomorphism `𝒪_y → 𝒪_x` of a morphism smooth at `x`), if `B` is reduced then so is `A`. -/
theorem isReduced_of_flat_of_isLocalHom [IsLocalRing A] [IsLocalRing B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] [IsReduced B] : IsReduced A :=
  have : Module.FaithfullyFlat A B := .of_flat_of_isLocalHom
  isReduced_of_injective (algebraMap A B) (FaithfulSMul.algebraMap_injective A B)

/-- II.3.1, "normal", descent: along a faithfully flat homomorphism (e.g. a flat local
homomorphism of local rings), if `B` is an integrally closed domain then so is `A`. -/
theorem isIntegrallyClosed_of_faithfullyFlat [Module.FaithfullyFlat A B] [IsDomain B]
    [IsIntegrallyClosed B] : IsDomain A ∧ IsIntegrallyClosed A := by
  have hinj := FaithfulSMul.algebraMap_injective A B
  have : IsDomain A := hinj.isDomain _
  refine ⟨this, (isIntegrallyClosed_iff (FractionRing A)).mpr fun {x} hx ↦ ?_⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
  let φ : FractionRing A →ₐ[A] FractionRing B :=
    { IsFractionRing.map (A := A) (K := FractionRing A) (L := FractionRing B) hinj with
      commutes' := fun r ↦ by
        simp [IsFractionRing.map, IsLocalization.map_eq,
          IsScalarTower.algebraMap_apply A B (FractionRing B)] }
  have hb' : algebraMap A B b ≠ 0 := by
    rw [map_ne_zero_iff _ hinj]; exact nonZeroDivisors.ne_zero hb
  have hφ : φ (algebraMap A _ a / algebraMap A _ b) =
      algebraMap B (FractionRing B) (algebraMap A B a) /
        algebraMap B (FractionRing B) (algebraMap A B b) := by
    rw [map_div₀, φ.commutes, φ.commutes, IsScalarTower.algebraMap_apply A B (FractionRing B),
      IsScalarTower.algebraMap_apply A B (FractionRing B)]
  have hint : IsIntegral B (φ (algebraMap A _ a / algebraMap A _ b)) :=
    (hx.map φ).tower_top
  obtain ⟨c, hc⟩ := (isIntegrallyClosed_iff (FractionRing B)).mp inferInstance hint
  rw [hφ, eq_div_iff (by simpa using hb'), ← map_mul,
    (IsFractionRing.injective B (FractionRing B)).eq_iff] at hc
  have : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B) (Ideal.span {b}), Ideal.mem_comap,
      Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, hc⟩
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp this
  refine ⟨d, ?_⟩
  rw [map_mul, mul_div_assoc, div_self (by simpa using nonZeroDivisors.ne_zero hb), mul_one]

end Local

section Scheme

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The local rings at the points of an affine open with regular ring of sections are
regular. -/
theorem isRegularLocalRing_stalk_of_isRegularRing {U : X.Opens} (hU : IsAffineOpen U)
    [IsRegularRing Γ(X, U)] (x : U) : IsRegularLocalRing (X.presheaf.stalk x) :=
  have := hU.isLocalization_stalk x
  .of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf x).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- Conversely, a noetherian ring of sections over an affine open whose points have regular
local rings is a regular ring. -/
theorem isRegularRing_of_isRegularLocalRing_stalk {U : X.Opens} (hU : IsAffineOpen U)
    [IsNoetherianRing Γ(X, U)] (h : ∀ x : U, IsRegularLocalRing (X.presheaf.stalk x)) :
    IsRegularRing Γ(X, U) := by
  rw [isRegularRing_iff]
  intro p hp
  have hy : hU.fromSpec ⟨p, hp⟩ ∈ U := hU.range_fromSpec.subset ⟨_, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec ⟨p, hp⟩, hy⟩
  have : IsLocalization p.primeCompl (X.presheaf.stalk (hU.fromSpec ⟨p, hp⟩)) :=
    hU.isLocalization_stalk' ⟨p, hp⟩ hy
  have : IsRegularLocalRing (X.presheaf.stalk (hU.fromSpec ⟨p, hp⟩)) := h ⟨_, hy⟩
  exact .of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hU.fromSpec ⟨p, hp⟩)) (Localization.AtPrime p)).toRingEquiv

set_option backward.isDefEq.respectTransparency.types false in
/-- II.3.1, "regular", ascent: if `f : X ⟶ Y` is smooth and `Y` is locally noetherian with regular
local rings, then all local rings of `X` are regular. (SGA's statement is pointwise and
assumes regularity only at `f(x)`.) -/
theorem isRegularLocalRing_stalk_of_smooth (f : X ⟶ Y) [Smooth f] [IsLocallyNoetherian Y]
    (hY : ∀ y, IsRegularLocalRing (Y.presheaf.stalk y)) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have hsm := f.smooth_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : IsRegularRing Γ(Y, U) := isRegularRing_of_isRegularLocalRing_stalk hU fun y ↦ hY y
  have : IsRegularRing Γ(X, V) := by
    have : IsNoetherianRing Γ(X, V) := Algebra.FiniteType.isNoetherianRing Γ(Y, U) Γ(X, V)
    rw [isRegularRing_iff]
    intro q _
    exact isRegularLocalRing_localization_of_smooth (R := Γ(Y, U)) q
  exact isRegularLocalRing_stalk_of_isRegularRing hV ⟨x, hxV⟩

/-- The local rings at the points of an affine open with reduced ring of sections are
reduced. -/
theorem isReduced_stalk_of_isReduced {U : X.Opens} (hU : IsAffineOpen U)
    [_root_.IsReduced Γ(X, U)] (x : U) : _root_.IsReduced (X.presheaf.stalk x) :=
  have := hU.isLocalization_stalk x
  isReduced_localizationPreserves (hU.primeIdealOf x).asIdeal.primeCompl _ ‹_›

set_option backward.isDefEq.respectTransparency.types false in
/-- II.3.1, "reduced", ascent: if `f : X ⟶ Y` is smooth and `Y` is reduced and locally
noetherian, then `X` is reduced. (SGA's statement is pointwise.) -/
theorem isReduced_of_smooth_of_isReduced (f : X ⟶ Y) [Smooth f] [IsLocallyNoetherian Y]
    [AlgebraicGeometry.IsReduced Y] : AlgebraicGeometry.IsReduced X := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
    have hsm := f.smooth_appLE hU hV hVU
    algebraize [(f.appLE U V hVU).hom]
    have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    have : _root_.IsReduced Γ(X, V) := isReduced_of_smooth (R := Γ(Y, U))
    exact isReduced_stalk_of_isReduced hV ⟨x, hxV⟩
  exact isReduced_of_isReduced_stalk X

/-- II.3.1, "reduced", descent: if `f` is flat at `x` (e.g. smooth at `x`) and `𝒪_x` is reduced,
then `𝒪_{f(x)}` is reduced. -/
theorem isReduced_stalk_of_flat (f : X ⟶ Y) (x : X) (hf : (f.stalkMap x).hom.Flat)
    [IsReduced (X.presheaf.stalk x)] : IsReduced (Y.presheaf.stalk (f x)) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  exact isReduced_of_flat_of_isLocalHom (B := X.presheaf.stalk x)

/-- II.3.1, "normal", descent: if `f` is flat at `x` (e.g. smooth at `x`) and `𝒪_x` is an
integrally closed domain, then so is `𝒪_{f(x)}`. -/
theorem isIntegrallyClosed_stalk_of_flat (f : X ⟶ Y) (x : X) (hf : (f.stalkMap x).hom.Flat)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)] :
    IsDomain (Y.presheaf.stalk (f x)) ∧ IsIntegrallyClosed (Y.presheaf.stalk (f x)) := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    .of_flat_of_isLocalHom
  exact isIntegrallyClosed_of_faithfullyFlat (B := X.presheaf.stalk x)

end Scheme

end SGA.SGA1.ExposeII
