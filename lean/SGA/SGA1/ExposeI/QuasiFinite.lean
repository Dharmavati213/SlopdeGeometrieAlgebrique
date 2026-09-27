/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.Noetherian
import Mathlib.RingTheory.LocalRing.Length
import SGA.SGA1.ExposeI.Completion
import SGA.Foundations.CompleteLocalQuasiFinite

/-!
# SGA 1, Exposé I, §2: quasi-finite morphisms

SGA calls a local homomorphism `A → B` quasi-finite when the special fibre
`B/mB` is finite-dimensional over `k = A/m`. For morphisms of schemes, being
quasi-finite at a point means that the point is isolated in its fibre.
Mathlib's `Algebra.QuasiFinite` asks the same finite-dimensionality of every
fibre `κ(p) ⊗ S`; `Scheme.Hom.QuasiFiniteAt` is the pointwise condition.
The equivalence I.2.1 (i) ⇔ (ii) is proved with lengths (`finite_quotient_iff`).
After no. I.2 the exposé assumes locally noetherian schemes. Over an artinian
ring (which is complete), quasi-finite is equivalent to module-finite, a special case
of I.2.2. I.2.2 (over a complete base, a quasi-finite local algebra essentially of finite type is
finite) follows from Zariski's main theorem and the splitting of finite algebras over complete
local rings (`SGA.Foundations.CompleteLocalQuasiFinite`). The characterisation I.2.1(iii) by
completions is `finite_quotient_iff_finite_completion` in `CompletionCriteria`.
-/

universe u

namespace SGA.SGA1.ExposeI

open AlgebraicGeometry Algebra IsLocalRing

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- I.2.1(i): the special fibre `κ(m) ⊗ S` of a local homomorphism is
finite-dimensional. For a local ring this is SGA's `B/mB`. -/
def IsQuasiFiniteLocal [IsLocalRing R] : Prop :=
  Module.Finite (Ideal.ResidueField (maximalIdeal R)) ((maximalIdeal R).Fiber S)

/-- I.2.1: a globally quasi-finite algebra has finite-dimensional special fibre. -/
theorem isQuasiFiniteLocal_of_quasiFinite (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] [QuasiFinite R S] :
    Module.Finite (Ideal.ResidueField (maximalIdeal R)) ((maximalIdeal R).Fiber S) :=
  QuasiFinite.finite_fiber (maximalIdeal R)

/-- I.2.1: for a finite-type algebra, quasi-finite means finite fibres of spectra. -/
theorem quasiFinite_iff_finite_fibers [FiniteType R S] :
    QuasiFinite R S ↔
      ∀ p : PrimeSpectrum R, (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {p}).Finite :=
  ⟨fun _ p ↦ QuasiFinite.finite_comap_preimage_singleton p,
    fun h ↦ (QuasiFinite.iff_finite_comap_preimage_singleton (R := R) (S := S)).mpr h⟩

/-- I.2.2, special case of an artinian (hence complete) base: an algebra is quasi-finite (all its
fibres are finite) iff it is finite (mathlib; no finite type hypothesis is needed). -/
theorem quasiFinite_iff_finite [IsArtinianRing R] :
    QuasiFinite R S ↔ Module.Finite R S :=
  QuasiFinite.iff_of_isArtinianRing

/-- I.2.1, (i) ⇔ (ii): for a local homomorphism of noetherian local rings, `B/𝔪_A B` is
finite over `A` (i.e. finite-dimensional over `k`) iff `𝔪_A B` is an ideal of definition
of `B` and the residue field extension is finite. -/
theorem finite_quotient_iff (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
    [IsNoetherianRing B] :
    Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B)) ↔
      (∃ n, maximalIdeal B ^ n ≤ (maximalIdeal A).map (algebraMap A B)) ∧
        Module.Finite (ResidueField A) (ResidueField B) := by
  set I := (maximalIdeal A).map (algebraMap A B)
  have hI : I ≤ maximalIdeal B := map_maximalIdeal_le _
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top
    (maximalIdeal.isMaximal B).ne_top hI)
  have : IsLocalRing (B ⧸ I) := .of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hmax : maximalIdeal (B ⧸ I) = (maximalIdeal B).map (Ideal.Quotient.mk I) :=
    (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  constructor
  · intro hfin
    let := Ideal.Quotient.field (maximalIdeal A)
    have : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Module.Finite.of_restrictScalars_finite A _ _
    have : IsArtinianRing (B ⧸ I) := IsArtinianRing.of_finite (A ⧸ maximalIdeal A) _
    refine ⟨?_, ?_⟩
    · obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal (B ⧸ I)).mp inferInstance
      refine ⟨n, ?_⟩
      rw [hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker,
        Ideal.mk_ker] at hn
      exact hn
    · have : Module.Finite A (ResidueField B) :=
        Module.Finite.of_surjective (Ideal.Quotient.factorₐ A hI).toLinearMap
          (Ideal.Quotient.factor_surjective hI)
      exact Module.Finite.of_restrictScalars_finite A _ _
  · rintro ⟨⟨n, hn⟩, hk⟩
    have : IsArtinianRing (B ⧸ I) := by
      rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
      refine ⟨n, ?_⟩
      rw [hmax, ← Ideal.map_pow, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
      exact hn
    have : IsArtinian B (B ⧸ I) :=
      isArtinian_of_surjective_algebraMap (R := B ⧸ I) Ideal.Quotient.mk_surjective
    have h1 : Module.length B (B ⧸ I) ≠ ⊤ := Module.length_ne_top
    have h2 : Module.length (ResidueField A) (ResidueField B) ≠ ⊤ := Module.length_ne_top
    have h3 : Module.length A (B ⧸ I) ≠ ⊤ := by
      rw [IsLocalRing.length_restrictScalars A B]
      exact WithTop.mul_ne_top h1 h2
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h3)).1
    exact Module.IsNoetherian.finite A _

/-- I.2.2: let `A` be a complete noetherian local ring and `B` a local ring essentially of finite
type over `A` (a local ring of an `A`-scheme of finite type), with `A → B` local and quasi-finite
(`B ⧸ 𝔪_A B` finite over `A`). Then `B` is finite over `A`. Writing `B = C_Q` with `C` of finite
type, Zariski's main theorem and the splitting of finite algebras over complete local rings
give `e ∉ Q` such that `C_e` is finite over `A` and all primes of `C_e` lie in `Q`
(`IsLocalRing.exists_notMem_forall_le_and_finite`, EGA IV 18.12.1); then `C_e → C_Q = B` is
surjective. -/
theorem finite_of_quasiFinite_of_isAdicComplete (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] [EssFiniteType A B]
    (h : Module.Finite A (B ⧸ (maximalIdeal A).map (algebraMap A B))) : Module.Finite A B := by
  -- `B` is the localization of a finite type `A`-algebra `C` at a prime `Q`
  let C := EssFiniteType.subalgebra A B
  let M := EssFiniteType.submonoid A B
  let Q := (maximalIdeal B).comap (algebraMap C B)
  have : IsLocalization.AtPrime B (maximalIdeal B) :=
    IsLocalization.of_le_isUnit fun x hx ↦ IsLocalRing.notMem_maximalIdeal.mp hx
  have : IsLocalization.AtPrime B Q :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M B (maximalIdeal B)
  have hQA : Q.comap (algebraMap A C) = maximalIdeal A := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
    exact IsLocalRing.maximalIdeal_comap (algebraMap A B)
  have : Q.LiesOver (maximalIdeal A) := ⟨hQA.symm⟩
  -- `C` is quasi-finite at `Q`
  have : Algebra.QuasiFiniteAt A Q := by
    have : Algebra.WeaklyQuasiFiniteAt A Q := by
      rw [Algebra.weaklyQuasiFiniteAt_iff, show Q.under A = maximalIdeal A from hQA]
      let e : B ≃ₐ[A] Localization.AtPrime Q :=
        (IsLocalization.algEquiv Q.primeCompl B (Localization.AtPrime Q)).restrictScalars A
      have hJ : (maximalIdeal A).map (algebraMap A B) ≤
          ((maximalIdeal A).map (algebraMap A (Localization.AtPrime Q))).comap e.toAlgHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simp only [Ideal.mem_comap]
        change e (algebraMap A B a) ∈ _
        rw [AlgEquiv.commutes]
        exact Ideal.mem_map_of_mem _ ha
      exact .of_surjective_algHom (S := B ⧸ (maximalIdeal A).map (algebraMap A B))
        (Ideal.quotientMapₐ _ e.toAlgHom hJ) (Ideal.quotientMap_surjective (H := hJ) e.surjective)
    exact .of_weaklyQuasiFiniteAt Q
  obtain ⟨e, heQ, hle, hfin⟩ := IsLocalRing.exists_notMem_forall_le_and_finite (A := A) Q
  let L := Localization.Away e
  have : Module.Finite A L := hfin L
  -- the map `C_e → C_Q = B` is surjective
  have heB : IsUnit (algebraMap C B e) := IsLocalRing.notMem_maximalIdeal.mp heQ
  let φ : L →ₐ[A] B := IsLocalization.liftAlgHom (M := Submonoid.powers e)
    (f := IsScalarTower.toAlgHom A C B) fun y ↦ by
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      change IsUnit (algebraMap C B y)
      rw [← hn, map_pow]
      exact heB.pow n
  have hφ (c : C) : φ (algebraMap C L c) = algebraMap C B c := IsLocalization.lift_eq _ c
  refine Module.Finite.of_surjective φ.toLinearMap fun b ↦ ?_
  obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b
  have ht : IsUnit (algebraMap C L t) := by
    by_contra ht
    obtain ⟨N, hN, htN⟩ := Ideal.exists_le_maximal (Ideal.span {algebraMap C L t})
      (by rwa [Ne, Ideal.span_singleton_eq_top])
    have heN : e ∉ N.comap (algebraMap C L) := fun h ↦ hN.ne_top
      (N.eq_top_of_isUnit_mem h (IsLocalization.Away.algebraMap_isUnit e))
    exact t.2 (hle _ (Ideal.comap_isPrime _ _) heN (htN (Ideal.subset_span rfl)))
  obtain ⟨v, hv⟩ := ht.exists_right_inv
  refine ⟨algebraMap C L c * v, ?_⟩
  change φ (algebraMap C L c * v) = _
  rw [IsLocalization.eq_mk'_iff_mul_eq, map_mul, ← hφ, ← hφ, mul_assoc, ← map_mul,
    mul_comm v, hv, map_one, mul_one]

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- I.2: quasi-finite at a point, in SGA's language. -/
abbrev QuasiFiniteAt (x : X) : Prop := f.QuasiFiniteAt x

/-- I.2: a morphism of finite type is quasi-finite at `x` iff `{x}` is open in its fibre. -/
theorem quasiFiniteAt_iff_isolated_in_fiber [LocallyOfFiniteType f] {x : X} :
    f.QuasiFiniteAt x ↔ IsOpen {f.asFiber x} :=
  f.quasiFiniteAt_iff_isOpen_singleton_asFiber

/-- I.2: a locally quasi-finite morphism is quasi-finite at every point. -/
theorem quasiFiniteAt_of_locallyQuasiFinite [LocallyQuasiFinite f] (x : X) :
    f.QuasiFiniteAt x :=
  f.quasiFiniteAt x

end SGA.SGA1.ExposeI
