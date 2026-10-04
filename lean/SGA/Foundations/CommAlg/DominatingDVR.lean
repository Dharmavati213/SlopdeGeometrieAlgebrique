/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.EssentialFiniteness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.PowerSeries.Inverse
import SGA.Foundations.Blowup.AffineAlgebra
import SGA.Foundations.CommAlg.KrullAkizuki

/-!
# Discrete valuation rings dominating a noetherian local domain

EGA II 7.1.7 (Stacks, Tag 00PH): let `A` be a noetherian local domain which is not a field, with
fraction field `K`, and let `L` be a finitely generated field extension of `K`. Then there is a
discrete valuation ring with fraction field `L` which dominates `A`.

We prove the case of a finite extension `L` of `K`
(`IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_of_finiteDimensional`); its case
`L = K`, `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing`, is what SGA 1 uses (IX.2.6,
X.3.8): a valuation subring `V` of `K` which is a DVR, contains `A` and dominates it. The general
statement is recorded as `IsLocalRing.DominatingDVRStatement` (registry row A41); it is proved for
every finitely generated `L` in `SGA.Foundations.CommAlg.DominatingDVRGeneral`
(`IsLocalRing.dominatingDVRStatement`).

## Proof (Stacks 00PH, with a valuative choice of the blow-up chart)

Let `V₀` be any valuation ring of `K` dominating `A` (Chevalley, mathlib's
`IsLocalRing.exists_factor_valuationRing`). Choose generators `g₁, …, gₙ` of `𝔪_A` and among them
`x` with largest `V₀`-valuation; then all `gᵢ / x` lie in `V₀`. The ring `B' = A[g₁/x, …, gₙ/x]`
is a noetherian subring of `V₀` with `𝔪_A B' ⊆ x B'`, and `x` is not a unit of `B'` since it is not
one of `V₀`. Let `𝔮` be a minimal prime of `B'` over `x B'`; by Krull's principal ideal theorem it
has height one, so `B = B'_𝔮` is a one-dimensional noetherian local domain with fraction field
`K` dominating `A`. Finally a valuation ring `V` of `L` dominating `B` is a DVR by Krull–Akizuki
(`ValuationSubring.isDiscreteValuationRing_of_finiteDimensional`; for `L = K`,
`ValuationSubring.isDiscreteValuationRing_of_krullDimLE_one`). The chart `B'` is the affine blowup
algebra `Ideal.affineBlowupAlgebra` of `Foundations/Blowup/AffineAlgebra.lean` (row A49).

(Choosing `x` by the valuation avoids the classical argument that some generator has a
non-nilpotent initial form in the associated graded ring.)

## Main results

* `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_of_finiteDimensional`: EGA II 7.1.7
  for `L` finite over `K`; `IsLocalRing.exists_valuationSubring_isDiscreteValuationRing`: `L = K`.
* `IsLocalRing.exists_isDiscreteValuationRing_dominating`: the same, as an injective local
  homomorphism `A → R` to a DVR `R` in the universe of `A` (the form used by `xiii43`).
* `IsLocalRing.exists_injective_isLocalHom_isDiscreteValuationRing`: every noetherian local
  domain, field or not, has an injective local homomorphism to a DVR (for a field `k`, `k⟦X⟧`).
-/

universe u

open IsLocalRing

namespace IsLocalRing

section Blowup

variable {A : Type*} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]

/-- EGA II 7.1.7 (Stacks 00PH), case of a finite extension: let `A` be a noetherian local domain
which is not a field, `K` its fraction field and `L` a finite extension of `K`. There is a discrete
valuation ring `V` with fraction field `L` dominating `A`: `V` is a valuation subring of `L` which
is a DVR, contains (the image of) `A`, and every element of `𝔪_A` has valuation `< 1` on `V`. -/
theorem exists_valuationSubring_isDiscreteValuationRing_of_finiteDimensional (hA : ¬ IsField A)
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ a : A, algebraMap A L a ∈ V) ∧
      ∀ a ∈ maximalIdeal A, V.valuation (algebraMap A L a) < 1 := by
  classical
  -- A valuation ring `V₀` of `K` dominating `A`.
  obtain ⟨V₀, hV₀, hloc₀⟩ := IsLocalRing.exists_factor_valuationRing (algebraMap A K)
  have hv₀ : ∀ a ∈ maximalIdeal A, V₀.valuation (algebraMap A K a) < 1 := by
    intro a ha
    have hnu : ¬ IsUnit ((algebraMap A K).codRestrict V₀.toSubring hV₀ a) :=
      fun h ↦ (mem_maximalIdeal a).mp ha (isUnit_of_map_unit _ a h)
    exact (V₀.valuation_lt_one_iff ⟨algebraMap A K a, hV₀ a⟩).mp hnu
  -- Generators of `𝔪_A`, and the one of largest valuation.
  obtain ⟨s, hs⟩ : (maximalIdeal A).FG := IsNoetherian.noetherian _
  have hm : maximalIdeal A ≠ ⊥ := fun h ↦ hA (isField_iff_maximalIdeal_eq.mpr h)
  have hsne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    apply hm
    rw [← hs]
    simp
  have hsm : ∀ g ∈ s, g ∈ maximalIdeal A := fun g hg ↦ hs ▸ Ideal.subset_span hg
  obtain ⟨x, hxs, hxmax⟩ := s.exists_max_image (fun g ↦ V₀.valuation (algebraMap A K g)) hsne
  have hx0 : algebraMap A K x ≠ 0 := by
    intro h0
    apply hm
    rw [← hs, Ideal.span_eq_bot]
    intro g hg
    have hle := hxmax g hg
    rw [h0, map_zero] at hle
    have : algebraMap A K g = 0 := (Valuation.zero_iff _).mp (le_antisymm hle zero_le)
    exact IsFractionRing.injective A K (by rw [this, map_zero])
  -- The chart `B' = A[g/x : g ∈ s]` of the blow-up of `𝔪_A`.
  have hxu : IsUnit (algebraMap A K x) := Ne.isUnit hx0
  have hxinv : (↑hxu.unit⁻¹ : K) = (algebraMap A K x)⁻¹ := by
    rw [Units.val_inv_eq_inv_val, IsUnit.unit_spec]
  let B' : Subalgebra A K := (maximalIdeal A).affineBlowupAlgebra hxu
  have : IsNoetherianRing B' := Ideal.isNoetherianRing_affineBlowupAlgebra
  have hB'V₀ : ∀ b ∈ B', b ∈ V₀ := by
    let V₀' : Subalgebra A K := { V₀.toSubring with algebraMap_mem' := hV₀ }
    have hle : B' ≤ V₀' := by
      change (maximalIdeal A).affineBlowupAlgebra hxu ≤ V₀'
      rw [Ideal.affineBlowupAlgebra_eq_adjoin hs]
      refine Algebra.adjoin_le ?_
      rintro z ⟨g, hg, rfl⟩
      apply V₀.mem_of_valuation_le_one
      simp only [hxinv, ← div_eq_mul_inv, map_div₀]
      exact div_le_one_of_le₀ (hxmax g hg) zero_le
    exact fun b hb ↦ hle hb
  -- `x` is a non-unit of `B'` and `𝔪_A B' ⊆ x B'`.
  let R' : Subring K := B'.toSubring
  let x' : R' := ⟨algebraMap A K x, B'.algebraMap_mem x⟩
  have hx'u : ¬ IsUnit x' := by
    intro hu
    obtain ⟨w, hw⟩ := isUnit_iff_exists_inv.mp hu
    have hwK : algebraMap A K x * (w : K) = 1 := congrArg Subtype.val hw
    have hwV : V₀.valuation (w : K) ≤ 1 := (V₀.valuation_le_one_iff _).mpr (hB'V₀ _ w.2)
    have := congrArg V₀.valuation hwK
    rw [map_mul, map_one] at this
    exact (lt_of_le_of_lt (mul_le_of_le_one_right' hwV) (hv₀ x (hsm x hxs))).ne this
  let φ' : A →+* R' := (algebraMap A K).codRestrict R' fun a ↦ B'.algebraMap_mem a
  have hmx : ∀ a ∈ maximalIdeal A, φ' a ∈ Ideal.span {x'} := by
    intro a ha
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, Ideal.algebraMap_mul_inv_mem_affineBlowupAlgebra (ha := hxu) ha⟩, Subtype.ext ?_⟩
    exact Ideal.algebraMap_mul_inv_mul_self (ha := hxu) a
  -- A minimal prime `𝔮` over `x B'`; it has height `≤ 1`.
  have hspan : Ideal.span {x'} ≠ ⊤ := by rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨𝔮, h𝔮⟩ := Ideal.nonempty_minimalPrimes hspan
  have : 𝔮.IsPrime := h𝔮.1.1
  have hht : 𝔮.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ 𝔮 h𝔮
  have hx𝔮 : x' ∈ 𝔮 := h𝔮.1.2 (Ideal.mem_span_singleton_self _)
  -- `B = B'_𝔮`, a one-dimensional noetherian local domain with fraction field `K`.
  let B : LocalSubring K := LocalSubring.ofPrime R' 𝔮
  have : IsNoetherianRing B.toSubring :=
    IsLocalization.isNoetherianRing 𝔮.primeCompl B.toSubring inferInstance
  have : Ring.KrullDimLE 1 B.toSubring := by
    rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 B.toSubring]
    exact_mod_cast hht
  have hAB : ∀ a : A, algebraMap A K a ∈ B.toSubring :=
    fun a ↦ LocalSubring.le_ofPrime R' 𝔮 (B'.algebraMap_mem a)
  have : IsFractionRing B.toSubring K := by
    refine IsFractionRing.of_field B.toSubring K fun z ↦ ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    exact ⟨⟨_, hAB a⟩, ⟨_, hAB b⟩, rfl⟩
  have hBnu : ∀ r ∈ 𝔮, ¬ IsUnit (algebraMap R' B.toSubring r) := fun r hr h ↦
    ((IsLocalization.AtPrime.isUnit_to_map_iff B.toSubring 𝔮 r).mp h) hr
  -- A valuation ring `V` of `L` dominating `B`; it is a DVR by Krull–Akizuki.
  let f : K →+* L := algebraMap K L
  obtain ⟨V, hBV⟩ := (B.map f).exists_le_valuationSubring
  obtain ⟨hBV₁, hBV₂⟩ := hBV
  have hBL : ∀ y ∈ B.toSubring, f y ∈ V := fun y hy ↦ hBV₁ ⟨y, hy, rfl⟩
  have hVnu : ∀ r ∈ 𝔮, V.valuation (f (r : K)) < 1 := by
    intro r hr
    have := hBV₂
    let e := B.toSubring.equivMapOfInjective f f.injective
    have hnu : ¬ IsUnit (Subring.inclusion hBV₁ (e (algebraMap R' B.toSubring r))) := by
      intro h
      apply hBnu r hr
      have h' := (isUnit_of_map_unit (Subring.inclusion hBV₁) _ h).map e.symm.toRingHom
      have he : e.symm (e (algebraMap R' B.toSubring r)) = algebraMap R' B.toSubring r :=
        e.symm_apply_apply _
      exact he ▸ h'
    exact (V.valuation_lt_one_iff ⟨f (r : K), hBL _ (LocalSubring.le_ofPrime R' 𝔮 r.2)⟩).mp hnu
  have hAL : ∀ a : A, algebraMap A L a = f (algebraMap A K a) := fun a ↦
    IsScalarTower.algebraMap_apply A K L a
  have hAV : ∀ a ∈ maximalIdeal A, V.valuation (algebraMap A L a) < 1 := fun a ha ↦ by
    rw [hAL]
    exact hVnu (φ' a) (h𝔮.1.2 (hmx a ha))
  have hx0' : algebraMap A L x ≠ 0 := by
    rw [hAL]
    exact (map_ne_zero f).mpr hx0
  have hne : V ≠ ⊤ := by
    intro hV
    have hxi : (algebraMap A L x)⁻¹ ∈ V := hV ▸ ValuationSubring.mem_top _
    have hxV : algebraMap A L x ∈ V := by rw [hAL]; exact hBL _ (hAB x)
    have hu : IsUnit (⟨algebraMap A L x, hxV⟩ : V) :=
      isUnit_iff_exists_inv.mpr ⟨⟨_, hxi⟩, Subtype.ext (mul_inv_cancel₀ hx0')⟩
    exact (ne_of_lt (hAV x (hsm x hxs))) ((V.valuation_eq_one_iff _).mp hu)
  refine ⟨V, ?_, fun a ↦ by rw [hAL]; exact hBL _ (hAB a), hAV⟩
  let : Algebra B.toSubring L := (f.comp B.toSubring.subtype).toAlgebra
  have : IsScalarTower B.toSubring K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact V.isDiscreteValuationRing_of_finiteDimensional (A := B.toSubring) (K := K)
    (fun b ↦ hBL _ b.2) hne

/-- EGA II 7.1.7 (Stacks 00PH), case `L = K`: a noetherian local domain `A` which is not a field
is dominated by a discrete valuation ring `V` of its fraction field `K`: `V` is a valuation
subring of `K` which is a DVR, contains (the image of) `A`, and every element of `𝔪_A` has
valuation `< 1` on `V`. -/
theorem exists_valuationSubring_isDiscreteValuationRing (hA : ¬ IsField A) :
    ∃ V : ValuationSubring K, IsDiscreteValuationRing V ∧ (∀ a : A, algebraMap A K a ∈ V) ∧
      ∀ a ∈ maximalIdeal A, V.valuation (algebraMap A K a) < 1 :=
  exists_valuationSubring_isDiscreteValuationRing_of_finiteDimensional (K := K) hA K

end Blowup

/-- EGA II 7.1.7, in the form used by `xiii43` (X.3.8): a noetherian local domain `A` which is not
a field has an injective local homomorphism to a discrete valuation ring `R`, in the universe of
`A`. (`R` is a valuation subring of `FractionRing A`.) -/
theorem exists_isDiscreteValuationRing_dominating (A : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] [IsNoetherianRing A] (hA : ¬ IsField A) :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), Function.Injective φ ∧ IsLocalHom φ := by
  obtain ⟨V, hV, hAV, hmV⟩ :=
    exists_valuationSubring_isDiscreteValuationRing (K := FractionRing A) hA
  refine ⟨V, inferInstance, inferInstance, hV, (algebraMap A (FractionRing A)).codRestrict V hAV,
    fun a b h ↦ IsFractionRing.injective A (FractionRing A) (congrArg Subtype.val h), ⟨?_⟩⟩
  intro a ha
  by_contra hna
  have := hmV a ((mem_maximalIdeal a).mpr hna)
  exact this.ne ((V.valuation_eq_one_iff _).mp ha)

/-- Every noetherian local domain `A` (a field or not) has an injective local homomorphism to a
discrete valuation ring in the universe of `A`: EGA II 7.1.7 if `A` is not a field, and
`A → A⟦X⟧` if it is. -/
theorem exists_injective_isLocalHom_isDiscreteValuationRing (A : Type u) [CommRing A]
    [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] :
    ∃ (R : Type u) (_ : CommRing R) (_ : IsDomain R) (_ : IsDiscreteValuationRing R)
      (φ : A →+* R), Function.Injective φ ∧ IsLocalHom φ := by
  by_cases hA : IsField A
  · let := hA.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C,
      PowerSeries.C_injective, ⟨fun a ha ↦ ?_⟩⟩
    by_contra hna
    have : a = 0 := by
      by_contra h0
      exact hna (isUnit_iff_ne_zero.mpr h0)
    rw [this, map_zero] at ha
    exact not_isUnit_zero ha
  · exact exists_isDiscreteValuationRing_dominating A hA

/-- EGA II 7.1.7 (Stacks, Tag 00PH), statement: let `A` be a noetherian local domain which is not
a field, `K` its fraction field and `L` a finitely generated field extension of `K` (written
`Algebra.EssFiniteType K L`). There is a discrete valuation ring `V` with fraction field `L`
dominating `A`: a valuation subring `V` of `L` which is a DVR, contains the image of `A`, and on
which every element of `𝔪_A` has valuation `< 1`. All rings are in the same universe `u`.
The case `L` finite over `K` is
`exists_valuationSubring_isDiscreteValuationRing_of_finiteDimensional`; the general case is
`IsLocalRing.dominatingDVRStatement` in `SGA.Foundations.CommAlg.DominatingDVRGeneral`. -/
def DominatingDVRStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A], ¬ IsField A →
    ∀ (K L : Type u) [Field K] [Field L] [Algebra A K] [IsFractionRing A K] [Algebra K L]
      [Algebra A L] [IsScalarTower A K L] [Algebra.EssFiniteType K L],
      ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧ (∀ a : A, algebraMap A L a ∈ V) ∧
        ∀ a ∈ maximalIdeal A, V.valuation (algebraMap A L a) < 1

end IsLocalRing
