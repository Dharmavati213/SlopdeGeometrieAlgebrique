/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.TensorProduct.Quotient
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.SGA1.ExposeI.StandardEtale
import SGA.SGA1.ExposeII.Permanence
import SGA.SGA1.ExposeX.TameLiftingGalois
import SGA.SGA1.ExposeXIII.AbhyankarPurity

/-!
# SGA 1, Exposé X, 3.8: the generic point of the closed fibre

Let `R` be a discrete valuation ring with uniformizer `π` and `X` smooth over `R`. In the proof of
X.3.8 SGA uses that the local ring of `X` at a generic point `ξ` of the closed fibre is a discrete
valuation ring with uniformizer `π` (`X` is regular, `ξ` has codimension one, and the closed fibre
is reduced at `ξ`); Abhyankar's lemma X.3.6 is then applied over it. We prove this in ring form:

* `isDiscreteValuationRing_localization_of_smooth`: for `A` smooth over `R` and `q` a prime of `A`
  minimal over `π A`, `A_q` is a discrete valuation ring and `π` is a uniformizer of it;
* `isEtaleAt_integralClosure_of_isGalois`: after the Kummer base change `R_n = R[T]/(Tⁿ - π)`, a
  covering of the generic fibre which is generically Galois of degree `n` (`n` prime to the
  residue characteristic) becomes unramified above `ξ`: it is tamely ramified at `ξ` with
  ramification indices dividing `n` (X.3), and X.3.6 applies over `A_q`
  (`SGA.SGA1.ExposeXIII.formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt`);
* `comap_mem_minimalPrimes_of_height_eq_one`: on the Kummer chart, the height-one primes
  containing `T` lie over generic points of the closed fibre.
-/

universe u

open IsLocalRing TensorProduct Polynomial

namespace SGA.SGA1.ExposeX

section Smooth

variable {R A : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing A]
  [Algebra R A] [Algebra.Smooth R A]

/-- The closed fibre `A ⊗_R κ(R)` of an algebra smooth over a discrete valuation ring is reduced
(it is smooth over the residue field). -/
theorem isReduced_tensor_residueField_of_smooth : IsReduced (A ⊗[R] ResidueField R) := by
  have : IsReduced (ResidueField R ⊗[R] A) := ExposeII.isReduced_of_smooth (R := ResidueField R)
  exact isReduced_of_injective (Algebra.TensorProduct.comm R A (ResidueField R)).toRingHom
    (Algebra.TensorProduct.comm R A (ResidueField R)).injective

/-- At a prime `q` of an algebra `A` smooth over a discrete valuation ring `R`, the fibre
`A_q ⊗_R κ(R) = A_q / 𝔪_R A_q` is reduced (a localization of the closed fibre `A ⊗_R κ(R)`). -/
theorem isReduced_localization_tensor_residueField_of_smooth (q : Ideal A) [q.IsPrime] :
    IsReduced (Localization.AtPrime q ⊗[R] ResidueField R) := by
  have := isReduced_tensor_residueField_of_smooth (R := R) (A := A)
  let : Algebra (A ⊗[R] ResidueField R)
      (Localization.AtPrime q ⊗[A] (A ⊗[R] ResidueField R)) :=
    Algebra.TensorProduct.rightAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[R] ResidueField R) q.primeCompl)
      (Localization.AtPrime q ⊗[A] (A ⊗[R] ResidueField R)) :=
    IsLocalization.tensorRight (A := Localization.AtPrime q) (S := A ⊗[R] ResidueField R)
      q.primeCompl
  have : IsReduced (Localization.AtPrime q ⊗[A] (A ⊗[R] ResidueField R)) :=
    isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (A ⊗[R] ResidueField R) q.primeCompl)
      (Localization.AtPrime q ⊗[A] (A ⊗[R] ResidueField R)) ‹_›
  let e := Algebra.TensorProduct.cancelBaseChange R A (Localization.AtPrime q)
    (Localization.AtPrime q) (ResidueField R)
  exact isReduced_of_injective e.symm.toRingHom e.symm.injective

/-- A step of the proof of X.3.8 (the core statement is `TameLiftingDVRStatement`): at a prime
`q` of an algebra `A` smooth over a discrete valuation ring `R` with
uniformizer `π`, minimal over `π A` (a generic point of the closed fibre), the local ring `A_q` is
a discrete valuation ring with uniformizer `π`: it is regular (II.5.3) of dimension one (Krull's
principal ideal theorem; `π` is regular since `A` is flat), and `A_q / π A_q` is reduced. -/
theorem isDiscreteValuationRing_localization_of_smooth [IsDomain A] {π : R} (hπ : Irreducible π)
    (q : Ideal A) [q.IsPrime] (hq : q ∈ (Ideal.span {algebraMap R A π}).minimalPrimes) :
    IsDiscreteValuationRing (Localization.AtPrime q) ∧
      Irreducible (algebraMap R (Localization.AtPrime q) π) := by
  let Aq := Localization.AtPrime q
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  have : IsRegularLocalRing Aq := ExposeII.isRegularLocalRing_localization_of_smooth (R := R) q
  have : Module.Flat R Aq := Module.Flat.trans R A Aq
  -- `π` is nonzero in `A_q` (`A_q` is flat over `R`)
  have hπ0 : algebraMap R Aq π ≠ 0 := by
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Aq)
      (mem_nonZeroDivisors_of_ne_zero hπ.ne_zero)
    intro h0
    have : π • (1 : Aq) = π • (0 : Aq) := by rw [Algebra.smul_def, mul_one, h0, smul_zero]
    exact one_ne_zero (hreg this)
  have hπm : algebraMap R Aq π ∈ maximalIdeal Aq := by
    rw [IsScalarTower.algebraMap_apply R A Aq, ← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (hq.1.2 (Ideal.mem_span_singleton_self _))
  -- `dim A_q ≤ 1` (Krull), so `A_q` is a discrete valuation ring
  have hle : ringKrullDim Aq ≤ 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Aq]
    exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq
  have : IsPrincipalIdealRing Aq :=
    IsRegularLocalRing.isPrincipalIdealRing_of_ringKrullDim_le_one hle
  have : IsDiscreteValuationRing Aq :=
    { not_a_field' := fun h ↦ hπ0 (by rw [h] at hπm; exact hπm) }
  refine ⟨this, ?_⟩
  -- `A_q / π A_q` is reduced, so `π` is a uniformizer
  have hred : IsReduced (Aq ⧸ Ideal.span {algebraMap R Aq π}) := by
    have : IsReduced (Aq ⊗[R] (R ⧸ maximalIdeal R)) :=
      isReduced_localization_tensor_residueField_of_smooth (R := R) q
    have hmap : (maximalIdeal R).map (algebraMap R Aq) = Ideal.span {algebraMap R Aq π} := by
      rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
    let e := (Ideal.quotEquivOfEq hmap.symm).trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot Aq (maximalIdeal R)).toRingEquiv
    exact isReduced_of_injective e.toRingHom e.injective
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Aq
  obtain ⟨n, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hπ0 hϖ
  have hϖπ : ϖ ∈ Ideal.span {algebraMap R Aq π} := by
    have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {algebraMap R Aq π}) ϖ) := by
      refine ⟨n, ?_⟩
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
      exact ⟨↑v⁻¹, by rw [hv, ← mul_assoc, Units.inv_mul, one_mul]⟩
    exact Ideal.Quotient.eq_zero_iff_mem.mp hnil.eq_zero
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  refine le_antisymm ?_ ?_
  · rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.span_le,
      Set.singleton_subset_iff]
    exact hϖπ
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hπm

end Smooth

section Kummer

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {π : R}
  [hπ : Fact (Irreducible π)] {n : ℕ} [NeZero n]
  {A' : Type u} [CommRing A'] [IsDomain A'] [Algebra R A'] [Algebra.Smooth R A']
  {A : Type u} [CommRing A] [Algebra A' A] [Algebra R A]
  [Algebra (AdjoinRoot ((X : R[X]) ^ n - C π)) A]
  [IsScalarTower R A' A] [IsScalarTower R (AdjoinRoot ((X : R[X]) ^ n - C π)) A]
  [Algebra.IsPushout R A' (AdjoinRoot ((X : R[X]) ^ n - C π)) A]

/-- The local ring of the Kummer cover at the generic point of the closed fibre: if
`A = A' ⊗_R R[T]/(Tⁿ - π)`, then `A'_{q'} ⊗_{A'} A ≅ A'_{q'}[T]/(Tⁿ - π)`. -/
noncomputable def localizationAdjoinRootEquiv (q' : Ideal A') [q'.IsPrime] :
    Localization.AtPrime q' ⊗[A'] A ≃ₐ[Localization.AtPrime q']
      AdjoinRoot ((X : (Localization.AtPrime q')[X]) ^ n -
        C (algebraMap R (Localization.AtPrime q') π)) :=
  ((Algebra.TensorProduct.congr AlgEquiv.refl
      (Algebra.IsPushout.equiv R A' (AdjoinRoot ((X : R[X]) ^ n - C π)) A).symm).trans
    (Algebra.TensorProduct.cancelBaseChange R A' (Localization.AtPrime q')
      (Localization.AtPrime q') (AdjoinRoot ((X : R[X]) ^ n - C π)))).trans
  ((ExposeI.tensorAdjoinRootEquiv (Localization.AtPrime q') ((X : R[X]) ^ n - C π)).trans
    (AdjoinRoot.algEquivOfEq (Localization.AtPrime q') _ _ (by simp)))

set_option maxHeartbeats 800000 in
-- the instance problems on the localizations and tensor products below are large
/-- A step of the proof of X.3.8 (the core statement is `TameLiftingDVRStatement`): Abhyankar's
lemma X.3.6 at a generic point of the closed fibre after the Kummer base change, on an affine chart.
Let `R` be a discrete valuation ring with uniformizer `π`, `n` prime to the residue characteristic,
`R_n = R[T]/(Tⁿ - π)`, `A'` a domain smooth over `R` (a chart of `X`) with `A'π = A'[1/π]` (the
chart of the generic fibre), `q'` a prime of `A'` minimal over `π` (a generic point `ξ` of the
closed fibre), and `A = A' ⊗_R R_n` (the chart of `X_n = X ×_R R_n`). Let `W₀` be a finite étale
`A'π`-algebra (a covering of the generic fibre) which is generically Galois of degree `n`: for the
fraction field `K` of `A'`, `K ⊗_{A'π} W₀` is a domain of degree `n` over `K` with at least `n`
automorphisms (`isDomain_and_finrank_eq_card_aut_of_isGalois` gives this for a Galois covering of
degree `n`). Let `W` be an `A`-algebra generated by the image of `W₀` (e.g. `A ⊗_{A'} W₀`, the
pulled back covering). Then the normalization of `A` in `W` is étale over `A` at every prime lying
over a prime of `A'` contained in `q'`.

Over the discrete valuation ring `A'_{q'}` (`isDiscreteValuationRing_localization_of_smooth`),
`K ⊗_{A'π} W₀` is tamely ramified with ramification indices dividing `n`
(`isTamelyRamifiedAt_and_dvd_of_card`); localizing at `A' - q'` gives `A'_{q'}[T]/(Tⁿ - π)`
(`localizationAdjoinRootEquiv`), over which X.3.6 is
`SGA.SGA1.ExposeXIII.formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt`. -/
theorem isEtaleAt_integralClosure_of_isGalois (hnR : (n : R) ∉ maximalIdeal R)
    (q' : Ideal A') [q'.IsPrime] (hq' : q' ∈ (Ideal.span {algebraMap R A' π}).minimalPrimes)
    (A'π : Type u) [CommRing A'π] [Algebra A' A'π] [IsLocalization.Away (algebraMap R A' π) A'π]
    (W₀ : Type u) [CommRing W₀] [Algebra A' W₀] [Algebra A'π W₀] [IsScalarTower A' A'π W₀]
    [Module.Finite A'π W₀] [Algebra.Etale A'π W₀]
    (hgal : ∀ (K : Type u) [Field K] [Algebra A'π K] [IsFractionRing A'π K],
      IsDomain (K ⊗[A'π] W₀) ∧ Module.finrank K (K ⊗[A'π] W₀) = n ∧
        Module.finrank K (K ⊗[A'π] W₀) ≤ Nat.card ((K ⊗[A'π] W₀) ≃ₐ[K] (K ⊗[A'π] W₀)))
    (W : Type u) [CommRing W] [Algebra A W] [Algebra A' W] [Algebra W₀ W] [IsScalarTower A' A W]
    [IsScalarTower A' W₀ W] (hgen : ∀ c : W, c ∈ Algebra.adjoin A (Set.range (algebraMap W₀ W)))
    (Q : Ideal (integralClosure A W)) [Q.IsPrime]
    (hQ : (Q.comap (algebraMap A (integralClosure A W))).comap (algebraMap A' A) ≤ q') :
    Algebra.IsEtaleAt A Q := by
  classical
  -- the discrete valuation ring `R₀ = A'_{q'}` with uniformizer `u = π`
  obtain ⟨hdvr, hu⟩ := isDiscreteValuationRing_localization_of_smooth hπ.out q' hq'
  have : Fact (Irreducible (algebraMap R (Localization.AtPrime q') π)) := ⟨hu⟩
  have hnR0 : ((n : ℕ) : Localization.AtPrime q') ∉ maximalIdeal (Localization.AtPrime q') := by
    rw [← map_natCast (algebraMap A' (Localization.AtPrime q')),
      IsLocalization.AtPrime.to_map_mem_maximal_iff _ q', ← map_natCast (algebraMap R A')]
    intro hn
    exact (Ideal.IsPrime.ne_top ‹_›) (Ideal.eq_top_of_isUnit_mem _ hn
      ((IsLocalRing.notMem_maximalIdeal.mp hnR).map _))
  set R₀ := Localization.AtPrime q'
  -- the function field `K₀` of `A'`, an `A'π`-algebra
  set K₀ := FractionRing A'
  have hπK : IsUnit (algebraMap A' K₀ (algebraMap R A' π)) := by
    rw [IsScalarTower.algebraMap_apply A' R₀ K₀, ← IsScalarTower.algebraMap_apply R A' R₀]
    exact isUnit_iff_ne_zero.mpr ((map_ne_zero_iff _ (IsFractionRing.injective R₀ K₀)).mpr
      hu.ne_zero)
  let : Algebra A'π K₀ := (IsLocalization.Away.lift (algebraMap R A' π) hπK).toAlgebra
  have : IsScalarTower A' A'π K₀ :=
    .of_algebraMap_eq fun a ↦ (IsLocalization.Away.lift_eq _ hπK a).symm
  have : IsFractionRing A'π K₀ :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
      (Submonoid.powers (algebraMap R A' π)) A'π K₀
  obtain ⟨hdomB, hdegB, hcardB⟩ := hgal K₀
  -- the generic algebra `B = K₀ ⊗_{A'π} W₀`: tamely ramified over `R₀`, indices dividing `n`
  set B := K₀ ⊗[A'π] W₀
  have : IsScalarTower R₀ K₀ B := inferInstance
  have htame : ∀ (P : Ideal (integralClosure R₀ B)) [P.IsPrime],
      P.LiesOver (maximalIdeal R₀) →
      ExposeXIII.IsTamelyRamifiedAt R₀ P ∧ P.ramificationIdx R₀ ∣ n := by
    intro P _ hP
    have := isTamelyRamifiedAt_and_dvd_of_card R₀ K₀ B hcardB (by rw [hdegB]; exact hnR0) P hP
    rwa [hdegB] at this
  -- `S₀ = R₀ ⊗_{A'} A ≅ R₀[T]/(Tⁿ - u)`, the localization of `A` at `A' - q'`
  let S₀ := R₀ ⊗[A'] A
  let : Algebra A S₀ := Algebra.TensorProduct.rightAlgebra
  let N := Algebra.algebraMapSubmonoid A q'.primeCompl
  have : IsLocalization N S₀ := IsLocalization.tensorRight (A := R₀) (S := A) q'.primeCompl
  let ρ : S₀ ≃ₐ[R₀] AdjoinRoot ((X : R₀[X]) ^ n - C (algebraMap R R₀ π)) :=
    localizationAdjoinRootEquiv q'
  -- `W' = W_{A' - q'}`, an `S₀`-algebra
  let W' := Localization (Algebra.algebraMapSubmonoid W N)
  have hunitsR : ∀ y : q'.primeCompl, IsUnit (Algebra.ofId A' W' y) := by
    rintro ⟨a, ha⟩
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A' W W',
      IsScalarTower.algebraMap_apply A' A W, ← IsScalarTower.algebraMap_apply A W W']
    exact IsLocalization.map_units (M := Algebra.algebraMapSubmonoid W N) W'
      ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem
        (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : q'.primeCompl)⟩ : N)⟩
  let gR : R₀ →ₐ[A'] W' := IsLocalization.liftAlgHom (M := q'.primeCompl)
    (f := Algebra.ofId A' W') hunitsR
  let lR : S₀ →ₐ[A'] W' := Algebra.TensorProduct.lift gR (IsScalarTower.toAlgHom A' A W')
    fun _ _ ↦ Commute.all _ _
  let : Algebra S₀ W' := lR.toRingHom.toAlgebra
  let : Algebra R₀ W' := gR.toRingHom.toAlgebra
  have : IsScalarTower R₀ S₀ W' := .of_algebraMap_eq fun r ↦ by
    change gR r = lR (r ⊗ₜ 1)
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  have : IsScalarTower A S₀ W' := .of_algebraMap_eq fun a ↦ by
    change algebraMap A W' a = lR ((1 : R₀) ⊗ₜ a)
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    rfl
  have hA' (a : A') : algebraMap R₀ W' (algebraMap A' R₀ a) =
      algebraMap W W' (algebraMap W₀ W (algebraMap A' W₀ a)) := by
    change gR (algebraMap A' R₀ a) = _
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply A' W₀ W,
      IsScalarTower.algebraMap_apply A' W W']
  have hπW : IsUnit (algebraMap R₀ W' (algebraMap R R₀ π)) := by
    rw [IsScalarTower.algebraMap_apply R A' R₀, hA', IsScalarTower.algebraMap_apply A' A'π W₀]
    exact (((IsLocalization.Away.algebraMap_isUnit _).map _).map _).map _
  -- `W'` is a `K₀`-algebra: the nonzero elements of `R₀` are units in `W'`
  have hunitsK : ∀ y : nonZeroDivisors R₀, IsUnit (algebraMap R₀ W' y) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hy) hu
    change IsUnit (algebraMap R₀ W' y)
    rw [hv, map_mul, map_pow]
    exact (v.isUnit.map _).mul (hπW.pow k)
  let : Algebra K₀ W' := (IsLocalization.lift (M := nonZeroDivisors R₀) hunitsK).toAlgebra
  have : IsScalarTower R₀ K₀ W' :=
    .of_algebraMap_eq fun r ↦ (IsLocalization.lift_eq (M := nonZeroDivisors R₀) hunitsK r).symm
  have : IsScalarTower A' K₀ W' := .of_algebraMap_eq fun a ↦ by
    rw [IsScalarTower.algebraMap_apply A' R₀ K₀, ← IsScalarTower.algebraMap_apply R₀ K₀ W']
    exact (gR.commutes a).symm
  let : Algebra A'π W' := ((algebraMap K₀ W').comp (algebraMap A'π K₀)).toAlgebra
  have : IsScalarTower A'π K₀ W' := .of_algebraMap_eq fun _ ↦ rfl
  -- the map `W₀ → W'` and `β : B → W'`
  let g₀ : W₀ →+* W' := (algebraMap W W').comp (algebraMap W₀ W)
  have hg₀ : g₀.comp (algebraMap A'π W₀) = algebraMap A'π W' := by
    refine IsLocalization.ringHom_ext (Submonoid.powers (algebraMap R A' π)) ?_
    ext a
    simp only [RingHom.comp_apply, g₀, ← IsScalarTower.algebraMap_apply A' A'π W₀,
      ← IsScalarTower.algebraMap_apply A' W₀ W, ← IsScalarTower.algebraMap_apply A' W W']
    change _ = algebraMap K₀ W' (algebraMap A'π K₀ (algebraMap A' A'π a))
    rw [← IsScalarTower.algebraMap_apply A' A'π K₀, ← IsScalarTower.algebraMap_apply A' K₀ W']
  let g : W₀ →ₐ[A'π] W' := { g₀ with commutes' := fun a ↦ congrArg (· a) hg₀ }
  let β : B →ₐ[K₀] W' :=
    Algebra.TensorProduct.lift (Algebra.ofId K₀ W') g fun _ _ ↦ Commute.all _ _
  -- `W'` is generated over `S₀` by the image of `B`
  have hW (x : W) : algebraMap W W' x ∈ Algebra.adjoin S₀ (Set.range β) := by
    have hle : (Algebra.adjoin A (Set.range (algebraMap W₀ W))).map
        (IsScalarTower.toAlgHom A W W') ≤
        (Algebra.adjoin S₀ (Set.range β)).restrictScalars A := by
      rw [AlgHom.map_adjoin, Algebra.adjoin_le_iff]
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      refine Algebra.subset_adjoin ⟨1 ⊗ₜ w, ?_⟩
      change Algebra.TensorProduct.lift _ _ _ ((1 : K₀) ⊗ₜ w) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
    exact hle ⟨x, hgen x, rfl⟩
  have hgen' (c : W') : c ∈ Algebra.adjoin S₀ (Set.range β) := by
    obtain ⟨⟨x, ⟨_, s, hs, rfl⟩⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid W N) c
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    refine Subalgebra.mul_mem _ (hW x) ?_
    obtain ⟨a, ha, rfl⟩ := hs
    have : IsLocalization.mk' W' (1 : W) ⟨algebraMap A W (algebraMap A' A a),
        Algebra.mem_algebraMapSubmonoid_of_mem
          (⟨_, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, ha⟩ : q'.primeCompl)⟩ : N)⟩ =
        algebraMap S₀ W' (IsLocalization.mk' R₀ (1 : A') (⟨a, ha⟩ : q'.primeCompl) ⊗ₜ 1) := by
      rw [IsLocalization.mk'_eq_iff_eq_mul, map_one]
      change 1 = lR (_ ⊗ₜ 1) * algebraMap W W' (algebraMap A W (algebraMap A' A a))
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one,
        ← IsScalarTower.algebraMap_apply A' A W, ← IsScalarTower.algebraMap_apply A' W W']
      rw [← gR.commutes a, ← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  -- X.3.6 over `R₀` (`formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt`)
  have hS₀ (x : S₀) : x ∈ Algebra.adjoin S₀ (Set.range (Algebra.ofId R₀ S₀)) :=
    Subalgebra.algebraMap_mem (Algebra.adjoin S₀ (Set.range (Algebra.ofId R₀ S₀))) x
  have := ExposeXIII.formallyEtale_integralClosure_of_forall_isTamelyRamifiedAt R₀ K₀
    (algebraMap R R₀ π) n hnR0 S₀ ρ R₀ B htame S₀ (Algebra.ofId R₀ S₀) hS₀ W' β hgen'
  -- back to `W` by localization
  refine ExposeXIII.isEtaleAt_integralClosure_of_isLocalization (S' := S₀) (C' := W') N Q ?_
  rintro _ ⟨a, ha, rfl⟩ haQ
  exact ha (hQ haQ)

/-- On the chart `A = A' ⊗_R R[T]/(Tⁿ - π)` of the Kummer cover, a height-one prime `P` containing
`T` lies over a prime of `A'` minimal over `π` (a generic point of the closed fibre): its
contraction contains `Tⁿ = π`, has height at most one since `A' → A` is flat (going down), and is
nonzero. -/
theorem comap_mem_minimalPrimes_of_height_eq_one (hπ0 : algebraMap R A' π ≠ 0)
    (P : Ideal A) [P.IsPrime]
    (ht : algebraMap (AdjoinRoot ((X : R[X]) ^ n - C π)) A (AdjoinRoot.root _) ∈ P)
    (hP : P.height = 1) :
    P.comap (algebraMap A' A) ∈ (Ideal.span {algebraMap R A' π}).minimalPrimes := by
  have : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing R A'
  have : Module.Flat A' A :=
    Module.Flat.isBaseChange (R := R) (S := A') (M := AdjoinRoot ((X : R[X]) ^ n - C π))
      (N := A) Algebra.IsPushout.out
  have hπP : algebraMap R A' π ∈ P.comap (algebraMap A' A) := by
    rw [Ideal.mem_comap, ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R (AdjoinRoot ((X : R[X]) ^ n - C π)) A,
      ← ExposeXIII.root_X_pow_sub_C_pow, map_pow]
    exact Ideal.pow_mem_of_mem _ ht _ (Nat.pos_of_ne_zero (NeZero.ne n))
  have hht := Ideal.height_under_le_height_of_hasGoingDown (R := A') P
  rw [hP] at hht
  have : (⊥ : Ideal A').IsPrime := Ideal.isPrime_bot
  refine ⟨⟨Ideal.comap_isPrime _ _, (Ideal.span_singleton_le_iff_mem _).mpr hπP⟩, ?_⟩
  rintro r ⟨hr, hπr⟩ hle
  by_contra hne
  have hlt : r < P.comap (algebraMap A' A) := lt_of_le_of_ne hle fun h ↦ hne (h ▸ le_rfl)
  have h1 := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
  have h0 : (⊥ : Ideal A') < r := bot_lt_iff_ne_bot.mpr fun h ↦ hπ0 (by
    have := hπr (Ideal.mem_span_singleton_self (algebraMap R A' π))
    rwa [h, Ideal.mem_bot] at this)
  have h2 := Ideal.height_strict_mono_of_isPrime_of_isPrime h0
  rw [Ideal.height_bot] at h2
  exact absurd ((Order.one_le_iff_pos.mpr h2).trans_lt h1) (not_lt.mpr hht)

end Kummer

end SGA.SGA1.ExposeX
