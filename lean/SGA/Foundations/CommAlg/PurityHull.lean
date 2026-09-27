/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import SGA.Foundations.CommAlg.PurityLift
import SGA.Foundations.CommAlg.RegularLocalRing
import SGA.Foundations.CommAlg.Depth
import SGA.Foundations.CommAlg.Factorial
import SGA.Foundations.CommAlg.RegularPair

/-!
# The S₂-hull of an algebra étale over the punctured spectrum

Let `R` be a noetherian local ring, `x, y ∈ 𝔪` a regular sequence on `R` and `S` an `R`-algebra
which is finite étale over the punctured spectrum of `R`: `S_g` is finite étale over `R_g` for
`g ∈ 𝔪` (for instance `S` finite over `R` and étale over the punctured spectrum,
`etale_away_of_mem_maximalIdeal`, `finite_awayMap_of_finite`). The sections of `Spec S` over
`D(x) ∪ D(y)` form a finite `R`-algebra `H = Localization.pairSections x y` on which `x, y` is a
regular sequence, which is étale over the punctured spectrum and agrees with `S` over it
(`finite_pairSections`, `isWeaklyRegular_pairSections_of_forall_isEtaleAt`,
`isEtaleAt_pairSections`, `exists_pow_mul_eq_algebraMap_pairSections`). This is the algebraic
form of `j_* j^* S` used in the proof of purity.

We also collect the other ingredients of the inductive proof of purity
(`SGA.Foundations.CommAlg.PurityInduction`):

* `IsRegularLocalRing.exists_isWeaklyRegular_notMem_sq`: a regular sequence `x, y` in a regular
  local ring of dimension `≥ 3` extends to a regular sequence `x, y, f` with `f ∉ 𝔪²`.
* `IsRegularLocalRing.surjective_of_forall_notMem`: a map `φ : B → C` from an algebra of depth
  `≥ 2`, étale over the punctured spectrum, to a finite flat algebra is surjective as soon as it is
  surjective at the primes of the hypersurface `V(f)` (the non-surjectivity locus has codimension
  `≤ 1` by Hartogs, hence meets `V(f)` outside the closed point when `dim A ≥ 3`).
* `Algebra.exists_algHom_mkₐ_comp_eq_of_isAdicComplete`: lifting maps to a complete algebra.
-/

open RingTheory.Sequence IsLocalRing Pointwise

universe u

section Quotient

/-- If `r :: rs` is weakly regular on an `A`-algebra `S`, then `rs` is weakly regular on the ring
`S ⧸ (r)`. -/
theorem isWeaklyRegular_quotient_of_cons {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    {r : A} {rs : List A} (h : IsWeaklyRegular S (r :: rs)) {J : Ideal S}
    (hJ : J = Ideal.span {algebraMap A S r}) :
    IsWeaklyRegular (S ⧸ J) (rs.map (algebraMap A (S ⧸ J))) := by
  have h1 := ((isWeaklyRegular_cons_iff S r rs).mp h).2
  have hsub : (r • ⊤ : Submodule A S) = J.restrictScalars A := by
    ext s
    rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem, hJ,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨t, -, rfl⟩
      exact ⟨t, by rw [Algebra.smul_def, mul_comm]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, Submodule.mem_top, by rw [Algebra.smul_def, mul_comm]⟩
  let e : QuotSMulTop r S ≃ₗ[A] S ⧸ J :=
    Submodule.quotEquivOfEq _ _ hsub ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv A J
  exact (isWeaklyRegular_map_algebraMap_iff (S ⧸ J) (S ⧸ J) rs).mpr
    ((e.isWeaklyRegular_congr rs).mp h1)

end Quotient

section Hull

variable {R S : Type u} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S] {x y : R}

local notation "𝓗" => Localization.pairSections (algebraMap R S x) (algebraMap R S y)

/-- A finite algebra étale over the punctured spectrum is étale over `D(g)`, `g ∈ 𝔪`. -/
theorem etale_away_of_mem_maximalIdeal [IsNoetherianRing R] [Module.Finite R S]
    (hU : ∀ (Q : Ideal S) [Q.IsPrime], Q.comap (algebraMap R S) ≠ maximalIdeal R →
      Algebra.IsEtaleAt R Q) {g : R} (hg : g ∈ maximalIdeal R) :
    Algebra.Etale R (Localization.Away (algebraMap R S g)) := by
  have : Algebra.FinitePresentation R S :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine Algebra.basicOpen_subset_etaleLocus_iff_etale.mp fun Q hQ ↦ ?_
  have : Q.asIdeal.comap (algebraMap R S) ≠ maximalIdeal R := fun h ↦ hQ (by
    rw [← Ideal.mem_comap, h]
    exact hg)
  exact hU Q.asIdeal this

omit [IsLocalRing R] in
/-- The localization `R_g → S_g` of a finite algebra is finite. -/
theorem finite_awayMap_of_finite [Module.Finite R S] (g : R) :
    (Localization.awayMap (algebraMap R S) g).Finite := by
  let Sg := Localization.Away (algebraMap R S g)
  let _ : Algebra (Localization.Away g) Sg := (Localization.awayMap (algebraMap R S) g).toAlgebra
  have : IsScalarTower R (Localization.Away g) Sg := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_comp, IsScalarTower.algebraMap_eq R S Sg])
  have : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers g)) Sg := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]; infer_instance
  exact Module.Finite.of_isLocalization R S (Submonoid.powers g)

omit [IsLocalRing R] in
/-- A regular sequence on `R` stays regular on a flat localization `S_g`. -/
theorem isWeaklyRegular_away_pair_of_flat {g : R}
    [Module.Flat R (Localization.Away (algebraMap R S g))] (hreg : IsWeaklyRegular R [x, y]) :
    IsWeaklyRegular (Localization.Away (algebraMap R S g))
      [algebraMap S (Localization.Away (algebraMap R S g)) (algebraMap R S x),
        algebraMap S (Localization.Away (algebraMap R S g)) (algebraMap R S y)] := by
  have := hreg.of_flat (S := Localization.Away (algebraMap R S g))
  simpa only [List.map_cons, List.map_nil, ← IsScalarTower.algebraMap_apply] using this

variable (hreg : IsWeaklyRegular R [x, y])
  (hE : ∀ g ∈ maximalIdeal R, Algebra.Etale R (Localization.Away (algebraMap R S g)))
include hreg hE

/-- `x, y` is a regular sequence on the hull. -/
theorem isWeaklyRegular_pairSections_of_forall_isEtaleAt (hy : y ∈ maximalIdeal R) :
    IsWeaklyRegular (Localization.pairSections (algebraMap R S x) (algebraMap R S y)) [x, y] := by
  have := hE y hy
  have h := isWeaklyRegular_away_pair_of_flat (S := S) (g := y) hreg
  have hx := ((isWeaklyRegular_cons_iff _ _ _).mp h).1
  have := Localization.isWeaklyRegular_pairSections _ _ hx
  rw [← isWeaklyRegular_map_algebraMap_iff (R := R)
    (Localization.pairSections (algebraMap R S x) (algebraMap R S y))]
  simpa only [List.map_cons, List.map_nil, ← IsScalarTower.algebraMap_apply] using this

/-- The hull is a finite `R`-algebra, if `S` is finite over `D(g)` for `g ∈ 𝔪`. -/
theorem finite_pairSections [IsNoetherianRing R]
    (hF : ∀ g ∈ maximalIdeal R, (Localization.awayMap (algebraMap R S) g).Finite)
    (hx : x ∈ maximalIdeal R) (hy : y ∈ maximalIdeal R) :
    Module.Finite R (Localization.pairSections (algebraMap R S x) (algebraMap R S y)) := by
  set a := algebraMap R S x
  set b := algebraMap R S y
  let H := Localization.pairSections a b
  have hH := isWeaklyRegular_pairSections_of_forall_isEtaleAt hreg hE hy
  have hxH : IsSMulRegular H x := ((isWeaklyRegular_cons_iff H x [y]).mp hH).1
  have hmapH : ∀ f : R, Algebra.algebraMapSubmonoid H (Submonoid.powers f) =
      Submonoid.powers (algebraMap S H (algebraMap R S f)) := fun f ↦ by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers, IsScalarTower.algebraMap_apply R S H]
  -- the chart at `x`
  let Cx := Localization.Away a
  let _ : Algebra H Cx := (Localization.pairSectionsFst a b).toRingHom.toAlgebra
  have hCx := Localization.isLocalization_pairSectionsFst a b
  have : IsScalarTower R H Cx := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R Cx r = Localization.pairSectionsFst a b (algebraMap R H r)
    rw [IsScalarTower.algebraMap_apply R S H, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Algebra.algebraMapSubmonoid H (Submonoid.powers x)) Cx := by
    rw [hmapH]; exact hCx
  let _ : Algebra (Localization.Away x) Cx := (Localization.awayMap (algebraMap R S) x).toAlgebra
  have : IsScalarTower R (Localization.Away x) Cx := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_comp, IsScalarTower.algebraMap_eq R S Cx])
  have : Module.Finite (Localization.Away x) Cx := hF x hx
  have : Algebra.Etale R Cx := hE x hx
  have : Module.Flat (Localization.Away x) Cx :=
    (Module.flat_iff_of_isLocalization (Localization.Away x) (Submonoid.powers x) Cx).mpr
      inferInstance
  have : Module.FinitePresentation (Localization.Away x) Cx :=
    Module.finitePresentation_of_finite _ _
  have : Module.Projective (Localization.Away x) Cx := Module.Flat.projective_of_finitePresentation
  -- the chart at `y`
  let Cy := Localization.Away b
  let _ : Algebra H Cy := (Localization.pairSectionsSnd a b).toRingHom.toAlgebra
  have hCy := Localization.isLocalization_pairSectionsSnd a b
  have : IsScalarTower R H Cy := IsScalarTower.of_algebraMap_eq fun r ↦ by
    change algebraMap R Cy r = Localization.pairSectionsSnd a b (algebraMap R H r)
    rw [IsScalarTower.algebraMap_apply R S H, AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  have : IsLocalization (Algebra.algebraMapSubmonoid H (Submonoid.powers y)) Cy := by
    rw [hmapH]; exact hCy
  let _ : Algebra (Localization.Away y) Cy := (Localization.awayMap (algebraMap R S) y).toAlgebra
  have : IsScalarTower R (Localization.Away y) Cy := IsScalarTower.of_algebraMap_eq' (by
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_comp, IsScalarTower.algebraMap_eq R S Cy])
  have : Module.Finite (Localization.Away y) Cy := hF y hy
  exact Module.finite_of_isLocalization_pair hreg hxH (Localization.Away x) Cx
    (Localization.Away y) Cy

/-- The hull agrees with `S` over `D(g)`, `g ∈ 𝔪`: the localization at `g` of the hull is `S_g`. -/
theorem exists_isLocalization_away_pairSections {g : R} (hg : g ∈ maximalIdeal R) :
    ∃ φ : Localization.pairSections (algebraMap R S x) (algebraMap R S y) →ₐ[S]
        Localization.Away (algebraMap R S g),
      letI := φ.toRingHom.toAlgebra
      IsLocalization.Away
        (algebraMap R (Localization.pairSections (algebraMap R S x) (algebraMap R S y)) g)
        (Localization.Away (algebraMap R S g)) := by
  have := hE g hg
  obtain ⟨φ, hφ⟩ := Localization.exists_isLocalization_pairSections_away (algebraMap R S x)
    (algebraMap R S y) (algebraMap R S g) (isWeaklyRegular_away_pair_of_flat hreg)
  refine ⟨φ, ?_⟩
  let _ := φ.toRingHom.toAlgebra
  change IsLocalization.Away (algebraMap R (Localization.pairSections (algebraMap R S x)
    (algebraMap R S y)) g) _
  rw [IsScalarTower.algebraMap_apply R S (Localization.pairSections (algebraMap R S x)
    (algebraMap R S y)) g]
  exact hφ

/-- `S → H` is injective over `D(g)`, `g ∈ 𝔪`. -/
theorem exists_pow_mul_eq_zero_of_algebraMap_pairSections_eq_zero {g : R}
    (hg : g ∈ maximalIdeal R) {s : S}
    (hs : algebraMap S (Localization.pairSections (algebraMap R S x) (algebraMap R S y)) s = 0) :
    ∃ j : ℕ, algebraMap R S g ^ j * s = 0 := by
  obtain ⟨φ, hφ⟩ := exists_isLocalization_away_pairSections hreg hE hg
  have h : algebraMap S (Localization.Away (algebraMap R S g)) s = 0 := by
    rw [← φ.commutes, hs, map_zero]
  obtain ⟨⟨_, j, rfl⟩, hj⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers
    (algebraMap R S g)) _ s).mp h
  exact ⟨j, hj⟩

/-- `S → H` is surjective over `D(g)`, `g ∈ 𝔪`. -/
theorem exists_pow_mul_eq_algebraMap_pairSections {g : R} (hg : g ∈ maximalIdeal R)
    (β : Localization.pairSections (algebraMap R S x) (algebraMap R S y)) :
    ∃ (j : ℕ) (s : S), algebraMap R _ g ^ j * β = algebraMap S _ s := by
  obtain ⟨φ, hφ⟩ := exists_isLocalization_away_pairSections hreg hE hg
  let _ := φ.toRingHom.toAlgebra
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.surj (Submonoid.powers (algebraMap R S g)) (φ β)
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp t.2
  have h1 : algebraMap 𝓗 (Localization.Away (algebraMap R S g)) (β * algebraMap R 𝓗 g ^ k) =
      algebraMap 𝓗 (Localization.Away (algebraMap R S g)) (algebraMap S 𝓗 s) := by
    change φ (β * algebraMap R 𝓗 g ^ k) = φ (algebraMap S 𝓗 s)
    rw [map_mul, map_pow, IsScalarTower.algebraMap_apply R S 𝓗, φ.commutes, φ.commutes,
      ← map_pow, hk]
    exact hst
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (algebraMap R 𝓗 g)) h1
  obtain ⟨i, hi⟩ := (Submonoid.mem_powers_iff _ _).mp c.2
  refine ⟨i + k, algebraMap R S g ^ i * s, ?_⟩
  rw [map_mul, map_pow, ← IsScalarTower.algebraMap_apply, pow_add, hi, ← hc]
  ring

/-- The hull is étale over the punctured spectrum. -/
theorem isEtaleAt_pairSections
    (Q : Ideal (Localization.pairSections (algebraMap R S x) (algebraMap R S y))) [Q.IsPrime]
    (hQ : Q.comap (algebraMap R _) ≠ maximalIdeal R) : Algebra.IsEtaleAt R Q := by
  let H := 𝓗
  obtain ⟨g, hgm, hgQ⟩ : ∃ g ∈ maximalIdeal R, g ∉ Q.comap (algebraMap R H) := by
    by_contra! h
    exact hQ (le_antisymm (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
      fun g hg ↦ h g hg)
  have : Algebra.Etale R (Localization.Away (algebraMap R S g)) := hE g hgm
  obtain ⟨φ, hφ⟩ := exists_isLocalization_away_pairSections hreg hE hgm
  let _ := φ.toRingHom.toAlgebra
  have : IsScalarTower R H (Localization.Away (algebraMap R S g)) :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      change _ = φ (algebraMap R H r)
      rw [IsScalarTower.algebraMap_apply R S H, φ.commutes, ← IsScalarTower.algebraMap_apply]
  let e : Localization.Away (algebraMap R H g) ≃ₐ[R] Localization.Away (algebraMap R S g) :=
    (IsLocalization.algEquiv (Submonoid.powers (algebraMap R H g)) _ _).restrictScalars R
  have : Algebra.FormallyEtale R (Localization.Away (algebraMap R H g)) :=
    Algebra.FormallyEtale.of_equiv e.symm
  exact (Algebra.basicOpen_subset_etaleLocus_iff (R := R)).mpr this
    (show (⟨Q, ‹_›⟩ : PrimeSpectrum H) ∈ PrimeSpectrum.basicOpen (algebraMap R H g) from hgQ)

end Hull
