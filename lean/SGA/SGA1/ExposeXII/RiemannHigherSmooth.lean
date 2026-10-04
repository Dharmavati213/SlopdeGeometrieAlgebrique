/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeXII.RiemannHigher
import SGA.SGA1.ExposeXII.RiemannReductionFiniteEtale
import SGA.SGA1.ExposeXII.RiemannReductionUniverse
import SGA.SGA1.ExposeXII.BranchedCover
import Mathlib.RingTheory.NoetherNormalization

/-!
# SGA 1, Exposé XII, 5.1 for smooth affine domains, from hypersurface complements

Step 3 of the route of `SGA.SGA1.ExposeXII.RiemannHigher` (this project's route, not SGA's): a
domain `A` of finite type over `ℂ` has, by Noether normalization (mathlib's
`exists_finite_inj_algHom_of_fg`) and generic finite étaleness in characteristic `0`
(`exists_isStandardEtale_localizationAway`), a nonzero `g` such that `A_g` is finite étale over a
hypersurface complement `ℂ[x₁, …, x_s][1/r]` (`exists_finiteEtale_hypersurfaceComplement`).
Hence (`isEquivalence_pointsFunctor_of_smooth_of_isDomain`): if XII.5.1 holds for hypersurface
complements (`HypersurfaceComplementRiemannExistenceStatement`), it holds for `A_g`
(`isEquivalence_pointsFunctor_of_finiteEtale`), and if moreover coverings extend across divisors
of smooth schemes (`DivisorExtensionStatement`), it holds for every smooth domain `A`.

Both hypotheses are open; they are the subject of the other `RiemannHigher*` files.
-/

noncomputable section

open CategoryTheory Topology

namespace SGA.SGA1.ExposeXII

open RiemannHigher CommAlgCat

/-- XII.5.1 for a smooth `A` from XII.5.1 for a dense basic open `D(g)`, given the extension
across divisors (`DivisorExtensionStatement`). -/
theorem isEquivalence_pointsFunctor_of_isEquivalence_away (hD : DivisorExtensionStatement)
    (A : Type) [CommRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] [Algebra.Smooth ℂ A]
    (g : A) (hg : g ∈ nonZeroDivisors A)
    [(pointsFunctor ℂ (Localization.Away g)).IsEquivalence] :
    (pointsFunctor ℂ A).IsEquivalence where
  essSurj := ⟨fun E ↦ hD A g hg E (Functor.EssSurj.mem_essImage _ _)⟩

/-- Generic finite étaleness over a Noether normalization: a domain `A` of finite type over `ℂ`
has a nonzero `g` such that `A_g` is isomorphic, as a `ℂ`-algebra, to a finite étale algebra over a
hypersurface complement `ℂ[x₁, …, x_s][1/r]`, `r ≠ 0`. -/
theorem exists_finiteEtale_hypersurfaceComplement (A : Type) [CommRing A] [IsDomain A]
    [Algebra ℂ A] [Algebra.FiniteType ℂ A] :
    ∃ (s : ℕ) (r : MvPolynomial (Fin s) ℂ) (_ : r ≠ 0) (T : FiniteEtale.{0} (Localization.Away r))
      (g : A) (_ : g ≠ 0),
      Nonempty (letI := algebraOfFiniteEtale ℂ (Localization.Away r) T
        T ≃ₐ[ℂ] Localization.Away g) := by
  obtain ⟨s, φ, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ A
  let R := MvPolynomial (Fin s) ℂ
  let : Algebra R A := φ.toRingHom.toAlgebra
  have : IsScalarTower ℂ R A := .of_algebraMap_eq fun c ↦ (φ.commutes c).symm
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hinj
  have : Module.Finite R A := hfin
  have : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (algebraMap ℂ (FractionRing R)).injective
  obtain ⟨H, hH, hst⟩ := exists_isStandardEtale_localizationAway R A
  let g : A := algebraMap R A H
  let Rr := Localization.Away H
  let Sr := Localization.Away g
  have hu : IsUnit (algebraMap R Sr H) := by
    rw [IsScalarTower.algebraMap_apply R A Sr]
    exact IsLocalization.Away.algebraMap_isUnit _
  let : Algebra Rr Sr := (IsLocalization.Away.lift H hu).toAlgebra
  have : IsScalarTower R Rr Sr := .of_algebraMap_eq fun x ↦
    (IsLocalization.Away.lift_eq H hu x).symm
  have : Algebra.Etale R Rr := .of_isLocalizationAway H
  have : Algebra.Etale R Sr := inferInstance
  have : Algebra.Etale Rr Sr := .of_restrictScalars R Rr Sr
  have : IsLocalization (Algebra.algebraMapSubmonoid A (Submonoid.powers H)) Sr := by
    rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
    infer_instance
  have : Module.Finite Rr Sr := .of_isLocalization R A (Submonoid.powers H)
  let T : FiniteEtale.{0} Rr := FiniteEtale.of Rr Sr
  have hg : g ≠ 0 := by
    rw [ne_eq, ← map_zero (algebraMap R A)]
    exact (FaithfulSMul.algebraMap_injective R A).ne hH
  have hc (c : ℂ) : algebraMap Rr Sr (algebraMap ℂ Rr c) = algebraMap ℂ Sr c := by
    rw [IsScalarTower.algebraMap_apply ℂ R Rr, ← IsScalarTower.algebraMap_apply R Rr Sr,
      IsScalarTower.algebraMap_apply R A Sr, ← IsScalarTower.algebraMap_apply ℂ R A,
      ← IsScalarTower.algebraMap_apply ℂ A Sr]
  exact ⟨s, H, hH, T, g, hg, ⟨@AlgEquiv.ofRingEquiv ℂ Sr Sr _ _ _
    (algebraOfFiniteEtale ℂ Rr T) _ (RingEquiv.refl Sr) hc⟩⟩

/-- XII.5.1 for smooth affine domains, from the hypersurface complements and the extension across
divisors: by Noether normalization and generic étaleness, `A_g` is finite étale over some
`ℂ[x₁, …, x_s][1/r]` (`exists_finiteEtale_hypersurfaceComplement`), so `Ψ` is an equivalence for
`A_g` (`isEquivalence_pointsFunctor_of_finiteEtale`), hence for `A` by
`DivisorExtensionStatement`. -/
theorem isEquivalence_pointsFunctor_of_smooth_of_isDomain
    (hH : ∀ d, HypersurfaceComplementRiemannExistenceStatement d) (hD : DivisorExtensionStatement)
    (A : Type) [CommRing A] [IsDomain A] [Algebra ℂ A] [Algebra.FiniteType ℂ A]
    [Algebra.Smooth ℂ A] : (pointsFunctor ℂ A).IsEquivalence := by
  obtain ⟨s, r, hr, T, g, hg, ⟨e⟩⟩ := exists_finiteEtale_hypersurfaceComplement A
  have := hH s r hr
  have hT := isEquivalence_pointsFunctor_of_finiteEtale T
  let := algebraOfFiniteEtale ℂ (Localization.Away r) T
  have : (pointsFunctor ℂ (Localization.Away g)).IsEquivalence :=
    (isEquivalence_pointsFunctor_iff_of_algEquiv e).mp hT
  exact isEquivalence_pointsFunctor_of_isEquivalence_away hD A g (mem_nonZeroDivisors_of_ne_zero hg)

end SGA.SGA1.ExposeXII
