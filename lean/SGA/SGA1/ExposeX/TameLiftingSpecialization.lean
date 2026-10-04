/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TameLiftingProof
import SGA.SGA1.ExposeXIII.ProLShortExact

/-!
# SGA 1, Exposé X, 3.8 over a complete discrete valuation ring

For `Y = Spec R`, `R` a complete discrete valuation ring with separably closed residue field,
`y₀` the closed and `y₁` the generic point, X.3.8 (in the existence form of
`TameSpecializationStatement`) follows from its core `tameLiftingDVRStatement`. The specialization
homomorphism is `π₁(X_{b₁}) → π₁(X) ≅ π₁(X_{b₀})`. Here `π₁(X_{b₀}) → π₁(X)` is bijective, by X.2.1
for the normal `X` and X.1.4 over the trivial `π₁(Spec R)`
(`exists_tameSpecialization_of_isDiscreteValuationRing`). X.3.9 follows for these bases
(`exists_primeToQuotientEquiv_of_isDiscreteValuationRing`,
`exists_bijective_specialization_of_isDiscreteValuationRing`).

The general case of `TameSpecializationStatement` reduces to this one through a discrete
valuation ring dominating the local ring of the closure of `y₁` at `y₀` (EGA II 7.1.7, not
formalized) and its completed strict henselization; see `notes/topics/hard-parts.md` §5.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory IsLocalRing

namespace SGA.SGA1.ExposeX

/-- A field extension does not change the characteristic exponent. -/
lemma ringExpChar_eq_of_ringHom {K L : Type*} [Field K] [Field L] (φ : K →+* L) :
    ringExpChar K = ringExpChar L := by
  let : Algebra K L := φ.toAlgebra
  simp only [ringExpChar, Algebra.ringChar_eq K L]

set_option backward.isDefEq.respectTransparency false in
/-- **X.3.8 over a complete discrete valuation ring with separably closed residue field**, for
`y₀` the closed and `y₁` the generic point: let `f : X ⟶ Spec R` be proper and smooth with
geometrically connected fibres, `b₀ : Spec Ω₀ ⟶ Spec R` a geometric point over the closed point
and `b₁ : Spec Ω₁ ⟶ Spec R` one over the generic point (`Ω₀`, `Ω₁` algebraically closed), and
`a₀`, `a₁` geometric points of `X_{b₀}`, `X_{b₁}`. Then there is a continuous surjective
homomorphism `π₁(X_{b₁}, a₁) → π₁(X_{b₀}, a₀)` through which every continuous homomorphism of
`π₁(X_{b₁}, a₁)` into a finite group of order prime to the characteristic exponent of `Ω₀`
factors. This is `TameSpecializationStatement` for `Y = Spec R` and this pair of points. -/
theorem exists_tameSpecialization_of_isDiscreteValuationRing (R : Type u) [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] [IsAdicComplete (maximalIdeal R) R]
    [IsSepClosed (ResidueField R)] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f]
    [GeometricallyConnected f] (Ω₀ Ω₁ : Type u) [Field Ω₀] [IsAlgClosed Ω₀] [Field Ω₁]
    [IsAlgClosed Ω₁] (b₀ : Spec (.of Ω₀) ⟶ Spec (.of R)) (hb₀ : ∀ x, b₀.base x = closedPoint R)
    (b₁ : Spec (.of Ω₁) ⟶ Spec (.of R)) (hb₁ : Function.Injective (Spec.preimage b₁).hom)
    (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀) (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁) :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Surjective sp ∧ FactorsPrimeTo sp (ringExpChar Ω₀) := by
  have : ConnectedSpace X := ExposeIX.connectedSpace_of_universally_isQuotientMap f
    (ExposeIX.universally_isQuotientMap_of_universallyClosed f)
  -- `i₁ : π₁(X_{b₁}) → π₁(X)`: the core of X.3.8, and X.1.4
  let i₁ := ExposeV.etaleFundamentalGroup.map Ω₁ (pullback.fst f b₁) a₁
  have hi₁s : Function.Surjective i₁ :=
    surjective_map_fst_of_isSepClosed_residueField R f Ω₁ b₁ Ω₁ a₁
  have hi₁ : FactorsPrimeTo i₁ (ringExpChar (ResidueField R)) := by
    obtain ⟨φ, rfl⟩ : ∃ φ : CommRingCat.of R ⟶ CommRingCat.of Ω₁, b₁ = Spec.map φ :=
      ⟨Spec.preimage b₁, (Spec.map_preimage b₁).symm⟩
    let : Algebra R Ω₁ := φ.hom.toAlgebra
    have hinj : Function.Injective φ.hom := by
      simpa [Spec.preimage_map] using hb₁
    exact tameLiftingDVRStatement R f Ω₁ hinj Ω₁ a₁
  -- `i₀ : π₁(X_{b₀}) → π₁(X)` is bijective: X.2.1 for the normal `X`, and X.1.4
  let i₀ := ExposeV.etaleFundamentalGroup.map Ω₀ (pullback.fst f b₀) a₀
  have hX : IsNormalScheme X := isNormalScheme_of_isRegularScheme (isRegularScheme_of_smooth R f)
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsIntegral X := isIntegral_of_isNormalScheme hX
  have hi₀i : Function.Injective i₀ :=
    ExposeXIII.injective_map_fst_of_liftsFiniteEtale R f
      (liftsFiniteEtale_fiberι_closedPoint_of_isNormalScheme R f hX) Ω₀ b₀ hb₀ Ω₀ a₀
  have hi₀s : Function.Surjective i₀ :=
    surjective_map_fst_of_isSepClosed_residueField R f Ω₀ b₀ Ω₀ a₀
  let e₀ : ExposeV.etaleFundamentalGroup Ω₀ a₀ ≃ₜ
      ExposeV.etaleFundamentalGroup Ω₀ (a₀ ≫ pullback.fst f b₀) :=
    (ExposeV.etaleFundamentalGroup.continuous_map _ _ _).homeoOfEquivCompactToT2
      (f := Equiv.ofBijective i₀ ⟨hi₀i, hi₀s⟩)
  let E₀ : ExposeV.etaleFundamentalGroup Ω₀ a₀ ≃* ExposeV.etaleFundamentalGroup Ω₀
      (a₀ ≫ pullback.fst f b₀) := MulEquiv.ofBijective i₀ ⟨hi₀i, hi₀s⟩
  -- a path from `a₁` to `a₀` in `X`
  obtain ⟨φ⟩ := ExposeV.nonempty_iso_of_fiberFunctor
    (ExposeV.FEt.fiber Ω₁ (a₁ ≫ pullback.fst f b₁)) (ExposeV.FEt.fiber Ω₀ (a₀ ≫ pullback.fst f b₀))
  let c := φ.conjAut
  have hc : Continuous c := ExposeV.continuous_conjAut φ
  have hcinv : Continuous c.symm := ExposeV.continuous_conjAut φ.symm
  let sp := E₀.symm.toMonoidHom.comp (c.toMonoidHom.comp i₁)
  have hE₀ : Continuous E₀.symm := e₀.symm.continuous
  refine ⟨sp, hE₀.comp (hc.comp (ExposeV.etaleFundamentalGroup.continuous_map _ _ _)),
    E₀.symm.surjective.comp (c.surjective.comp hi₁s), ?_⟩
  -- every continuous map to a finite group of order prime to `p` factors through `sp`
  intro Q _ _ _ _ hQ ψ hψ
  have hp : ringExpChar Ω₀ = ringExpChar (ResidueField R) := by
    let ψ := (Spec.preimage b₀).hom
    have h₀ := hb₀ (closedPoint Ω₀)
    rw [← Spec.map_preimage b₀] at h₀
    have hker : ∀ a ∈ maximalIdeal R, ψ a = 0 := by
      intro a ha
      have h₁ := congrArg PrimeSpectrum.asIdeal h₀
      change Ideal.comap ψ (closedPoint Ω₀).asIdeal = maximalIdeal R at h₁
      rw [← h₁] at ha
      have h₂ : (closedPoint Ω₀).asIdeal = ⊥ :=
        @Ideal.eq_bot_of_prime _ _ _ (closedPoint Ω₀).isPrime
      rw [h₂, Ideal.mem_comap, Ideal.mem_bot] at ha
      exact ha
    exact (ringExpChar_eq_of_ringHom (Ideal.Quotient.lift (maximalIdeal R) ψ hker)).symm
  rw [hp] at hQ
  obtain ⟨g, hg, hgi⟩ := hi₁ Q hQ ψ hψ
  refine ⟨(g.comp c.symm.toMonoidHom).comp E₀.toMonoidHom,
    (hg.comp hcinv).comp (ExposeV.etaleFundamentalGroup.continuous_map _ _ _), ?_⟩
  ext σ
  simp only [sp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
    MulEquiv.symm_apply_apply]
  exact DFunLike.congr_fun hgi σ

section X39

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f] (Ω₀ Ω₁ : Type u)
  [Field Ω₀] [IsAlgClosed Ω₀] [Field Ω₁] [IsAlgClosed Ω₁] (b₀ : Spec (.of Ω₀) ⟶ Spec (.of R))
  (hb₀ : ∀ x, b₀.base x = closedPoint R) (b₁ : Spec (.of Ω₁) ⟶ Spec (.of R))
  (hb₁ : Function.Injective (Spec.preimage b₁).hom) (a₀ : Spec (.of Ω₀) ⟶ pullback f b₀)
  (a₁ : Spec (.of Ω₁) ⟶ pullback f b₁)
include hb₀ hb₁

/-- X.3.9 over a complete discrete valuation ring with separably closed residue field (`y₀` the
closed and `y₁` the generic point): the specialization homomorphism
`sp : π₁(X_{b₁}) → π₁(X_{b₀})` of `exists_tameSpecialization_of_isDiscreteValuationRing` has
kernel contained in the intersection of the kernels of the continuous homomorphisms to finite
groups of order prime to `p`, and induces an isomorphism `π₁(X_{b₁})^(p) ≅ π₁(X_{b₀})^(p)`. -/
theorem exists_primeToQuotientEquiv_of_isDiscreteValuationRing :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Surjective sp ∧
        sp.ker ≤ primeToKernel (ringExpChar Ω₀) (ExposeV.etaleFundamentalGroup Ω₁ a₁) ∧
        ∃ e : ExposeV.etaleFundamentalGroup Ω₁ a₁ ⧸
            primeToKernel (ringExpChar Ω₀) (ExposeV.etaleFundamentalGroup Ω₁ a₁) ≃*
          ExposeV.etaleFundamentalGroup Ω₀ a₀ ⧸
            primeToKernel (ringExpChar Ω₀) (ExposeV.etaleFundamentalGroup Ω₀ a₀),
          ∀ x, e (QuotientGroup.mk x) = QuotientGroup.mk (sp x) := by
  obtain ⟨sp, hc, hs, hfac⟩ :=
    exists_tameSpecialization_of_isDiscreteValuationRing R f Ω₀ Ω₁ b₀ hb₀ b₁ hb₁ a₀ a₁
  exact ⟨sp, hc, hs, ker_le_primeToKernel hc hs hfac, primeToQuotientEquiv hc hs hfac,
    primeToQuotientEquiv_mk hc hs hfac⟩

/-- X.3.9 over a complete discrete valuation ring with separably closed residue field of
characteristic `0` (`y₀` the closed and `y₁` the generic point): the specialization
homomorphism `π₁(X_{b₁}) → π₁(X_{b₀})` is an isomorphism. -/
theorem exists_bijective_specialization_of_isDiscreteValuationRing [CharZero Ω₀] :
    ∃ sp : ExposeV.etaleFundamentalGroup Ω₁ a₁ →* ExposeV.etaleFundamentalGroup Ω₀ a₀,
      Continuous sp ∧ Function.Bijective sp := by
  obtain ⟨sp, hc, hs, hfac⟩ :=
    exists_tameSpecialization_of_isDiscreteValuationRing R f Ω₀ Ω₁ b₀ hb₀ b₁ hb₁ a₀ a₁
  rw [ringExpChar.eq_one Ω₀] at hfac
  exact ⟨sp, hc, bijective_of_forall_factor hc hs hfac⟩

end X39

end SGA.SGA1.ExposeX
