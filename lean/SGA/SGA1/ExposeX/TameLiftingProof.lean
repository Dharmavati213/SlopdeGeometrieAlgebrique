/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeX.TameLiftingExtension
import SGA.SGA1.ExposeX.TameLiftingFiniteLevel
import SGA.SGA1.ExposeX.TameLiftingNormalization
import SGA.SGA1.ExposeX.TameLiftingReduction

/-!
# SGA 1, Exposé X, 3.8: the core over a complete discrete valuation ring

We prove `TameLiftingDVRStatement`, the case of X.3.8 to which SGA reduces the theorem in X.3.7:
for `R` a complete discrete valuation ring with separably closed residue field of characteristic
exponent `p` and `f : X ⟶ Spec R` proper and smooth with geometrically connected fibres, every
continuous homomorphism of `π₁(X_η̄)` into a finite group of order prime to `p` factors through
`π₁(X_η̄) → π₁(X)`.

As in SGA, it suffices (`factorsPrimeTo_of_forall_isGalois`) that every Galois covering `Z` of
`X_η̄` of degree `n` prime to `p` be the inverse image of an étale covering of `X`:

* `Z` comes from a Galois covering `Y₀` of `X_{K₀}`, `K₀` a finite separable extension of the
  fraction field `K` of `R` (`exists_isGalois_finiteDimensional_of_isGalois`);
* the normalization `V₀` of `R` in `K₀` is a complete discrete valuation ring with purely
  inseparable residue extension (`TameLiftingNormalization`), and `X_{K₀}` is the generic fibre
  `U₀ = X_{V₀}[1/π₀]` of `X_{V₀}` (`isLocalization_away_of_irreducible`);
* after the Kummer base change `V₀[T]/(Tⁿ - π₀)`, `Y₀` extends to an étale covering of `X_{V₀}`
  (`exists_iso_pullback_of_isGalois_of_isAdicComplete`: Abhyankar's lemma X.3.6 and purity
  X.3.1), which comes from `X` (`isEquivalence_pullback_baseChange_of_smooth`); embedding
  `V₀[T]/(Tⁿ - π₀)` in `Ω` over `V₀` identifies the inverse images on `X_η̄`
  (`exists_iso_pullback_of_isGalois_of_finiteDimensional`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory IsLocalRing Polynomial

namespace SGA.SGA1.ExposeX

/-- The fraction field of a discrete valuation ring is its localization away from a uniformizer. -/
theorem isLocalization_away_of_irreducible {V : Type*} (K : Type*) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] {π : V}
    (hπ : Irreducible π) : IsLocalization.Away π K where
  map_units := by
    rintro ⟨_, k, rfl⟩
    exact (map_ne_zero_iff _ (IsFractionRing.injective V K)).mpr
      (pow_ne_zero k hπ.ne_zero) |>.isUnit
  surj z := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := V) z
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (nonZeroDivisors.ne_zero hb) hπ
    refine ⟨⟨a * ↑u⁻¹, ⟨π ^ k, k, rfl⟩⟩, ?_⟩
    have hu : algebraMap V K u ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V K)).mpr u.ne_zero
    have hπk : algebraMap V K (π ^ k) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V K)).mpr (pow_ne_zero k hπ.ne_zero)
    have hu' : algebraMap V K ↑u⁻¹ * algebraMap V K u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    simp only [map_mul]
    field_simp
    linear_combination -(algebraMap V K a) * hu'
  exists_of_eq h := ⟨1, by rw [IsFractionRing.injective V K h]⟩

/-- An integer prime to the characteristic exponent of a field is nonzero in it. -/
theorem natCast_ne_zero_of_coprime_ringExpChar {k : Type*} [Field k] {n : ℕ} (hn : n ≠ 0)
    (h : n.Coprime (ringExpChar k)) : (n : k) ≠ 0 := by
  obtain ⟨p, hp⟩ : ∃ p, ExpChar k p := ⟨_, ringExpChar.of_eq rfl⟩
  rw [ringExpChar.eq k p] at h
  cases hp with
  | zero => exact Nat.cast_ne_zero.mpr hn
  | prime hprime =>
    intro h0
    rw [CharP.cast_eq_zero_iff k p] at h0
    exact hprime.one_lt.ne' (Nat.Coprime.eq_one_of_dvd h.symm h0)

section Extension

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [IsAdicComplete (maximalIdeal R) R] [IsSepClosed (ResidueField R)]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
  (K₀ : Type u) [Field K₀] [Algebra K K₀] [Algebra R K₀] [IsScalarTower R K K₀]
  [FiniteDimensional K K₀] [Algebra.IsSeparable K K₀]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [IsProper f] [Smooth f] [GeometricallyConnected f]
  (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra K₀ Ω] [Algebra R Ω] [IsScalarTower R K₀ Ω]

set_option backward.isDefEq.respectTransparency false in
include K in
/-- A step of the proof of X.3.8 (the core statement is `TameLiftingDVRStatement`): let `R` be a
complete discrete valuation ring with separably closed residue field, `K` its fraction field,
`K₀` a finite separable extension of `K`, `f : X ⟶ Spec R` proper and smooth with geometrically
connected fibres, and `Y₀` a Galois étale covering of `X_{K₀}` whose number `n` of automorphisms is
prime to the residue characteristic. Then for every algebraically closed field `Ω` over `K₀`, the
inverse image of `Y₀` on `X_Ω` is the inverse image of an étale covering of `X`. -/
theorem exists_iso_pullback_of_isGalois_of_finiteDimensional
    (Y₀ : FEt (pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀))))) [IsGalois Y₀]
    (hn : ((Nat.card (Aut Y₀) : ℕ) : R) ∉ maximalIdeal R) :
    ∃ E : FEt X, Nonempty
      ((FEt.pullback (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R Ω))))).obj E ≅
        (FEt.pullback (pullbackMapOfIsScalarTower R f K₀ Ω)).obj Y₀) := by
  classical
  let n := Nat.card (Aut Y₀)
  have : Finite (Aut Y₀) := by
    obtain ⟨x⟩ : Nonempty ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R K₀)))) :=
      inferInstance
    let F := ExposeV.FEt.fiber _ (ExposeV.geometricPointAt _ x)
    obtain ⟨y⟩ := nonempty_fiber_of_isConnected F Y₀
    exact Finite.of_equiv _ (evaluationEquivOfIsGalois F Y₀ y).symm
  have hn0 : n ≠ 0 := Nat.card_pos.ne'
  have : NeZero n := ⟨hn0⟩
  -- the normalization `V₀` of `R` in `K₀`
  let V₀ := integralClosure R K₀
  have : IsDiscreteValuationRing V₀ := isDiscreteValuationRing_integralClosure R K K₀
  have : IsLocalHom (algebraMap R V₀) := isLocalHom_integralClosure R K K₀
  have : IsAdicComplete (maximalIdeal V₀) V₀ := isAdicComplete_integralClosure R K K₀
  have : Module.Finite (ResidueField R) (ResidueField V₀) :=
    finite_residueField_integralClosure R K K₀
  have : IsPurelyInseparable (ResidueField R) (ResidueField V₀) :=
    isPurelyInseparable_residueField_integralClosure R K K₀
  have : IsFractionRing V₀ K₀ :=
    integralClosure.isFractionRing_of_finite_extension (A := R) (K := K) K₀
  obtain ⟨π₀, hπ₀⟩ := IsDiscreteValuationRing.exists_irreducible V₀
  have : Fact (Irreducible π₀) := ⟨hπ₀⟩
  have hnV : (n : V₀) ∉ maximalIdeal V₀ := by
    have hu : IsUnit ((n : ℕ) : R) := (IsLocalRing.notMem_maximalIdeal).mp hn
    have := hu.map (algebraMap R V₀)
    rw [map_natCast] at this
    exact (IsLocalRing.notMem_maximalIdeal).mpr this
  -- `X_{V₀}` and its generic fibre `U₀ = X_{V₀}[1/π₀]`
  let gV : Spec (.of V₀) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R V₀))
  let f₀ : pullback f gV ⟶ Spec (.of V₀) := pullback.snd f gV
  have : Smooth f₀ := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsProper f₀ := MorphismProperty.pullback_snd _ _ inferInstance
  have : GeometricallyConnected f₀ := MorphismProperty.pullback_snd _ _ inferInstance
  let U₀ : (pullback f gV).Opens :=
    (pullback f gV).basicOpen (f₀.appTop ((Scheme.ΓSpecIso (.of V₀)).inv π₀))
  -- `Spec K₀ ⟶ Spec V₀` is the open immersion of `D(π₀)`
  have : IsLocalization.Away π₀ K₀ := isLocalization_away_of_irreducible K₀ hπ₀
  let jV : Spec (.of K₀) ⟶ Spec (.of V₀) := Spec.map (CommRingCat.ofHom (algebraMap V₀ K₀))
  have : IsOpenImmersion jV := IsOpenImmersion.of_isLocalization π₀
  have hjV : jV.opensRange = (Spec (.of V₀)).basicOpen ((Scheme.ΓSpecIso (.of V₀)).inv π₀) := by
    rw [basicOpen_eq_of_affine]
    ext1
    exact PrimeSpectrum.localization_away_comap_range K₀ π₀
  have hU₀ : f₀ ⁻¹ᵁ jV.opensRange = U₀ := by
    rw [hjV, Scheme.preimage_basicOpen_top]
  have hrange : Set.range (U₀.ι ≫ f₀) ⊆ Set.range jV := by
    rintro _ ⟨x, rfl⟩
    have : f₀ (U₀.ι x) ∈ jV.opensRange := by
      rw [← Scheme.Hom.mem_preimage, hU₀]
      exact x.2
    exact this
  let g₀ : (U₀ : Scheme) ⟶ Spec (.of K₀) := IsOpenImmersion.lift jV (U₀.ι ≫ f₀) hrange
  have hg₀ : g₀ ≫ jV = U₀.ι ≫ f₀ := IsOpenImmersion.lift_fac _ _ _
  have hsqL : IsPullback g₀ U₀.ι jV f₀ :=
    IsOpenImmersion.isPullback g₀ U₀.ι jV f₀ hg₀.symm (by rw [hU₀, Scheme.Opens.opensRange_ι])
  let tK₀ : Spec (.of K₀) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R K₀))
  have hjg : jV ≫ gV = tK₀ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hU : IsPullback (U₀.ι ≫ pullback.fst f gV) g₀ f tK₀ := by
    rw [← hjg]
    exact hsqL.flip.paste_horiz (IsPullback.of_hasPullback f gV)
  let eU : (U₀ : Scheme) ≅ pullback f tK₀ := hU.isoPullback
  have : ConnectedSpace U₀ :=
    Function.Surjective.connectedSpace (f := Scheme.homeoOfIso eU.symm)
      (Scheme.homeoOfIso eU.symm).surjective (Scheme.homeoOfIso eU.symm).continuous
  -- the covering `Z₀` of `U₀` corresponding to `Y₀`
  let Z₀ : FEt (U₀ : Scheme) := (FEt.pullback eU.hom).obj Y₀
  let iZ₀ : (FEt.pullback eU.inv).obj Z₀ ≅ Y₀ :=
    ((MorphismProperty.Over.pullbackComp eU.inv eU.hom).app Y₀).symm ≪≫
      (MorphismProperty.Over.pullbackCongr eU.inv_hom_id).app Y₀ ≪≫
      (ExposeV.FEt.pullbackId _).app Y₀
  obtain ⟨x₀⟩ : Nonempty U₀ := inferInstance
  let a₀ := ExposeV.geometricPointAt (U₀ : Scheme) x₀
  let F₀ := ExposeV.FEt.fiber _ a₀
  have : IsGalois ((FEt.pullback eU.inv).obj Z₀) :=
    isGalois_of_iso (ExposeV.FEt.fiber _ (a₀ ≫ eU.hom)) iZ₀.symm
  have eF := ExposeV.FEt.pullbackFiberIso _ eU.inv (a₀ ≫ eU.hom)
  have : IsGalois Z₀ := isGalois_of_liftsEndos (FEt.pullback eU.inv) eF Z₀ (LiftsEndos.of_full _ _)
  have hcard : Nat.card (Aut Z₀) = n := by
    rw [natCard_aut_eq_of_isGalois (FEt.pullback eU.inv) eF Z₀]
    exact Nat.card_congr iZ₀.conjAut.toEquiv
  -- the extension after the Kummer base change (X.3.6, X.3.1)
  obtain ⟨E₀, ⟨eE₀⟩⟩ := exists_iso_pullback_of_isGalois_of_isAdicComplete (π := π₀) hnV f₀ U₀ rfl
    Z₀ hcard
  -- it comes from `X`
  have : (FEt.pullback (pullback.fst f gV)).IsEquivalence :=
    isEquivalence_pullback_baseChange_of_smooth R V₀ f
  let E := (FEt.pullback (pullback.fst f gV)).objPreimage E₀
  let iE : (FEt.pullback (pullback.fst f gV)).obj E ≅ E₀ :=
    (FEt.pullback (pullback.fst f gV)).objObjPreimageIso E₀
  -- an embedding `V₀[T]/(Tⁿ - π₀) → Ω` over `V₀ → K₀ → Ω`
  let φV : V₀ →+* Ω := (algebraMap K₀ Ω).comp (algebraMap V₀ K₀)
  have hφVinj : Function.Injective φV :=
    (algebraMap K₀ Ω).injective.comp (IsFractionRing.injective V₀ K₀)
  have hφV : φV.comp (algebraMap R V₀) = algebraMap R Ω := by
    ext r
    change algebraMap K₀ Ω (algebraMap V₀ K₀ (algebraMap R V₀ r)) = _
    rw [← IsScalarTower.algebraMap_apply R V₀ K₀, ← IsScalarTower.algebraMap_apply R K₀ Ω]
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (φV π₀) (Nat.pos_of_ne_zero hn0)
  have hroot : ((Polynomial.X : V₀[X]) ^ n - Polynomial.C π₀).eval₂ φV r = 0 := by simp [hr]
  let ρn : AdjoinRoot ((Polynomial.X : V₀[X]) ^ n - Polynomial.C π₀) →+* Ω :=
    AdjoinRoot.lift φV r hroot
  have hρn : ρn.comp (algebraMap V₀ (AdjoinRoot ((Polynomial.X : V₀[X]) ^ n - Polynomial.C π₀))) =
      φV := by
    ext v
    exact AdjoinRoot.lift_of hroot
  let gn := Spec.map (CommRingCat.ofHom
    (algebraMap V₀ (AdjoinRoot ((Polynomial.X : V₀[X]) ^ n - Polynomial.C π₀))))
  let s := Spec.map (CommRingCat.ofHom (algebraMap R Ω))
  have hsV : s = Spec.map (CommRingCat.ofHom φV) ≫ gV := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hφV]
  let δ : pullback f s ⟶ pullback f gV :=
    pullback.lift (pullback.fst f s) (pullback.snd f s ≫ Spec.map (CommRingCat.ofHom φV))
      ((pullback.condition).trans ((congrArg (pullback.snd f s ≫ ·) hsV).trans
        (Category.assoc _ _ _).symm))
  have hδ₁ : δ ≫ pullback.fst f gV = pullback.fst f s := pullback.lift_fst _ _ _
  have hδ₂ : δ ≫ f₀ = pullback.snd f s ≫ Spec.map (CommRingCat.ofHom φV) :=
    pullback.lift_snd _ _ _
  have hρgn : Spec.map (CommRingCat.ofHom ρn) ≫ gn = Spec.map (CommRingCat.ofHom φV) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρn]
  let γ' : pullback f s ⟶ pullback gn f₀ :=
    pullback.lift (pullback.snd f s ≫ Spec.map (CommRingCat.ofHom ρn)) δ
      (by rw [Category.assoc, hρgn, hδ₂])
  have hγ'₂ : γ' ≫ pullback.snd gn f₀ = δ := pullback.lift_snd _ _ _
  -- `γ'` lands in the generic fibre
  have hD (p : Spec (.of Ω)) : (Spec.map (CommRingCat.ofHom φV)) p ∈
      ((Spec (.of V₀)).basicOpen ((Scheme.ΓSpecIso (.of V₀)).inv π₀) : (Spec (.of V₀)).Opens) := by
    rw [basicOpen_eq_of_affine, PrimeSpectrum.mem_basicOpen]
    change π₀ ∉ (PrimeSpectrum.comap φV p).asIdeal
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.eq_bot_of_prime p.asIdeal,
      Ideal.mem_bot]
    exact (map_ne_zero_iff φV hφVinj).mpr hπ₀.ne_zero
  have hγ' : Set.range γ' ⊆ Set.range (pullback.snd gn f₀ ⁻¹ᵁ U₀).ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change pullback.snd gn f₀ (γ' x) ∈ U₀
    rw [← Scheme.Hom.comp_apply, hγ'₂]
    rw [show U₀ = f₀ ⁻¹ᵁ _ from (Scheme.preimage_basicOpen_top _ _).symm]
    change f₀ (δ x) ∈
      ((Spec (.of V₀)).basicOpen ((Scheme.ΓSpecIso (.of V₀)).inv π₀) : (Spec (.of V₀)).Opens)
    rw [← Scheme.Hom.comp_apply, hδ₂, Scheme.Hom.comp_apply]
    exact hD _
  let γ := IsOpenImmersion.lift (pullback.snd gn f₀ ⁻¹ᵁ U₀).ι γ' hγ'
  have hγ : γ ≫ (pullback.snd gn f₀ ⁻¹ᵁ U₀).ι = γ' := IsOpenImmersion.lift_fac _ _ _
  have hγα : γ ≫ (pullback.snd gn f₀ ∣_ U₀) ≫ eU.hom = pullbackMapOfIsScalarTower R f K₀ Ω := by
    apply pullback.hom_ext
    · rw [pullbackMapOfIsScalarTower_fst, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_fst, ← Category.assoc (pullback.snd gn f₀ ∣_ U₀),
        morphismRestrict_ι, Category.assoc, reassoc_of% hγ, reassoc_of% hγ'₂, hδ₁]
    · rw [pullbackMapOfIsScalarTower_snd, Category.assoc, Category.assoc,
        IsPullback.isoPullback_hom_snd, ← cancel_mono jV]
      simp only [Category.assoc]
      rw [hg₀, ← Category.assoc (pullback.snd gn f₀ ∣_ U₀), morphismRestrict_ι, Category.assoc,
        reassoc_of% hγ, reassoc_of% hγ'₂, hδ₂, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have hfst : pullback.fst f s =
      γ ≫ ((pullback.snd gn f₀ ⁻¹ᵁ U₀).ι ≫ pullback.snd gn f₀) ≫ pullback.fst f gV := by
    simp only [Category.assoc]
    rw [reassoc_of% hγ, reassoc_of% hγ'₂, hδ₁]
  refine ⟨E, ⟨?_⟩⟩
  exact (MorphismProperty.Over.pullbackCongr hfst).app E ≪≫
    (MorphismProperty.Over.pullbackComp γ _).app E ≪≫
    (FEt.pullback γ).mapIso ((MorphismProperty.Over.pullbackComp _ (pullback.fst f gV)).app E ≪≫
      (FEt.pullback _).mapIso iE ≪≫ eE₀ ≪≫
      ((MorphismProperty.Over.pullbackComp (pullback.snd gn f₀ ∣_ U₀) eU.hom).app Y₀).symm) ≪≫
    ((MorphismProperty.Over.pullbackComp γ ((pullback.snd gn f₀ ∣_ U₀) ≫ eU.hom)).app Y₀).symm ≪≫
    (MorphismProperty.Over.pullbackCongr hγα).app Y₀

end Extension

set_option backward.isDefEq.respectTransparency false in
/-- **X.3.8, the core** (the case to which SGA reduces X.3.8 in X.3.7): let `R` be a complete
discrete valuation ring with separably closed residue field of characteristic exponent `p`,
`f : X ⟶ Spec R` proper and smooth with geometrically connected fibres, and `η̄ : Spec Ω₁ ⟶ Spec R`
a geometric generic point. Then every continuous homomorphism of `π₁(X_η̄)` into a finite group of
order prime to `p` factors through `π₁(X_η̄) → π₁(X)`. -/
theorem tameLiftingDVRStatement : TameLiftingDVRStatement.{u} := by
  intro R _ _ _ _ _ X f _ _ _ Ω₁ _ _ _ hinj Ω _ _ a
  let K := FractionRing R
  let φK : K →+* Ω₁ := IsFractionRing.lift hinj
  let : Algebra K Ω₁ := φK.toAlgebra
  have : IsScalarTower R K Ω₁ := IsScalarTower.of_algebraMap_eq fun r ↦
    (IsFractionRing.lift_algebraMap hinj r).symm
  refine factorsPrimeTo_of_forall_isGalois R f Ω₁ _ Ω a _ fun Z _ hcop ↦ ?_
  obtain ⟨K₀, _, _, _, _, _, _, _, _, Y₀, _, hcard, ⟨iY⟩⟩ :=
    exists_isGalois_finiteDimensional_of_isGalois R f K Ω₁ Z
  have hn : ((Nat.card (Aut Y₀) : ℕ) : R) ∉ maximalIdeal R := by
    obtain ⟨z⟩ := nonempty_fiber_of_isConnected (ExposeV.FEt.fiber Ω a) Z
    have hZ : Nat.card (Aut Z) = Nat.card ((ExposeV.FEt.fiber Ω a).obj Z) :=
      Nat.card_congr (evaluationEquivOfIsGalois (ExposeV.FEt.fiber Ω a) Z z)
    have hne : Nat.card ((ExposeV.FEt.fiber Ω a).obj Z) ≠ 0 :=
      Nat.card_pos (α := (ExposeV.FEt.fiber Ω a).obj Z).ne'
    rw [hcard, hZ, ← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact natCast_ne_zero_of_coprime_ringExpChar hne hcop
  obtain ⟨E, ⟨iE⟩⟩ := exists_iso_pullback_of_isGalois_of_finiteDimensional R K K₀ f Ω₁ Y₀ hn
  exact ⟨E, ⟨iE ≪≫ iY⟩⟩

end SGA.SGA1.ExposeX
