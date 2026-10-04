/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.EtaleStalkStructureSheaf
import SGA.SGA1.ExposeXIII.MultiplicativeGroupInertia

/-!
# SGA 1, XIII.2.12 for `g = 0`, `n = 2`: inertia at the origin of an affine chart

Let `k` be algebraically closed of characteristic `p`, `X` a scheme, `V ⊆ X` an affine open with
`φ : Γ(V) ≅ k[t]`, `o ∈ V` the point `t = 0` (`AffineLineChart.origin`) and `U = D(t) ⊆ V`, so
that `Γ(U) ≅ k[T, T⁻¹]`, `T ↦ t` (`AffineLineChart.basicOpenEquiv`). Every inertia subgroup `H` of
`π₁(U)` at a geometric point over `o` (`IsInertiaSubgroupAt`) maps onto `π₁^{p'}(U)`
(`AffineLineChart.topologicalClosure_sup_proLKernel_eq_top`). This is the inertia condition of
XIII.2.12 for `ℙ¹ - {0, ∞}`, at `0` (chart `D₊(x₀)`) and at `∞` (chart `D₊(x₁)`), and for
`𝔾_m = D(t) ⊆ 𝔸¹` at `0`.

* The local ring `𝒪_{X,o}` is `k[t]_{(t)}` (`IsAffineOpen.isLocalization_stalk`), so the strict
  localization `𝒪^{sh}` at a geometric point over `o` is a discrete valuation ring with uniformizer
  `π` the image of `t` (`isDiscreteValuationRing_strictLocalization`,
  `irreducible_uniformizer`).
* `U ×_X Spec 𝒪^{sh} ≅ Spec 𝒪^{sh}[1/π]` (`pullbackIso`), and `𝒪^{sh}[1/π]` is the field of
  fractions of `𝒪^{sh}`; the map to `U ≅ Spec k[T, T⁻¹]` is `T ↦ π`
  (`pullbackIso_inv_fst_basicOpenIso_hom`).
* The pullback of the Kummer covering `z^m = T` of `U` to `U ×_X Spec 𝒪^{sh}` is
  `Spec Frac(𝒪^{sh})[z]/(z^m - π)`, a field since `z^m - π` is Eisenstein
  (`connectedSpace_pullback_kummerCovering`). The criterion
  `topologicalClosure_sup_proLKernel_eq_top_of_isInertiaSubgroupAt` concludes, `π₁^{p'}(U)` being
  procyclic (`multiplicativeGroupPrimeToPStatement`, transported by `exists_bijective_eval_of_iso`).
* `AffineLineChart.coe_eq_compl_origin`: if `X = V ∪ W` and `V ∩ W = D(t)`, then `W = X - {o}` (the
  charts of `ℙ¹`).

References: SGA 1 XIII.2.12; for strict localizations EGA IV 18.8, Stacks 04HX.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open scoped Polynomial LaurentPolynomial

namespace SGA.SGA1.ExposeXIII.AffineLineChart

variable {k : Type u} [Field k] {X : Scheme.{u}} {V : X.Opens}

section Origin

variable (hV : IsAffineOpen V) (φ : Γ(X, V) ≃+* k[X])

/-- The ideal `(t)` of `Γ(V) ≅ k[t]`. -/
noncomputable def originIdeal : Ideal Γ(X, V) :=
  (Ideal.span {Polynomial.X} : Ideal k[X]).comap φ

instance isMaximal_originIdeal : (originIdeal φ).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ φ.surjective
    (H := PrincipalIdealRing.isMaximal_of_irreducible Polynomial.irreducible_X)

lemma originIdeal_eq : originIdeal φ = Ideal.span {φ.symm Polynomial.X} := by
  ext x
  rw [originIdeal, Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
  have := map_dvd_iff φ (a := φ.symm Polynomial.X) (b := x)
  rwa [RingEquiv.apply_symm_apply] at this

/-- The origin `t = 0` of the chart `V`, `Γ(V) ≅ k[t]`. -/
noncomputable def origin : X :=
  hV.fromSpec ⟨originIdeal φ, inferInstance⟩

lemma origin_mem : origin hV φ ∈ V := by
  have : origin hV φ ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
  rwa [hV.range_fromSpec] at this

lemma origin_notMem_basicOpen : origin hV φ ∉ X.basicOpen (φ.symm Polynomial.X) := by
  intro h
  have h₂ : (⟨originIdeal φ, inferInstance⟩ : PrimeSpectrum Γ(X, V)) ∈
      PrimeSpectrum.basicOpen (φ.symm Polynomial.X) := by
    rw [← hV.fromSpec_preimage_basicOpen]
    exact h
  refine h₂ ?_
  change φ.symm Polynomial.X ∈ originIdeal φ
  rw [originIdeal_eq]
  exact Ideal.subset_span rfl

variable {hV φ} in
lemma primeIdealOf_eq {x : X} (hxV : x ∈ V) (hx : x ∉ X.basicOpen (φ.symm Polynomial.X)) :
    hV.primeIdealOf ⟨x, hxV⟩ = ⟨originIdeal φ, inferInstance⟩ := by
  have hp : hV.primeIdealOf ⟨x, hxV⟩ ∉ PrimeSpectrum.basicOpen (φ.symm Polynomial.X) := by
    rw [← hV.fromSpec_preimage_basicOpen]
    change hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) ∉ X.basicOpen _
    rwa [hV.fromSpec_primeIdealOf]
  have hle : originIdeal φ ≤ (hV.primeIdealOf ⟨x, hxV⟩).asIdeal := by
    rw [originIdeal_eq, Ideal.span_le, Set.singleton_subset_iff]
    exact not_not.mp hp
  exact PrimeSpectrum.ext
    ((isMaximal_originIdeal φ).eq_of_le (hV.primeIdealOf _).isPrime.ne_top hle).symm

/-- The origin is the only point of `V` outside `D(t)`. -/
lemma eq_origin {x : X} (hxV : x ∈ V) (hx : x ∉ X.basicOpen (φ.symm Polynomial.X)) :
    x = origin hV φ := by
  have := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  rw [primeIdealOf_eq hxV hx] at this
  exact this.symm

/-- If `X = V ∪ W` and `V ∩ W = D(t)`, then `W = X - {o}`, `o` the origin of `V` (e.g. the two
charts of `ℙ¹`). -/
lemma coe_eq_compl_origin {W : X.Opens} (hVW : V ⊔ W = ⊤)
    (hW : X.basicOpen (φ.symm Polynomial.X) = V ⊓ W) : (W : Set X) = {origin hV φ}ᶜ := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, SetLike.mem_coe]
  constructor
  · rintro hxW rfl
    apply origin_notMem_basicOpen hV φ
    rw [hW]
    exact ⟨origin_mem hV φ, hxW⟩
  · intro hx
    by_contra hxW
    have hxV : x ∈ V := by
      have : x ∈ V ⊔ W := by rw [hVW]; trivial
      exact (TopologicalSpace.Opens.mem_sup.mp this).resolve_right hxW
    refine hx (eq_origin hV φ hxV fun h ↦ hxW ?_)
    rw [hW] at h
    exact h.2

end Origin

section Stalk

variable {hV : IsAffineOpen V} (φ : Γ(X, V) ≃+* k[X]) {x : X} (hxV : x ∈ V)
  (hx : x ∉ X.basicOpen (φ.symm Polynomial.X))

include φ in
lemma isDomain_sections : IsDomain Γ(X, V) :=
  MulEquiv.isDomain k[X] φ.toMulEquiv

include φ in
lemma isPrincipalIdealRing_sections : IsPrincipalIdealRing Γ(X, V) :=
  IsPrincipalIdealRing.of_surjective φ.symm.toRingHom φ.symm.surjective

include hV φ hxV in
lemma isDomain_stalk : IsDomain (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := isDomain_sections φ
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl)
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl_le_nonZeroDivisors

include hV hx in
/-- The local ring of `X` at the origin of `V ≅ 𝔸¹` is a discrete valuation ring. -/
lemma isDiscreteValuationRing_stalk :
    haveI := isDomain_stalk (hV := hV) φ hxV
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  have := isDomain_sections φ
  have := isPrincipalIdealRing_sections φ
  have := isDomain_stalk (hV := hV) φ hxV
  refine IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Γ(X, V)
    (P := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal) ?_ _
  rw [primeIdealOf_eq hxV hx]
  change originIdeal φ ≠ ⊥
  rw [originIdeal_eq, ne_eq, Ideal.span_singleton_eq_bot, map_eq_zero_iff _ φ.symm.injective]
  exact Polynomial.X_ne_zero

include hV hx in
/-- The maximal ideal of the local ring of `X` at the origin of `V ≅ 𝔸¹` is generated by `t`. -/
lemma maximalIdeal_stalk :
    maximalIdeal (X.presheaf.stalk x) =
      Ideal.span {X.presheaf.germ V x hxV (φ.symm Polynomial.X)} := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have := hV.isLocalization_stalk ⟨x, hxV⟩
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal,
    primeIdealOf_eq hxV hx]
  change Ideal.map _ (originIdeal φ) = _
  rw [originIdeal_eq, Ideal.map_span, Set.image_singleton]
  rfl

end Stalk

section StrictLocalization

variable {Ω₀ : Type u} [Field Ω₀] {xb : Spec (.of Ω₀) ⟶ X} (hxV : xb.imagePoint ∈ V)

/-- The ring map `Γ(V) → 𝒪^{sh}_{X,x̄}` to the strict localization. -/
noncomputable def toStrictLocalization : Γ(X, V) ⟶ xb.strictLocalization :=
  X.presheaf.germ V _ hxV ≫ xb.toStrictLocalization

lemma fromSpecStrictLocalization_eq (hV : IsAffineOpen V) :
    xb.fromSpecStrictLocalization = Spec.map (toStrictLocalization hxV) ≫ hV.fromSpec :=
  Scheme.Hom.fromSpecStrictLocalization_eq_SpecMap xb hV hxV

variable {hV : IsAffineOpen V} (φ : Γ(X, V) ≃+* k[X]) (hx : xb.imagePoint ∉ X.basicOpen
  (φ.symm Polynomial.X))

attribute [local instance] Scheme.Hom.residueFieldAlgebra Scheme.Hom.stalkAlgebra
  Scheme.Hom.isScalarTower_stalkAlgebra isLocalHom_algebraMap_of_isScalarTower

include hV hxV hx in
lemma isDomain_strictLocalization : IsDomain xb.strictLocalization := by
  have := isDomain_stalk (hV := hV) φ hxV
  have := isDiscreteValuationRing_stalk (hV := hV) φ hxV hx
  exact inferInstanceAs (IsDomain (StrictHenselization (X.presheaf.stalk xb.imagePoint) Ω₀))

include hV hxV hx in
/-- The strict localization of `X` at a geometric point over the origin of `V ≅ 𝔸¹` is a discrete
valuation ring. -/
lemma isDiscreteValuationRing_strictLocalization :
    haveI := isDomain_strictLocalization (hV := hV) hxV φ hx
    IsDiscreteValuationRing xb.strictLocalization := by
  have := isDomain_stalk (hV := hV) φ hxV
  have := isDiscreteValuationRing_stalk (hV := hV) φ hxV hx
  exact inferInstanceAs (IsDiscreteValuationRing
    (StrictHenselization (X.presheaf.stalk xb.imagePoint) Ω₀))

include hV hx in
/-- The image `π` of `t` in the strict localization at a geometric point over the origin is a
uniformizer. -/
lemma irreducible_uniformizer :
    Irreducible (toStrictLocalization hxV (φ.symm Polynomial.X)) := by
  have := isDomain_strictLocalization (hV := hV) hxV φ hx
  have := isDiscreteValuationRing_strictLocalization (hV := hV) hxV φ hx
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  have h := StrictHenselization.map_maximalIdeal
    (R := X.presheaf.stalk xb.imagePoint) (K := Ω₀)
  rw [maximalIdeal_stalk (hV := hV) φ hxV hx, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end StrictLocalization

section Pullback

variable {Ω₀ : Type u} [Field Ω₀] {xb : Spec (.of Ω₀) ⟶ X} (hxV : xb.imagePoint ∈ V)
  (t : Γ(X, V))

/-- `𝒪^{sh}[1/π]` (`π` the image of `t`), the ring of `D(t) ×_X Spec 𝒪^{sh}`. -/
abbrev StrictLocalizationAway : Type u :=
  Localization.Away (toStrictLocalization hxV t)

variable (hV : IsAffineOpen V)

include hV in
lemma preimage_basicOpen :
    xb.fromSpecStrictLocalization ⁻¹ᵁ X.basicOpen t =
      PrimeSpectrum.basicOpen (toStrictLocalization hxV t) := by
  rw [fromSpecStrictLocalization_eq hxV hV, Scheme.Hom.comp_preimage,
    hV.fromSpec_preimage_basicOpen, SpecMap_preimage_basicOpen]

/-- `D(t) ×_X Spec 𝒪^{sh} ≅ Spec 𝒪^{sh}[1/π]`. -/
noncomputable def pullbackIso :
    pullback (X.basicOpen t).ι xb.fromSpecStrictLocalization ≅
      Spec (.of (StrictLocalizationAway hxV t)) :=
  pullbackSymmetry _ _ ≪≫
    pullbackRestrictIsoRestrict xb.fromSpecStrictLocalization (X.basicOpen t) ≪≫
    Scheme.isoOfEq _ (preimage_basicOpen hxV t hV) ≪≫
    basicOpenIsoSpecAway (toStrictLocalization hxV t)

lemma pullbackIso_inv_snd :
    (pullbackIso hxV t hV).inv ≫ pullback.snd (X.basicOpen t).ι xb.fromSpecStrictLocalization =
      Spec.map (CommRingCat.ofHom
        (algebraMap xb.strictLocalization (StrictLocalizationAway hxV t))) := by
  rw [Iso.inv_comp_eq]
  simp only [pullbackIso, Iso.trans_hom, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap]
  have h : (Scheme.isoOfEq (Spec xb.strictLocalization) (preimage_basicOpen hxV t hV)).hom ≫
      Scheme.Opens.ι (X := Spec xb.strictLocalization)
        (PrimeSpectrum.basicOpen (toStrictLocalization hxV t)) =
      (xb.fromSpecStrictLocalization ⁻¹ᵁ X.basicOpen t).ι := Scheme.isoOfEq_hom_ι _ _
  erw [h]
  rw [pullbackRestrictIsoRestrict_hom_ι, pullbackSymmetry_hom_comp_fst]

variable (φ : Γ(X, V) ≃+* k[X]) (hx : xb.imagePoint ∉ X.basicOpen (φ.symm Polynomial.X))

include hV hx in
lemma isDomain_strictLocalizationAway :
    IsDomain (StrictLocalizationAway hxV (φ.symm Polynomial.X)) := by
  have := isDomain_strictLocalization (hV := hV) hxV φ hx
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (M := Submonoid.powers (toStrictLocalization hxV (φ.symm Polynomial.X)))
    (powers_le_nonZeroDivisors_of_noZeroDivisors
      (irreducible_uniformizer (hV := hV) hxV φ hx).ne_zero)

include hV hx in
/-- `𝒪^{sh}[1/π]` is the field of fractions of the discrete valuation ring `𝒪^{sh}`. -/
lemma isFractionRing_strictLocalizationAway :
    haveI := isDomain_strictLocalization (hV := hV) hxV φ hx
    IsFractionRing xb.strictLocalization (StrictLocalizationAway hxV (φ.symm Polynomial.X)) := by
  have := isDomain_strictLocalization (hV := hV) hxV φ hx
  have := isDiscreteValuationRing_strictLocalization (hV := hV) hxV φ hx
  have hπ := irreducible_uniformizer (hV := hV) hxV φ hx
  refine IsLocalization.isLocalization_of_is_exists_mul_mem _
    (Submonoid.powers (toStrictLocalization hxV (φ.symm Polynomial.X))) (nonZeroDivisors _)
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero) ?_
  rintro ⟨y, hy⟩
  obtain ⟨n, v, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hy) hπ
  exact ⟨↑v⁻¹, n, by simp [← mul_assoc]⟩

include hxV hV hx in
/-- `D(t) ×_X Spec 𝒪^{sh}_{X,x̄}` is connected (it is `Spec` of a field) for `x̄` over the
origin. -/
lemma connectedSpace_pullback :
    ConnectedSpace
      ↥(pullback (X.basicOpen (φ.symm Polynomial.X)).ι xb.fromSpecStrictLocalization) := by
  have := isDomain_strictLocalizationAway hxV hV φ hx
  exact Scheme.connectedSpace_of_iso (pullbackIso hxV _ hV)

end Pullback

section Kummer

variable {Ω₀ : Type u} [Field Ω₀] {xb : Spec (.of Ω₀) ⟶ X} (hxV : xb.imagePoint ∈ V)
  (hV : IsAffineOpen V) (φ : Γ(X, V) ≃+* k[X])
  (ψ : Γ(X, X.basicOpen (φ.symm Polynomial.X)) ≃+* k[T;T⁻¹])

/-- `Γ(D(t)) ≅ k[T, T⁻¹]`: both are `Γ(V) ≅ k[t]` with `t` inverted. -/
noncomputable def basicOpenEquiv : Γ(X, X.basicOpen (φ.symm Polynomial.X)) ≃+* k[T;T⁻¹] :=
  haveI := hV.isLocalization_basicOpen (φ.symm Polynomial.X)
  IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers (φ.symm Polynomial.X))
    (T := Submonoid.powers Polynomial.X) _ k[T;T⁻¹] φ
    (by rw [Submonoid.map_powers]; exact congrArg _ (φ.apply_symm_apply _))

lemma basicOpenEquiv_coord :
    basicOpenEquiv hV φ (X.presheaf.map (homOfLE (X.basicOpen_le _)).op (φ.symm Polynomial.X)) =
      LaurentPolynomial.T 1 := by
  have := hV.isLocalization_basicOpen (φ.symm Polynomial.X)
  change basicOpenEquiv hV φ (algebraMap Γ(X, V) _ (φ.symm Polynomial.X)) = _
  rw [basicOpenEquiv, IsLocalization.ringEquivOfRingEquiv_eq, RingEquiv.apply_symm_apply,
    ← Polynomial.toLaurent_X]
  rfl

/-- `U = D(t) ≅ Spec k[T, T⁻¹]`, through a ring isomorphism `ψ : Γ(U) ≅ k[T, T⁻¹]` (e.g.
`basicOpenEquiv`). -/
noncomputable def basicOpenIso :
    (X.basicOpen (φ.symm Polynomial.X) : Scheme.{u}) ≅ Spec (.of k[T;T⁻¹]) :=
  (hV.basicOpen _).isoSpec ≪≫ (Scheme.Spec.mapIso ψ.toCommRingCatIso.op).symm

lemma basicOpenIso_inv_ι :
    (basicOpenIso hV φ ψ).inv ≫ (X.basicOpen (φ.symm Polynomial.X)).ι =
      Spec.map (X.presheaf.map (homOfLE (X.basicOpen_le _)).op ≫ CommRingCat.ofHom ψ.toRingHom) ≫
        hV.fromSpec := by
  rw [Spec.map_comp, Category.assoc, hV.map_fromSpec (hV.basicOpen _)]
  rfl

/-- `k[T, T⁻¹] → 𝒪^{sh}[1/π]`, the ring map of `U ×_X Spec 𝒪^{sh} → U ≅ Spec k[T, T⁻¹]`. -/
noncomputable def laurentToAway : k[T;T⁻¹] →+* StrictLocalizationAway hxV (φ.symm Polynomial.X) :=
  haveI := hV.isLocalization_basicOpen (φ.symm Polynomial.X)
  (IsLocalization.Away.lift (φ.symm Polynomial.X)
    (g := (algebraMap xb.strictLocalization (StrictLocalizationAway hxV (φ.symm Polynomial.X))).comp
      (toStrictLocalization hxV).hom)
    (show IsUnit (algebraMap _ (StrictLocalizationAway hxV (φ.symm Polynomial.X))
      (toStrictLocalization hxV (φ.symm Polynomial.X))) from
      IsLocalization.Away.algebraMap_isUnit _)).comp ψ.symm.toRingHom

lemma laurentToAway_apply (s : Γ(X, V)) :
    laurentToAway hxV hV φ ψ (ψ (X.presheaf.map (homOfLE (X.basicOpen_le _)).op s)) =
      algebraMap _ (StrictLocalizationAway hxV (φ.symm Polynomial.X))
        (toStrictLocalization hxV s) := by
  have := hV.isLocalization_basicOpen (φ.symm Polynomial.X)
  simp only [laurentToAway, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  exact IsLocalization.lift_eq _ s

lemma pullbackIso_inv_fst_basicOpenIso_hom :
    (pullbackIso hxV _ hV).inv ≫
      pullback.fst (X.basicOpen (φ.symm Polynomial.X)).ι xb.fromSpecStrictLocalization ≫
      (basicOpenIso hV φ ψ).hom = Spec.map (CommRingCat.ofHom (laurentToAway hxV hV φ ψ)) := by
  rw [← cancel_mono ((basicOpenIso hV φ ψ).inv ≫ (X.basicOpen (φ.symm Polynomial.X)).ι),
    Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, pullback.condition, ← Category.assoc,
    pullbackIso_inv_snd, fromSpecStrictLocalization_eq hxV hV, basicOpenIso_inv_ι,
    ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext s
  exact (laurentToAway_apply hxV hV φ ψ s).symm

variable {hxV hV φ ψ} (hx : xb.imagePoint ∉ X.basicOpen (φ.symm Polynomial.X))
  (hψ : ψ (X.presheaf.map (homOfLE (X.basicOpen_le _)).op (φ.symm Polynomial.X)) =
    LaurentPolynomial.T 1)
  (m : ℕ) [NeZero m] (hm : (m : k) ≠ 0)

include hx hψ in
/-- The ring of the pullback of the Kummer covering `z^m = T` of `U` to `U ×_X Spec 𝒪^{sh}` is a
domain: `z^m - π` is irreducible over the fraction field of the discrete valuation ring `𝒪^{sh}`
(Eisenstein). -/
lemma isDomain_kummer_tensor :
    letI : Algebra k[T;T⁻¹] (StrictLocalizationAway hxV (φ.symm Polynomial.X)) :=
      (laurentToAway hxV hV φ ψ).toAlgebra
    IsDomain (TensorProduct k[T;T⁻¹]
      (ExposeXI.KummerAlgebra k[T;T⁻¹] m (LaurentPolynomial.T 1))
      (StrictLocalizationAway hxV (φ.symm Polynomial.X))) := by
  let A := StrictLocalizationAway hxV (φ.symm Polynomial.X)
  let : Algebra k[T;T⁻¹] A := (laurentToAway hxV hV φ ψ).toAlgebra
  have := isDomain_strictLocalization (hV := hV) hxV φ hx
  have := isDiscreteValuationRing_strictLocalization (hV := hV) hxV φ hx
  have := isFractionRing_strictLocalizationAway hxV hV φ hx
  let : Field A := IsFractionRing.toField xb.strictLocalization
  have : Fact (Irreducible (toStrictLocalization hxV (φ.symm Polynomial.X))) :=
    ⟨irreducible_uniformizer (hV := hV) hxV φ hx⟩
  have hmap : (Polynomial.X ^ m - Polynomial.C (LaurentPolynomial.T 1 : k[T;T⁻¹])).map
      (algebraMap k[T;T⁻¹] A) = Polynomial.X ^ m - Polynomial.C (algebraMap
        xb.strictLocalization A (toStrictLocalization hxV (φ.symm Polynomial.X))) := by
    rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C]
    congr 2
    change laurentToAway hxV hV φ ψ (LaurentPolynomial.T 1) = _
    rw [← hψ, laurentToAway_apply]
  have : Fact (Irreducible ((Polynomial.X ^ m -
      Polynomial.C (LaurentPolynomial.T 1 : k[T;T⁻¹])).map (algebraMap k[T;T⁻¹] A))) := by
    rw [hmap]
    exact ⟨ExposeXIII.irreducible_X_pow_sub_C_algebraMap _ m _⟩
  let e := (Algebra.TensorProduct.comm k[T;T⁻¹] _ _).toRingEquiv.trans
    (ExposeI.tensorAdjoinRootEquiv A
      (Polynomial.X ^ m - Polynomial.C (LaurentPolynomial.T 1 : k[T;T⁻¹]))).toRingEquiv
  exact e.toMulEquiv.isDomain _

include hxV hx hψ in
/-- The pullback of the Kummer covering `z^m = T` of `U = D(t)` to `U ×_X Spec 𝒪^{sh}_{X,x̄}`
(`x̄` over the origin) is connected. -/
lemma connectedSpace_pullback_kummerCovering :
    ConnectedSpace ↥((ExposeV.FEt.pullback (pullback.fst (X.basicOpen (φ.symm Polynomial.X)).ι
      xb.fromSpecStrictLocalization)).obj (kummerCovering m hm (basicOpenIso hV φ ψ))).left := by
  let A := StrictLocalizationAway hxV (φ.symm Polynomial.X)
  let : Algebra k[T;T⁻¹] A := (laurentToAway hxV hV φ ψ).toAlgebra
  have := isDomain_kummer_tensor (hxV := hxV) (hV := hV) hx hψ m
  set q := pullback.fst (X.basicOpen (φ.symm Polynomial.X)).ι xb.fromSpecStrictLocalization
  set e := basicOpenIso hV φ ψ
  set K := (ExposeV.specFunctor (.of k[T;T⁻¹])).obj (Opposite.op (kummerFiniteEtale k m hm))
  set f := Spec.map (CommRingCat.ofHom (laurentToAway hxV hV φ ψ))
  have hq : q ≫ e.hom = (pullbackIso hxV _ hV).hom ≫ f := by
    rw [← Iso.inv_comp_eq, pullbackIso_inv_fst_basicOpenIso_hom]
  have h5 : ConnectedSpace ↥(pullback K.hom f) :=
    Scheme.connectedSpace_of_iso (pullbackSpecIso k[T;T⁻¹]
      (ExposeXI.KummerAlgebra k[T;T⁻¹] m (LaurentPolynomial.T 1)) A)
  have h4 : ConnectedSpace ↥(pullback (pullback.snd K.hom f) (pullbackIso hxV _ hV).hom) :=
    Scheme.connectedSpace_of_iso (asIso (pullback.fst _ _))
  have h3 : ConnectedSpace ↥(pullback K.hom ((pullbackIso hxV _ hV).hom ≫ f)) :=
    Scheme.connectedSpace_of_iso (pullbackLeftPullbackSndIso _ _ _).symm
  have h2 : ConnectedSpace ↥(pullback K.hom (q ≫ e.hom)) :=
    Scheme.connectedSpace_of_iso (pullback.congrHom rfl hq)
  exact Scheme.connectedSpace_of_iso (pullbackLeftPullbackSndIso K.hom e.hom q)

end Kummer

section Main

open ExposeV

/-- XIII.2.12 for `g = 0`, `n = 2`, inertia condition at a point of an affine chart: let `k` be
algebraically closed of characteristic `p`, `V ⊆ X` an affine open with `Γ(V) ≅ k[t]`,
`U = D(t) ⊆ V` and `x̄` a geometric point over the origin `t = 0` of `V`. Then every inertia
subgroup `H` of `π₁(U, ξ)` at `x̄` maps onto `π₁^{p'}(U, ξ)`: `H · proLKernel` is dense. -/
theorem topologicalClosure_sup_proLKernel_eq_top (p : ℕ) [IsAlgClosed k] [CharP k p]
    (hV : IsAffineOpen V) (φ : Γ(X, V) ≃+* k[X]) {U : X.Opens}
    (hU : X.basicOpen (φ.symm Polynomial.X) = U) {Ω₀ : Type u} [Field Ω₀] [IsSepClosed Ω₀]
    {xb : Spec (.of Ω₀) ⟶ X}
    (hxb : xb.imagePoint = origin hV φ) {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    {ξ : Spec (.of Ω) ⟶ (U : Scheme.{u})} {H : Subgroup (etaleFundamentalGroup Ω ξ)}
    (hH : IsInertiaSubgroupAt U xb ξ H) :
    (H ⊔ proLKernel (primesDifferentFrom p) (etaleFundamentalGroup Ω ξ)).topologicalClosure =
      ⊤ := by
  subst hU
  let ψ := basicOpenEquiv hV φ
  have hψ := basicOpenEquiv_coord hV φ
  have hxV : xb.imagePoint ∈ V := hxb ▸ origin_mem hV φ
  have hx : xb.imagePoint ∉ X.basicOpen (φ.symm Polynomial.X) :=
    hxb ▸ origin_notMem_basicOpen hV φ
  have : ConnectedSpace (X.basicOpen (φ.symm Polynomial.X) : Scheme.{u}) :=
    Scheme.connectedSpace_of_iso (basicOpenIso hV φ ψ)
  have := connectedSpace_pullback hxV hV φ hx
  obtain ⟨σ, hσ⟩ := exists_bijective_eval_of_iso p k (basicOpenIso hV φ ψ) Ω ξ
  refine topologicalClosure_sup_proLKernel_eq_top_of_isInertiaSubgroupAt hH hσ fun m hm hmL ↦ ?_
  have hmk : (m : k) ≠ 0 := natCast_ne_zero_of_primesDifferentFrom hm hmL
  have : NeZero m := ⟨hm⟩
  have := connectedSpace_pullback_kummerCovering (hxV := hxV) (hV := hV) hx hψ m hmk
  exact ⟨kummerCovering m hmk (basicOpenIso hV φ ψ),
    isGalois_kummerCovering m hmk (basicOpenIso hV φ ψ) Ω ξ,
    card_fiber_kummerCovering m hmk (basicOpenIso hV φ ψ) Ω ξ,
    FEt.isConnected_of_connectedSpace _⟩

end Main

end SGA.SGA1.ExposeXIII.AffineLineChart
