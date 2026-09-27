/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.QuasiFinite.Basic

/-!
# Étaleness at a point of a scheme, via stalks

For a morphism of schemes `f : X ⟶ Y` and `x : X`:

* `AlgebraicGeometry.formallyEtale_stalkMap_iff`: on affine charts `x ∈ V ⊆ f⁻¹ U`, the stalk map
  of `f` at `x` is formally étale iff `Γ(X, V)` is étale over `Γ(Y, U)` at the prime of `x`.
* `AlgebraicGeometry.formallyEtale_stalkMap_of_etale_ι`: if `f` is étale on an open neighbourhood
  of `x`, the stalk map at `x` is formally étale.
* `AlgebraicGeometry.exists_etale_of_formallyEtale_stalkMap`: conversely, for `f` locally of
  finite presentation, if the stalk map at `x` is formally étale then `f` is étale on an open
  neighbourhood of `x`.
* `AlgebraicGeometry.stalkMap_injective_of_isDominant`: stalk maps of a dominant morphism of
  integral schemes are injective.
* `IsLocalRing.ringKrullDim_le_of_quasiFinite`: a quasi-finite local extension does not raise the
  dimension.
-/

universe u

open CategoryTheory IsLocalRing

namespace RingHom

/-- A ring isomorphism is formally étale. -/
lemma FormallyEtale.of_ringEquiv {S T : Type*} [CommRing S] [CommRing T] (e : S ≃+* T) :
    e.toRingHom.FormallyEtale := by
  algebraize [e.toRingHom]
  exact Algebra.FormallyEtale.of_equiv (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)

/-- Formally étale ring maps respect isomorphisms. -/
lemma FormallyEtale.respectsIso : RespectsIso FormallyEtale :=
  ⟨fun _ e hf ↦ hf.comp (of_ringEquiv e), fun _ e hf ↦ (of_ringEquiv e).comp hf⟩

end RingHom

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- On affine charts `x ∈ V ⊆ f⁻¹ U`, the stalk map of `f` at `x` is formally étale iff `Γ(X, V)`
is étale over `Γ(Y, U)` at the prime corresponding to `x`. -/
lemma formallyEtale_stalkMap_iff {f : X ⟶ Y} {x : X} (U : Y.Opens) (hU : IsAffineOpen U)
    (V : X.Opens) (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U) (hx : x ∈ V) :
    letI := (f.appLE U V hVU).hom.toAlgebra
    (f.stalkMap x).hom.FormallyEtale ↔
      Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let p := (hU.primeIdealOf ⟨f x, hVU hx⟩).asIdeal
  let q := (hV.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.LiesOver p :=
    ⟨congr($(IsAffineOpen.comap_primeIdealOf_appLE U hU V hV hVU hx).1).symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  trans Algebra.FormallyEtale (Localization.AtPrime p) (Localization.AtPrime q)
  · rw [← RingHom.formallyEtale_algebraMap]
    exact RingHom.FormallyEtale.respectsIso.arrow_mk_iso_iff
      (IsAffineOpen.arrowStalkMapIso f U hU V hV hVU hx)
  · exact Algebra.FormallyEtale.iff_restrictScalars.symm

/-- The stalk maps of an étale morphism are formally étale. -/
lemma formallyEtale_stalkMap_of_etale (f : X ⟶ Y) [Etale f] (x : X) :
    (f.stalkMap x).hom.FormallyEtale := by
  have h1 : (f.stalkMap x).hom.FormallyUnramified := FormallyUnramified.stalkMap f x
  have h2 : (f.stalkMap x).hom.FormallySmooth := by
    have : x ∈ f.smoothLocus := by rw [f.smoothLocus_eq_top]; trivial
    exact Scheme.Hom.mem_smoothLocus.mp this
  algebraize [(f.stalkMap x).hom]
  exact Algebra.FormallyEtale.iff_formallyUnramified_and_formallySmooth.mpr ⟨h1, h2⟩

/-- If `f` is étale on an open neighbourhood `U` of `x`, its stalk map at `x` is formally
étale. -/
lemma formallyEtale_stalkMap_of_etale_ι (f : X ⟶ Y) (U : X.Opens) {x : X} (hx : x ∈ U)
    [Etale (U.ι ≫ f)] : (f.stalkMap x).hom.FormallyEtale := by
  obtain ⟨p, rfl⟩ : ∃ p : U.toScheme, U.ι p = x := ⟨⟨x, hx⟩, rfl⟩
  have h := formallyEtale_stalkMap_of_etale (U.ι ≫ f) p
  have h' : (f.stalkMap (U.ι p) ≫ U.ι.stalkMap p).hom.FormallyEtale := by
    rw [← Scheme.Hom.stalkMap_comp]
    exact h
  exact (RingHom.FormallyEtale.respectsIso.cancel_right_isIso _ _).mp h'

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `f` is locally of finite presentation and its stalk map at `x` is formally étale, then `f`
is étale on an open neighbourhood of `x`. -/
lemma exists_etale_of_formallyEtale_stalkMap (f : X ⟶ Y) [LocallyOfFinitePresentation f]
    (x : X) (H : (f.stalkMap x).hom.FormallyEtale) :
    ∃ U : X.Opens, x ∈ U ∧ Etale (U.ι ≫ f) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (U.2.preimage f.continuous)
  have := f.finitePresentation_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  have : Algebra.IsEtaleAt Γ(Y, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    (formallyEtale_stalkMap_iff U hU V hV hVU hxV).mp H
  obtain ⟨r, hrx, hr⟩ := Algebra.exists_etale_of_isEtaleAt (R := Γ(Y, U))
    (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hle : X.basicOpen r ≤ f ⁻¹ᵁ U := (X.basicOpen_le r).trans hVU
  refine ⟨X.basicOpen r, ?_, ?_⟩
  · rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hrx
  · have happ : (f.appLE U (X.basicOpen r) hle).hom.Etale := by
      have := hV.isLocalization_basicOpen r
      rw [← RingHom.etale_algebraMap] at hr
      convert RingHom.Etale.respectsIso.1 _
        (IsLocalization.algEquiv (.powers r) _ Γ(X, X.basicOpen r)).toRingEquiv hr
      ext
      dsimp
      simp only [IsScalarTower.algebraMap_apply Γ(Y, U) Γ(X, V) (Localization _),
        IsLocalization.map_eq]
      simp only [RingHom.algebraMap_toAlgebra, RingHomCompTriple.comp_apply,
        ← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map]
    have hres : Etale (f.resLE U (X.basicOpen r) hle) := by
      have hU' : IsAffine U := hU
      have hV' : IsAffine (X.basicOpen r) := hV.basicOpen r
      rw [HasRingHomProperty.iff_of_isAffine (P := @Etale)]
      exact (RingHom.Etale.respectsIso.arrow_mk_iso_iff
        (arrowResLEAppIso f U (X.basicOpen r) hle)).mpr happ
    rw [← Scheme.Hom.resLE_comp_ι (f := f) (U := U) (V := X.basicOpen r) (e := hle)]
    infer_instance

/-- A dominant morphism of irreducible schemes maps the generic point to the generic point. -/
lemma Scheme.Hom.genericPoint_eq_of_isDominant (f : X ⟶ Y) [IsDominant f] [IrreducibleSpace X]
    [IrreducibleSpace Y] : f (genericPoint X) = genericPoint Y := by
  refine IsGenericPoint.eq ?_ (genericPoint_spec Y)
  rw [isGenericPoint_def, Set.eq_univ_iff_forall]
  intro y
  have hsub : Set.range f ⊆ closure {f (genericPoint X)} := by
    rintro _ ⟨a, rfl⟩
    exact specializes_iff_mem_closure.mp
      ((genericPoint_specializes a).map f.continuous)
  have := closure_minimal hsub isClosed_closure
  rw [f.denseRange.closure_range] at this
  exact this (Set.mem_univ y)

/-- The stalk maps of a dominant morphism of integral schemes are injective. -/
lemma Scheme.Hom.stalkMap_injective_of_isDominant (f : X ⟶ Y) [IsDominant f] [IsIntegral X]
    [IsIntegral Y] (x : X) : Function.Injective (f.stalkMap x) := by
  let η := genericPoint X
  have hηx : η ⤳ x := genericPoint_specializes x
  -- the stalk of `Y` at `f η` is a field
  have hfield : IsField (Y.presheaf.stalk (f η)) := by
    have := f.genericPoint_eq_of_isDominant
    change IsField (Y.presheaf.stalk (f (genericPoint X)))
    rw [this]
    exact Field.toIsField Y.functionField
  let _ := hfield.toField
  have h1 : Function.Injective (f.stalkMap η) := (f.stalkMap η).hom.injective
  -- specialization maps of the integral scheme `Y` are injective
  have h2 : Function.Injective
      (Y.presheaf.stalkSpecializes (f.base.hom.map_specializes hηx)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    obtain ⟨U, hU, s, rfl⟩ := Y.presheaf.exists_germ_eq a
    have hηU : f η ∈ U := (f.base.hom.map_specializes hηx).mem_open U.isOpen hU
    rw [← CommRingCat.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] at ha
    rw [← map_zero (Y.presheaf.germ U (f η) hηU).hom] at ha
    have := germ_injective_of_isIntegral Y (f η) hηU ha
    rw [this, map_zero]
  rw [injective_iff_map_eq_zero]
  intro a ha
  apply h2
  apply h1
  rw [map_zero, map_zero, f.stalkSpecializes_stalkMap_apply η x hηx a, ha, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is étale on a neighbourhood of every proper generization of `z`, then the stalk
`𝒪_{X,z}` is étale over `𝒪_{Y,f z}` at every non-maximal prime: such a prime is the ideal of a
proper generization `w` of `z`, and `(𝒪_{X,z})_p = 𝒪_{X,w}`. -/
lemma isEtaleAt_stalk_of_forall_specializes {f : X ⟶ Y} {z : X}
    (h : ∀ w : X, w ⤳ z → w ≠ z → ∃ U : X.Opens, w ∈ U ∧ Etale (U.ι ≫ f))
    (p : Ideal (X.presheaf.stalk z)) [p.IsPrime] (hp : p ≠ maximalIdeal _) :
    letI := (f.stalkMap z).hom.toAlgebra
    Algebra.IsEtaleAt (Y.presheaf.stalk (f z)) p := by
  let _ := (f.stalkMap z).hom.toAlgebra
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f z)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hzU (U.2.preimage f.continuous)
  let R := Γ(Y, U)
  let S := Γ(X, V)
  let A := Y.presheaf.stalk (f z)
  let B := X.presheaf.stalk z
  let Q := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
  let _ : Algebra R S := (f.appLE U V hVU).hom.toAlgebra
  let _ : Algebra S B := X.presheaf.algebra_section_stalk ⟨z, hzV⟩
  let _ : Algebra R A := Y.presheaf.algebra_section_stalk ⟨f z, hVU hzV⟩
  let _ : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  have : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
  have hB : IsLocalization.AtPrime B Q := hV.isLocalization_stalk ⟨z, hzV⟩
  have hA : IsLocalization.AtPrime A (hU.primeIdealOf ⟨f z, hVU hzV⟩).asIdeal :=
    hU.isLocalization_stalk ⟨f z, hVU hzV⟩
  -- the square `R → A → B = R → S → B`
  have hsq : ∀ r : R, algebraMap A B (algebraMap R A r) = algebraMap R B r := by
    intro r
    change (Y.presheaf.germ U (f z) (hVU hzV) ≫ f.stalkMap z) r =
      (f.appLE U V hVU ≫ X.presheaf.germ V z hzV) r
    rw [Scheme.Hom.germ_stalkMap, ← X.presheaf.germ_res (homOfLE hVU) _ hzV,
      Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  have : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq fun r ↦ (hsq r).symm
  -- the prime `P` of `S` below `p`, and the point `w` of `X`
  let P := p.comap (algebraMap S B)
  have hPQ : P ≤ Q := by
    rw [← IsLocalization.AtPrime.under_maximalIdeal B Q]
    exact Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))
  have hPne : P ≠ Q := by
    intro hPQ'
    apply hp
    rw [← IsLocalization.map_under Q.primeCompl B p, ← IsLocalization.map_under Q.primeCompl B
      (maximalIdeal B)]
    change Ideal.map _ P = _
    rw [hPQ', IsLocalization.AtPrime.under_maximalIdeal B Q]
  let w := hV.fromSpec ⟨P, Ideal.IsPrime.comap _⟩
  have hwV : w ∈ V := by
    change w ∈ (V : Set X)
    rw [← hV.range_fromSpec]
    exact ⟨_, rfl⟩
  have hinj : Function.Injective hV.fromSpec := hV.fromSpec.isOpenEmbedding.injective
  have hwP : hV.primeIdealOf ⟨w, hwV⟩ = ⟨P, Ideal.IsPrime.comap _⟩ :=
    hinj (hV.fromSpec_primeIdealOf ⟨w, hwV⟩)
  have hzQ : hV.fromSpec (hV.primeIdealOf ⟨z, hzV⟩) = z := hV.fromSpec_primeIdealOf ⟨z, hzV⟩
  have hwz : w ⤳ z := by
    rw [← hzQ]
    exact ((PrimeSpectrum.le_iff_specializes _ _).mp hPQ).map hV.fromSpec.continuous
  have hwne : w ≠ z := by
    intro hwz'
    apply hPne
    have := hinj (hwz'.trans hzQ.symm)
    exact congrArg PrimeSpectrum.asIdeal this
  -- `S` is étale over `R` at `P`
  obtain ⟨U', hwU', hU'⟩ := h w hwz hwne
  have hst := formallyEtale_stalkMap_of_etale_ι f U' hwU'
  have hEtP := (formallyEtale_stalkMap_iff U hU V hV hVU hwV).mp hst
  rw [hwP] at hEtP
  change Algebra.FormallyEtale R (Localization.AtPrime P) at hEtP
  -- `B_p = S_P`
  let Bp := Localization.AtPrime p
  have hL : IsLocalization.AtPrime Bp P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization Q.primeCompl Bp p
  let e : Localization.AtPrime P ≃ₐ[S] Bp := IsLocalization.algEquiv P.primeCompl _ _
  have : Algebra.FormallyEtale R Bp := Algebra.FormallyEtale.of_equiv (e.restrictScalars R)
  have : Algebra.FormallyEtale R A :=
    Algebra.FormallyEtale.of_isLocalization (hU.primeIdealOf ⟨f z, hVU hzV⟩).asIdeal.primeCompl
  exact Algebra.FormallyEtale.of_restrictScalars (R := R)

end AlgebraicGeometry

/-- A quasi-finite local extension of noetherian local rings does not raise the dimension:
`dim B ≤ dim A` (the closed fibre has dimension `0`). -/
theorem IsLocalRing.ringKrullDim_le_of_quasiFinite {A B : Type*} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Algebra.QuasiFinite A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  have hm : (maximalIdeal B).comap (algebraMap A B) = maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap _
  have : (maximalIdeal B).LiesOver (maximalIdeal A) := ⟨hm.symm⟩
  let I := (maximalIdeal A).map (algebraMap A B)
  have hI : I ≤ maximalIdeal B := Ideal.map_le_iff_le_comap.mpr hm.ge
  have h := Ideal.height_le_height_add_of_liesOver (maximalIdeal A) (maximalIdeal B)
  have hP : ((maximalIdeal B).map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hI
  have h0 : ((maximalIdeal B).map (Ideal.Quotient.mk I)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨hP, bot_le⟩, fun J hJ hJP ↦ ?_⟩
    have := hJ.1
    let J' := J.comap (Ideal.Quotient.mk I)
    have hJ'm : J' ≤ maximalIdeal B := by
      have := Ideal.comap_mono (f := Ideal.Quotient.mk I) hJP
      rwa [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
        Ideal.mk_ker, sup_eq_left.mpr hI] at this
    have hIJ' : I ≤ J' := fun z hz ↦ by
      change Ideal.Quotient.mk I z ∈ J
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz]
      exact J.zero_mem
    have hunder : J'.under A = (maximalIdeal B).under A := by
      refine le_antisymm (Ideal.comap_mono hJ'm) ?_
      rw [Ideal.under, hm]
      exact Ideal.map_le_iff_le_comap.mp hIJ'
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq J' (maximalIdeal B) hJ'm hunder
    rw [← this, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  rw [h0, add_zero] at h
  rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
  exact_mod_cast h
