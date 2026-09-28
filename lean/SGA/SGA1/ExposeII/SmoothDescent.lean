/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.Etale.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.AlgebraicGeometry.PullbackCarrier
import SGA.SGA1.ExposeII.Criteria

/-!
# SGA 1, Exposé II, II.4.13: smoothness at a point descends along flat base change

II.4.13 says: let `Y` be locally of finite type over `S`, `S'` flat over `S`, `Y' = Y ×_S S'`, `x'`
a point of `Y'` and `x` its image in `Y`; then `Y` is smooth over `S` at `x` iff `Y'` is smooth over
`S'` at `x'`. We prove the affine form (`isSmoothAt_tensorProduct_iff`): `Spec S = Spec R`,
`S' = Spec T` with `T` flat over `R`, `Y = Spec S` finitely presented over `R`, and a prime `Q'` of
`T ⊗_R S` over the prime `Q` of `S`. For schemes (`mem_smoothLocus_iff_of_isPullback_of_flat`) we
reduce to it on affine charts: smoothness at a point does not change under restriction to open
subschemes of the source and the target (`mem_smoothLocus_iff_of_isOpenImmersion`), and the fibre
product of affine charts is an open subscheme of `Y'`. Consequently the global form holds for every
flat surjective `S' → S`, without the quasi-compactness required by mathlib's fpqc descent
(`smooth_iff_of_isPullback_of_flat_of_surjective`). The ascent under arbitrary base change is
`mem_smoothLocus_of_isPullback` in `SGA.SGA1.ExposeII.Criteria`.

SGA reduces to the criterion II.4.10 (iv) in an affine space. We use instead mathlib's description
of the smooth locus: `S` is smooth at `Q` iff `H¹(L_{S/R})_Q = 0` and `Ω¹_{S/R}` is free at `Q`.
Both `H¹(L)` and `Ω¹` commute with flat base change (`tensorH1CotangentEquiv`, mathlib's
`tensorKaehlerEquiv`), and `S_Q → (T ⊗_R S)_{Q'}` is faithfully flat, so the vanishing and the
freeness at `Q` ascend and descend (`notMem_support_of_notMem_support_baseChange`,
`mem_freeLocus_of_mem_freeLocus_baseChange`).

The auxiliary results on supports, free loci and `H¹` of the cotangent complex are general
commutative algebra and would belong in `SGA.Foundations`.
-/

universe u

open Algebra TensorProduct AlgebraicGeometry CategoryTheory Limits

namespace SGA.SGA1.ExposeII

/-- Localization at `Q` is reflected by a flat base change `S → S'` at a prime `Q'` over `Q`:
if `(S' ⊗_S M)_{Q'} = 0` then `M_Q = 0`. -/
lemma notMem_support_of_notMem_support_baseChange {S S' : Type*} [CommRing S] [CommRing S']
    [Algebra S S'] [Module.Flat S S'] (M : Type*) [AddCommGroup M] [Module S M]
    (Q' : PrimeSpectrum S') (h : Q' ∉ Module.support S' (S' ⊗[S] M)) :
    PrimeSpectrum.comap (algebraMap S S') Q' ∉ Module.support S M := by
  set Q := PrimeSpectrum.comap (algebraMap S S') Q'
  have : Q'.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver Q.asIdeal Q'.asIdeal
  have : Module.Flat S (Localization.AtPrime Q'.asIdeal) := .trans S S' _
  have : Module.Flat (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q'.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime Q.asIdeal) Q.asIdeal.primeCompl
      _).mpr ‹_›
  have : Module.FaithfullyFlat (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q'.asIdeal) := .of_flat_of_isLocalHom
  rw [Module.notMem_support_iff] at h ⊢
  have e₁ := (IsLocalizedModule.isBaseChange Q'.asIdeal.primeCompl
    (Localization.AtPrime Q'.asIdeal)
    (LocalizedModule.mkLinearMap Q'.asIdeal.primeCompl (S' ⊗[S] M))).equiv
  have e₂ := (IsLocalizedModule.isBaseChange Q.asIdeal.primeCompl
    (Localization.AtPrime Q.asIdeal) (LocalizedModule.mkLinearMap Q.asIdeal.primeCompl M)).equiv
  have : Subsingleton (Localization.AtPrime Q'.asIdeal ⊗[S] M) :=
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange S S' (Localization.AtPrime Q'.asIdeal)
      (Localization.AtPrime Q'.asIdeal) M).symm.trans e₁).subsingleton
  have : Subsingleton (Localization.AtPrime Q'.asIdeal ⊗[Localization.AtPrime Q.asIdeal]
      (Localization.AtPrime Q.asIdeal ⊗[S] M)) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q'.asIdeal) (Localization.AtPrime Q'.asIdeal) M).subsingleton
  have := Module.FaithfullyFlat.lTensor_reflects_triviality (Localization.AtPrime Q.asIdeal)
    (Localization.AtPrime Q'.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[S] M)
  exact e₂.symm.subsingleton

/-- Freeness at `Q` of a finitely presented module descends along a flat base change `S → S'`
at a prime `Q'` over `Q`. -/
lemma mem_freeLocus_of_mem_freeLocus_baseChange {S S' : Type*} [CommRing S] [CommRing S']
    [Algebra S S'] [Module.Flat S S'] (N : Type*) [AddCommGroup N] [Module S N]
    [Module.FinitePresentation S N] (Q' : PrimeSpectrum S')
    (h : Q' ∈ Module.freeLocus S' (S' ⊗[S] N)) :
    PrimeSpectrum.comap (algebraMap S S') Q' ∈ Module.freeLocus S N := by
  set Q := PrimeSpectrum.comap (algebraMap S S') Q'
  have : Q'.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver Q.asIdeal Q'.asIdeal
  have : Module.Flat S (Localization.AtPrime Q'.asIdeal) := .trans S S' _
  have : Module.Flat (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q'.asIdeal) :=
    (Module.flat_iff_of_isLocalization (Localization.AtPrime Q.asIdeal) Q.asIdeal.primeCompl
      _).mpr ‹_›
  have : Module.FaithfullyFlat (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q'.asIdeal) := .of_flat_of_isLocalHom
  rw [Module.mem_freeLocus_iff_tensor _ (Localization.AtPrime Q'.asIdeal)] at h
  rw [Module.mem_freeLocus_iff_tensor _ (Localization.AtPrime Q.asIdeal)]
  let e := (TensorProduct.AlgebraTensorModule.cancelBaseChange S S'
    (Localization.AtPrime Q'.asIdeal) (Localization.AtPrime Q'.asIdeal) N).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q'.asIdeal) (Localization.AtPrime Q'.asIdeal) N).symm
  have : Module.Flat (Localization.AtPrime Q'.asIdeal)
      (Localization.AtPrime Q'.asIdeal ⊗[Localization.AtPrime Q.asIdeal]
        (Localization.AtPrime Q.asIdeal ⊗[S] N)) := .of_linearEquiv e.symm
  have : Module.Flat (Localization.AtPrime Q.asIdeal) (Localization.AtPrime Q.asIdeal ⊗[S] N) :=
    .of_flat_tensorProduct _ _ (Localization.AtPrime Q'.asIdeal)
  exact Module.free_of_flat_of_isLocalRing

/-- If `M_Q = 0`, then `(S' ⊗_S M)_{Q'} = 0` for every prime `Q'` of `S'` over `Q`. -/
lemma notMem_support_baseChange {S S' : Type*} [CommRing S] [CommRing S'] [Algebra S S']
    (M : Type*) [AddCommGroup M] [Module S M] (Q' : PrimeSpectrum S')
    (h : PrimeSpectrum.comap (algebraMap S S') Q' ∉ Module.support S M) :
    Q' ∉ Module.support S' (S' ⊗[S] M) := by
  set Q := PrimeSpectrum.comap (algebraMap S S') Q'
  have : Q'.asIdeal.LiesOver Q.asIdeal := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver Q.asIdeal Q'.asIdeal
  rw [Module.notMem_support_iff] at h ⊢
  have e₁ := (IsLocalizedModule.isBaseChange Q'.asIdeal.primeCompl
    (Localization.AtPrime Q'.asIdeal)
    (LocalizedModule.mkLinearMap Q'.asIdeal.primeCompl (S' ⊗[S] M))).equiv
  have e₂ := (IsLocalizedModule.isBaseChange Q.asIdeal.primeCompl
    (Localization.AtPrime Q.asIdeal) (LocalizedModule.mkLinearMap Q.asIdeal.primeCompl M)).equiv
  have : Subsingleton (Localization.AtPrime Q.asIdeal ⊗[S] M) := e₂.subsingleton
  have : Subsingleton (Localization.AtPrime Q'.asIdeal ⊗[Localization.AtPrime Q.asIdeal]
      (Localization.AtPrime Q.asIdeal ⊗[S] M)) := inferInstance
  have : Subsingleton (Localization.AtPrime Q'.asIdeal ⊗[S] M) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange S (Localization.AtPrime Q.asIdeal)
      (Localization.AtPrime Q'.asIdeal) (Localization.AtPrime Q'.asIdeal) M).symm.subsingleton
  exact (e₁.symm.trans (TensorProduct.AlgebraTensorModule.cancelBaseChange S S'
    (Localization.AtPrime Q'.asIdeal) (Localization.AtPrime Q'.asIdeal) M)).subsingleton

section BaseChange

variable (R S T : Type u) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The map `T ⊗_R M → (T ⊗_R S) ⊗_S M`, `t ⊗ m ↦ (t ⊗ 1) ⊗ m`. -/
noncomputable def tensorBaseChangeAux (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] : T ⊗[R] M →ₗ[R] (T ⊗[R] S) ⊗[S] M :=
  TensorProduct.lift (((TensorProduct.mk S (T ⊗[R] S) M).restrictScalars₁₂ R R).comp
    (IsScalarTower.toAlgHom R T (T ⊗[R] S)).toLinearMap)

lemma tensorBaseChangeAux_tmul (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] (t : T) (m : M) :
    tensorBaseChangeAux R S T M (t ⊗ₜ m) = (t ⊗ₜ[R] (1 : S)) ⊗ₜ[S] m := rfl

lemma tensorBaseChangeAux_surjective (M : Type*) [AddCommGroup M] [Module S M] [Module R M]
    [IsScalarTower R S M] : Function.Surjective (tensorBaseChangeAux R S T M) := by
  intro z
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨a, rfl⟩ := ha
    obtain ⟨b, rfl⟩ := hb
    exact ⟨a + b, map_add _ _ _⟩
  | tmul y m =>
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by rw [map_zero, TensorProduct.zero_tmul]⟩
    | add a b ha hb =>
      obtain ⟨a', ha'⟩ := ha
      obtain ⟨b', hb'⟩ := hb
      exact ⟨a' + b', by rw [map_add, ha', hb', TensorProduct.add_tmul]⟩
    | tmul t s =>
      refine ⟨t ⊗ₜ (s • m), ?_⟩
      rw [tensorBaseChangeAux_tmul, ← TensorProduct.smul_tmul]
      congr 1
      rw [Algebra.smul_def]
      change (1 ⊗ₜ[R] s) * (t ⊗ₜ[R] (1 : S)) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]

/-- Flat base change for `H¹` of the cotangent complex, as an isomorphism of
`T ⊗_R S`-modules: `(T ⊗_R S) ⊗_S H¹(L_{S/R}) ≅ H¹(L_{T ⊗ S/T})`. -/
noncomputable def tensorH1CotangentEquiv [Module.Flat R T] :
    (T ⊗[R] S) ⊗[S] H1Cotangent R S ≃ₗ[T ⊗[R] S] H1Cotangent T (T ⊗[R] S) := by
  let φ := LinearMap.liftBaseChange (T ⊗[R] S) (H1Cotangent.map R T S (T ⊗[R] S))
  have hφ : (φ.restrictScalars R).comp (tensorBaseChangeAux R S T (H1Cotangent R S)) =
      ((tensorH1CotangentOfFlat R S T).toLinearMap.restrictScalars R) := by
    ext t x
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.restrictScalars_apply,
      TensorProduct.AlgebraTensorModule.curry_apply, TensorProduct.curry_apply,
      LinearEquiv.coe_coe, tensorH1CotangentOfFlat_tmul, tensorBaseChangeAux_tmul, φ,
      LinearMap.liftBaseChange_tmul]
    congr 2
  have hc := tensorBaseChangeAux_surjective R S T (H1Cotangent R S)
  refine LinearEquiv.ofBijective φ ⟨fun z₁ z₂ h ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨w₁, rfl⟩ := hc z₁
    obtain ⟨w₂, rfl⟩ := hc z₂
    have h₁ : φ (tensorBaseChangeAux R S T _ w₁) = tensorH1CotangentOfFlat R S T w₁ :=
      congr($hφ w₁)
    have h₂ : φ (tensorBaseChangeAux R S T _ w₂) = tensorH1CotangentOfFlat R S T w₂ :=
      congr($hφ w₂)
    rw [(tensorH1CotangentOfFlat R S T).injective (h₁.symm.trans (h.trans h₂))]
  · obtain ⟨w, rfl⟩ := (tensorH1CotangentOfFlat R S T).surjective y
    exact ⟨_, congr($hφ w)⟩

/-- II.4.13, pointwise affine form: let `T` be flat over `R` (`S' → S` flat), `S` finitely
presented over `R` (`Y` locally of finite presentation), and `Q'` a prime of `T ⊗_R S` (a point
`x'` of `Y'`) over the prime `Q` of `S` (its image `x`). If `T ⊗_R S` is smooth over `T` at `Q'`,
then `S` is smooth over `R` at `Q`. As `H¹` of the cotangent complex and `Ω¹` commute with flat base
change, and `S_Q → (T ⊗_R S)_{Q'}` is faithfully flat, the vanishing of `H¹` and the freeness of
`Ω¹` at `Q` descend (this replaces SGA's appeal to the criterion II.4.10 (iv)). -/
theorem isSmoothAt_of_isSmoothAt_tensorProduct [Module.Flat R T] [FinitePresentation R S]
    (Q' : Ideal (T ⊗[R] S)) [Q'.IsPrime] [IsSmoothAt T Q'] (Q : Ideal S) [Q.IsPrime]
    (hQ : Q'.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S) = Q) :
    IsSmoothAt R Q := by
  have : Module.Flat S (T ⊗[R] S) :=
    .of_linearEquiv (Algebra.TensorProduct.commRight R S T).symm.toLinearEquiv
  have hsm : (⟨Q', ‹_›⟩ : PrimeSpectrum (T ⊗[R] S)) ∈ smoothLocus T (T ⊗[R] S) := ‹_›
  rw [smoothLocus_eq_compl_support_inter] at hsm
  obtain ⟨hH1, hΩ⟩ := hsm
  have hQ' : PrimeSpectrum.comap (algebraMap S (T ⊗[R] S)) ⟨Q', ‹_›⟩ = ⟨Q, ‹_›⟩ :=
    PrimeSpectrum.ext hQ
  change (⟨Q, ‹_›⟩ : PrimeSpectrum S) ∈ smoothLocus R S
  rw [smoothLocus_eq_compl_support_inter, ← hQ']
  refine ⟨notMem_support_of_notMem_support_baseChange _ _ ?_,
    mem_freeLocus_of_mem_freeLocus_baseChange _ _ ?_⟩
  · rwa [(tensorH1CotangentEquiv R S T).support_eq]
  · rwa [Module.freeLocus_congr (KaehlerDifferential.tensorKaehlerEquiv R T S (T ⊗[R] S))]

/-- II.1.3 (ii), pointwise affine form, for a flat base change (the converse of II.4.13): if `S`
is smooth over `R` at `Q`, then `T ⊗_R S` is smooth over `T` at every prime `Q'` over `Q`. -/
theorem isSmoothAt_tensorProduct [Module.Flat R T] [FinitePresentation R S]
    (Q' : Ideal (T ⊗[R] S)) [Q'.IsPrime]
    (Q : Ideal S) [Q.IsPrime] [IsSmoothAt R Q]
    (hQ : Q'.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S) = Q) :
    IsSmoothAt T Q' := by
  have hQ' : PrimeSpectrum.comap (algebraMap S (T ⊗[R] S)) ⟨Q', ‹_›⟩ = ⟨Q, ‹_›⟩ :=
    PrimeSpectrum.ext hQ
  have hsm : (⟨Q, ‹_›⟩ : PrimeSpectrum S) ∈ smoothLocus R S := ‹_›
  rw [smoothLocus_eq_compl_support_inter, ← hQ'] at hsm
  obtain ⟨hH1, hΩ⟩ := hsm
  change (⟨Q', ‹_›⟩ : PrimeSpectrum (T ⊗[R] S)) ∈ smoothLocus T (T ⊗[R] S)
  rw [smoothLocus_eq_compl_support_inter]
  refine ⟨?_, ?_⟩
  · rw [← (tensorH1CotangentEquiv R S T).support_eq]
    exact notMem_support_baseChange _ _ hH1
  · rw [← Module.freeLocus_congr (KaehlerDifferential.tensorKaehlerEquiv R T S (T ⊗[R] S))]
    exact Module.comap_freeLocus_le hΩ

/-- II.4.13, pointwise affine form: for `T` flat over `R`, `S` finitely presented over `R` and a
prime `Q'` of `T ⊗_R S` over the prime `Q` of `S`, `T ⊗_R S` is smooth over `T` at `Q'` iff `S`
is smooth over `R` at `Q`. -/
theorem isSmoothAt_tensorProduct_iff [Module.Flat R T] [FinitePresentation R S]
    (Q' : Ideal (T ⊗[R] S)) [Q'.IsPrime] (Q : Ideal S) [Q.IsPrime]
    (hQ : Q'.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] T ⊗[R] S) = Q) :
    IsSmoothAt T Q' ↔ IsSmoothAt R Q :=
  ⟨fun _ ↦ isSmoothAt_of_isSmoothAt_tensorProduct R S T Q' Q hQ,
    fun _ ↦ isSmoothAt_tensorProduct R S T Q' Q hQ⟩

end BaseChange

section Scheme

/-- Smoothness at a point is unchanged under restriction to open subschemes of the source and
the target: for a commutative square `f₁ ≫ b = a ≫ f` with `a`, `b` open immersions, `f₁` is
smooth at `x₁` iff `f` is smooth at `a x₁`. -/
theorem mem_smoothLocus_iff_of_isOpenImmersion {X₁ X Y₁ Y : Scheme.{u}} (f₁ : X₁ ⟶ Y₁)
    (f : X ⟶ Y) (a : X₁ ⟶ X) (b : Y₁ ⟶ Y) [IsOpenImmersion a] [IsOpenImmersion b]
    (e : f₁ ≫ b = a ≫ f) [LocallyOfFinitePresentation f₁] [LocallyOfFinitePresentation f]
    (x₁ : X₁) : x₁ ∈ f₁.smoothLocus ↔ a x₁ ∈ f.smoothLocus := by
  have hP := RingHom.FormallySmooth.respectsIso
  rw [Scheme.Hom.mem_smoothLocus, Scheme.Hom.mem_smoothLocus]
  have h1 := Scheme.Hom.stalkMap_comp f₁ b x₁
  have h2 := Scheme.Hom.stalkMap_comp a f x₁
  have h3 := Scheme.Hom.stalkMap_congr_hom _ _ e x₁
  rw [h1, h2] at h3
  have k1 : RingHom.FormallySmooth (f₁.stalkMap x₁).hom ↔
      RingHom.FormallySmooth (b.stalkMap (f₁ x₁) ≫ f₁.stalkMap x₁).hom :=
    (hP.cancel_left_isIso _ _).symm
  rw [k1, h3]
  exact (hP.cancel_left_isIso _ _).trans (hP.cancel_right_isIso _ _)

set_option backward.isDefEq.respectTransparency false in
/-- On spectra, smoothness at a prime is the ring-theoretic `Algebra.IsSmoothAt`. -/
theorem mem_smoothLocus_SpecMap_iff {R S : CommRingCat.{u}} (φ : R ⟶ S)
    [LocallyOfFinitePresentation (Spec.map φ)] (q : Spec S) :
    q ∈ (Spec.map φ).smoothLocus ↔ letI := φ.hom.toAlgebra; Algebra.IsSmoothAt R q.asIdeal := by
  let := φ.hom.toAlgebra
  have : q.asIdeal.LiesOver (q.asIdeal.comap φ.hom) := ⟨rfl⟩
  let := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.comap φ.hom) q.asIdeal
  rw [Scheme.Hom.mem_smoothLocus]
  trans Algebra.FormallySmooth (Localization.AtPrime (q.asIdeal.comap φ.hom))
    (Localization.AtPrime q.asIdeal)
  · rw [← RingHom.formallySmooth_algebraMap]
    exact RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso φ q)
  · exact Algebra.FormallySmooth.iff_restrictScalars.symm

set_option backward.isDefEq.respectTransparency false in
/-- II.4.13, pointwise, affine form on spectra. -/
theorem mem_smoothLocus_of_pullback_Spec {R T A : CommRingCat.{u}} (gT : Spec T ⟶ Spec R)
    (fA : Spec A ⟶ Spec R) [Flat gT] [LocallyOfFinitePresentation fA]
    (q : ↥(pullback gT fA)) (hq : q ∈ (pullback.fst gT fA).smoothLocus) :
    pullback.snd gT fA q ∈ fA.smoothLocus := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective gT
  obtain ⟨φ, rfl⟩ := Spec.map_surjective fA
  have hψ : ψ.hom.Flat := Flat.SpecMap_iff.mp ‹_›
  have hφ' : φ.hom.FinitePresentation :=
    HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation).mp ‹_›
  algebraize [ψ.hom, φ.hom]
  let e := pullbackSpecIso R T A
  have : LocallyOfFinitePresentation
      (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] A)))) :=
    HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have hsm : e.hom q ∈ (Spec.map (CommRingCat.ofHom (algebraMap T (T ⊗[R] A)))).smoothLocus :=
    (mem_smoothLocus_iff_of_isOpenImmersion (pullback.fst _ _) _ e.hom (𝟙 _)
      (by rw [Category.comp_id]; exact (pullbackSpecIso_hom_fst' R T A).symm) q).mp hq
  rw [mem_smoothLocus_SpecMap_iff] at hsm
  rw [mem_smoothLocus_SpecMap_iff]
  have hsm' : Algebra.IsSmoothAt T (e.hom q).asIdeal :=
    (iff_of_eq (congrArg (fun I : Algebra T (T ⊗[R] A) ↦ letI := I
      Algebra.IsSmoothAt T (e.hom q).asIdeal) toAlgebra_algebraMap)).mp hsm
  have hQ : (e.hom q).asIdeal.comap
      (Algebra.TensorProduct.includeRight : A →ₐ[R] T ⊗[R] A) =
        (pullback.snd (Spec.map ψ) (Spec.map φ) q).asIdeal := by
    have := congrArg (fun φ ↦ φ q) (pullbackSpecIso_hom_snd R T A)
    simp only [Scheme.Hom.comp_apply, Spec.map_apply] at this
    exact congrArg PrimeSpectrum.asIdeal this
  exact isSmoothAt_of_isSmoothAt_tensorProduct R A T _ _ hQ

set_option backward.isDefEq.respectTransparency false in
/-- II.4.13, pointwise, for schemes: for a cartesian square `Y' = Y ×_S S'` with `S' → S` flat
and `Y → S` locally of finite presentation, if `Y'` is smooth over `S'` at `y'`, then `Y` is
smooth over `S` at the image of `y'`. -/
theorem mem_smoothLocus_of_isPullback_of_flat {Y' S' Y S : Scheme.{u}} {f' : Y' ⟶ S'}
    {g' : Y' ⟶ Y} {g : S' ⟶ S} {f : Y ⟶ S} (h : IsPullback f' g' g f) [Flat g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] {y' : Y'}
    (hy : y' ∈ f'.smoothLocus) : g' y' ∈ f.smoothLocus := by
  -- replace `Y'` by the pullback
  set p := h.isoPullback.hom y'
  have hp : p ∈ (pullback.fst g f).smoothLocus :=
    (mem_smoothLocus_iff_of_isOpenImmersion f' (pullback.fst g f) h.isoPullback.hom (𝟙 S')
      (by rw [Category.comp_id, h.isoPullback_hom_fst]) y').mp hy
  have hpf : pullback.fst g f p = f' y' := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
  have hps : pullback.snd g f p = g' y' := by
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_snd]
  -- an affine chart of `S`
  obtain ⟨R, iS, _, s₀, hs₀⟩ := S.exists_Spec_apply_eq (f (g' y'))
  -- an affine chart of `Y` over it
  obtain ⟨yb, hyb⟩ : g' y' ∈ Set.range (pullback.fst f iS) := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨s₀, hs₀⟩
  obtain ⟨A, jY, _, a₀, ha₀⟩ := (pullback f iS).exists_Spec_apply_eq yb
  -- an affine chart of `S'` over it
  obtain ⟨sb, hsb⟩ : f' y' ∈ Set.range (pullback.fst g iS) := by
    rw [Scheme.Pullback.range_fst]
    refine ⟨s₀, hs₀.trans ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h.w]
  obtain ⟨T, jS, _, t₀, ht₀⟩ := (pullback g iS).exists_Spec_apply_eq sb
  have eY : (jY ≫ pullback.snd f iS) ≫ iS = (jY ≫ pullback.fst f iS) ≫ f := by
    simp [pullback.condition]
  have eT : (jS ≫ pullback.snd g iS) ≫ iS = (jS ≫ pullback.fst g iS) ≫ g := by
    simp [pullback.condition]
  have : Flat (jS ≫ pullback.snd g iS) := inferInstance
  -- the pullback of the charts is an open subscheme of `Y ×_S S'` containing `p`
  let m := pullback.map (jS ≫ pullback.snd g iS) (jY ≫ pullback.snd f iS) g f
    (jS ≫ pullback.fst g iS) (jY ≫ pullback.fst f iS) iS eT eY
  obtain ⟨q, hqp⟩ : p ∈ Set.range m := by
    rw [Scheme.Pullback.range_map]
    refine ⟨⟨t₀, ?_⟩, ⟨a₀, ?_⟩⟩
    · rw [hpf, Scheme.Hom.comp_apply, ht₀, hsb]
    · rw [hps, Scheme.Hom.comp_apply, ha₀, hyb]
  have hq : q ∈ (pullback.fst (jS ≫ pullback.snd g iS) (jY ≫ pullback.snd f iS)).smoothLocus :=
    (mem_smoothLocus_iff_of_isOpenImmersion _ (pullback.fst g f) m (jS ≫ pullback.fst g iS)
      (pullback.lift_fst _ _ _).symm q).mpr (hqp ▸ hp)
  have hqa := mem_smoothLocus_of_pullback_Spec _ _ q hq
  have := (mem_smoothLocus_iff_of_isOpenImmersion (jY ≫ pullback.snd f iS) f
    (jY ≫ pullback.fst f iS) iS eY _).mp hqa
  rwa [← Scheme.Hom.comp_apply,
    show pullback.snd _ _ ≫ jY ≫ pullback.fst f iS = m ≫ pullback.snd g f from
      (pullback.lift_snd _ _ _).symm, Scheme.Hom.comp_apply, hqp, hps] at this

/-- II.4.13, pointwise, for schemes: let `Y' = Y ×_S S'` with `S' → S` flat and `Y → S` locally
of finite presentation, `y'` a point of `Y'` and `y` its image in `Y`. Then `Y'` is smooth over `S'`
at `y'` iff `Y` is smooth over `S` at `y`. -/
theorem mem_smoothLocus_iff_of_isPullback_of_flat {Y' S' Y S : Scheme.{u}} {f' : Y' ⟶ S'}
    {g' : Y' ⟶ Y} {g : S' ⟶ S} {f : Y ⟶ S} (h : IsPullback f' g' g f) [Flat g]
    [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation f'] (y' : Y') :
    y' ∈ f'.smoothLocus ↔ g' y' ∈ f.smoothLocus :=
  ⟨mem_smoothLocus_of_isPullback_of_flat h, mem_smoothLocus_of_isPullback h⟩

/-- II.4.13, global form: if `S' → S` is flat and surjective and `Y' = Y ×_S S'`, with `Y → S`
locally of finite presentation, then `Y` is smooth over `S` iff `Y'` is smooth over `S'` (no
quasi-compactness is needed, as in SGA, thanks to the pointwise form). -/
theorem smooth_iff_of_isPullback_of_flat_of_surjective {Y' S' Y S : Scheme.{u}} {f' : Y' ⟶ S'}
    {g' : Y' ⟶ Y} {g : S' ⟶ S} {f : Y ⟶ S} (h : IsPullback f' g' g f) [Flat g] [Surjective g]
    [LocallyOfFinitePresentation f] : Smooth f' ↔ Smooth f := by
  have : LocallyOfFinitePresentation f' := MorphismProperty.of_isPullback h.flip inferInstance
  refine ⟨fun _ ↦ ?_, fun _ ↦ MorphismProperty.of_isPullback h.flip inferInstance⟩
  have : Surjective g' := MorphismProperty.of_isPullback h inferInstance
  rw [← Scheme.Hom.smoothLocus_eq_top_iff]
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨y', rfl⟩ := g'.surjective y
  exact mem_smoothLocus_of_isPullback_of_flat h (f'.smoothLocus_eq_top ▸ trivial)

end Scheme

end SGA.SGA1.ExposeII
