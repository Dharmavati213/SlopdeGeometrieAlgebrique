/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.BaseChangeCover
import SGA.Foundations.Cohomology.GeometricConnectedness
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The Stein factorization of a proper flat morphism with geometrically reduced fibres is étale

EGA III 7.8.10 (i) (Stacks, the étaleness of the Stein factorization; SGA 1 X.1.2): let
`f : X ⟶ Y` be proper and flat with geometrically reduced fibres, `Y` locally noetherian. Then
`f_* 𝒪_X` is a finite étale `𝒪_Y`-algebra, i.e. the finite part `Y' = Spec_Y f_* 𝒪_X ⟶ Y` of the
Stein factorization (mathlib's relative normalization `f.normalization`) is étale:
`AlgebraicGeometry.etale_fromNormalization`.

* `AlgebraicGeometry.etale_specStructureRingHom_of_isLocalRing`: over a noetherian local ring
  `A`, `A → Γ(X, 𝒪_X)` is finite étale (the local theorem `CohomologyAux.BaseChangeData.etale`,
  with the Čech data of `CohomologyAux.baseChangeData`); moreover `Γ(X, 𝒪_X)` is free
  (`free_sections_of_isLocalRing`).
* `CohomologyAux.etale_of_forall_isPushout`: a finite ring map `A → B`, `A` noetherian, is étale
  if its base changes to the localizations of `A` at maximal ideals are.
* `AlgebraicGeometry.etale_app_of_isProper`: `Γ(Y, U) → Γ(X, f⁻¹ U)` is étale for `U` affine, by
  flat base change to `Spec 𝒪_{Y,y}` (`CohomologyAux.isPushout_app_pullback_snd`); hence
  `f_* 𝒪_X` is locally free (`projective_app_of_isProper`).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite TensorProduct

namespace AlgebraicGeometry.CohomologyAux

section Local

variable {A : CommRingCat.{u}} [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A)

omit [IsLocalRing A] [IsNoetherianRing A] in
lemma structMapV_top : structMapV f ⊤ = f.specStructureRingHom := by
  ext a
  rw [structMapV_eq_map, presheaf_map_self]

/-- The local theorem for schemes: the Čech data of a finite affine cover with affine
intersections satisfy `BaseChangeData`, so `Γ(X, 𝒪_X)` is finite étale and free over `A`. -/
theorem etale_and_free_of_isLocalRing [IsProper f] [Flat f] [GeometricallyReduced f] :
    f.specStructureRingHom.Etale ∧
      (letI := f.specStructureRingHom.toAlgebra; Module.Free A Γ(X, ⊤)) := by
  let _ : ∀ V : X.Opens, Algebra A Γ(X, V) := fun V ↦ (structMapV f V).toAlgebra
  have hA : ∀ V : X.Opens, algebraMap A Γ(X, V) = structMapV f V := fun V ↦ rfl
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have := isAffineHom_diagonal_of_isSeparated f
  obtain ⟨n, U, hU, hUa⟩ := exists_cechCover' X
  have hUa₂ : ∀ i j, IsAffineOpen (U i ⊓ U j) := fun i j ↦ (hUa i).inf (hUa j)
  have H := baseChangeData f hA U hU hUa hUa₂
  have : Module.Finite A Γ(X, ⊤) := finite_sections_top f hA
  have : Module.Flat A (∀ i, Γ(X, U i)) := flat_pi_sections f hA U hUa
  have : Module.Flat A (∀ p : Fin n × Fin n, Γ(X, U p.1 ⊓ U p.2)) :=
    flat_pi_sections f hA _ fun p ↦ hUa₂ p.1 p.2
  rw [← structMapV_top]
  exact ⟨H.etale, H.free⟩

end Local

section Global

/-- **Étaleness is local on the base, via localizations at maximal ideals.** Let `φ : A → B` be
finite with `A` noetherian. If for every maximal ideal `P` of `A` there is a pushout square
`A → A_P`, `B → D = A_P ⊗_A B` with `A_P → D` étale, then `φ` is étale. -/
theorem etale_of_forall_isPushout {A B : CommRingCat.{u}} [IsNoetherianRing A] (φ : A ⟶ B)
    (hφ : φ.hom.Finite)
    (H : ∀ (P : Ideal A) [P.IsMaximal], ∃ (A' D : CommRingCat.{u}) (ι : A ⟶ A') (ψ : A' ⟶ D)
      (β : B ⟶ D), IsPushout φ ι β ψ ∧
        (letI := ι.hom.toAlgebra; IsLocalization.AtPrime A' P) ∧ ψ.hom.Etale) :
    φ.hom.Etale := by
  let _ : Algebra A B := φ.hom.toAlgebra
  -- the base change to a maximal ideal, as algebras
  have key : ∀ (P : Ideal A) [P.IsMaximal], ∃ (A' D : CommRingCat.{u}) (_ : Algebra A A')
      (_ : Algebra A' D) (_ : Algebra B D) (_ : Algebra A D) (_ : IsScalarTower A A' D)
      (_ : IsScalarTower A B D), IsLocalization.AtPrime A' P ∧ Algebra.IsPushout A A' B D ∧
        Module.Flat A' D ∧ Algebra.FormallyUnramified A' D := by
    intro P _
    obtain ⟨A', D, ι, ψ, β, hpush, hloc, hét⟩ := H P
    let _ : Algebra A A' := ι.hom.toAlgebra
    let _ : Algebra A' D := ψ.hom.toAlgebra
    let _ : Algebra B D := β.hom.toAlgebra
    let _ : Algebra A D := (ψ.hom.comp ι.hom).toAlgebra
    have : IsScalarTower A A' D := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq fun a ↦
      (ConcreteCategory.congr_hom hpush.w a).symm
    have hP' : Algebra.IsPushout A A' B D :=
      CommRingCat.isPushout_iff_isPushout.mp hpush.flip
    obtain ⟨hflat, hfu, -⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp hét
    exact ⟨A', D, _, _, _, _, ‹_›, ‹_›, hloc, hP', hflat, hfu⟩
  rw [RingHom.Etale.iff_flat_and_formallyUnramified]
  refine ⟨?_, ?_, RingHom.FinitePresentation.of_finiteType.mp hφ.finiteType⟩
  · -- flatness is local on `A`
    change Module.Flat A B
    refine Module.flat_of_localized_maximal B fun P _ ↦ ?_
    obtain ⟨A', D, _, _, _, _, _, _, hloc, hP', hflat, -⟩ := key P
    have : IsLocalizedModule P.primeCompl (IsScalarTower.toAlgHom A B D).toLinearMap :=
      (isLocalizedModule_iff_isBaseChange P.primeCompl A' _).mpr hP'.out
    have : Module.Flat A A' := IsLocalization.flat A' P.primeCompl
    have : Module.Flat A D := Module.Flat.trans A A' D
    exact Module.Flat.of_linearEquiv (IsLocalizedModule.iso P.primeCompl
      (IsScalarTower.toAlgHom A B D).toLinearMap)
  · -- `Ω_{B/A}` vanishes at every maximal ideal of `A`
    change Algebra.FormallyUnramified A B
    refine ⟨subsingleton_of_forall_eq 0 fun x ↦ ?_⟩
    let J : Ideal A := LinearMap.ker (LinearMap.toSpanSingleton A Ω[B⁄A] x)
    by_cases hJ : J = ⊤
    · have : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
      simpa [J] using this
    obtain ⟨P, hPm, hJP⟩ := Ideal.exists_le_maximal J hJ
    obtain ⟨A', D, _, _, _, _, _, _, hloc, hP', -, hfu⟩ := key P
    have : IsLocalization (Algebra.algebraMapSubmonoid B P.primeCompl) D :=
      (Algebra.isLocalization_iff_isPushout P.primeCompl A').mpr hP'.symm
    have hloc' : IsLocalizedModule (Algebra.algebraMapSubmonoid B P.primeCompl)
        (TensorProduct.mk B D Ω[B⁄A] 1) :=
      (isLocalizedModule_iff_isBaseChange _ D _).mpr (TensorProduct.isBaseChange B Ω[B⁄A] D)
    have hsub : Subsingleton (D ⊗[B] Ω[B⁄A]) :=
      (KaehlerDifferential.tensorKaehlerEquiv A A' B D).toEquiv.subsingleton
    obtain ⟨⟨_, s, hs, rfl⟩, hsx⟩ := (IsLocalizedModule.eq_zero_iff
      (Algebra.algebraMapSubmonoid B P.primeCompl) (TensorProduct.mk B D Ω[B⁄A] 1)).mp
      (Subsingleton.elim _ _)
    have : s ∈ J := by
      change s • x = 0
      rw [← algebraMap_smul B s x]
      exact hsx
    exact absurd (hJP this) hs

end Global

section Stalk

variable {Y : Scheme.{u}}

/-- Every point of `Spec 𝒪_{Y,y}` maps into every open neighbourhood of `y`. -/
lemma le_preimage_fromSpecStalk {y : Y} {U : Y.Opens} (hy : y ∈ U) :
    ⊤ ≤ Y.fromSpecStalk y ⁻¹ᵁ U := by
  intro z _
  have : Y.fromSpecStalk y z ⤳ y := by
    have h : Y.fromSpecStalk y z ∈ Set.range (Y.fromSpecStalk y) := ⟨z, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  exact this.mem_open U.isOpen hy

end Stalk

end AlgebraicGeometry.CohomologyAux

namespace AlgebraicGeometry

open CohomologyAux

section Local

variable {A : CommRingCat.{u}} [IsLocalRing A] [IsNoetherianRing A] {X : Scheme.{u}}
  (f : X ⟶ Spec A)

/-- **EGA III 7.8.10 (i), local form**: for `f : X ⟶ Spec A` proper and flat with geometrically
reduced fibres over a noetherian local ring, `Γ(X, 𝒪_X)` is a finite étale `A`-algebra. -/
theorem etale_specStructureRingHom_of_isLocalRing [IsProper f] [Flat f]
    [GeometricallyReduced f] : f.specStructureRingHom.Etale :=
  (etale_and_free_of_isLocalRing f).1

/-- **Cohomology and base change in degree `0`, local form** (EGA III 7.8.6, 7.8.7): under the
hypotheses of `etale_specStructureRingHom_of_isLocalRing`, `Γ(X, 𝒪_X)` is a free `A`-module. -/
theorem free_sections_of_isLocalRing [IsProper f] [Flat f] [GeometricallyReduced f] :
    letI := f.specStructureRingHom.toAlgebra
    Module.Free A Γ(X, ⊤) :=
  (etale_and_free_of_isLocalRing f).2

end Local

section Proper

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **EGA III 7.8.10 (i), affine form**: for `f : X ⟶ Y` proper and flat with geometrically
reduced fibres and `Y` locally noetherian, `Γ(Y, U) → Γ(X, f⁻¹ U)` is finite étale for every
affine open `U`. By flat base change (`isPushout_app_pullback_snd`) its base change to `𝒪_{Y,y}`
is `𝒪_{Y,y} → Γ(X ×_Y Spec 𝒪_{Y,y}, 𝒪)`, which is étale by the local theorem. -/
theorem etale_app_of_isProper [IsProper f] [Flat f] [GeometricallyReduced f]
    [IsLocallyNoetherian Y] {U : Y.Opens} (hU : IsAffineOpen U) : (f.app U).hom.Etale := by
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  refine etale_of_forall_isPushout (f.app U) (finite_app_of_isProper f hU) fun P _ ↦ ?_
  let p : PrimeSpectrum Γ(Y, U) := ⟨P, inferInstance⟩
  set y := hU.fromSpec p
  have hy : y ∈ U := by
    rw [← SetLike.mem_coe, ← hU.range_fromSpec]
    exact ⟨p, rfl⟩
  let ι := Y.fromSpecStalk y
  have hιU := le_preimage_fromSpecStalk hy
  refine ⟨Γ(Spec (Y.presheaf.stalk y), ⊤), Γ(pullback f ι, pullback.snd f ι ⁻¹ᵁ ⊤),
    ι.appLE U ⊤ hιU, (pullback.snd f ι).app ⊤, _,
    isPushout_app_pullback_snd f ι hU (isAffineOpen_top _) hιU, ?_, ?_⟩
  · -- `Γ(Spec 𝒪_{Y,y}, ⊤)` is the localization of `Γ(Y, U)` at `P`
    let _ := TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
    have hloc := hU.isLocalization_stalk' p hy
    have e : (ι.appLE U ⊤ hιU).hom =
        (Scheme.ΓSpecIso (Y.presheaf.stalk y)).symm.commRingCatIsoToRingEquiv.toRingHom.comp
          (Y.presheaf.germ U y hy).hom := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hy]
      ext a
      change (Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE hιU).op
        ((Spec (Y.presheaf.stalk y)).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv (Y.presheaf.germ U y hy a))) = _
      rw [presheaf_map_map, presheaf_map_self]
      rfl
    have := (IsLocalization.isLocalization_iff_of_ringEquiv P.primeCompl
      (Scheme.ΓSpecIso (Y.presheaf.stalk y)).symm.commRingCatIsoToRingEquiv).mp hloc
    convert this
    exact e
  · -- the base change is étale by the local theorem
    have h := etale_specStructureRingHom_of_isLocalRing (pullback.snd f ι)
    have e : ((pullback.snd f ι).app ⊤).hom =
        (pullback.snd f ι).specStructureRingHom.comp
          (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom.hom := by
      rw [Scheme.Hom.specStructureRingHom, ← CommRingCat.hom_comp, ← Category.assoc,
        Iso.hom_inv_id, Category.id_comp]
      rfl
    rw [e]
    exact RingHom.Etale.stableUnderComposition _ _
      (.of_bijective (ConcreteCategory.bijective_of_isIso _)) h

/-- **`f_* 𝒪_X` is locally free** (EGA III 7.8.10 (i), 7.8.6): under the hypotheses of
`etale_app_of_isProper`, `Γ(X, f⁻¹ U)` is a finite projective `Γ(Y, U)`-module for `U` affine. -/
theorem projective_app_of_isProper [IsProper f] [Flat f] [GeometricallyReduced f]
    [IsLocallyNoetherian Y] {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Module.Projective Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  let _ := (f.app U).hom.toAlgebra
  have : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := finite_app_of_isProper f hU
  obtain ⟨hflat, -, -⟩ := RingHom.Etale.iff_flat_and_formallyUnramified.mp
    (etale_app_of_isProper f hU)
  have : Module.Flat Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := hflat
  have : Module.FinitePresentation Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
    Module.finitePresentation_of_finite _ _
  exact Module.Flat.projective_of_finitePresentation

/-- **The Stein factorization of a proper flat morphism with geometrically reduced fibres is
étale** (EGA III 7.8.10 (i); SGA 1 X.1.2): for `f : X ⟶ Y` proper and flat with geometrically
reduced fibres, `Y` locally noetherian, the relative normalization `Y' = Spec_Y f_* 𝒪_X ⟶ Y` (the
finite part of the Stein factorization, `AlgebraicGeometry.steinFactorizationStatement`) is
étale. -/
theorem etale_fromNormalization [IsProper f] [Flat f] [GeometricallyReduced f]
    [IsLocallyNoetherian Y] : Etale f.fromNormalization := by
  rw [HasRingHomProperty.iff_appLE (P := @Etale)]
  intro U V e
  have hrestr :
      (Scheme.Hom.appLE (𝟙 f.normalization) (f.fromNormalization ⁻¹ᵁ U) V e).hom.Etale :=
    HasRingHomProperty.appLE (P := @Etale) (𝟙 f.normalization) inferInstance
      ⟨_, U.2.preimage _⟩ V e
  have happ : (f.fromNormalization.app U).hom.Etale := by
    let _ := (f.app U).hom.toAlgebra
    have hint := isIntegral_app_of_isProper f U.2
    rw [Scheme.Hom.fromNormalization_app f U.2, CommRingCat.hom_comp]
    refine RingHom.Etale.stableUnderComposition _ _ ?_
      (.of_bijective (ConcreteCategory.bijective_of_isIso _))
    -- `integralClosure = Γ(X, f⁻¹ U)`
    let v : integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U) ≃+* Γ(X, f ⁻¹ᵁ U) :=
      RingEquiv.ofBijective (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom
        ⟨Subtype.val_injective, fun x ↦ ⟨⟨x, Algebra.IsIntegral.isIntegral x⟩, rfl⟩⟩
    have e' : (CommRingCat.ofHom (algebraMap Γ(Y, U)
        (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)))).hom =
        v.symm.toRingHom.comp (f.app U).hom := by
      ext a
      change algebraMap Γ(Y, U) Γ(X, f ⁻¹ᵁ U) a = v (v.symm ((f.app U) a))
      rw [RingEquiv.apply_symm_apply]
      rfl
    rw [e']
    exact RingHom.Etale.stableUnderComposition _ _ (etale_app_of_isProper f U.2)
      (.of_bijective v.symm.bijective)
  have : (f.fromNormalization.appLE U V e).hom =
      (Scheme.Hom.appLE (𝟙 f.normalization) (f.fromNormalization ⁻¹ᵁ U) V e).hom.comp
        (f.fromNormalization.app U).hom := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_app, CommRingCat.hom_comp]
    rfl
  rw [this]
  exact RingHom.Etale.stableUnderComposition _ _ happ hrestr

end Proper

end AlgebraicGeometry
