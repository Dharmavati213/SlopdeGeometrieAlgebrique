/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeX.Purity
import SGA.SGA1.ExposeI.Permanence
import SGA.Foundations.CommAlg.Normal
import SGA.Foundations.CommAlg.PurityScheme

/-!
# SGA 1, Exposé X: étale coverings of a normal scheme and dense opens

For the birational invariance X.3.4 we need, besides purity X.3.3, that restricting étale
coverings of an integral normal scheme `X` to a nonempty open `U` is fully faithful
(`fullyFaithful_pullback_of_isNormalScheme`). This is I.10.2 in scheme form: an étale covering `Y`
of `X` is the relative normalization of `X` in `Y ×_X U`
(`isIso_normalizationDesc_pullbackFst_of_isNormalScheme`). Over an affine open `V` of `X` meeting
`U` in some `D(a)`, the ring `B = Γ(Y_V)` is étale over the normal domain `A = Γ(V)`, hence
integrally closed in `B ⊗_A Frac(A)` (I.9.5), and so every element of `Γ(Y_{V ∩ U}) ⊆ B[1/a]`
integral over `A` lies in `B`.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry TensorProduct

namespace SGA.SGA1.ExposeX

section Algebra

variable {A B Ba : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
  [Algebra A B] [Algebra.Smooth A B] [CommRing Ba] [Algebra B Ba] [Algebra A Ba]
  [IsScalarTower A B Ba]

/-- Let `B` be smooth (e.g. étale) over an integrally closed domain `A` and `a ∈ A` nonzero. An
element of `B[1/a]` integral over `A` lies in `B` (I.9.5: `B` is integrally closed in
`B ⊗_A Frac(A)`). -/
theorem mem_range_of_isIntegral_of_isLocalization_away {a : A} (ha : a ≠ 0)
    [IsLocalization.Away (algebraMap A B a) Ba] {z : Ba} (hz : IsIntegral A z) :
    z ∈ Set.range (algebraMap B Ba) := by
  let K := FractionRing A
  let L := B ⊗[A] K
  have hcl : IsIntegrallyClosedIn B L := ExposeI.isIntegrallyClosedIn_tensor_fractionRing K
  have hunit : IsUnit (IsScalarTower.toAlgHom A B L (algebraMap A B a)) := by
    rw [IsScalarTower.toAlgHom_apply, ← IsScalarTower.algebraMap_apply,
      ← (Algebra.TensorProduct.includeRight : K →ₐ[A] L).commutes]
    refine IsUnit.map _ (Ne.isUnit ?_)
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  let ψ : Ba →ₐ[A] L := IsLocalization.Away.liftAlgHom (algebraMap A B a) hunit
  have hψ : ∀ b, ψ (algebraMap B Ba b) = algebraMap B L b := fun b ↦
    IsLocalization.Away.lift_eq _ hunit b
  have hψinj : Function.Injective ψ := by
    refine (IsLocalization.injective_iff_map_algebraMap_eq
      (Submonoid.powers (algebraMap A B a)) (ψ : Ba →+* L)).mpr fun b b' ↦
        ⟨fun h ↦ by rw [h], fun h ↦ ?_⟩
    change ψ _ = ψ _ at h
    rw [hψ, hψ] at h
    rw [ExposeI.injective_algebraMap_tensor_fractionRing K h]
  obtain ⟨b, hb⟩ := hcl.isIntegral_iff.mp ((hz.map ψ).tower_top (A := B))
  exact ⟨b, hψinj (by rw [hψ, hb])⟩

end Algebra

section Scheme

variable {X : Scheme.{u}} [IsIntegral X] (hX : IsNormalScheme X)
include hX

/-- On an integral normal scheme, the sections over a nonempty affine open form an integrally
closed domain. -/
lemma isIntegrallyClosed_of_isAffineOpen {V : X.Opens} (hV : IsAffineOpen V) [Nonempty V] :
    IsIntegrallyClosed Γ(X, V) := by
  refine IsIntegrallyClosed.of_localization_maximal fun p _ _ ↦ ?_
  exact (ExposeI.isDomain_and_isIntegrallyClosed_of_ringEquiv
    (hV.localizationAtPrimeEquivStalk ⟨p, inferInstance⟩).symm
    (hX (hV.fromSpec ⟨p, inferInstance⟩))).2

variable {U : X.Opens} (hU : (U : Set X).Nonempty)
include hU

/-- Let `y : Y ⟶ X` be finite étale over an integral normal scheme, `U` a nonempty open and `V` a
nonempty affine open of `X`. Then `Γ(y⁻¹V) → Γ(y⁻¹V ∩ y⁻¹U)` is injective, and its image contains
every section integral over `Γ(V)`. -/
theorem injective_restrict_and_mem_range {V : X.Opens} (hV : IsAffineOpen V)
    (hVne : (V : Set X).Nonempty) {Y : Scheme.{u}} (y : Y ⟶ X) [IsFinite y] [Etale y] :
    Function.Injective (Y.presheaf.map (homOfLE inf_le_left : y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U ⟶ y ⁻¹ᵁ V).op) ∧
      ∀ z, (y.app V ≫ Y.presheaf.map
        (homOfLE inf_le_left : y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U ⟶ y ⁻¹ᵁ V).op).hom.IsIntegralElem z →
        z ∈ Set.range (Y.presheaf.map (homOfLE inf_le_left : y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U ⟶ y ⁻¹ᵁ V).op) := by
  have : Nonempty V := hVne.to_subtype
  have := isIntegrallyClosed_of_isAffineOpen hX hV
  obtain ⟨x, hxV, hxU⟩ := nonempty_preirreducible_inter V.2 U.2 hVne hU
  obtain ⟨a, haU, hxa⟩ := hV.exists_basicOpen_le ⟨x, hxU⟩ hxV
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hxa
    exact hxa
  have hD : Y.basicOpen (y.app V a) ≤ y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U := by
    rw [← Scheme.preimage_basicOpen]
    exact le_inf (y.preimage_mono (X.basicOpen_le _)) (y.preimage_mono haU)
  have hs := injective_restrict_preimage_basicOpen U hV (mem_nonZeroDivisors_of_ne_zero ha0) y hD
  have hYV : IsAffineOpen (y ⁻¹ᵁ V) := hV.preimage y
  let r := Y.presheaf.map (homOfLE inf_le_left : y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U ⟶ y ⁻¹ᵁ V).op
  let s := Y.presheaf.map (homOfLE hD).op
  let B := Γ(Y, y ⁻¹ᵁ V)
  let Ba := Γ(Y, Y.basicOpen (y.app V a))
  have hrs : ∀ b, s (r b) = algebraMap B Ba b := fun b ↦ by
    change (Y.presheaf.map _) ((Y.presheaf.map _) b) = (Y.presheaf.map _) b
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  let _ : Algebra Γ(X, V) B := (y.app V).hom.toAlgebra
  let _ : Algebra Γ(X, V) Ba := ((algebraMap B Ba).comp (algebraMap Γ(X, V) B)).toAlgebra
  have : IsScalarTower Γ(X, V) B Ba := IsScalarTower.of_algebraMap_eq' rfl
  have : IsLocalization.Away (algebraMap Γ(X, V) B a) Ba :=
    hYV.isLocalization_basicOpen (y.app V a)
  have het : (y.app V).hom.Etale := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Etale) y inferInstance ⟨V, hV⟩ ⟨_, hYV⟩ le_rfl
  have : Algebra.Etale Γ(X, V) B := het
  refine ⟨fun b b' hbb' ↦ ?_, fun z hz ↦ ?_⟩
  · have hreg : algebraMap Γ(X, V) B a ∈ nonZeroDivisors B := by
      have := (Module.Flat.isSMulRegular_of_nonZeroDivisors (M := B)
        (mem_nonZeroDivisors_of_ne_zero ha0))
      exact mem_nonZeroDivisors_iff_right.mpr fun c hc ↦
        this.right_eq_zero_of_smul (by rw [Algebra.smul_def, mul_comm, hc])
    have hinj : Function.Injective (algebraMap B Ba) :=
      IsLocalization.injective Ba (M := Submonoid.powers _) (Submonoid.powers_le.mpr hreg)
    apply hinj
    rw [← hrs, ← hrs, hbb']
  · have hcomp : algebraMap Γ(X, V) Ba = s.hom.comp (y.app V ≫ r).hom :=
      RingHom.ext fun c ↦ (hrs _).symm
    have hz' : IsIntegral Γ(X, V) (s z) := by
      obtain ⟨p, hpm, hp⟩ := hz
      refine ⟨p, hpm, ?_⟩
      rw [hcomp, ← Polynomial.hom_eval₂, hp, map_zero]
    obtain ⟨b, hb⟩ := mem_range_of_isIntegral_of_isLocalization_away (B := B) ha0 hz'
    exact ⟨b, hs (by rw [hrs, hb])⟩

variable [IsLocallyNoetherian X]

/-- I.10.2 in scheme form: an étale covering `Y` of an integral normal locally noetherian scheme `X`
is the relative normalization of `X` in `Y ×_X U`, for any nonempty open `U`. -/
theorem isIso_normalizationDesc_pullbackFst_of_isNormalScheme {Y : Scheme.{u}} (y : Y ⟶ X)
    [IsFinite y] [Etale y] :
    IsIso ((pullback.fst y U.ι ≫ y).normalizationDesc (pullback.fst y U.ι) y rfl) := by
  let j := pullback.fst y U.ι
  let ι := {V : X.affineOpens // ((V : X.Opens) : Set X).Nonempty}
  have key : ∀ V : ι, Function.Injective (j.app (y ⁻¹ᵁ V.1.1)) ∧
      ∀ z, ((j ≫ y).app V.1.1).hom.IsIntegralElem z → z ∈ Set.range (j.app (y ⁻¹ᵁ V.1.1)) := by
    rintro ⟨⟨V, hV⟩, hVne⟩
    have h1 := Scheme.Hom.appLE_appIso_inv j (le_refl (j ⁻¹ᵁ y ⁻¹ᵁ V))
    rw [← Scheme.Hom.app_eq_appLE] at h1
    have hO : j ''ᵁ (j ⁻¹ᵁ y ⁻¹ᵁ V) = y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_pullbackFst,
        Scheme.Opens.opensRange_ι, inf_comm]
    have key' : ∀ (O : Y.Opens) (hO' : O ≤ y ⁻¹ᵁ V), O = y ⁻¹ᵁ V ⊓ y ⁻¹ᵁ U →
        Function.Injective (Y.presheaf.map (homOfLE hO').op) ∧
        ∀ z, (y.app V ≫ Y.presheaf.map (homOfLE hO').op).hom.IsIntegralElem z →
          z ∈ Set.range (Y.presheaf.map (homOfLE hO').op) := by
      rintro O hO' rfl
      exact injective_restrict_and_mem_range hX hU hV hVne y
    obtain ⟨hinj, hrange⟩ := key' _ _ hO
    set ρ := Y.presheaf.map (homOfLE ((j.image_mono (le_refl (j ⁻¹ᵁ y ⁻¹ᵁ V))).trans
      (j.image_preimage_eq_opensRange_inf (y ⁻¹ᵁ V) ▸ inf_le_right))).op with hρ
    set g := (j.appIso (j ⁻¹ᵁ y ⁻¹ᵁ V)).inv
    have hj : j.app (y ⁻¹ᵁ V) = ρ ≫ (j.appIso (j ⁻¹ᵁ y ⁻¹ᵁ V)).hom :=
      (Iso.comp_inv_eq _).mp h1
    have hbij := ConcreteCategory.bijective_of_isIso (j.appIso (j ⁻¹ᵁ y ⁻¹ᵁ V)).hom
    refine ⟨?_, fun z hz ↦ ?_⟩
    · rw [hj, ConcreteCategory.coe_comp]
      exact hbij.1.comp hinj
    · have hz' : (y.app V ≫ ρ).hom.IsIntegralElem (g z) := by
        obtain ⟨p, hpm, hp⟩ := hz
        refine ⟨p, hpm, ?_⟩
        have hp' : Polynomial.eval₂ (y.app V ≫ j.app (y ⁻¹ᵁ V)).hom z p = 0 := hp
        have := Polynomial.hom_eval₂ p (y.app V ≫ j.app (y ⁻¹ᵁ V)).hom g.hom z
        rw [hp', map_zero] at this
        rw [← h1, ← Category.assoc, CommRingCat.hom_comp]
        exact this.symm
      obtain ⟨b, hb⟩ := hrange _ hz'
      refine ⟨b, ?_⟩
      rw [hj, CommRingCat.comp_apply, hb]
      exact (j.appIso (j ⁻¹ᵁ y ⁻¹ᵁ V)).inv_hom_id_apply z
  refine Scheme.Hom.isIso_normalizationDesc_of_injective j y (fun V : ι ↦ V.1.1)
    (fun V ↦ V.1.2) ?_ (fun V ↦ (key V).1) (fun V ↦ (key V).2)
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, ⟨x, hxV⟩⟩, hxV⟩

/-- Restricting étale coverings of an integral normal locally noetherian scheme `X` to a nonempty
open `U` is faithful. -/
theorem faithful_pullback_of_isNormalScheme : (FEt.pullback U.ι).Faithful :=
  AlgebraicGeometry.faithful_pullback_of_isIso_normalizationDesc fun y _ _ ↦
    isIso_normalizationDesc_pullbackFst_of_isNormalScheme hX hU y

/-- Restricting étale coverings of an integral normal locally noetherian scheme `X` to a nonempty
open `U` is full. -/
theorem full_pullback_of_isNormalScheme : (FEt.pullback U.ι).Full :=
  AlgebraicGeometry.full_pullback_of_isIso_normalizationDesc fun y _ _ ↦
    isIso_normalizationDesc_pullbackFst_of_isNormalScheme hX hU y

/-- Restricting étale coverings of an integral normal locally noetherian scheme `X` to a nonempty
open `U` is fully faithful (I.10.2, I.10.3 in scheme form). -/
noncomputable def fullyFaithful_pullback_of_isNormalScheme : (FEt.pullback U.ι).FullyFaithful :=
  have := faithful_pullback_of_isNormalScheme hX hU
  have := full_pullback_of_isNormalScheme hX hU
  .ofFullyFaithful _

end Scheme

/-- A regular scheme is normal. -/
lemma isNormalScheme_of_isRegularScheme {X : Scheme.{u}} (hX : IsRegularScheme X) :
    IsNormalScheme X := fun x ↦
  have := hX x
  ⟨inferInstance, inferInstance⟩

end SGA.SGA1.ExposeX
