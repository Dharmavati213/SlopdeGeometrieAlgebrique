/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.GlobalExtension
import SGA.SGA1.ExposeIII.Thickening
import SGA.SGA1.ExposeIII.SmoothLift

/-!
# SGA 1, Exposé III, 6.8: uniqueness of smooth lifts of affine schemes

Under the conditions of III.4.1 (`Y` locally noetherian, `Y₀ ⊆ Y` a closed subscheme with the
same underlying space), SGA 1 III.6.8 shows that a smooth `Y₀`-scheme `X₀` which is affine lifts
to a smooth `Y`-scheme `X`, unique up to (non-unique) isomorphism.

`exists_iso_of_smooth_of_isAffine` is the uniqueness: two smooth lifts `X₁`, `X₂` of `X₀`, with
`X₁` affine, are isomorphic over `Y` by an isomorphism inducing the given one on `X₀`. The
isomorphism is obtained from III.5.5 (`exists_extension_of_isNilpotent`, applied to the affine
thickening `X₀ ⊆ X₁`) and III.4.2 (`isIso_of_isPullback`). We assume `X₁` affine rather than
`X₀`; the two are equivalent (EGA I 5.1.9), which is not formalized here.

`exists_smooth_lift_of_isAffine` is the existence, for an affine base `Y`: it is the scheme form
of `smoothLiftAffineStatement` (`SmoothLift.lean`).
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

/-- A scheme locally of finite type over a locally noetherian scheme is locally noetherian. -/
lemma isLocallyNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsLocallyNoetherian Y] : IsLocallyNoetherian X := by
  let ι := {p : Y.affineOpens × X.affineOpens // (p.2 : X.Opens) ≤ f ⁻¹ᵁ p.1}
  refine isLocallyNoetherian_of_affine_cover (S := fun p : ι ↦ p.1.2) ?_ fun p ↦ ?_
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hxW (f ⁻¹ᵁ W).2
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(⟨W, hW⟩, ⟨V, hV⟩), hVW⟩, hxV⟩
  · have hft : (f.appLE p.1.1 p.1.2 p.2).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance p.1.1 p.1.2 p.2
    have : IsNoetherianRing Γ(Y, p.1.1) := IsLocallyNoetherian.component_noetherian p.1.1
    algebraize [(f.appLE p.1.1 p.1.2 p.2).hom]
    exact Algebra.FiniteType.isNoetherianRing Γ(Y, p.1.1) Γ(X, p.1.2)

/-- The ideal of a surjective closed immersion into an affine noetherian scheme is nilpotent. -/
lemma isNilpotent_ker_of_surjective {X Z : Scheme.{u}} [IsAffine X] [IsLocallyNoetherian X]
    (k : Z ⟶ X) [IsClosedImmersion k] (hk : Function.Surjective k) : IsNilpotent k.ker := by
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have hnil : IsNilpotent (RingHom.ker (k.app ⊤).hom) := by
    refine (Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)).mpr ?_
    have := ker_appLE_le_nilradical k hk (U := ⊤) isCompact_univ
    rwa [← Scheme.Hom.app_eq_appLE] at this
  obtain ⟨m, hm⟩ := hnil
  refine ⟨m, Scheme.IdealSheafData.ext_of_isAffine ?_⟩
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply]
  exact hm

/-- III.6.8 (uniqueness) and III.4.1 for an affine lift: let `Y` be locally noetherian,
`j : Y₀ → Y` a surjective closed immersion, and `X₁`, `X₂` smooth `Y`-schemes reducing to
`Z₁ ≅ Z₂` over `Y₀`. If `X₁` is affine, the isomorphism `Z₁ ≅ Z₂` lifts to an isomorphism
`X₁ ≅ X₂` over `Y`. -/
theorem exists_iso_of_smooth_of_isAffine {Y Y₀ X₁ X₂ Z₁ Z₂ : Scheme.{u}} [IsLocallyNoetherian Y]
    (j : Y₀ ⟶ Y) [IsClosedImmersion j] (hj : Function.Surjective j)
    (f₁ : X₁ ⟶ Y) [Smooth f₁] (f₂ : X₂ ⟶ Y) [Smooth f₂] [IsAffine X₁]
    {k₁ : Z₁ ⟶ X₁} {p₁ : Z₁ ⟶ Y₀} (h₁ : IsPullback k₁ p₁ f₁ j)
    {k₂ : Z₂ ⟶ X₂} {p₂ : Z₂ ⟶ Y₀} (h₂ : IsPullback k₂ p₂ f₂ j)
    (e₀ : Z₁ ≅ Z₂) (he₀ : e₀.hom ≫ p₂ = p₁) :
    ∃ φ : X₁ ≅ X₂, φ.hom ≫ f₂ = f₁ ∧ k₁ ≫ φ.hom = e₀.hom ≫ k₂ := by
  have : IsClosedImmersion k₁ := MorphismProperty.of_isPullback h₁.flip ‹_›
  have hk₁ : Function.Surjective k₁ :=
    (MorphismProperty.of_isPullback (P := @Surjective) h₁.flip ⟨hj⟩).surj
  have : IsLocallyNoetherian X₁ := isLocallyNoetherian_of_locallyOfFiniteType f₁
  obtain ⟨g, hg₁, hg₂⟩ := exists_extension_of_isNilpotent f₂ f₁ k₁
    (isNilpotent_ker_of_surjective k₁ hk₁) (e₀.hom ≫ k₂) (by
      rw [Category.assoc, h₂.w, ← Category.assoc, he₀, h₁.w])
  have : IsIso g := isIso_of_isPullback f₁ f₂ j hj h₁ h₂ g hg₁ e₀.hom hg₂.symm
  exact ⟨asIso g, hg₁, hg₂⟩

set_option backward.isDefEq.respectTransparency false in
/-- III.6.8 (existence), for an affine base: let `Y` be affine, `j : Y₀ → Y` a closed immersion
defined by a nilpotent ideal, and `X₀` an affine smooth `Y₀`-scheme. Then `X₀` is the reduction
of a smooth affine `Y`-scheme `X`: there is a cartesian square `X₀ → X`, `X₀ → Y₀`, `X → Y`,
`Y₀ → Y`. -/
theorem exists_smooth_lift_of_isAffine {Y Y₀ X₀ : Scheme.{u}} [IsAffine Y] (j : Y₀ ⟶ Y)
    [IsClosedImmersion j] (hj : IsNilpotent j.ker) (f₀ : X₀ ⟶ Y₀) [Smooth f₀] [IsAffine X₀] :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y) (_ : Smooth f) (_ : IsAffine X) (k : X₀ ⟶ X),
      IsPullback k f₀ f j := by
  obtain ⟨_, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine j
  set ρ := j.appTop
  set φ := f₀.appTop
  have hφ : φ.hom.Smooth := (HasRingHomProperty.iff_of_isAffine (P := @Smooth)).mp ‹_›
  have hnil : IsNilpotent (RingHom.ker ρ.hom) := by
    obtain ⟨m, hm⟩ := hj
    refine ⟨m, ?_⟩
    have h := congrArg (fun K : Y.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top Y⟩) hm
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply] at h
    exact h
  algebraize [ρ.hom, φ.hom]
  obtain ⟨S, _, _, hS, ⟨e⟩⟩ := smoothLiftAffineStatement Γ(Y, ⊤) Γ(Y₀, ⊤) Γ(X₀, ⊤)
    hsurj hnil hφ
  let a : Γ(Y, ⊤) ⟶ CommRingCat.of S := CommRingCat.ofHom (algebraMap Γ(Y, ⊤) S)
  let σ : CommRingCat.of S ⟶ Γ(X₀, ⊤) :=
    CommRingCat.ofHom (e.toRingEquiv.toRingHom.comp
      (Algebra.TensorProduct.includeRight (R := Γ(Y, ⊤)) (A := Γ(Y₀, ⊤)) (B := S)).toRingHom)
  have hpo : IsPushout ρ a φ σ :=
    (CommRingCat.isPushout_tensorProduct Γ(Y, ⊤) Γ(Y₀, ⊤) S).of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) e.toRingEquiv.toCommRingCatIso (by ext; rfl) (by ext; rfl)
      (by ext r; exact e.commutes r) (by ext; rfl)
  have hA := (isPullback_SpecMap_of_isPushout _ _ _ _ hpo).flip
  have hSsm : Smooth (Spec.map a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr hS
  refine ⟨Spec (.of S), Spec.map a ≫ Y.isoSpec.inv, inferInstance, inferInstance,
    X₀.isoSpec.hom ≫ Spec.map σ, ?_⟩
  refine hA.of_iso X₀.isoSpec.symm (Iso.refl _) Y₀.isoSpec.symm Y.isoSpec.symm ?_ ?_ ?_ ?_
  · simp
  · exact Scheme.isoSpec_inv_naturality f₀
  · simp
  · exact Scheme.isoSpec_inv_naturality j

end SGA.SGA1.ExposeIII
