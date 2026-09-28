/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.InertiaGroups

/-!
# SGA 1, Exposé V, V.2.6 and V.2.7 for schemes

Let `p : X ⟶ Y` be as in V.1.3 (`G` finite acting on the right, `p` affine and invariant with
`𝒪_Y = p_*(𝒪_X)^G`), and assume all inertia groups trivial, so that `p` is étale (V.2.3). With
no finiteness or noetherian hypothesis:

* V.2.7 (`isIso_sigmaDesc_of_section`): if `p` has a section `s`, then `Y × G ⟶ X`,
  `(y, g) ↦ T g (s y)`, is an isomorphism;
* V.2.6, (i) ⇒ (iii) and (i) ⇒ (ii bis) with `Y₁ = X` (`isIso_sigmaDesc_pullbackLift`):
  `X × G ⟶ X ×_Y X`, `(x, g) ↦ (x, T g x)`, is an isomorphism.

Both follow from the fact that the images of the sections of an étale morphism are open, and
two sections agree where one lands in the image of the other
(`section_eq_on_preimage_opensRange`); disjointness of the images comes from the triviality
of inertia, and they cover by V.1.1 (iii) on points (`exists_comp_eq_of_comp_eq`). The other
implications of V.2.6 are in `QuotientDescent.lean` (affine case: `PrincipalCovering.lean`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace SGA.SGA1.ExposeV

section Sections

variable {X Y : Scheme.{u}} (π : X ⟶ Y)

/-- Two sections `s₁, s₂` of `π`, with `s₁` an open immersion, agree on the open subset where
`s₂` lands in the image of `s₁`. -/
lemma section_eq_on_preimage_opensRange {s₁ s₂ : Y ⟶ X} [IsOpenImmersion s₁]
    (h₁ : s₁ ≫ π = 𝟙 Y) (h₂ : s₂ ≫ π = 𝟙 Y) :
    (s₂ ⁻¹ᵁ s₁.opensRange).ι ≫ s₂ = (s₂ ⁻¹ᵁ s₁.opensRange).ι ≫ s₁ := by
  let W := s₂ ⁻¹ᵁ s₁.opensRange
  have hr : Set.range (W.ι ≫ s₂) ⊆ Set.range s₁ := by
    rintro _ ⟨w, rfl⟩
    exact w.2
  let t := IsOpenImmersion.lift s₁ (W.ι ≫ s₂) hr
  have ht : t ≫ s₁ = W.ι ≫ s₂ := IsOpenImmersion.lift_fac _ _ _
  have ht' : t = W.ι := by
    have := congr_arg (· ≫ π) ht
    simpa [h₁, h₂] using this
  rw [← ht, ht']

/-- If two morphisms `a, b : Y ⟶ X` agree on an open subset containing `y`, they agree on the
point `Spec κ(y) ⟶ Y`. -/
lemma fromSpecResidueField_comp_eq_of_opens {Z : Scheme.{u}} {a b : Y ⟶ Z} (W : Y.Opens)
    (h : W.ι ≫ a = W.ι ≫ b) {y : Y} (hy : y ∈ W) :
    Y.fromSpecResidueField y ≫ a = Y.fromSpecResidueField y ≫ b := by
  let w : W.toScheme := ⟨y, hy⟩
  have hι := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField W.ι w
  change Y.fromSpecResidueField (W.ι w) ≫ a = Y.fromSpecResidueField (W.ι w) ≫ b
  rw [← cancel_epi (Spec.map (W.ι.residueFieldMap w)), reassoc_of% hι, reassoc_of% hι, h]

end Sections

section Principal

variable {G : Type*} [Group G] {X Y : Scheme.{u}} {T : G → (X ⟶ X)}
  (hT : IsRightAction T) {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p)

include hT in
/-- If `x ⟶ X` composed with `T g` and with `T h` gives the same point `Spec κ(x) ⟶ X`, then
`h g⁻¹` lies in the inertia group of `x`. -/
lemma mul_inv_mem_inertiaGroup {x : X} {g h : G}
    (e : X.fromSpecResidueField x ≫ T g = X.fromSpecResidueField x ≫ T h) :
    h * g⁻¹ ∈ inertiaGroup T x := by
  change X.fromSpecResidueField x ≫ T (h * g⁻¹) = X.fromSpecResidueField x
  rw [hT.map_mul, ← Category.assoc, ← e, Category.assoc, hT.comp_inv, Category.comp_id]

include hT in
/-- V.2.7, for any `p` as in V.1.3 (no finiteness or noetherian hypothesis): if the inertia
groups are trivial and `p` has a section `s`, then `X` is trivial: `Y × G ⟶ X`,
`(y, g) ↦ T g (s y)`, is an isomorphism. -/
theorem isIso_sigmaDesc_of_section [Finite G] [IsAffineHom p]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    (hfree : ∀ x g, g ∈ inertiaGroup T x → g = 1) (s : Y ⟶ X) (hs : s ≫ p = 𝟙 Y) :
    IsIso (Sigma.desc fun g : G ↦ s ≫ T g) := by
  have : Etale p := etale_of_inertiaGroup_eq hT hTp hsec hfree
  have : IsOpenImmersion s := SGA.SGA1.ExposeI.isOpenImmersion_of_section p hs
  have := hT.isIso
  let φ : G → (Y ⟶ X) := fun g ↦ s ≫ T g
  have hφ : ∀ g, φ g ≫ p = 𝟙 Y := fun g ↦ by simp [φ, hTp, hs]
  have horb := (surjective_and_orbit_of_sectionsAreInvariant hT fun U _ ↦ hsec U).2
  have hcov : ⨆ g, (φ g).opensRange = ⊤ := by
    refine top_le_iff.mp fun x _ ↦ ?_
    obtain ⟨g, hg⟩ := horb (s (p x)) x (by
      rw [← Scheme.Hom.comp_apply, hs]
      rfl)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨g, p x, hg⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun g ↦ (φ g).opensRange) := by
    intro g h hgh
    refine disjoint_iff.mpr (le_bot_iff.mp fun z hz ↦ ?_)
    obtain ⟨⟨y₁, rfl⟩, ⟨y₂, hy⟩⟩ := hz
    have hy₁₂ : y₂ = y₁ := by
      have := congr_arg p hy
      rwa [← Scheme.Hom.comp_apply, hφ, ← Scheme.Hom.comp_apply, hφ] at this
    subst hy₁₂
    have e := fromSpecResidueField_comp_eq_of_opens _
      (section_eq_on_preimage_opensRange p (hφ g) (hφ h)) (y := y₂) ⟨y₂, hy.symm⟩
    have hs' := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField s y₂
    simp only [φ] at e
    rw [← reassoc_of% hs', ← reassoc_of% hs', cancel_epi] at e
    have := hfree _ _ (mul_inv_mem_inertiaGroup hT e.symm)
    exact hgh (mul_inv_eq_one.mp this).symm
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of φ hcov hdisj
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X φ)).mp ⟨hc⟩

include hT in
/-- V.2.6, (i) ⇒ (iii), for any `p` as in V.1.3: if the inertia groups are trivial, then `X` is
formally principal homogeneous under `G`: `X × G ⟶ X ×_Y X`, `(x, g) ↦ (x, T g x)`, is an
isomorphism. (Together with `p` étale (V.2.3), surjective and affine, hence faithfully flat and
quasi-compact, this is condition (iii) of V.2.6.) -/
theorem isIso_sigmaDesc_pullbackLift [Finite G] [IsAffineHom p]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U)
    (hfree : ∀ x g, g ∈ inertiaGroup T x → g = 1) :
    IsIso (Sigma.desc fun g : G ↦ pullback.lift (𝟙 X) (T g) (by rw [Category.id_comp, hTp])
      : ∐ (fun _ : G ↦ X) ⟶ pullback p p) := by
  have : Etale p := etale_of_inertiaGroup_eq hT hTp hsec hfree
  let φ : G → (X ⟶ pullback p p) := fun g ↦
    pullback.lift (𝟙 X) (T g) (by rw [Category.id_comp, hTp])
  have hφ : ∀ g, φ g ≫ pullback.fst p p = 𝟙 X := fun g ↦ pullback.lift_fst _ _ _
  have hφ₂ : ∀ g, φ g ≫ pullback.snd p p = T g := fun g ↦ pullback.lift_snd _ _ _
  have : ∀ g, IsOpenImmersion (φ g) := fun g ↦
    SGA.SGA1.ExposeI.isOpenImmersion_of_section (pullback.fst p p) (hφ g)
  have hcov : ⨆ g, (φ g).opensRange = ⊤ := by
    refine top_le_iff.mp fun z _ ↦ ?_
    let x₁ := (pullback p p).fromSpecResidueField z ≫ pullback.fst p p
    let x₂ := (pullback p p).fromSpecResidueField z ≫ pullback.snd p p
    have hx : x₁ ≫ p = x₂ ≫ p := by simp only [x₁, x₂, Category.assoc, pullback.condition]
    obtain ⟨g, hg⟩ := exists_comp_eq_of_comp_eq hT hTp hsec x₁ x₂ hx
    have hg' : x₁ ≫ T g = x₂ := hg
    have hz : x₁ ≫ φ g = (pullback p p).fromSpecResidueField z := by
      apply pullback.hom_ext
      · rw [Category.assoc, hφ, Category.comp_id]
      · rw [Category.assoc, hφ₂, hg']
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨g, x₁ (IsLocalRing.closedPoint _), ?_⟩
    have := congr($(hz) (IsLocalRing.closedPoint ((pullback p p).residueField z)))
    exact this.trans (Scheme.fromSpecResidueField_apply z _)
  have hdisj : Pairwise (Function.onFun Disjoint fun g ↦ (φ g).opensRange) := by
    intro g h hgh
    refine disjoint_iff.mpr (le_bot_iff.mp fun z hz ↦ ?_)
    obtain ⟨⟨x₁, rfl⟩, ⟨x₂, hx⟩⟩ := hz
    have hx₁₂ : x₂ = x₁ := by
      have := congr_arg (pullback.fst p p) hx
      rwa [← Scheme.Hom.comp_apply, hφ, ← Scheme.Hom.comp_apply, hφ] at this
    subst hx₁₂
    have e₀ := section_eq_on_preimage_opensRange (pullback.fst p p) (hφ g) (hφ h)
    have e₁ : (φ h ⁻¹ᵁ (φ g).opensRange).ι ≫ T h = (φ h ⁻¹ᵁ (φ g).opensRange).ι ≫ T g := by
      rw [← hφ₂, ← hφ₂, reassoc_of% e₀]
    have e := fromSpecResidueField_comp_eq_of_opens _ e₁ (y := x₂) ⟨x₂, hx.symm⟩
    have := hfree _ _ (mul_inv_mem_inertiaGroup hT e.symm)
    exact hgh (mul_inv_eq_one.mp this).symm
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of φ hcov hdisj
  exact (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk _ φ)).mp ⟨hc⟩

end Principal

end SGA.SGA1.ExposeV
