/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import SGA.SGA1.ExposeV.FiniteQuotientBaseChange
import SGA.SGA1.ExposeV.FiniteQuotientProperties

/-!
# SGA 1, Exposé V, V.1.9: quotients commute with flat base change

Let `G` act admissibly on `X` with quotient `p : X ⟶ Y` as in V.1.3, and let `g : Y' ⟶ Y` be
flat. Then `p' : X ×_Y Y' ⟶ Y'` satisfies the hypotheses of V.1.3 for the action of `G` on the
first factor (`sectionsAreInvariant_pullback`), so `(X/G) ×_Y Y' = (X ×_Y Y')/G`
(`isQuotient_pullback_snd`); in SGA's form, over a base `Z` with `Z' ⟶ Z` flat,
`(X/G) ×_Z Z' = (X ×_Z Z')/G` (`isQuotient_pullbackMap`).

Over affine opens `U ⊆ Y`, `V' ⊆ g⁻¹ U`, the ring of `p'⁻¹ V'` is
`Γ(Y', V') ⊗_{Γ(Y, U)} Γ(X, p⁻¹ U)` (mathlib's `isIso_pushoutSection_of_isAffineOpen`), and the
affine case `isInvariant_tensorProduct` applies.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry Opposite TensorProduct

namespace SGA.SGA1.ExposeV

section FlatBaseChange

variable {G : Type*} {X Y Y' : Scheme.{u}} {T : G → (X ⟶ X)}
  {p : X ⟶ Y} (hTp : ∀ g, T g ≫ p = p) (g : Y' ⟶ Y)

/-- The action of `G` on `X ×_Y Y'` through the first factor. -/
noncomputable def pullbackAction (h : G) : pullback p g ⟶ pullback p g :=
  pullback.map p g p g (T h) (𝟙 Y') (𝟙 Y) (by rw [Category.comp_id, hTp]) (by simp)

@[reassoc (attr := simp)]
lemma pullbackAction_fst (h : G) :
    pullbackAction hTp g h ≫ pullback.fst p g = pullback.fst p g ≫ T h :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma pullbackAction_snd (h : G) :
    pullbackAction hTp g h ≫ pullback.snd p g = pullback.snd p g :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

variable [Group G] (hT : IsRightAction T)

include hT in
lemma isRightAction_pullbackAction : IsRightAction (pullbackAction hTp g) where
  map_one := pullback.hom_ext (by simp [hT.map_one]) (by simp)
  map_mul h k := pullback.hom_ext (by simp [hT.map_mul]) (by simp)

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.1.9 over an affine open: if `U ⊆ Y` and `V' ⊆ g⁻¹ U` are affine and `g` is flat, then
`Γ(Y', V') = Γ(X ×_Y Y', p'⁻¹ V')^G`. The ring of `p'⁻¹ V'` is `Γ(Y', V') ⊗_{Γ(Y, U)} Γ(X, p⁻¹ U)`
(mathlib's `isIso_pushoutSection_of_isAffineOpen`), and invariants commute with flat base change
(`isInvariant_tensorProduct`). -/
lemma sectionsAreInvariant_pullback_of_isAffineOpen [Finite G] [IsAffineHom p] [Flat g]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) {U : Y.Opens} (hU : IsAffineOpen U)
    {V' : Y'.Opens} (hV' : IsAffineOpen V') (hVU : V' ≤ g ⁻¹ᵁ U) :
    SectionsAreInvariant (pullbackAction hTp g) (pullback.snd p g)
      (pullbackAction_snd hTp g) V' := by
  let fst := pullback.fst p g
  let snd := pullback.snd p g
  let UX := p ⁻¹ᵁ U
  let UY := snd ⁻¹ᵁ V'
  have hUX : IsAffineOpen UX := hU.preimage p
  have hUY : UY = fst ⁻¹ᵁ UX ⊓ snd ⁻¹ᵁ V' := by
    refine (inf_eq_right.mpr fun z hz ↦ ?_).symm
    change p (fst z) ∈ U
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    exact hVU hz
  have H := IsPullback.of_hasPullback p g
  have hPO := (isIso_pushoutSection_iff H hVU le_rfl hUY).mp
    (isIso_pushoutSection_of_isAffineOpen H hVU le_rfl hUY hU hV' hUX)
  -- the rings
  let B := Γ(Y, U)
  let A := Γ(X, UX)
  let B' := Γ(Y', V')
  let _ : Algebra B A := (p.appLE U UX le_rfl).hom.toAlgebra
  let _ : Algebra B B' := (g.appLE U V' hVU).hom.toAlgebra
  let _ : MulSemiringAction G A :=
    sectionsAction hT UX fun h ↦ preimage_le_preimage_of_comp_eq (hTp h) U
  have : SMulCommClass G B A := ⟨fun h r s ↦ by
    change (T h).appLE _ _ _ (p.appLE U UX le_rfl r * s) = p.appLE U UX le_rfl r * _
    rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
      appLE_congr_hom (hTp h) _ _ _ le_rfl]
    rfl⟩
  have hinj : Function.Injective (algebraMap B A) := by
    change Function.Injective (p.appLE U UX le_rfl)
    rw [Scheme.Hom.appLE_eq_app]
    exact (hsec U).1
  have : Algebra.IsInvariant B A G := ⟨fun s hs ↦ by
    obtain ⟨t, ht⟩ := (hsec U).2 s hs
    exact ⟨t, by change p.appLE U UX le_rfl t = s; rw [Scheme.Hom.appLE_eq_app]; exact ht⟩⟩
  have : Module.Flat B B' := by
    have := HasRingHomProperty.appLE @Flat g ‹_› ⟨U, hU⟩ ⟨V', hV'⟩ hVU
    exact this
  let _ := tensorAction (B := B) (A := A) B' G
  obtain ⟨hinj', hinv'⟩ := isInvariant_tensorProduct B' G hinj
  -- identify `Γ(X', p'⁻¹ V')` with `B' ⊗_B A`
  have hT' := (CommRingCat.isPushout_tensorProduct B B' A)
  have hPO' : IsPushout (CommRingCat.ofHom (algebraMap B B')) (CommRingCat.ofHom (algebraMap B A))
      (snd.appLE V' UY le_rfl) (fst.appLE UX UY (by rw [hUY]; exact inf_le_left)) := hPO.flip
  let e := hT'.isoIsPushout _ _ hPO'
  have he₁ : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom =
      snd.appLE V' UY le_rfl := hT'.inl_isoIsPushout_hom _ _ hPO'
  have he₂ : CommRingCat.ofHom (Algebra.TensorProduct.includeRight.toRingHom) ≫ e.hom =
      fst.appLE UX UY (by rw [hUY]; exact inf_le_left) := hT'.inr_isoIsPushout_hom _ _ hPO'
  -- compatibility with the actions
  have hact : ∀ h : G, e.hom ≫ (pullbackAction hTp g h).appLE UY UY
      (preimage_le_preimage_of_comp_eq (pullbackAction_snd hTp g h) V') =
      CommRingCat.ofHom (MulSemiringAction.toRingHom G (B' ⊗[B] A) h) ≫ e.hom := by
    intro h
    refine hT'.hom_ext ?_ ?_
    · rw [reassoc_of% he₁, Scheme.Hom.appLE_comp_appLE, ← Category.assoc]
      have : CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫
          CommRingCat.ofHom (MulSemiringAction.toRingHom G (B' ⊗[B] A) h) =
          CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom := by
        ext b
        change h • (b ⊗ₜ[B] (1 : A)) = b ⊗ₜ 1
        rw [tensorAction_tmul, smul_one]
      rw [this, he₁]
      exact appLE_congr_hom (pullbackAction_snd hTp g h) _ _ _ _
    · rw [reassoc_of% he₂, Scheme.Hom.appLE_comp_appLE, ← Category.assoc]
      have : CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
          CommRingCat.ofHom (MulSemiringAction.toRingHom G (B' ⊗[B] A) h) =
          CommRingCat.ofHom (MulSemiringAction.toRingHom G A h) ≫
          CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom := by
        ext a
        exact tensorAction_tmul B' G h 1 a
      rw [this, Category.assoc, he₂]
      change _ = (T h).appLE UX UX _ ≫ fst.appLE UX UY _
      rw [Scheme.Hom.appLE_comp_appLE]
      exact appLE_congr_hom (pullbackAction_fst hTp g h) _ _ _ _
  refine ⟨?_, fun s hs ↦ ?_⟩
  · rw [Scheme.Hom.app_eq_appLE, ← he₁]
    exact (ConcreteCategory.bijective_of_isIso e.hom).1.comp hinj'
  · obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso e.hom).2 s
    have hti : ∀ h : G, h • t = t := fun h ↦ by
      apply (ConcreteCategory.bijective_of_isIso e.hom).1
      have := congr($(hact h) t)
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at this
      refine this.symm.trans ?_
      rw [ht]
      exact hs h
    obtain ⟨b, rfl⟩ := hinv'.isInvariant t hti
    refine ⟨b, ?_⟩
    rw [Scheme.Hom.app_eq_appLE, ← he₁, ← ht]
    rfl

include hT in
/-- V.1.9: if `G` acts admissibly on `X` with quotient `p : X ⟶ Y` (as in V.1.3) and `g : Y' ⟶ Y`
is flat, then `p' : X ×_Y Y' ⟶ Y'` still satisfies the hypotheses of V.1.3 for the action of `G`
through the first factor (`p'` being affine in any case). -/
theorem sectionsAreInvariant_pullback [Finite G] [IsAffineHom p] [Flat g]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) (V' : Y'.Opens) :
    SectionsAreInvariant (pullbackAction hTp g) (pullback.snd p g) (pullbackAction_snd hTp g)
      V' := by
  refine sectionsAreInvariant_of_basis (fun y' N hy'N ↦ ?_) V'
  obtain ⟨U, hU, hyU⟩ := exists_isAffineOpen_mem (g y')
  obtain ⟨V, hV, hy'V, hVN⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    Y'.isBasis_affineOpens) (show y' ∈ N ⊓ g ⁻¹ᵁ U from ⟨hy'N, hyU⟩)
  exact ⟨V, hVN.trans inf_le_left, hy'V, sectionsAreInvariant_pullback_of_isAffineOpen hTp g hT
    hsec hU hV (hVN.trans inf_le_right)⟩

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.1.9: under flat base change `g : Y' ⟶ Y`, `G` still acts admissibly on `X ×_Y Y'`, with
quotient `Y'`, i.e. `(X/G) ×_Y Y' = (X ×_Y Y')/G`. -/
theorem isQuotient_pullback_snd [Finite G] [IsAffineHom p] [Flat g]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) :
    IsQuotient (pullbackAction hTp g) (pullback.snd p g) :=
  have : IsAffineHom (pullback.snd p g) :=
    MorphismProperty.pullback_snd (P := @IsAffineHom) p g ‹_›
  isQuotient_of_sectionsAreInvariant (isRightAction_pullbackAction hTp g hT) fun V' _ ↦
    sectionsAreInvariant_pullback hTp g hT hsec V'

set_option backward.isDefEq.respectTransparency false in
include hT in
/-- V.1.9, in SGA's form: let `G` act admissibly on `X` with quotient `p : X ⟶ Y`, `Y` a scheme
over `Z` and `Z' ⟶ Z` flat. Then `Y ×_Z Z'` is the quotient of `X ×_Z Z'` by `G` (acting on the
first factor). -/
theorem isQuotient_pullbackMap [Finite G] [IsAffineHom p]
    (hsec : ∀ U, SectionsAreInvariant T p hTp U) {Z Z' : Scheme.{u}} (q : Y ⟶ Z) (h : Z' ⟶ Z)
    [Flat h] :
    IsQuotient (fun k ↦ pullback.map (p ≫ q) h (p ≫ q) h (T k) (𝟙 Z') (𝟙 Z)
        (by rw [Category.comp_id, reassoc_of% (hTp k)]) (by simp))
      (pullback.map (p ≫ q) h q h p (𝟙 Z') (𝟙 Z) (by simp) (by simp)) := by
  let e := pullbackRightPullbackFstIso q h p
  have hq := isQuotient_pullback_snd hTp (pullback.fst q h) hT hsec
  have he : ∀ k, pullback.map (p ≫ q) h (p ≫ q) h (T k) (𝟙 Z') (𝟙 Z)
      (by rw [Category.comp_id, reassoc_of% (hTp k)]) (by simp) ≫ e.inv =
      e.inv ≫ pullbackAction hTp (pullback.fst q h) k := by
    intro k
    apply pullback.hom_ext
    · simp [e, pullback.map]
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullbackAction_snd, e,
          pullbackRightPullbackFstIso_inv_snd_fst]
        simp [pullback.map, hTp]
      · simp [e, pullback.map]
  convert hq.iso_comp e.symm he using 1
  apply pullback.hom_ext
  · simp [e, pullback.map]
  · simp [e, pullback.map]

end FlatBaseChange

end SGA.SGA1.ExposeV
