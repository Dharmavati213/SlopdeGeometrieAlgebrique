/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Quasi-affine morphisms

A morphism of schemes `f : X ⟶ Y` is quasi-affine if the inverse image of every affine open subset
of `Y` is a quasi-affine scheme (EGA II 5.1.1, Stacks Project, section "Quasi-affine morphisms").
Mathlib has quasi-affine schemes (`AlgebraicGeometry.Scheme.IsQuasiAffine`); this file adds the
relative notion.

## Main results

- `Scheme.IsQuasiAffine.of_iSup_basicOpen_eq_top`: a quasi-compact scheme covered by quasi-affine
  basic opens `X_{tᵢ}` of global sections is quasi-affine.
- `AlgebraicGeometry.IsQuasiAffineHom`: the class of quasi-affine morphisms, with the instance
  `HasAffineProperty @IsQuasiAffineHom fun X _ _ _ ↦ X.IsQuasiAffine`. In particular being
  quasi-affine is local on the target.
- Quasi-affine morphisms are quasi-compact and separated, stable under composition and base change;
  affine morphisms and quasi-compact immersions are quasi-affine.
- `Scheme.IsQuasiAffine.of_isQuasiAffineHom`: the source of a quasi-affine morphism to a
  quasi-affine scheme is quasi-affine.
- `IsQuasiAffineHom.of_comp`: if `f ≫ g` is quasi-affine and `g` is quasi-separated, `f` is
  quasi-affine.
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace Scheme.IsQuasiAffine

/-- A scheme isomorphic to a quasi-affine scheme is quasi-affine. -/
lemma of_isIso [IsIso f] [Y.IsQuasiAffine] : X.IsQuasiAffine :=
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  .of_isImmersion f

instance (U : X.Opens) [X.IsQuasiAffine] [CompactSpace U] : U.toScheme.IsQuasiAffine :=
  .of_isImmersion U.ι

instance (r : Γ(X, ⊤)) [X.IsQuasiAffine] : (X.basicOpen r).toScheme.IsQuasiAffine :=
  .of_isAffineHom (X.basicOpen r).ι

set_option backward.isDefEq.respectTransparency false in
/-- A quasi-compact scheme `X` covered by basic opens `X_{tᵢ}` of global sections, each of which is
quasi-affine, is quasi-affine. -/
lemma of_iSup_basicOpen_eq_top (X : Scheme.{u}) [CompactSpace X] {ι : Type*}
    (t : ι → Γ(X, ⊤)) (ht : ⨆ i, X.basicOpen (t i) = ⊤)
    (H : ∀ i, (X.basicOpen (t i)).toScheme.IsQuasiAffine) : X.IsQuasiAffine := by
  have : QuasiSeparatedSpace X := .of_isOpenCover (U := fun i ↦ X.basicOpen (t i)) ht
    (fun _ ↦ isRetrocompact_basicOpen _) fun i ↦
      (isQuasiSeparated_iff_quasiSeparatedSpace _ (X.basicOpen (t i)).isOpen).mpr
        (inferInstanceAs (QuasiSeparatedSpace (X.basicOpen (t i)).toScheme))
  refine .of_forall_exists_mem_basicOpen _ fun x ↦ ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (ht.ge (Set.mem_univ x))
  set U := X.basicOpen (t i)
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (isBasis_basicOpen U).exists_subset_of_mem_open
    (Set.mem_univ (⟨x, hi⟩ : U)) isOpen_univ
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (t i)
  obtain ⟨⟨s, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers (t i)) (U.topIso.hom r)
  have e' : U.ι ''ᵁ U.toScheme.basicOpen r = X.basicOpen (s * t i) := by
    have h₁ := U.ι_image_basicOpen_topIso_inv (U.topIso.hom r)
    rw [Iso.hom_inv_id_apply] at h₁
    have hu : IsUnit (algebraMap Γ(X, ⊤) Γ(X, U) (t i ^ n)) :=
      IsLocalization.map_units _ (⟨_, n, rfl⟩ : Submonoid.powers (t i))
    have h₂ := congrArg X.basicOpen e
    dsimp only at h₂
    rw [X.basicOpen_mul, X.basicOpen_of_isUnit hu, inf_eq_left.mpr (X.basicOpen_le _),
      RingHom.algebraMap_toAlgebra, X.basicOpen_res] at h₂
    rw [h₁, h₂, X.basicOpen_mul, inf_comm]
  refine ⟨s * t i, e' ▸ hr.image_of_isOpenImmersion U.ι, ?_⟩
  rw [← e']
  exact ⟨_, hxr, rfl⟩

end Scheme.IsQuasiAffine

/-- A morphism of schemes `f : X ⟶ Y` is quasi-affine if the inverse image of every affine open
subset of `Y` is a quasi-affine scheme (EGA II 5.1.1). -/
@[mk_iff]
class IsQuasiAffineHom (f : X ⟶ Y) : Prop where
  isQuasiAffine_preimage : ∀ U : Y.Opens, IsAffineOpen U → (f ⁻¹ᵁ U).toScheme.IsQuasiAffine

lemma IsAffineOpen.isQuasiAffine_preimage {U : Y.Opens} (hU : IsAffineOpen U) [IsQuasiAffineHom f] :
    (f ⁻¹ᵁ U).toScheme.IsQuasiAffine :=
  IsQuasiAffineHom.isQuasiAffine_preimage U hU

set_option backward.isDefEq.respectTransparency false in
instance : HasAffineProperty @IsQuasiAffineHom fun X _ _ _ ↦ X.IsQuasiAffine where
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : Y.IsQuasiAffine := H
        exact Scheme.IsQuasiAffine.of_isIso e.hom
      · exact fun _ _ _ ↦ id
    · intro X Y _ f r H
      have : X.IsQuasiAffine := H
      change (f ⁻¹ᵁ Y.basicOpen r).toScheme.IsQuasiAffine
      rw [Scheme.preimage_basicOpen_top]
      infer_instance
    · intro X Y _ f s hs H
      have H' (r : (s : Set Γ(Y, ⊤))) : (X.basicOpen (f.appTop r.1)).toScheme.IsQuasiAffine := by
        rw [← Scheme.preimage_basicOpen_top]
        exact H ⟨r.1, r.2⟩
      have hX : ⨆ r : (s : Set Γ(Y, ⊤)), X.basicOpen (f.appTop r.1) = ⊤ := by
        have := (isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs
        apply_fun (f ⁻¹ᵁ ·) at this
        rw [Scheme.Hom.preimage_iSup, Scheme.Hom.preimage_top] at this
        simpa only [Scheme.preimage_basicOpen_top] using this
      have : CompactSpace X := by
        rw [← isCompact_univ_iff, ← TopologicalSpace.Opens.coe_top, ← hX,
          TopologicalSpace.Opens.coe_iSup]
        exact isCompact_iUnion fun r ↦ isCompact_iff_compactSpace.mpr (H' r).toCompactSpace
      exact Scheme.IsQuasiAffine.of_iSup_basicOpen_eq_top X _ hX H'
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [targetAffineLocally, Scheme.affineOpens, Set.coe_ofPred, Set.mem_ofPred_eq,
      Subtype.forall, isQuasiAffineHom_iff]

set_option backward.isDefEq.respectTransparency false in
lemma isQuasiAffineHom_iff_isQuasiAffine [IsAffine Y] : IsQuasiAffineHom f ↔ X.IsQuasiAffine :=
  HasAffineProperty.iff_of_isAffine (P := @IsQuasiAffineHom)

lemma isQuasiAffine_of_isQuasiAffineHom [IsAffine Y] [IsQuasiAffineHom f] : X.IsQuasiAffine :=
  (isQuasiAffineHom_iff_isQuasiAffine f).mp ‹_›

set_option backward.isDefEq.respectTransparency false in
instance : IsZariskiLocalAtTarget @IsQuasiAffineHom := inferInstance

instance (U : Y.Opens) [IsQuasiAffineHom f] : IsQuasiAffineHom (f ∣_ U) :=
  IsZariskiLocalAtTarget.restrict ‹_› U

instance (priority := 900) [IsAffineHom f] : IsQuasiAffineHom f :=
  ⟨fun _ hU ↦ have : IsAffine _ := hU.preimage f; inferInstance⟩

instance (priority := 900) [IsQuasiAffineHom f] : QuasiCompact f :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU ↦
    have := hU.isQuasiAffine_preimage f
    isCompact_iff_compactSpace.mpr this.toCompactSpace

instance (priority := 900) [IsQuasiAffineHom f] : IsSeparated f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : Y.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top Y) fun U ↦ ?_
  have := U.2.isQuasiAffine_preimage f
  infer_instance

/-- A quasi-compact immersion is quasi-affine. -/
instance (priority := 900) [IsImmersion f] [QuasiCompact f] : IsQuasiAffineHom f := by
  refine ⟨fun U hU ↦ ?_⟩
  have : IsAffine U := hU
  have : CompactSpace (f ⁻¹ᵁ U) := isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
  exact .of_isImmersion (f ∣_ U)

set_option backward.isDefEq.respectTransparency false in
/-- The source of a quasi-affine morphism to a quasi-affine scheme is quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_isQuasiAffineHom [IsQuasiAffineHom f] [Y.IsQuasiAffine] :
    X.IsQuasiAffine := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let t : { r : Γ(Y, ⊤) // IsAffineOpen (Y.basicOpen r) } → Γ(X, ⊤) := fun r ↦ f.appTop r.1
  refine .of_iSup_basicOpen_eq_top X t ?_ fun r ↦ ?_
  · simp_rw [t, ← Scheme.preimage_basicOpen_top, ← Scheme.Hom.preimage_iSup]
    rw [← Scheme.Hom.preimage_top f]
    congr 1
    exact top_le_iff.mp fun y _ ↦ by
      obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hyr, -⟩ :=
        (isBasis_basicOpen Y).exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hyr⟩
  · rw [← Scheme.preimage_basicOpen_top]
    exact r.2.isQuasiAffine_preimage f

instance [IsQuasiAffineHom f] [IsQuasiAffineHom g] : IsQuasiAffineHom (f ≫ g) := by
  refine ⟨fun U hU ↦ ?_⟩
  have := hU.isQuasiAffine_preimage g
  rw [Scheme.Hom.comp_preimage]
  exact .of_isQuasiAffineHom (f ∣_ (g ⁻¹ᵁ U))

instance : MorphismProperty.IsMultiplicative @IsQuasiAffineHom where
  id_mem _ := inferInstance
  comp_mem _ _ _ _ := inferInstance


set_option backward.isDefEq.respectTransparency false in
instance isQuasiAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsQuasiAffineHom := by
  apply HasAffineProperty.isStableUnderBaseChange
  let := HasAffineProperty.isLocal_affineProperty @IsQuasiAffineHom
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g (H : Y.IsQuasiAffine)
  have : QuasiCompact (pullback.fst f g) := MorphismProperty.pullback_fst _ _ inferInstance
  have : CompactSpace ↥(pullback f g) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst f g)
  let h : Spec Γ(Y, ⊤) ⟶ S := Spec.map g.appTop ≫ S.isoSpec.inv
  have e : g = Y.toSpecΓ ≫ h := by simp [h, ← Scheme.toSpecΓ_naturality_assoc]
  have : IsImmersion (pullback.map f g f h (𝟙 _) Y.toSpecΓ (𝟙 _) (by simp) (by simp [e])) :=
    MorphismProperty.pullbackMap (P := @IsImmersion) (inferInstanceAs (IsImmersion (𝟙 _)))
      (inferInstanceAs (IsImmersion Y.toSpecΓ)) (by simp) e
  exact .of_isImmersion (pullback.map f g f h (𝟙 _) Y.toSpecΓ (𝟙 _) _ _)

set_option backward.isDefEq.respectTransparency false in
instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsQuasiAffineHom g] :
    IsQuasiAffineHom (pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ ‹_›

set_option backward.isDefEq.respectTransparency false in
instance {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsQuasiAffineHom f] :
    IsQuasiAffineHom (pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ ‹_›

instance : MorphismProperty.HasOfPostcompProperty @IsQuasiAffineHom @QuasiSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsQuasiAffineHom _)

/-- If `f ≫ g` is quasi-affine and `g` is quasi-separated, then `f` is quasi-affine. -/
lemma IsQuasiAffineHom.of_comp [IsQuasiAffineHom (f ≫ g)] [QuasiSeparated g] :
    IsQuasiAffineHom f :=
  MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

/-- A morphism from a quasi-affine scheme is quasi-affine as soon as it is quasi-compact. -/
lemma isQuasiAffineHom_of_isQuasiAffine [X.IsQuasiAffine] [QuasiCompact f] :
    IsQuasiAffineHom f := by
  refine ⟨fun U hU ↦ ?_⟩
  have : CompactSpace (f ⁻¹ᵁ U) := isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
  infer_instance

/-- A morphism is quasi-affine iff it is quasi-compact and, for every affine open `U` of the
target, the canonical morphism `f⁻¹(U) ⟶ Spec Γ(f⁻¹(U), 𝒪)` is an open immersion. -/
lemma isQuasiAffineHom_iff_isOpenImmersion_toSpecΓ :
    IsQuasiAffineHom f ↔ QuasiCompact f ∧
      ∀ U : Y.Opens, IsAffineOpen U → IsOpenImmersion (f ⁻¹ᵁ U).toScheme.toSpecΓ := by
  refine ⟨fun _ ↦ ⟨inferInstance, fun U hU ↦ have := hU.isQuasiAffine_preimage f;
    inferInstance⟩, fun ⟨_, H⟩ ↦ ⟨fun U hU ↦ ?_⟩⟩
  have : CompactSpace (f ⁻¹ᵁ U) := isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
  have := H U hU
  constructor

end AlgebraicGeometry
