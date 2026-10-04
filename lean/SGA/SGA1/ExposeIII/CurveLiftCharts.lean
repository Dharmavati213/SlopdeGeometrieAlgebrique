/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIII.TwoChartLift

/-!
# SGA 1, Exposé III, 6.7 for two charts, keeping track of the charts

`exists_smooth_lift_of_sup_eq_top` (`SGA.SGA1.ExposeIII.TwoChartLift`) lifts a smooth `Y₀`-scheme
`X₀ = U₁ ∪ U₂` (`U₁`, `U₂`, `U₁ ∩ U₂` affine) along a nilpotent closed immersion `Y₀ ⟶ Y`, `Y`
affine and locally noetherian, to a smooth `Y`-scheme `X = V₁ ∪ V₂`. For the lifting of curves
(III.7.4, `SGA.SGA1.ExposeIII.CurveLift`) we need that the charts of the lift are the lifts of the
given charts: `k⁻¹ V₁ = U₁` and `k⁻¹ V₂ = U₂` for `k : X₀ ⟶ X`
(`exists_smooth_lift_of_sup_eq_top_preimage`). The proof is that of
`exists_smooth_lift_of_sup_eq_top`, which computes these inverse images on the way (the glued
scheme is the pushout of the lifts of `U₁` and `U₂` along the lift of `U₁ ∩ U₂`), with the extra
conclusion returned.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

set_option backward.isDefEq.respectTransparency false in
/-- III.6.7 (existence) for a scheme covered by two affine opens with affine intersection, with
the charts tracked: let `Y` be affine and locally noetherian, `j : Y₀ → Y` a closed immersion
defined by a nilpotent ideal, and `X₀` a smooth `Y₀`-scheme which is the union of two affine opens
`U₁`, `U₂` with `U₁ ∩ U₂` affine. Then `X₀` is the reduction of a smooth `Y`-scheme `X`, which is
the union of two affine opens `V₁`, `V₂` with affine intersection whose inverse images in `X₀`
are `U₁` and `U₂`. -/
theorem exists_smooth_lift_of_sup_eq_top_preimage {Y Y₀ X₀ : Scheme.{u}} [IsAffine Y]
    [IsLocallyNoetherian Y] (j : Y₀ ⟶ Y) [IsClosedImmersion j] (hj : IsNilpotent j.ker)
    (f₀ : X₀ ⟶ Y₀) [Smooth f₀] (U₁ U₂ : X₀.Opens) (hU₁ : IsAffineOpen U₁)
    (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen (U₁ ⊓ U₂)) (hU : U₁ ⊔ U₂ = ⊤) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y) (_ : Smooth f) (k : X₀ ⟶ X), IsPullback k f₀ f j ∧
      ∃ V₁ V₂ : X.Opens, IsAffineOpen V₁ ∧ IsAffineOpen V₂ ∧ IsAffineOpen (V₁ ⊓ V₂) ∧
        V₁ ⊔ V₂ = ⊤ ∧ k ⁻¹ᵁ V₁ = U₁ ∧ k ⁻¹ᵁ V₂ = U₂ := by
  have hjs := surjective_of_isNilpotent_ker j hj
  -- smooth lifts of `U₁`, `U₂` and `U₁ ∩ U₂` (III.6.8)
  have lift (U : X₀.Opens) (hU : IsAffineOpen U) := by
    have : IsAffine U := hU
    exact exists_smooth_lift_of_isAffine j hj (U.ι ≫ f₀)
  obtain ⟨P₁, g₁, _, _, k₁, hk₁⟩ := lift U₁ hU₁
  obtain ⟨P₂, g₂, _, _, k₂, hk₂⟩ := lift U₂ hU₂
  obtain ⟨P, g, _, _, kW, hkW⟩ := lift (U₁ ⊓ U₂) hW
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsClosedImmersion kW := MorphismProperty.of_isPullback hkW.flip inferInstance
  have hkWs : Function.Surjective kW :=
    (MorphismProperty.of_isPullback (P := @Surjective) hkW.flip ⟨hjs⟩).surj
  have hnil : IsNilpotent kW.ker := isNilpotent_ker_of_surjective kW hkWs
  have hk₁i : Function.Injective k₁ :=
    (MorphismProperty.of_isPullback (P := @IsClosedImmersion) hk₁.flip
      inferInstance).isClosedEmbedding.injective
  have hk₂i : Function.Injective k₂ :=
    (MorphismProperty.of_isPullback (P := @IsClosedImmersion) hk₂.flip
      inferInstance).isClosedEmbedding.injective
  -- the transition maps `P → Pᵢ`, open immersions (III.5.5 and III.4.2)
  have trans (U' : X₀.Opens) (hle : U₁ ⊓ U₂ ≤ U') (P' : Scheme.{u}) (g' : P' ⟶ Y) [Smooth g']
      (k' : U'.toScheme ⟶ P') (hk' : IsPullback k' (U'.ι ≫ f₀) g' j) :
      ∃ a : P ⟶ P', IsOpenImmersion a ∧ a ≫ g' = g ∧ kW ≫ a = X₀.homOfLE hle ≫ k' := by
    obtain ⟨a, ha₁, ha₂⟩ := exists_extension_of_isNilpotent g' g kW hnil (X₀.homOfLE hle ≫ k')
      (by rw [Category.assoc, hk'.w, hkW.w]; simp only [← Category.assoc, Scheme.homOfLE_ι])
    exact ⟨a, isOpenImmersion_of_isPullback g g' j hjs hkW hk' a ha₁ (X₀.homOfLE hle) ha₂.symm,
      ha₁, ha₂⟩
  obtain ⟨a₁, _, ha₁, ha₁'⟩ := trans U₁ inf_le_left P₁ g₁ k₁ hk₁
  obtain ⟨a₂, _, ha₂, ha₂'⟩ := trans U₂ inf_le_right P₂ g₂ k₂ hk₂
  -- the glued scheme
  have hcomm : a₁ ≫ g₁ = a₂ ≫ g₂ := by rw [ha₁, ha₂]
  let f : pushout a₁ a₂ ⟶ Y := pushout.desc g₁ g₂ hcomm
  -- the morphism `X₀ → X`
  let Us : Bool → X₀.Opens := fun b ↦ cond b U₁ U₂
  let ks : ∀ b, (Us b).toScheme ⟶ pushout a₁ a₂ := fun b ↦ match b with
    | true => k₁ ≫ pushout.inl a₁ a₂
    | false => k₂ ≫ pushout.inr a₁ a₂
  have h₁₂ : X₀.homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁) ≫ k₁ ≫ pushout.inl a₁ a₂ =
      X₀.homOfLE inf_le_right ≫ k₂ ≫ pushout.inr a₁ a₂ := by
    rw [← reassoc_of% ha₁', pushout.condition, reassoc_of% ha₂']
  have hks (b c : Bool) : X₀.homOfLE (inf_le_left : Us b ⊓ Us c ≤ Us b) ≫ ks b =
      X₀.homOfLE inf_le_right ≫ ks c := by
    cases b <;> cases c
    · rfl
    · have e : U₂ ⊓ U₁ ≤ U₁ ⊓ U₂ := le_of_eq (inf_comm _ _)
      change X₀.homOfLE (inf_le_left : U₂ ⊓ U₁ ≤ U₂) ≫ k₂ ≫ pushout.inr a₁ a₂ =
        X₀.homOfLE (inf_le_right : U₂ ⊓ U₁ ≤ U₁) ≫ k₁ ≫ pushout.inl a₁ a₂
      rw [← X₀.homOfLE_homOfLE e inf_le_right, ← X₀.homOfLE_homOfLE e inf_le_left,
        Category.assoc, Category.assoc, h₁₂]
    · exact h₁₂
    · rfl
  have hUs : ⊤ ≤ ⨆ b, Us b := by
    rw [iSup_bool_eq]
    exact hU.ge
  let k : X₀ ⟶ pushout a₁ a₂ :=
    X₀.topIso.inv ≫ glueOpensOfLE Us (fun _ ↦ le_top) hUs ks hks
  have hk (b : Bool) : (Us b).ι ≫ k = ks b := by
    have e : (Us b).ι ≫ X₀.topIso.inv = X₀.homOfLE le_top := by
      rw [← cancel_mono (⊤ : X₀.Opens).ι, Category.assoc, Scheme.toIso_inv_ι, Category.comp_id,
        Scheme.homOfLE_ι]
    rw [← Category.assoc, e]
    exact homOfLE_glueOpensOfLE Us (fun _ ↦ le_top) hUs ks hks b
  have hkU₁ : U₁.ι ≫ k = k₁ ≫ pushout.inl a₁ a₂ := hk true
  have hkU₂ : U₂.ι ≫ k = k₂ ≫ pushout.inr a₁ a₂ := hk false
  -- the open cover of `X` by `P₁` and `P₂`
  have hcov (x : ↥(pushout a₁ a₂)) :
      x ∈ Set.range (pushout.inl a₁ a₂) ∨ x ∈ Set.range (pushout.inr a₁ a₂) := by
    obtain ⟨i, xi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span a₁ a₂) x
    rcases i with _ | ⟨_ | _⟩
    · refine Or.inl ⟨a₁ xi, ?_⟩
      rw [← Scheme.Hom.comp_apply]
      exact congrArg (fun h ↦ h xi) (colimit.w (span a₁ a₂) WalkingSpan.Hom.fst)
    · exact Or.inl ⟨xi, rfl⟩
    · exact Or.inr ⟨xi, rfl⟩
  let 𝒰 : (pushout a₁ a₂).OpenCover := Scheme.Cover.mkOfCovers Bool (fun b ↦ cond b P₁ P₂)
    (fun b ↦ match b with
      | true => pushout.inl a₁ a₂
      | false => pushout.inr a₁ a₂) (fun x ↦ by
      rcases hcov x with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact ⟨true, y, hy⟩
      · exact ⟨false, y, hy⟩) (fun b ↦ by cases b <;> infer_instance)
  have hsm : Smooth f := IsZariskiLocalAtSource.of_openCover 𝒰 fun b ↦ by
    cases b
    · change Smooth (pushout.inr a₁ a₂ ≫ f)
      rw [pushout.inr_desc]
      infer_instance
    · change Smooth (pushout.inl a₁ a₂ ≫ f)
      rw [pushout.inl_desc]
      infer_instance
  -- the preimages of `P₁` and `P₂` in `X₀`
  have hW₁ (x : X₀) (hx : x ∈ U₁ ⊓ U₂) : x ∈ U₁ := hx.1
  have hpre₁ : k ⁻¹ᵁ (pushout.inl a₁ a₂).opensRange = U₁ := by
    ext x
    refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun hx ↦ ⟨k₁ ⟨x, hx⟩, ?_⟩⟩
    · by_contra hx
      have hx₂ : x ∈ U₂ := by
        have : x ∈ U₁ ⊔ U₂ := hU ▸ trivial
        exact this.resolve_left hx
      have e₂ : k x = pushout.inr a₁ a₂ (k₂ ⟨x, hx₂⟩) := by
        rw [← Scheme.Hom.comp_apply, ← hkU₂]
        rfl
      obtain ⟨w, -, hw⟩ := exists_eq_of_inl_eq_inr a₁ a₂ (hz.trans e₂)
      obtain ⟨w', rfl⟩ := hkWs w
      have : k₂ (X₀.homOfLE inf_le_right w') = k₂ ⟨x, hx₂⟩ := by
        rw [← Scheme.Hom.comp_apply, ← ha₂', Scheme.Hom.comp_apply, hw]
      have h' : w'.1 = x := by
        have := congrArg Subtype.val (hk₂i this)
        rwa [Scheme.homOfLE_apply] at this
      exact hx (h' ▸ w'.2.1)
    · rw [← Scheme.Hom.comp_apply, ← hkU₁]
      rfl
  have hpre₂ : k ⁻¹ᵁ (pushout.inr a₁ a₂).opensRange = U₂ := by
    ext x
    refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun hx ↦ ⟨k₂ ⟨x, hx⟩, ?_⟩⟩
    · by_contra hx
      have hx₁ : x ∈ U₁ := by
        have : x ∈ U₁ ⊔ U₂ := hU ▸ trivial
        exact this.resolve_right hx
      have e₁ : k x = pushout.inl a₁ a₂ (k₁ ⟨x, hx₁⟩) := by
        rw [← Scheme.Hom.comp_apply, ← hkU₁]
        rfl
      obtain ⟨w, hw, -⟩ := exists_eq_of_inl_eq_inr a₁ a₂ (e₁.symm.trans hz.symm)
      obtain ⟨w', rfl⟩ := hkWs w
      have : k₁ (X₀.homOfLE inf_le_left w') = k₁ ⟨x, hx₁⟩ := by
        rw [← Scheme.Hom.comp_apply, ← ha₁', Scheme.Hom.comp_apply, hw]
      have h' : w'.1 = x := by
        have := congrArg Subtype.val (hk₁i this)
        rwa [Scheme.homOfLE_apply] at this
      exact hx (h' ▸ w'.2.2)
    · rw [← Scheme.Hom.comp_apply, ← hkU₂]
      rfl
  -- `Uᵢ = X₀ ×_X Pᵢ`
  have hQ {U' : X₀.Opens} {P' : Scheme.{u}} (ι : P' ⟶ pushout a₁ a₂) [IsOpenImmersion ι]
      (k' : U'.toScheme ⟶ P') (hk' : U'.ι ≫ k = k' ≫ ι) (hpre : k ⁻¹ᵁ ι.opensRange = U') :
      IsPullback U'.ι k' k ι := by
    let eY := IsOpenImmersion.isoOfRangeEq ι.opensRange.ι ι (by simp)
    refine (isPullback_morphismRestrict k ι.opensRange).flip.of_iso (X₀.isoOfEq hpre)
      (Iso.refl _) eY (Iso.refl _) (by simp) ?_ (by simp) (by simp [eY])
    rw [← cancel_mono ι, Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, morphismRestrict_ι,
      Category.assoc, ← hk', Scheme.isoOfEq_hom_ι_assoc]
  have hQ₁ := hQ (pushout.inl a₁ a₂) k₁ hkU₁ hpre₁
  have hQ₂ := hQ (pushout.inr a₁ a₂) k₂ hkU₂ hpre₂
  have hinter : (pushout.inl a₁ a₂).opensRange ⊓ (pushout.inr a₁ a₂).opensRange =
      (a₁ ≫ pushout.inl a₁ a₂).opensRange := by
    ext x
    constructor
    · rintro ⟨⟨z, rfl⟩, ⟨y, hy⟩⟩
      obtain ⟨w, rfl, -⟩ := exists_eq_of_inl_eq_inr a₁ a₂ hy.symm
      exact ⟨w, rfl⟩
    · rintro ⟨w, rfl⟩
      refine ⟨⟨a₁ w, rfl⟩, ⟨a₂ w, ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, ← pushout.condition]
  refine ⟨pushout a₁ a₂, f, hsm, k, ?_, (pushout.inl a₁ a₂).opensRange,
    (pushout.inr a₁ a₂).opensRange, isAffineOpen_opensRange _, isAffineOpen_opensRange _,
    hinter ▸ isAffineOpen_opensRange _, eq_top_iff.mpr fun x _ ↦ ?_, hpre₁, hpre₂⟩
  rotate_left
  · rcases hcov x with h | h
    · exact Or.inl h
    · exact Or.inr h
  refine Scheme.isPullback_of_openCover k f₀ f j 𝒰 fun b ↦ ?_
  cases b
  · change IsPullback (pullback.snd k (pushout.inr a₁ a₂)) (pullback.fst k _ ≫ f₀)
      (pushout.inr a₁ a₂ ≫ f) j
    refine hk₂.of_iso hQ₂.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [f]) (by simp)
  · change IsPullback (pullback.snd k (pushout.inl a₁ a₂)) (pullback.fst k _ ≫ f₀)
      (pushout.inl a₁ a₂ ≫ f) j
    refine hk₁.of_iso hQ₁.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp) (by simp)
      (by simp [f]) (by simp)


end SGA.SGA1.ExposeIII
