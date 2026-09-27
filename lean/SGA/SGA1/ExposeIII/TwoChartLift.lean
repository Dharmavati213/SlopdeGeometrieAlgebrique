/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIII.AffineLift
import SGA.SGA1.ExposeIII.ExtensionSheaf
import SGA.SGA1.ExposeIII.FormalExtension
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Limits

/-!
# SGA 1, Exposé III, 6.7: smooth lifts of schemes covered by two affine opens

Corollary III.6.7: if `H²(X₀, 𝒢) = 0`, a smooth `Sₙ`-scheme `Xₙ` lifts to a smooth
`Sₙ₊₁`-scheme `Xₙ₊₁`. SGA glues local lifts `X^i` of an affine cover `(U_i)` along isomorphisms
`X^i|U_{ij} ≅ X^j|U_{ij}`; the obstruction to choosing them compatibly on the triple
intersections is a Čech `2`-cocycle of the cover (III.6.3).

For a cover by two affine opens `U₁`, `U₂` with affine intersection there are no triple
intersections, so the Čech obstruction group `H²` of the cover vanishes and the gluing always
works (`exists_smooth_lift_of_sup_eq_top`). This covers for instance every separated scheme which
is the union of two affine opens (e.g. a projective curve over a field). The lifts of `U₁`, `U₂`,
`U₁ ∩ U₂` are given by III.6.8 (`exists_smooth_lift_of_isAffine`), the transition maps by III.5.5,
and they are open immersions by the variant of III.4.2 for open immersions
(`isOpenImmersion_of_isPullback`). The glued scheme is the pushout along these open immersions.

Iterating, a smooth `Y₀`-scheme which is a union of two affine opens with affine intersection
lifts to a formal scheme smooth over the formal completion (III.6.10 in this case,
`exists_smooth_lift_seq_of_isUnionOfTwoAffines`).

The general case (the obstruction class of III.6.3 in `H²(X₀, 𝒢)` for an arbitrary affine cover)
is not formalized.
-/

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace SGA.SGA1.ExposeIII

set_option backward.isDefEq.respectTransparency false in
/-- Lemma III.4.2, variant for open immersions: under the hypotheses of `isIso_of_isPullback`, if
the reduction `u₀` of `u` is an open immersion, so is `u`. The morphism `u` factors through the
open subscheme `V` of `X'` with the same underlying set as the range of `u₀`, and `X → V` is an
isomorphism by III.4.2. -/
theorem isOpenImmersion_of_isPullback {X X' Y Y₀ X₀ X'₀ : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) (f' : X' ⟶ Y) [Flat f] (i : Y₀ ⟶ Y) [IsClosedImmersion i]
    (hi : Function.Surjective i) {iX : X₀ ⟶ X} {fX : X₀ ⟶ Y₀} (hX : IsPullback iX fX f i)
    {iX' : X'₀ ⟶ X'} {fX' : X'₀ ⟶ Y₀} (hX' : IsPullback iX' fX' f' i)
    (u : X ⟶ X') (hu : u ≫ f' = f) (u₀ : X₀ ⟶ X'₀) [IsOpenImmersion u₀]
    (hu₀ : u₀ ≫ iX' = iX ≫ u) : IsOpenImmersion u := by
  have : IsClosedImmersion iX := MorphismProperty.of_isPullback hX.flip ‹_›
  have : IsClosedImmersion iX' := MorphismProperty.of_isPullback hX'.flip ‹_›
  have hiX : Function.Surjective iX :=
    (MorphismProperty.of_isPullback (P := @Surjective) hX.flip ⟨hi⟩).surj
  have hiX' : Function.Surjective iX' :=
    (MorphismProperty.of_isPullback (P := @Surjective) hX'.flip ⟨hi⟩).surj
  -- the open subscheme `V` of `X'` corresponding to the range of `u₀`
  let V : X'.Opens := ⟨iX' '' Set.range u₀,
    isOpenMap_of_isClosedEmbedding_of_surjective iX'.isClosedEmbedding hiX' _
      u₀.isOpenEmbedding.isOpen_range⟩
  have hpre : iX' ⁻¹ᵁ V = u₀.opensRange := by
    ext z
    exact iX'.isClosedEmbedding.injective.mem_set_image
  have hrange : Set.range u ⊆ (V : Set X') := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := hiX x
    refine ⟨u₀ z, ⟨z, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hu₀, Scheme.Hom.comp_apply]
  let u' : X ⟶ V.toScheme := IsOpenImmersion.lift V.ι u (by rwa [Scheme.Opens.range_ι])
  have hu' : u' ≫ V.ι = u := IsOpenImmersion.lift_fac _ _ _
  -- the square for `V`
  have hV : IsPullback (iX' ∣_ V) ((iX' ⁻¹ᵁ V).ι ≫ fX') (V.ι ≫ f') i :=
    (isPullback_morphismRestrict iX' V).paste_vert hX'
  -- the reduction of `u'`
  let e := IsOpenImmersion.isoOfRangeEq u₀ (iX' ⁻¹ᵁ V).ι
    (by rw [Scheme.Opens.range_ι, hpre, Scheme.Hom.coe_opensRange])
  have he : e.hom ≫ (iX' ∣_ V) = iX ≫ u' := by
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι,
      IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Category.assoc, hu', hu₀]
  have : IsIso u' := isIso_of_isPullback f (V.ι ≫ f') i hi hX hV u'
    (by rw [reassoc_of% hu', hu]) e.hom he
  rw [← hu']
  infer_instance

/-- A closed immersion whose ideal is nilpotent is surjective. -/
lemma surjective_of_isNilpotent_ker {Y₀ Y : Scheme.{u}} (j : Y₀ ⟶ Y) [IsClosedImmersion j]
    (hj : IsNilpotent j.ker) : Function.Surjective j := by
  have : IsDominant j := by
    obtain ⟨n, hn⟩ := hj
    rw [isDominant_iff, denseRange_iff_closure_range, ← j.support_ker,
      ← j.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  have hd := j.denseRange
  rw [← Set.range_eq_univ, ← j.isClosedEmbedding.isClosed_range.closure_eq]
  exact hd.closure_range

/-- Two points identified in the pushout of two open immersions come from the common source. -/
lemma exists_eq_of_inl_eq_inr {P P₁ P₂ : Scheme.{u}} (a₁ : P ⟶ P₁) (a₂ : P ⟶ P₂)
    [IsOpenImmersion a₁] [IsOpenImmersion a₂] {z : P₁} {y : P₂}
    (h : pushout.inl a₁ a₂ z = pushout.inr a₁ a₂ y) : ∃ w, a₁ w = z ∧ a₂ w = y := by
  obtain ⟨k, fi, fj, w, hw₁, hw₂⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span a₁ a₂)).mp h
  cases fi <;> cases fj
  exact ⟨w, hw₁, hw₂⟩

set_option backward.isDefEq.respectTransparency false in
/-- III.6.7 (existence) for a scheme covered by two affine opens with affine intersection: let `Y`
be affine and locally noetherian, `j : Y₀ → Y` a closed immersion defined by a nilpotent ideal,
and `X₀` a smooth `Y₀`-scheme which is the union of two affine opens `U₁`, `U₂` with `U₁ ∩ U₂`
affine. Then `X₀` is the reduction of a smooth `Y`-scheme `X`: there is a cartesian square
`X₀ → X`, `X₀ → Y₀`, `X → Y`, `Y₀ → Y`; moreover `X` is again the union of two affine opens with
affine intersection (the lifts of `U₁`, `U₂`), so that the construction can be iterated. (SGA
assumes `H²(X₀, 𝒢) = 0`; for such a cover the Čech group `H²` of the cover vanishes, and no
hypothesis is needed.) -/
theorem exists_smooth_lift_of_sup_eq_top {Y Y₀ X₀ : Scheme.{u}} [IsAffine Y]
    [IsLocallyNoetherian Y] (j : Y₀ ⟶ Y) [IsClosedImmersion j] (hj : IsNilpotent j.ker)
    (f₀ : X₀ ⟶ Y₀) [Smooth f₀] (U₁ U₂ : X₀.Opens) (hU₁ : IsAffineOpen U₁)
    (hU₂ : IsAffineOpen U₂) (hW : IsAffineOpen (U₁ ⊓ U₂)) (hU : U₁ ⊔ U₂ = ⊤) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y) (_ : Smooth f) (k : X₀ ⟶ X), IsPullback k f₀ f j ∧
      ∃ V₁ V₂ : X.Opens, IsAffineOpen V₁ ∧ IsAffineOpen V₂ ∧ IsAffineOpen (V₁ ⊓ V₂) ∧
        V₁ ⊔ V₂ = ⊤ := by
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
    hinter ▸ isAffineOpen_opensRange _, eq_top_iff.mpr fun x _ ↦ ?_⟩
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

/-- A scheme is the union of two affine opens with affine intersection (e.g. a separated scheme
covered by two affine opens, such as a projective curve over a field). -/
def IsUnionOfTwoAffines (X : Scheme.{u}) : Prop :=
  ∃ U₁ U₂ : X.Opens, IsAffineOpen U₁ ∧ IsAffineOpen U₂ ∧ IsAffineOpen (U₁ ⊓ U₂) ∧ U₁ ⊔ U₂ = ⊤

/-- III.6.7 (existence) for a union of two affine opens, in the form of `IsUnionOfTwoAffines`: the
lift is again a union of two affine opens. -/
theorem exists_smooth_lift_of_isUnionOfTwoAffines {Y Y₀ X₀ : Scheme.{u}} [IsAffine Y]
    [IsLocallyNoetherian Y] (j : Y₀ ⟶ Y) [IsClosedImmersion j] (hj : IsNilpotent j.ker)
    (f₀ : X₀ ⟶ Y₀) [Smooth f₀] (hX₀ : IsUnionOfTwoAffines X₀) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Y) (_ : Smooth f) (k : X₀ ⟶ X), IsPullback k f₀ f j ∧
      IsUnionOfTwoAffines X := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hW, hU⟩ := hX₀
  exact exists_smooth_lift_of_sup_eq_top j hj f₀ U₁ U₂ hU₁ hU₂ hW hU

section Formal

variable {Y : Scheme.{u}} [IsAffine Y] [IsLocallyNoetherian Y] (𝓘 : Y.IdealSheafData)

/-- III.6.10 for a union of two affine opens: let `Y` be affine and locally noetherian, with a
quasi-coherent ideal `𝓘`, `Yₙ = V(𝓘ⁿ⁺¹)`. A smooth `Y₀`-scheme `X₀` which is the union of two
affine opens with affine intersection extends to successive smooth lifts `Xₙ → Yₙ`, with
`Xₙ = Xₙ₊₁ ×_{Yₙ₊₁} Yₙ`, i.e. to a formal scheme smooth over the completion of `Y` along `V(𝓘)`.
(SGA assumes `H²(X₀, 𝔤_{X₀/Y₀}) = 0`; for such `X₀` the obstructions of III.6.3 computed with the
cover by the two affine opens vanish.) -/
theorem exists_smooth_lift_seq_of_isUnionOfTwoAffines {X₀ : Scheme.{u}}
    (f₀ : X₀ ⟶ 𝓘.infinitesimalDiagram.obj 0) [Smooth f₀] (hX₀ : IsUnionOfTwoAffines X₀) :
    ∃ (X : ℕ → Scheme.{u}) (f : ∀ n, X n ⟶ 𝓘.infinitesimalDiagram.obj n)
      (k : ∀ n, X n ⟶ X (n + 1)) (e : X 0 ≅ X₀),
      (∀ n, Smooth (f n)) ∧ e.hom ≫ f₀ = f 0 ∧
        ∀ n, IsPullback (k n) (f n) (f (n + 1))
          (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ)) := by
  have step (n : ℕ) (X : Scheme.{u}) (f : X ⟶ 𝓘.infinitesimalDiagram.obj n) (_ : Smooth f)
      (hX : IsUnionOfTwoAffines X) :
      ∃ (X' : Scheme.{u}) (f' : X' ⟶ 𝓘.infinitesimalDiagram.obj (n + 1)) (_ : Smooth f')
        (k : X ⟶ X'), IsPullback k f f' (𝓘.infinitesimalDiagram.map (homOfLE n.le_succ)) ∧
          IsUnionOfTwoAffines X' := by
    have : IsLocallyNoetherian (𝓘.infinitesimalDiagram.obj (n + 1)) :=
      LocallyOfFiniteType.isLocallyNoetherian (𝓘 ^ (n + 1 + 1)).subschemeι
    exact exists_smooth_lift_of_isUnionOfTwoAffines _
      (isNilpotent_ker_infinitesimalDiagram_map 𝓘 n) f hX
  choose X' f' hf' k hk hX' using step
  let seq : ∀ n, Σ X : Scheme.{u}, Σ' (f : X ⟶ 𝓘.infinitesimalDiagram.obj n),
      Smooth f ∧ IsUnionOfTwoAffines X := fun n ↦
    Nat.rec ⟨X₀, f₀, inferInstance, hX₀⟩
      (fun n d ↦ ⟨X' n d.1 d.2.1 d.2.2.1 d.2.2.2, f' n _ _ d.2.2.1 d.2.2.2,
        hf' n _ _ _ _, hX' n _ _ _ _⟩) n
  exact ⟨fun n ↦ (seq n).1, fun n ↦ (seq n).2.1,
    fun n ↦ k n (seq n).1 (seq n).2.1 (seq n).2.2.1 (seq n).2.2.2, Iso.refl _,
    fun n ↦ (seq n).2.2.1, Category.id_comp _,
    fun n ↦ hk n (seq n).1 (seq n).2.1 (seq n).2.2.1 (seq n).2.2.2⟩

end Formal

end SGA.SGA1.ExposeIII
