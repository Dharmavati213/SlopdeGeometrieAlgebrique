/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.PropertiesLimitClosedImmersion

/-!
# Separatedness over a limit descends to a finite level

* `CategoryTheory.IsPullback.diagonal`: the diagonal of a base change is the base change of the
  diagonal.
* `CategoryTheory.IsPullback.pullback_map_fst`: `X' ×_{T} Y' ⟶ T` is the base change of
  `X ×_S Y ⟶ S` when `X'`, `Y'`, `T` are base changes of `X`, `Y`, `S`.
* `AlgebraicGeometry.Scheme.limitDescends_relative`: EGA IV 8.10.5 for a morphism `Y_j ⟶ Z_j` of
  schemes over `E j` (`Z_j` quasi-compact and quasi-separated over `E j`), from the statement for
  the diagram `k ↦ Z_j ×_{E j} E k`.
* `AlgebraicGeometry.Scheme.limitDescends_isSeparated` (EGA IV 8.10.5 (v)): separatedness
  descends, by descending the closed immersion property of the diagonal.

## References

* [EGA IV₃, 8.10.5][EGA4]
-/

universe u

open CategoryTheory Limits

namespace CategoryTheory.IsPullback

variable {C : Type*} [Category C] [HasPullbacks C]

set_option backward.isDefEq.respectTransparency false in
/-- The diagonal of a base change is the base change of the diagonal: if `X = X₀ ×_S T`, then
`Δ_{X/T}` is the base change of `Δ_{X₀/S}` along `X ×_T X ⟶ X₀ ×_S X₀`. -/
lemma diagonal {X X₀ T S : C} {e : X ⟶ X₀} {q : X ⟶ T} {f : X₀ ⟶ S} {g : T ⟶ S}
    (h : IsPullback e q f g) :
    IsPullback e (pullback.diagonal q) (pullback.diagonal f)
      (pullback.map q q f f e e g h.w.symm h.w.symm) := by
  refine ⟨⟨by ext <;> simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ s.snd ≫ pullback.fst q q)
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)⟩⟩
  · have := s.condition =≫ pullback.fst f f
    simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id, pullback.lift_fst] at this
    simp [this]
  · have h₁ : s.snd ≫ pullback.fst q q = s.snd ≫ pullback.snd q q := by
      apply h.hom_ext
      · have e₁ := s.condition =≫ pullback.fst f f
        have e₂ := s.condition =≫ pullback.snd f f
        simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
          pullback.lift_fst, pullback.lift_snd] at e₁ e₂
        simp only [Category.assoc]
        rw [← e₁, ← e₂]
      · simp only [Category.assoc, pullback.condition]
    apply pullback.hom_ext
    · simp
    · simp [h₁]
  · have := hm₂ =≫ pullback.fst q q
    simpa using this

set_option backward.isDefEq.respectTransparency false in
/-- If `X'`, `Y'`, `T` are base changes of `X`, `Y`, `S` along compatible maps, then
`X' ×_{T} Y' ⟶ T` is the base change of `X ×_S Y ⟶ S`. -/
lemma pullback_map_fst {X Y S X' Y' T : C} {f : X ⟶ S} {g : Y ⟶ S} {f' : X' ⟶ T}
    {g' : Y' ⟶ T} {eX : X' ⟶ X} {eY : Y' ⟶ Y} {t : T ⟶ S} (hX : IsPullback eX f' f t)
    (hY : IsPullback eY g' g t) :
    IsPullback (pullback.map f' g' f g eX eY t hX.w.symm hY.w.symm) (pullback.fst f' g' ≫ f')
      (pullback.fst f g ≫ f) t := by
  have hleft : IsPullback (pullback.map f' g' f g eX eY t hX.w.symm hY.w.symm)
      (pullback.fst f' g') (pullback.fst f g) eX := by
    refine IsPullback.of_right ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback f g).flip
    rw [pullback.lift_snd, hX.w]
    exact (IsPullback.of_hasPullback f' g').flip.paste_horiz hY
  exact hleft.paste_vert hX

end CategoryTheory.IsPullback

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- Stacks 02FV (the scheme version of the algebra lemma 00F4): if `f ≫ g` is locally of finite
presentation and `g` is locally of finite type, then `f` is locally of finite presentation. -/
@[stacks 02FV]
theorem LocallyOfFinitePresentation.of_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] :
    LocallyOfFinitePresentation f := by
  wlog hZ : IsAffine Z generalizing X Y Z
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (g.iSup_preimage_eq_top (iSup_affineOpens_eq_top Z))]
    intro U
    have H : LocallyOfFinitePresentation ((f ≫ g) ∣_ U.1) :=
      IsZariskiLocalAtTarget.restrict ‹_› U.1
    rw [morphismRestrict_comp] at H
    have hg' : LocallyOfFiniteType (g ∣_ U.1) := IsZariskiLocalAtTarget.restrict ‹_› U.1
    exact @this _ _ _ _ (g ∣_ U.1) H hg' U.2
  wlog hY : IsAffine Y generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top Y)]
    intro U
    have H : LocallyOfFinitePresentation ((f ⁻¹ᵁ U.1).ι ≫ f ≫ g) :=
      IsZariskiLocalAtSource.comp ‹_› _
    rw [← morphismRestrict_ι_assoc] at H
    have hg' : LocallyOfFiniteType (U.1.ι ≫ g) := IsZariskiLocalAtSource.comp ‹_› _
    exact @this _ _ _ (U.1.ι ≫ g) H hg' U.2
  wlog hX : IsAffine X generalizing X
  · rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @LocallyOfFinitePresentation) _
      (iSup_affineOpens_eq_top X)]
    intro U
    have H : LocallyOfFinitePresentation (U.1.ι ≫ f ≫ g) := IsZariskiLocalAtSource.comp ‹_› _
    rw [← Category.assoc] at H
    exact @this _ _ H U.2
  rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
  have h := (f ≫ g).finitePresentation_appTop
  have hg : g.appTop.hom.FiniteType :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).mp inferInstance
  rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] at h
  exact RingHom.FinitePresentation.of_comp_finiteType _ h hg

/-- The diagonal of a morphism locally of finite type is locally of finite presentation. -/
instance {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (pullback.diagonal f) := by
  have : LocallyOfFinitePresentation (pullback.diagonal f ≫ pullback.fst f f) := by
    rw [pullback.diagonal_fst]
    infer_instance
  exact LocallyOfFinitePresentation.of_comp _ (pullback.fst f f)

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
  [∀ i, QuasiSeparatedSpace (E.obj i)] {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 for morphisms over a member of the diagram: let `Z_j ⟶ E j` be quasi-compact and
quasi-separated with base change `Z ⟶ c.pt`, `u : Y_j ⟶ Z_j` of finite presentation with base
change `u' : Y ⟶ Z`. If `u'` has `P`, so has the base change of `u` along `Z_j ×_{E j} E k ⟶ Z_j`
for some `k`. -/
theorem Scheme.limitDescends_relative {P : MorphismProperty Scheme.{u}} [P.RespectsIso]
    (hP : Scheme.LimitDescendsStatement.{u} P) (hc : IsLimit c) {j : I} {Zj : Scheme.{u}}
    (pZ : Zj ⟶ E.obj j) [QuasiCompact pZ] [QuasiSeparated pZ] {Yj : Scheme.{u}} (u : Yj ⟶ Zj)
    [LocallyOfFinitePresentation u] [QuasiCompact u] [QuasiSeparated u] {Z : Scheme.{u}}
    {eZ : Z ⟶ Zj} {pZ' : Z ⟶ c.pt} (hZ : IsPullback eZ pZ' pZ (c.π.app j)) {Y : Scheme.{u}}
    {eY : Y ⟶ Yj} {u' : Y ⟶ Z} (hY : IsPullback eY u' u eZ) (hu : P u') :
    ∃ k : Over j, P (pullback.snd u (pullback.fst pZ (E.map k.hom))) := by
  have := Scheme.compactSpace_baseChangeDiagram (E := E) pZ
  have := Scheme.quasiSeparatedSpace_baseChangeDiagram (E := E) pZ
  let D := Scheme.baseChangeDiagram E pZ
  let C := Scheme.baseChangeCone hZ
  let o : Over j := Over.mk (𝟙 j)
  let fo := pullback.fst pZ (E.map o.hom)
  have hCo : C.π.app o ≫ fo = eZ := by simp [C, fo]
  have hY' : IsPullback eY u' u (C.π.app o ≫ fo) := by rwa [hCo]
  have sq := IsPullback.of_right' hY' (IsPullback.of_hasPullback u fo)
  obtain ⟨k, g, hk⟩ := hP D C (Scheme.isLimitBaseChangeCone hc hZ) (j := o)
    (pullback.snd u fo) _ u' sq hu
  refine ⟨k, ?_⟩
  have h1 := (MorphismProperty.arrow_mk_iso_iff P
    (Scheme.pullbackSndCompArrowIso u (D.map g) fo)).mpr hk
  have h2 : D.map g ≫ fo = pullback.fst pZ (E.map k.hom) := by
    simp [D, fo, pullback.map]
  exact Scheme.of_pullback_snd_eq h2 h1

set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.10.5 (v): separatedness descends along limits of cofiltered diagrams of
quasi-compact and quasi-separated schemes with affine transition maps. -/
theorem Scheme.limitDescends_isSeparated : Scheme.LimitDescendsStatement.{u} @IsSeparated := by
  intro I _ _ E _ _ _ c hc j X Xj qj _ _ _ e q h hq
  have hZ := IsPullback.pullback_map_fst h h
  have hY := h.diagonal
  have : IsClosedImmersion (pullback.diagonal q) := hq.1
  obtain ⟨k, hk⟩ := Scheme.limitDescends_relative Scheme.limitDescends_isClosedImmersion hc
    (pullback.fst qj qj ≫ qj) (pullback.diagonal qj) hZ hY this
  refine ⟨k.left, k.hom, ⟨?_⟩⟩
  -- the diagonal at level `k` is a base change of `Δ_{X_j/E j}`
  have hk' := (IsPullback.of_hasPullback qj (E.map k.hom))
  have hW := IsPullback.pullback_map_fst hk' hk'
  have hD := hk'.diagonal
  have h1 := Scheme.pullback_snd_comp_of_isStableUnderBaseChange (pullback.diagonal qj)
    hW.isoPullback.hom (pullback.fst (pullback.fst qj qj ≫ qj) (E.map k.hom)) hk
  rw [IsPullback.isoPullback_hom_fst] at h1
  exact (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk (hD.isoIsPullback _ _ (IsPullback.of_hasPullback _ _)) (Iso.refl _)
      (by simp))).mpr h1

end AlgebraicGeometry
