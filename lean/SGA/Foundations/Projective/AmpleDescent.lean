/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.AmpleProj
import SGA.Foundations.Projective.ProjBaseChange
import SGA.Foundations.Projective.SectionsBaseChange

/-!
# Faithfully flat descent of ampleness

Let `Y' ⟶ Y` be a faithfully flat morphism of affine schemes, `X ⟶ Y` a morphism with `X`
quasi-compact and quasi-separated, `X' = X ×_Y Y'`, and `L` a line bundle on `X`. If the inverse
image of `L` on `X'` is ample, then `L` is ample (EGA IV 2.7.2, SGA 1 VIII.5.8).

As in EGA, we use the characterization of ampleness by the canonical morphism
`X ⟶ Proj Γ_*(L)` (`SGA.Foundations.Projective.AmpleProj`): by flat base change,
`Γ_*(L') = Γ(Y') ⊗ Γ_*(L)` (`SGA.Foundations.Projective.SectionsBaseChange`), so
`Proj Γ_*(L') = Proj Γ_*(L) ×_Y Y'` (`SGA.Foundations.Projective.ProjBaseChange`), and the morphism
for `L'` is the base change of the morphism for `L`; open immersions descend along faithfully
flat quasi-compact morphisms.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite HomogeneousLocalization

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} {L : X.LineBundle} {R : Type u} [CommRing R] [Algebra R Γ(X, ⊤)]

section SectionRingMap

variable {T : Scheme.{u}} (g : T ⟶ X) (R' : Type u) [CommRing R'] [Algebra R' Γ(T, ⊤)]

variable (L R) in
/-- The inverse image of sections of `L^{⊗n}` over `X` along `g`. -/
noncomputable def pullAdd (n : ℕ) :
    L.sectionSubmodule R n →+ (L.pullback g).sectionSubmodule R' n where
  toFun s := ⟨L.famPullback g g.preimage_top.ge s.1, s.2.famPullback g _⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

variable (L R) in
/-- The ring homomorphism `Γ_*(L) → Γ_*(g^* L)` given by the inverse image of sections. -/
noncomputable def sectionRingMap : L.sectionRing R →+* (L.pullback g).sectionRing R' :=
  DirectSum.toSemiring (fun n ↦ (DirectSum.of _ n).comp (L.pullAdd R g R' n))
    (by
      change DirectSum.of _ 0 _ = DirectSum.of _ 0 _
      congr 1
      exact Subtype.ext (map_one _))
    (fun {i j} a b ↦ by
      change DirectSum.of _ (i + j) _ = DirectSum.of _ i _ * DirectSum.of _ j _
      rw [DirectSum.of_mul_of]
      congr 1
      exact Subtype.ext (map_mul _ _ _))

lemma sectionRingMap_of (n : ℕ) (s : L.sectionSubmodule R n) :
    L.sectionRingMap R g R' (DirectSum.of _ n s) =
      DirectSum.of _ n ⟨L.famPullback g g.preimage_top.ge s.1,
        s.2.famPullback g _⟩ :=
  DirectSum.toSemiring_of _ _ _ _ _

lemma coeFam_sectionRingMap (x : L.sectionRing R) :
    (L.pullback g).coeFam R' (L.sectionRingMap R g R' x) =
      L.famPullback g g.preimage_top.ge (L.coeFam R x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n s =>
    rw [sectionRingMap_of]
    simp only [coeFam_of]
  | add x y hx hy => simp only [map_add, hx, hy]

lemma sectionRingMap_mem {n : ℕ} {x : L.sectionRing R} (hx : x ∈ L.sectionGrading R n) :
    L.sectionRingMap R g R' x ∈ (L.pullback g).sectionGrading R' n := by
  obtain ⟨s, rfl⟩ := hx
  change L.sectionRingMap R g R' (DirectSum.of _ n s) ∈ _
  rw [sectionRingMap_of]
  exact DirectSum.of_mem_lofGrading _ n _

variable (L R) in
/-- `Γ_*(L) → Γ_*(g^* L)` as a homomorphism of graded rings. -/
noncomputable def sectionGradedHom : L.sectionGrading R →+*ᵍ (L.pullback g).sectionGrading R' where
  __ := L.sectionRingMap R g R'
  map_mem := sectionRingMap_mem g R'

lemma secLocus_sectionRingMap (x : L.sectionRing R) :
    (L.pullback g).secLocus R' (L.sectionRingMap R g R' x) = g ⁻¹ᵁ L.secLocus R x := by
  rw [secLocus, coeFam_sectionRingMap, famLocus_famPullback, top_inf_eq]

end SectionRingMap

section Naturality

variable {T : Scheme.{u}} {g : T ⟶ X} {R' : Type u} [CommRing R'] [Algebra R' Γ(T, ⊤)]
  (ψ : L.sectionGrading R →+*ᵍ (L.pullback g).sectionGrading R')
  (hψ : ∀ x, (L.pullback g).coeFam R' (ψ x) = L.famPullback g g.preimage_top.ge (L.coeFam R x))

include hψ in
lemma secLocus_of_coeFam_eq (x : L.sectionRing R) :
    (L.pullback g).secLocus R' (ψ x) = g ⁻¹ᵁ L.secLocus R x := by
  rw [secLocus, hψ, famLocus_famPullback, top_inf_eq]

include hψ in
lemma awayToSections_map_apply {d : ℕ} {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    (hψs : ψ s ∈ (L.pullback g).sectionGrading R' d)
    (e : (L.pullback g).secLocus R' (ψ s) ≤ g ⁻¹ᵁ L.secLocus R s)
    (y : Away (L.sectionGrading R) s) :
    g.appLE _ _ e (L.awayToSections hs y) =
      (L.pullback g).awayToSections hψs (Away.map ψ s y) := by
  refine famConst_injective (L := L.pullback g) ((L.pullback g).secLocus R' (ψ s)) ?_
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hs y
  refine (famPullback_famConst g e _).symm.trans ?_
  refine (congrArg (L.famPullback g e) (famConst_awayToSections hs _)).trans ?_
  refine Eq.trans ?_ (famConst_awayToSections hψs _).symm
  have hmem : ψ a ∈ (L.pullback g).sectionGrading R' (n • d) := ψ.2 ha
  have hmap : Away.map ψ s (Away.mk _ hs n a ha) = Away.mk _ hψs n (ψ a) hmem := Away.map_mk ..
  refine Eq.trans ?_ (congrArg ((L.pullback g).awayToFam hψs) hmap).symm
  symm
  refine (awayToFam_mk_eq_iff hψs n (ψ a) hmem _).mpr ?_
  have hv := (awayToFam_mk_eq_iff hs n a ha (L.awayToFam hs (Away.mk _ hs n a ha))).mp rfl
  have h := congrArg (L.famPullback g e) hv
  simp only [map_mul, map_pow, famPullback_famRes] at h
  simp only [hψ, famRes_famPullback]
  exact h

set_option backward.isDefEq.respectTransparency false in
include hψ in
/-- Naturality of `X ⟶ Proj Γ_*(L)` with respect to inverse images (EGA II 3.7.4). -/
theorem comp_toProjSectionRing (hG : L.SecCovers R) (hG' : (L.pullback g).SecCovers R')
    (hirr : HomogeneousIdeal.irrelevant ((L.pullback g).sectionGrading R') ≤
      (HomogeneousIdeal.irrelevant (L.sectionGrading R)).map ψ) :
    g ≫ L.toProjSectionRing R hG =
      (L.pullback g).toProjSectionRing R' hG' ≫ Proj.map ψ hirr := by
  have hcov : IsOpenCover (fun j : L.ProjIndex R ↦ (L.pullback g).secLocus R' (ψ j.1.2)) := by
    refine eq_top_iff.mpr fun t _ ↦ ?_
    obtain ⟨j, hj⟩ := hG (g t)
    exact Opens.mem_iSup.mpr ⟨j, by rw [secLocus_of_coeFam_eq ψ hψ]; exact hj⟩
  refine Scheme.Cover.hom_ext (T.openCoverOfIsOpenCover _ hcov) _ _ fun j ↦ ?_
  obtain ⟨⟨d, s⟩, hd, hs⟩ := j
  change ((L.pullback g).secLocus R' (ψ s)).ι ≫ _ = ((L.pullback g).secLocus R' (ψ s)).ι ≫ _
  have e : (L.pullback g).secLocus R' (ψ s) ≤ g ⁻¹ᵁ L.secLocus R s :=
    (secLocus_of_coeFam_eq ψ hψ s).le
  have hψs : ψ s ∈ (L.pullback g).sectionGrading R' d := ψ.2 hs
  rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι g e, Category.assoc,
    ι_toProjSectionRing hG hs hd, ← Category.assoc, ι_toProjSectionRing hG' hψs hd]
  simp only [projChart, Category.assoc]
  have hring : CommRingCat.ofHom (L.awayToSections hs) ≫ g.appLE _ _ e =
      CommRingCat.ofHom (Away.map ψ s) ≫
        CommRingCat.ofHom ((L.pullback g).awayToSections hψs) := by
    ext y
    exact awayToSections_map_apply ψ hψ hs hψs e y
  have key : Spec.map (g.appLE _ _ e) ≫ Spec.map (CommRingCat.ofHom (L.awayToSections hs)) =
      Spec.map (CommRingCat.ofHom ((L.pullback g).awayToSections hψs)) ≫
        Spec.map (CommRingCat.ofHom (Away.map ψ s)) := by
    simpa only [Spec.map_comp] using congrArg Spec.map hring
  rw [Proj.awayι_comp_map ψ hirr hd s hs]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  simpa only [Category.assoc] using congrArg (fun φ ↦ ((L.pullback g).secLocus R' (ψ s)).toSpecΓ ≫
    φ ≫ Proj.awayι (L.sectionGrading R) s hs hd) key

end Naturality

section StructureMap

lemma awayToSections_algebraMap {d : ℕ} {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    (r : R) : L.awayToSections hs (algebraMap R (Away (L.sectionGrading R) s) r) =
      X.presheaf.map (homOfLE (le_top : L.secLocus R s ≤ ⊤)).op (algebraMap R Γ(X, ⊤) r) := by
  have h0 : algebraMap R (L.sectionRing R) r ∈ L.sectionGrading R (0 • d) := by
    rw [zero_smul]
    exact SetLike.algebraMap_mem_graded _ r
  have e : algebraMap R (Away (L.sectionGrading R) s) r =
      Away.mk _ hs 0 (algebraMap R (L.sectionRing R) r) h0 := by
    ext
    rw [Away.val_mk, val_algebraMap,
      show (⟨s ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers s) = 1 from Subtype.ext (pow_zero s),
      Localization.mk_one_eq_algebraMap, ← IsScalarTower.algebraMap_apply]
  refine famConst_injective (L := L) (L.secLocus R s) ?_
  refine (famConst_awayToSections hs _).trans ?_
  refine (congrArg (L.awayToFam hs) e).trans ?_
  refine Eq.trans ?_ (algebraMap_fam L R _ r)
  refine (awayToFam_mk_eq_iff hs 0 _ h0 _).mpr ?_
  rw [pow_zero, one_mul, AlgHom.commutes, famRes_algebraMap]

variable {Y : Scheme.{u}} {f : X ⟶ Y} [Algebra Γ(Y, ⊤) Γ(X, ⊤)]
  (hf : algebraMap Γ(Y, ⊤) Γ(X, ⊤) = f.appTop.hom)

set_option backward.isDefEq.respectTransparency false in
include hf in
/-- The morphism `X ⟶ Proj Γ_*(L)` lies over the base `Y` (for `Y` affine). -/
theorem toProjSectionRing_toSpecBase (hG : L.SecCovers Γ(Y, ⊤)) :
    L.toProjSectionRing Γ(Y, ⊤) hG ≫
        Proj.toSpecBase (R := Γ(Y, ⊤)) (A := L.sectionRing Γ(Y, ⊤)) (L.sectionGrading Γ(Y, ⊤)) =
      (f ≫ Y.toSpecΓ : X ⟶ Spec (CommRingCat.of Γ(Y, ⊤))) := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr (hG x))) _ _ fun j ↦ ?_
  obtain ⟨⟨d, s⟩, hd, hs⟩ := j
  dsimp only at hd hs ⊢
  change (L.secLocus Γ(Y, ⊤) s).ι ≫ _ = (L.secLocus Γ(Y, ⊤) s).ι ≫ _
  have e : L.secLocus Γ(Y, ⊤) s ≤ f ⁻¹ᵁ ⊤ := le_top.trans f.preimage_top.ge
  have hring : CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Away (L.sectionGrading Γ(Y, ⊤)) s)) ≫
      CommRingCat.ofHom (L.awayToSections hs) = f.appLE ⊤ (L.secLocus Γ(Y, ⊤) s) e := by
    ext r
    change L.awayToSections hs (algebraMap Γ(Y, ⊤) _ r) = _
    rw [awayToSections_algebraMap, hf]
    rfl
  have key : Spec.map (CommRingCat.ofHom (L.awayToSections hs)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap Γ(Y, ⊤) (Away (L.sectionGrading Γ(Y, ⊤)) s))) =
        Spec.map (f.appLE ⊤ (L.secLocus Γ(Y, ⊤) s) e) := by
    simpa only [Spec.map_comp] using congrArg Spec.map hring
  rw [← Category.assoc, ι_toProjSectionRing hG hs hd, projChart, Category.assoc, Category.assoc,
    Proj.awayι_toSpecBase, key, Scheme.Opens.toSpecΓ_SpecMap_appLE,
    ← Scheme.Hom.resLE_comp_ι_assoc f e, Scheme.Opens.toSpecΓ_top]

end StructureMap

section QuasiAffine

lemma basicOpen_awayToSections_mk {d : ℕ} {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    (k : ℕ) (t : L.sectionRing R) (ht : t ∈ L.sectionGrading R (k • d)) :
    X.basicOpen (L.awayToSections hs (Away.mk _ hs k t ht)) =
      L.secLocus R s ⊓ L.secLocus R t := by
  have h := (awayToFam_mk_eq_iff hs k t ht _).mp rfl
  have h' := congrArg (L.famLocus _) h
  rw [famLocus_mul _ (L.isSection_awayToFam hs _), famLocus_famRes] at h'
  have hs1 : L.famLocus _ (L.famRes (famLocus_le (L.coeFam R s)) (L.coeFam R s) ^ k) =
      L.secLocus R s := by
    refine le_antisymm (famLocus_le _) ?_
    exact (famLocus_famRes_self _).ge.trans (famLocus_le_famLocus_pow _ k)
  rw [hs1, inf_eq_right.mpr (famLocus_le _)] at h'
  rw [← famLocus_famConst (L := L), famConst_awayToSections]
  exact h'.symm

/-- If `L` is ample, the non-vanishing loci `X_s` of the homogeneous elements of positive degree of
`Γ_*(L)` are quasi-affine (EGA II 4.5.2). -/
theorem IsAmple.isQuasiAffine_secLocus (hL : L.IsAmple) {d : ℕ} {s : L.sectionRing R}
    (hs : s ∈ L.sectionGrading R d) (hd : 0 < d) : (L.secLocus R s).toScheme.IsQuasiAffine := by
  have := hL.1
  have : CompactSpace (L.secLocus R s) := isCompact_iff_compactSpace.mp
    (isCompact_famLocus isCompact_univ (isSection_coeFam hs))
  refine .of_forall_exists_mem_basicOpen _ fun x ↦ ?_
  obtain ⟨n, -, t, hxt, htW, hta⟩ := hL.exists_nonvanishingLocus_le x.2
  have hb := basicOpen_awayToSections_isLocalizationElem hs hd (ofSections_mem (R := R) t)
  rw [secLocus_ofSections, inf_eq_right.mpr htW] at hb
  refine ⟨(L.secLocus R s).topIso.inv
    (L.awayToSections hs (Away.isLocalizationElem hs (ofSections_mem (R := R) t))), ?_, ?_⟩
  · rw [← (L.secLocus R s).ι.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Opens.ι_image_basicOpen_topIso_inv, hb]
    exact hta
  · rw [← Scheme.Hom.apply_mem_image_iff (L.secLocus R s).ι,
      Scheme.Opens.ι_image_basicOpen_topIso_inv, hb]
    exact hxt

/-- Over a quasi-compact quasi-separated `X`, a point `x` of a quasi-affine non-vanishing locus
`X_s` of a homogeneous element `s` of positive degree of `Γ_*(L)` lies in an affine non-vanishing
locus `X_{st}`: the affine basic opens `(X_s)_r` form a basis of `X_s`, and
`Γ(X_s, 𝒪_X) = Γ_*(L)_(s)` (EGA II 4.5.2). -/
theorem exists_isAffineOpen_of_isQuasiAffine_secLocus [CompactSpace X] [QuasiSeparatedSpace X]
    {d : ℕ} (hd : 0 < d) {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    [(L.secLocus R s).toScheme.IsQuasiAffine] {x : X} (hx : x ∈ L.secLocus R s) :
    ∃ (n : ℕ) (_ : 0 < n) (t : L.sections n), x ∈ L.nonvanishingLocus t ∧
      IsAffineOpen (L.nonvanishingLocus t) := by
  obtain ⟨_, ⟨r, hr, rfl⟩, hxr, -⟩ := Opens.isBasis_iff_nbhd.mp
    (IsQuasiAffine.isBasis_basicOpen (L.secLocus R s))
    (show (⟨x, hx⟩ : L.secLocus R s) ∈ (⊤ : (L.secLocus R s).toScheme.Opens) from _root_.trivial)
  obtain ⟨y, hy⟩ := (awayToSections_bijective hs).2 ((L.secLocus R s).topIso.hom r)
  obtain ⟨k, t, ht, rfl⟩ := Away.mk_surjective _ hs y
  have hr' : r = (L.secLocus R s).topIso.inv (L.awayToSections hs (Away.mk _ hs k t ht)) := by
    rw [hy, Iso.hom_inv_id_apply]
  have himage : (L.secLocus R s).ι ''ᵁ (L.secLocus R s).toScheme.basicOpen r =
      L.secLocus R (s * t) := by
    rw [hr', Scheme.Opens.ι_image_basicOpen_topIso_inv, basicOpen_awayToSections_mk,
      secLocus_mul s ht]
  have hst : s * t ∈ L.sectionGrading R (d + k • d) := SetLike.mul_mem_graded hs ht
  refine ⟨d + k • d, by positivity, L.sectionsOfFam _ (isSection_coeFam hst), ?_, ?_⟩ <;>
    rw [nonvanishingLocus_sectionsOfFam]
  · change x ∈ L.secLocus R (s * t)
    rw [← himage]
    exact ⟨⟨x, hx⟩, hxr, rfl⟩
  · change IsAffineOpen (L.secLocus R (s * t))
    rw [← himage, (L.secLocus R s).ι.isAffineOpen_iff_of_isOpenImmersion]
    exact hr

/-- Conversely, over a quasi-compact quasi-separated `X`, if the non-vanishing loci of the
homogeneous elements of positive degree of `Γ_*(L)` cover `X` and are quasi-affine, then `L` is
ample (EGA II 4.5.2). -/
theorem isAmple_of_isQuasiAffine_secLocus [CompactSpace X] [QuasiSeparatedSpace X]
    (hG : L.SecCovers R) (H : ∀ (d : ℕ) (s : L.sectionRing R), s ∈ L.sectionGrading R d →
      0 < d → (L.secLocus R s).toScheme.IsQuasiAffine) : L.IsAmple := by
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨⟨⟨d, s⟩, hd, hs⟩, hx⟩ := hG x
  dsimp only at hd hs hx
  have := H d s hs hd
  exact exists_isAffineOpen_of_isQuasiAffine_secLocus hd hs hx

/-- EGA II 4.5.2: over a quasi-compact quasi-separated `X`, `L` is ample if every point lies in
the non-vanishing locus `X_t` of a section `t` of a positive power of `L` with `X_t`
quasi-affine. -/
theorem isAmple_of_forall_exists_isQuasiAffine [CompactSpace X] [QuasiSeparatedSpace X]
    (H : ∀ x : X, ∃ (d : ℕ) (_ : 0 < d) (t : L.Fam ⊤), L.IsSection d ⊤ t ∧
      x ∈ L.famLocus ⊤ t ∧ (L.famLocus ⊤ t).toScheme.IsQuasiAffine) : L.IsAmple := by
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨d, hd, t, ht, hx, hqa⟩ := H x
  have hs := ofIsSection_mem (R := Γ(X, ⊤)) t ht
  have hloc : L.secLocus Γ(X, ⊤) (L.ofIsSection t ht) = L.famLocus ⊤ t := by
    simp only [secLocus, coeFam_ofIsSection]
  have : (L.secLocus Γ(X, ⊤) (L.ofIsSection t ht)).toScheme.IsQuasiAffine := hloc ▸ hqa
  exact exists_isAffineOpen_of_isQuasiAffine_secLocus hd hs (hloc ▸ hx)

end QuasiAffine

section Covering

variable {X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {fst : X' ⟶ X} {snd : X' ⟶ Y'}

set_option backward.isDefEq.respectTransparency false in
/-- If the non-vanishing loci of the sections of positive powers of the inverse image of `L` on
`X' = X ×_Y Y'` cover `X'`, for a faithfully flat morphism `Y' ⟶ Y` of affine schemes and `X`
quasi-compact and quasi-separated, then those of the sections of positive powers of `L` cover
`X`: by flat base change, the sections of `L'^{⊗d}` are combinations of inverse images of
sections of `L^{⊗d}`. -/
theorem exists_isSection_mem_famLocus_of_isPullback (H : IsPullback fst snd f g) [IsAffine Y]
    [IsAffine Y'] [Flat g] [Surjective g] [CompactSpace X] [QuasiSeparatedSpace X]
    (hL : ∀ x' : X', ∃ (d : ℕ) (_ : 0 < d) (s' : (L.pullback fst).Fam ⊤),
      (L.pullback fst).IsSection d ⊤ s' ∧ x' ∈ (L.pullback fst).famLocus ⊤ s') (x : X) :
    ∃ (d : ℕ) (_ : 0 < d) (s : L.Fam ⊤), L.IsSection d ⊤ s ∧ x ∈ L.famLocus ⊤ s := by
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  let : Algebra Γ(Y', ⊤) Γ(X', ⊤) := snd.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(Y', ⊤) := g.appTop.hom.toAlgebra
  let : Algebra Γ(Y, ⊤) Γ(X', ⊤) := (snd.appTop.hom.comp g.appTop.hom).toAlgebra
  have : IsScalarTower Γ(Y, ⊤) Γ(Y', ⊤) Γ(X', ⊤) := .of_algebraMap_eq' rfl
  have hfst : Surjective fst := MorphismProperty.of_isPullback H.flip inferInstance
  obtain ⟨x', rfl⟩ := hfst.surj x
  obtain ⟨d, hd, s', hs', hx'⟩ := hL x'
  have hbc := L.isBaseChange_pullLin rfl rfl rfl H (d : ℤ)
  suffices ∀ v : (L.pullback fst).sectionSubmoduleOn Γ(Y', ⊤) d ⊤,
      ∀ y' ∈ (L.pullback fst).famLocus ⊤ v.1,
        ∃ s : L.Fam ⊤, L.IsSection d ⊤ s ∧ fst y' ∈ L.famLocus ⊤ s by
    obtain ⟨s, hs, hxs⟩ := this ⟨s', hs'⟩ x' hx'
    exact ⟨d, hd, s, hs, hxs⟩
  intro v
  refine hbc.inductionOn v _ ?_ ?_ ?_ ?_
  · intro y' hy'
    simp only [ZeroMemClass.coe_zero, famLocus_zero] at hy'
    exact hy'.elim
  · intro m y' hy'
    refine ⟨m.1, m.2, ?_⟩
    rw [coe_pullLin, famLocus_famPullback, top_inf_eq] at hy'
    exact hy'
  · intro r w hw y' hy'
    refine hw y' ?_
    change y' ∈ (L.pullback fst).famLocus ⊤ (r • w.1) at hy'
    rw [Algebra.smul_def, famLocus_mul _ w.2] at hy'
    exact hy'.2
  · intro w₁ w₂ hw₁ hw₂ y' hy'
    rcases famLocus_add_le w₁.1 w₂.1 hy' with hy' | hy'
    exacts [hw₁ y' hy', hw₂ y' hy']

end Covering

end AlgebraicGeometry.Scheme.LineBundle
