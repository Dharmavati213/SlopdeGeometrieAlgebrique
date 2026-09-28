/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Projective.AmpleLocal
import SGA.Foundations.Projective.SectionRing
import SGA.Foundations.Projective.ToProj

/-!
# The canonical morphism to `Proj` of the ring of sections

Let `L` be a line bundle on a scheme `X` and `S = Γ_*(L) = ⊕ₙ Γ(X, L^{⊗n})`. If the non-vanishing
loci `X_s` of the homogeneous elements `s` of positive degree cover `X`, there is a canonical
morphism `X ⟶ Proj S`, given on `X_s` by `X_s ⟶ Spec Γ(X_s, 𝒪_X) ⟶ Spec S_(s) = D₊(s)`
(EGA II 3.7.1, 4.5.1). We show that the inverse image of `D₊(t)` is `X_t`, and that for `X`
quasi-compact and quasi-separated, `L` is ample iff this morphism is an open immersion
(EGA II 4.5.2).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite HomogeneousLocalization

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} {L : X.LineBundle} {R : Type u} [CommRing R] [Algebra R Γ(X, ⊤)]

section Chart

variable (L R) in
/-- The non-vanishing locus `X_s` of an element `s` of `Γ_*(L)`. -/
noncomputable abbrev secLocus (s : L.sectionRing R) : X.Opens :=
  L.famLocus ⊤ (L.coeFam R s)

lemma secLocus_mul_le_left {e : ℕ} (s : L.sectionRing R) {t : L.sectionRing R}
    (ht : t ∈ L.sectionGrading R e) : L.secLocus R (s * t) ≤ L.secLocus R s := by
  rw [secLocus, map_mul, famLocus_mul _ (isSection_coeFam ht)]
  exact inf_le_left

lemma secLocus_mul {e : ℕ} (s : L.sectionRing R) {t : L.sectionRing R}
    (ht : t ∈ L.sectionGrading R e) :
    L.secLocus R (s * t) = L.secLocus R s ⊓ L.secLocus R t := by
  rw [secLocus, map_mul, famLocus_mul _ (isSection_coeFam ht)]

/-- The restriction of the families of `Γ_*(L)_(s)` is compatible with `A_(s) → A_(st)`. -/
lemma famRes_awayToFam_awayMap {d e : ℕ} {s t x : L.sectionRing R}
    (hs : s ∈ L.sectionGrading R d) (ht : t ∈ L.sectionGrading R e) (hx : x = s * t)
    (hx' : x ∈ L.sectionGrading R (d + e)) {V : X.Opens} (hV : V ≤ L.secLocus R x)
    (y : Away (L.sectionGrading R) s) :
    L.famRes hV (L.awayToFam hx' (awayMap _ ht hx y)) =
      L.famRes (hV.trans (hx ▸ secLocus_mul_le_left s ht)) (L.awayToFam hs y) := by
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ hs y
  subst hx
  have hW := hV.trans (secLocus_mul_le_left s ht)
  -- the units `s` and `t` on `V`
  have hst := isUnit_famRes_famLocus (isSection_coeFam hx')
  simp only [map_mul] at hst
  have hsV : IsUnit (L.famRes (le_top : V ≤ ⊤) (L.coeFam R s)) := by
    have := (isUnit_of_mul_isUnit_left hst).map (L.famRes hV)
    simp only [famRes_famRes] at this
    exact this
  have htV : IsUnit (L.famRes (le_top : V ≤ ⊤) (L.coeFam R t)) := by
    have := (isUnit_of_mul_isUnit_right hst).map (L.famRes hV)
    simp only [famRes_famRes] at this
    exact this
  have hv := (awayToFam_mk_eq_iff hs n a ha (L.awayToFam hs (Away.mk _ hs n a ha))).mp rfl
  have hmem : a * t ^ n ∈ L.sectionGrading R (n • (d + e)) := by
    rw [smul_add]
    exact SetLike.mul_mem_graded ha (SetLike.pow_mem_graded n ht)
  have hw := (awayToFam_mk_eq_iff hx' n (a * t ^ n) hmem
    (L.awayToFam hx' (awayMap _ ht rfl (Away.mk _ hs n a ha)))).mp
    (congrArg (L.awayToFam hx') (awayMap_mk _ ht rfl n hs a ha)).symm
  have hv' := congrArg (L.famRes hW) hv
  have hw' := congrArg (L.famRes hV) hw
  simp only [map_mul, map_pow, famRes_famRes] at hv' hw'
  refine ((hsV.pow n).mul (htV.pow n)).mul_left_cancel ?_
  rw [hv'] at hw'
  linear_combination -1 * hw'

lemma awayToSections_awayMap_res {d e : ℕ} {s t x : L.sectionRing R}
    (hs : s ∈ L.sectionGrading R d) (ht : t ∈ L.sectionGrading R e) (hx : x = s * t)
    (hx' : x ∈ L.sectionGrading R (d + e)) {V : X.Opens} (hV : V ≤ L.secLocus R x) :
    CommRingCat.ofHom (L.awayToSections hs) ≫
        X.presheaf.map (homOfLE (hV.trans (hx ▸ secLocus_mul_le_left s ht))).op =
      CommRingCat.ofHom (awayMap _ ht hx) ≫ CommRingCat.ofHom (L.awayToSections hx') ≫
        X.presheaf.map (homOfLE hV).op := by
  ext y
  apply famConst_injective (L := L)
  have h1 := famRes_famConst (L := L) (hV.trans (hx ▸ secLocus_mul_le_left s ht))
    (L.awayToSections hs y)
  have h2 := famRes_famConst (L := L) hV (L.awayToSections hx' (awayMap _ ht hx y))
  simp only [famConst_awayToSections] at h1 h2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply]
  rw [← h1, ← h2, famRes_awayToFam_awayMap hs ht hx hx' hV]

lemma awayToSections_congr {d₁ d₂ : ℕ} {s : L.sectionRing R} (h₁ : s ∈ L.sectionGrading R d₁)
    (h₂ : s ∈ L.sectionGrading R d₂) (h : d₁ = d₂) :
    L.awayToSections h₁ = L.awayToSections h₂ := by
  subst h
  rfl

omit [Algebra R Γ(X, ⊤)] in
lemma _root_.AlgebraicGeometry.Proj.awayι_congr {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (x : A) {m₁ m₂ : ℕ} (h₁ : x ∈ 𝒜 m₁)
    (h₂ : x ∈ 𝒜 m₂) (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (h : m₁ = m₂) :
    Proj.awayι 𝒜 x h₁ hm₁ = Proj.awayι 𝒜 x h₂ hm₂ := by
  subst h
  rfl

variable (L R) in
/-- The chart `X_s ⟶ Spec Γ(X_s, 𝒪_X) ⟶ Spec Γ_*(L)_(s) = D₊(s) ⊆ Proj Γ_*(L)`. -/
noncomputable def projChart {d : ℕ} {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    (hd : 0 < d) : (L.secLocus R s).toScheme ⟶ Proj (L.sectionGrading R) :=
  (L.secLocus R s).toSpecΓ ≫ Spec.map (CommRingCat.ofHom (L.awayToSections hs)) ≫
    Proj.awayι _ s hs hd

lemma homOfLE_projChart {d e : ℕ} {s t x : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    (hd : 0 < d) (ht : t ∈ L.sectionGrading R e) (hx : x = s * t)
    (hx' : x ∈ L.sectionGrading R (d + e)) {V : X.Opens} (hV : V ≤ L.secLocus R x) :
    X.homOfLE (hV.trans (hx ▸ secLocus_mul_le_left s ht)) ≫ L.projChart R hs hd =
      V.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (L.awayToSections hx') ≫
        X.presheaf.map (homOfLE hV).op) ≫ Proj.awayι _ x hx' (by omega) := by
  rw [projChart, ← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc,
    awayToSections_awayMap_res hs ht hx hx' hV, Spec.map_comp, Category.assoc,
    Proj.SpecMap_awayMap_awayι]

end Chart

section Morphism

variable (L R) in
/-- The homogeneous elements of positive degree of `Γ_*(L)`. -/
def ProjIndex : Type u :=
  {p : ℕ × L.sectionRing R // 0 < p.1 ∧ p.2 ∈ L.sectionGrading R p.1}

variable (L R) in
/-- The non-vanishing loci of the homogeneous elements of positive degree of `Γ_*(L)` cover `X`
(for instance if `L` is ample). -/
def SecCovers : Prop :=
  ∀ x : X, ∃ j : L.ProjIndex R, x ∈ L.secLocus R j.1.2

lemma compat_projChart (j k : L.ProjIndex R) :
    X.homOfLE (inf_le_left : L.secLocus R j.1.2 ⊓ L.secLocus R k.1.2 ≤ _) ≫
        L.projChart R j.2.2 j.2.1 =
      X.homOfLE inf_le_right ≫ L.projChart R k.2.2 k.2.1 := by
  obtain ⟨⟨d, s⟩, hd, hs⟩ := j
  obtain ⟨⟨e, t⟩, he, ht⟩ := k
  have hx' : s * t ∈ L.sectionGrading R (d + e) := SetLike.mul_mem_graded hs ht
  have hx'' : s * t ∈ L.sectionGrading R (e + d) := add_comm d e ▸ hx'
  have hV : L.secLocus R s ⊓ L.secLocus R t ≤ L.secLocus R (s * t) := (secLocus_mul s ht).ge
  have h1 := homOfLE_projChart hs hd ht rfl hx' hV
  have h2 := homOfLE_projChart ht he hs (mul_comm s t) hx'' hV
  refine h1.trans (h2.trans ?_).symm
  rw [awayToSections_congr hx'' hx' (add_comm e d),
    Proj.awayι_congr _ _ hx'' hx' (by omega) (by omega) (add_comm e d)]

variable (L R) in
/-- The canonical morphism `X ⟶ Proj Γ_*(L)`, defined when the non-vanishing loci of the
homogeneous elements of positive degree cover `X` (EGA II 3.7.1, 4.5.1). -/
noncomputable def toProjSectionRing (hG : L.SecCovers R) : X ⟶ Proj (L.sectionGrading R) :=
  Scheme.glueOpens (fun j : L.ProjIndex R ↦ L.secLocus R j.1.2)
    (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr (hG x)) (fun j ↦ L.projChart R j.2.2 j.2.1)
    compat_projChart

variable (hG : L.SecCovers R)

@[reassoc]
lemma ι_toProjSectionRing {d : ℕ} {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d)
    (hd : 0 < d) : (L.secLocus R s).ι ≫ L.toProjSectionRing R hG = L.projChart R hs hd :=
  Scheme.ι_glueOpens _ _ _ _ (⟨⟨d, s⟩, hd, hs⟩ : L.ProjIndex R)

lemma basicOpen_awayToSections_isLocalizationElem {d e : ℕ} {s t : L.sectionRing R}
    (hs : s ∈ L.sectionGrading R d) (hd : 0 < d) (ht : t ∈ L.sectionGrading R e) :
    X.basicOpen (L.awayToSections hs (Away.isLocalizationElem hs ht)) =
      L.secLocus R s ⊓ L.secLocus R t := by
  have hmem : t ^ d ∈ L.sectionGrading R (e • d) := by
    rw [smul_eq_mul, mul_comm]
    exact SetLike.pow_mem_graded d ht
  have h := (awayToFam_mk_eq_iff hs e (t ^ d) hmem _).mp rfl
  have h' := congrArg (L.famLocus _) h
  rw [famLocus_mul _ (L.isSection_awayToFam hs _), map_pow, map_pow,
    famLocus_pow _ hd] at h'
  have hs1 : L.famLocus _ (L.famRes (famLocus_le (L.coeFam R s)) (L.coeFam R s) ^ e) =
      L.secLocus R s := by
    refine le_antisymm (famLocus_le _) ?_
    exact (famLocus_famRes_self _).ge.trans (famLocus_le_famLocus_pow _ e)
  rw [hs1, famLocus_famRes, inf_eq_right.mpr (famLocus_le _)] at h'
  rw [← famLocus_famConst (L := L), famConst_awayToSections]
  exact h'.symm

lemma projChart_preimage_basicOpen {d e : ℕ} {s t : L.sectionRing R}
    (hs : s ∈ L.sectionGrading R d) (hd : 0 < d) (ht : t ∈ L.sectionGrading R e) (he : 0 < e) :
    L.projChart R hs hd ⁻¹ᵁ Proj.basicOpen _ t = (L.secLocus R s).ι ⁻¹ᵁ L.secLocus R t := by
  rw [projChart, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    Proj.awayι_preimage_basicOpen _ hs hd ht he, SpecMap_preimage_basicOpen,
    Scheme.Opens.toSpecΓ_preimage_basicOpen]
  change (L.secLocus R s).ι ⁻¹ᵁ
    X.basicOpen (L.awayToSections hs (Away.isLocalizationElem hs ht)) = _
  rw [basicOpen_awayToSections_isLocalizationElem hs hd ht, Scheme.Hom.preimage_inf,
    Scheme.Opens.ι_preimage_self, top_inf_eq]

/-- The inverse image of `D₊(t)` under `X ⟶ Proj Γ_*(L)` is the non-vanishing locus `X_t`. -/
lemma toProjSectionRing_preimage_basicOpen {e : ℕ} {t : L.sectionRing R}
    (ht : t ∈ L.sectionGrading R e) (he : 0 < e) :
    L.toProjSectionRing R hG ⁻¹ᵁ Proj.basicOpen _ t = L.secLocus R t := by
  ext x
  obtain ⟨⟨⟨d, s⟩, hd, hs⟩, hx⟩ := hG x
  have h := congrArg (fun U : (L.secLocus R s).toScheme.Opens ↦ (⟨x, hx⟩ : L.secLocus R s) ∈ U)
    (projChart_preimage_basicOpen hs hd ht he)
  simp only [← ι_toProjSectionRing hG hs hd, Scheme.Hom.comp_preimage] at h
  exact propext_iff.mp h

end Morphism

section Ample

set_option backward.isDefEq.respectTransparency false in
/-- If `X` is quasi-compact and quasi-separated and `X_s` is affine, the chart at `s` is an open
immersion (EGA II 4.5.2, using `Γ(X_s, 𝒪_X) = Γ_*(L)_(s)`). -/
lemma isOpenImmersion_projChart [CompactSpace X] [QuasiSeparatedSpace X] {d : ℕ}
    {s : L.sectionRing R} (hs : s ∈ L.sectionGrading R d) (hd : 0 < d)
    (haff : IsAffineOpen (L.secLocus R s)) : IsOpenImmersion (L.projChart R hs hd) := by
  have : IsIso (L.secLocus R s).toSpecΓ := by
    rw [← haff.isoSpec_hom]
    infer_instance
  have : IsIso (CommRingCat.ofHom (L.awayToSections hs)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (awayToSections_bijective hs)
  unfold projChart
  infer_instance

/-- The element of `Γ_*(L)` defined by a global section of `L^{⊗n}`. -/
noncomputable def ofSections {n : ℕ} (t : L.sections n) : L.sectionRing R :=
  L.ofIsSection t.toFam t.isSection_toFam

lemma ofSections_mem {n : ℕ} (t : L.sections n) :
    ofSections (R := R) t ∈ L.sectionGrading R n :=
  ofIsSection_mem _ _

lemma secLocus_ofSections {n : ℕ} (t : L.sections n) :
    L.secLocus R (ofSections t) = L.nonvanishingLocus t := by
  simp only [secLocus, ofSections, coeFam_ofIsSection, sections.famLocus_toFam]

/-- If `L` is ample, the non-vanishing loci of the homogeneous elements of positive degree of
`Γ_*(L)` cover `X`. -/
lemma IsAmple.secCovers (hL : L.IsAmple) : L.SecCovers R := fun x ↦ by
  obtain ⟨n, hn, t, hx, -⟩ := hL.2 x
  exact ⟨⟨⟨n, ofSections t⟩, hn, ofSections_mem t⟩, by rwa [secLocus_ofSections]⟩

/-- EGA II 4.5.2 (a) ⇒ (d'): if `L` is ample, `X ⟶ Proj Γ_*(L)` is an open immersion. -/
theorem IsAmple.isOpenImmersion_toProjSectionRing (hL : L.IsAmple) :
    IsOpenImmersion (L.toProjSectionRing R hL.secCovers) := by
  have := hL.1
  have := hL.quasiSeparatedSpace
  have key (x : X) : ∃ (n : ℕ) (hn : 0 < n) (t : L.sections n), x ∈ L.nonvanishingLocus t ∧
      IsAffineOpen (L.secLocus R (ofSections t)) := by
    obtain ⟨n, hn, t, hx, ht⟩ := hL.2 x
    exact ⟨n, hn, t, hx, by rwa [secLocus_ofSections]⟩
  refine IsOpenImmersion.of_forall_source_exists (L.toProjSectionRing R hL.secCovers) ?_
    fun x ↦ ?_
  · intro x x' hxx'
    obtain ⟨n, hn, t, hx, haff⟩ := key x
    have hx₁ : x ∈ L.secLocus R (ofSections (R := R) t) := by rwa [secLocus_ofSections]
    have hx₂ : x' ∈ L.secLocus R (ofSections (R := R) t) := by
      rw [← toProjSectionRing_preimage_basicOpen hL.secCovers (ofSections_mem t) hn] at hx₁ ⊢
      change L.toProjSectionRing R hL.secCovers x' ∈
        Proj.basicOpen (L.sectionGrading R) (ofSections t)
      rw [← hxx']
      exact hx₁
    have := isOpenImmersion_projChart (ofSections_mem t) hn haff
    have h := (L.projChart R (ofSections_mem t) hn).isOpenEmbedding.injective
      (a₁ := ⟨x, hx₁⟩) (a₂ := ⟨x', hx₂⟩) (by
        rw [← ι_toProjSectionRing hL.secCovers (ofSections_mem t) hn]
        exact hxx')
    exact congrArg Subtype.val h
  · obtain ⟨n, hn, t, hx, haff⟩ := key x
    refine ⟨_, (L.secLocus R (ofSections t)).ι, inferInstance, ?_, ?_⟩
    · rw [Scheme.Opens.opensRange_ι, secLocus_ofSections]
      exact hx
    · rw [ι_toProjSectionRing hL.secCovers (ofSections_mem t) hn]
      exact isOpenImmersion_projChart _ hn haff

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.5.2 (d') ⇒ (a): if `X` is quasi-compact, the `X_s` cover `X` and `X ⟶ Proj Γ_*(L)`
is an open immersion, then `L` is ample. -/
theorem isAmple_of_isOpenImmersion [CompactSpace X] (hG : L.SecCovers R)
    [IsOpenImmersion (L.toProjSectionRing R hG)] : L.IsAmple := by
  refine ⟨inferInstance, fun x ↦ ?_⟩
  obtain ⟨⟨⟨d, s⟩, hd, hs⟩, hx⟩ := hG x
  have hrx : L.toProjSectionRing R hG x ∈ Proj.basicOpen (L.sectionGrading R) s := by
    rw [← Scheme.Hom.mem_preimage, toProjSectionRing_preimage_basicOpen hG hs hd]
    exact hx
  obtain ⟨_, ⟨f, rfl⟩, hxf, hfle⟩ := Opens.isBasis_iff_nbhd.mp (Proj.isBasis_basicOpen _)
    (show L.toProjSectionRing R hG x ∈ (L.toProjSectionRing R hG).opensRange ⊓
      Proj.basicOpen _ s from ⟨⟨x, rfl⟩, hrx⟩)
  rw [Proj.basicOpen_eq_iSup_proj] at hxf hfle
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxf
  have hg₀ : GradedRing.proj (L.sectionGrading R) i f * s ∈ L.sectionGrading R (i + d) :=
    SetLike.mul_mem_graded (by simp [GradedRing.proj_apply]) hs
  have hDg₀ : Proj.basicOpen (L.sectionGrading R) (GradedRing.proj (L.sectionGrading R) i f * s) ≤
      (L.toProjSectionRing R hG).opensRange := by
    rw [Proj.basicOpen_mul]
    exact (inf_le_left.trans (le_iSup (fun i ↦ Proj.basicOpen _
      (GradedRing.proj (L.sectionGrading R) i f)) i)).trans (hfle.trans inf_le_left)
  have hxg₀ : L.toProjSectionRing R hG x ∈
      Proj.basicOpen (L.sectionGrading R) (GradedRing.proj (L.sectionGrading R) i f * s) := by
    rw [Proj.basicOpen_mul]
    exact ⟨hi, hrx⟩
  generalize GradedRing.proj (L.sectionGrading R) i f * s = g at hg₀ hDg₀ hxg₀
  have hgd : 0 < i + d := by omega
  have hiso : IsIso (L.toProjSectionRing R hG ∣_ Proj.basicOpen (L.sectionGrading R) g) := by
    rw [isIso_iff_isOpenImmersion_and_surjective]
    refine ⟨inferInstance, ⟨fun y ↦ ?_⟩⟩
    obtain ⟨z, hz⟩ := hDg₀ y.2
    refine ⟨⟨z, show L.toProjSectionRing R hG z ∈ _ from hz ▸ y.2⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hz
  have haff : IsAffineOpen (L.toProjSectionRing R hG ⁻¹ᵁ Proj.basicOpen (L.sectionGrading R) g) :=
    @IsAffine.of_isIso _ _ (L.toProjSectionRing R hG ∣_ Proj.basicOpen (L.sectionGrading R) g)
      hiso (Proj.isAffineOpen_basicOpen (L.sectionGrading R) g hg₀ hgd)
  rw [toProjSectionRing_preimage_basicOpen hG hg₀ hgd] at haff
  refine ⟨i + d, hgd, L.sectionsOfFam _ (isSection_coeFam hg₀), ?_, ?_⟩ <;>
    rw [nonvanishingLocus_sectionsOfFam]
  · exact (toProjSectionRing_preimage_basicOpen hG hg₀ hgd).le hxg₀
  · exact haff

/-- EGA II 4.5.2 (a) ⇔ (d'): a line bundle `L` on a quasi-compact scheme `X` is ample iff the
non-vanishing loci of the homogeneous elements of positive degree of `Γ_*(L)` cover `X` and the
canonical morphism `X ⟶ Proj Γ_*(L)` is an open immersion. -/
theorem isAmple_iff_isOpenImmersion [CompactSpace X] :
    L.IsAmple ↔ ∃ hG : L.SecCovers R, IsOpenImmersion (L.toProjSectionRing R hG) :=
  ⟨fun hL ↦ ⟨hL.secCovers, hL.isOpenImmersion_toProjSectionRing⟩,
    fun ⟨hG, _⟩ ↦ isAmple_of_isOpenImmersion (R := R) hG⟩

end Ample

end AlgebraicGeometry.Scheme.LineBundle
