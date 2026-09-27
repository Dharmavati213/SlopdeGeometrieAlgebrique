/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Projective.SectionExtension

/-!
# Ample line bundles: basis of the topology, restriction, locality on the base

Using the extension of sections of powers of a line bundle over quasi-compact quasi-separated
opens (`SGA.Foundations.Projective.SectionExtension`), we prove:

- `Scheme.LineBundle.IsAmple.quasiSeparatedSpace`: a scheme with an ample line bundle is
  quasi-separated.
- `Scheme.LineBundle.IsAmple.exists_nonvanishingLocus_le`: if `L` is ample, the affine
  non-vanishing loci `X_s` of sections of positive powers of `L` form a basis of the topology
  of `X` (EGA II 4.5.2 (a')).
- `Scheme.LineBundle.IsAmple.pullback_ι`: the restriction of an ample line bundle to a
  quasi-compact open subset is ample (EGA II 4.5.6 (i)).
- `Scheme.LineBundle.exists_of_isAmple_pullback_basicOpen`: over a quasi-compact quasi-separated
  `X`, the points of `D(h)` at which `L|_{D(h)}` is ample have affine neighbourhoods `X_t ⊆ D(h)`.
- `Scheme.LineBundle.isRelativelyAmple_of_iSup_eq_top`: relative ampleness is local on the base
  (EGA II 4.6.4).
-/

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.LineBundle

variable {X : Scheme.{u}} {L : X.LineBundle}

set_option backward.isDefEq.respectTransparency false in
/-- A scheme with an ample line bundle is quasi-separated: it is covered by the affine opens
`X_s`, whose pairwise intersections are quasi-compact. -/
theorem IsAmple.quasiSeparatedSpace (hL : L.IsAmple) : QuasiSeparatedSpace X := by
  let I := {p : Σ n : ℕ, L.sections n // IsAffineOpen (L.nonvanishingLocus p.2)}
  refine Scheme.quasiSeparatedSpace_of_isOpenCover (I := I)
    (fun p ↦ L.nonvanishingLocus p.1.2) ?_ (fun p ↦ p.2) fun p q ↦ ?_
  · refine eq_top_iff.mpr fun x _ ↦ ?_
    obtain ⟨n, -, s, hx, hs⟩ := hL.2 x
    exact Opens.mem_iSup.mpr ⟨⟨⟨n, s⟩, hs⟩, hx⟩
  · have h := isCompact_famLocus (L := L) p.2.isCompact
      ((q.1.2.isSection_toFam).famRes (le_top : L.nonvanishingLocus p.1.2 ≤ ⊤))
    rwa [famLocus_famRes, sections.famLocus_toFam] at h

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.5.2 (a'): if `L` is ample, the affine non-vanishing loci `X_t` of sections of
positive powers of `L` form a basis of the topology of `X`. -/
theorem IsAmple.exists_nonvanishingLocus_le (hL : L.IsAmple) {W : X.Opens} {x : X}
    (hx : x ∈ W) : ∃ (n : ℕ) (_ : 0 < n) (t : L.sections n), x ∈ L.nonvanishingLocus t ∧
      L.nonvanishingLocus t ≤ W ∧ IsAffineOpen (L.nonvanishingLocus t) := by
  have := hL.1
  have := hL.quasiSeparatedSpace
  obtain ⟨n, hn, s, hxs, hsa⟩ := hL.2 x
  have hS := s.isSection_toFam
  have hSloc := s.famLocus_toFam
  rw [← hSloc] at hxs hsa
  obtain ⟨h, hhW, hxh⟩ := hsa.exists_basicOpen_le ⟨x, hx⟩ hxs
  obtain ⟨k, y, hy, hyr⟩ := exists_isSection_famRes_eq (U := ⊤) isCompact_univ
    (isQuasiSeparated_univ) hS (isSection_famConst (L := L) h)
  have hT : L.IsSection ((n + k * n : ℕ) : ℤ) ⊤ (s.toFam * y) :=
    (hS.mul hy).of_eq (by push_cast; ring)
  have hloc : L.famLocus ⊤ (s.toFam * y) = X.basicOpen h := by
    rw [famLocus_mul_eq hy (isSection_famConst h) hyr, famLocus_famConst]
  refine ⟨n + k * n, by positivity, L.sectionsOfFam _ hT, ?_, ?_, ?_⟩ <;>
    rw [nonvanishingLocus_sectionsOfFam, hloc]
  exacts [hxh, hhW, hsa.basicOpen h]

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.5.6 (i): the restriction of an ample line bundle to a quasi-compact open subset is
ample. -/
theorem IsAmple.pullback_ι (hL : L.IsAmple) {W : X.Opens} (hW : IsCompact (W : Set X)) :
    (L.pullback W.ι).IsAmple := by
  refine ⟨isCompact_iff_compactSpace.mp hW, fun y ↦ ?_⟩
  obtain ⟨n, hn, t, hxt, htW, hta⟩ := hL.exists_nonvanishingLocus_le y.2
  refine ⟨n, hn, t.pullback L W.ι, by rw [nonvanishingLocus_pullback]; exact hxt, ?_⟩
  rw [nonvanishingLocus_pullback, ← W.ι.isAffineOpen_iff_of_isOpenImmersion,
    Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right.mpr htW]
  exact hta

/-- The inverse image of an ample line bundle under an open immersion with quasi-compact source is
ample (EGA II 4.5.6 (i)). -/
theorem IsAmple.pullback_of_isOpenImmersion {Z : Scheme.{u}} (hL : L.IsAmple) (g : Z ⟶ X)
    [IsOpenImmersion g] [CompactSpace Z] : (L.pullback g).IsAmple := by
  have hc : IsCompact (g.opensRange : Set X) := by
    rw [Scheme.Hom.coe_opensRange, ← Set.image_univ]
    exact isCompact_univ.image g.continuous
  rw [← g.isoOpensRange_hom_ι, pullback_comp]
  exact (hL.pullback_ι hc).pullback _

/-- The inverse image of an ample line bundle under a quasi-compact immersion is ample
(EGA II 4.5.10 (i) for immersions). -/
theorem IsAmple.pullback_of_isImmersion {Z : Scheme.{u}} (hL : L.IsAmple) (g : Z ⟶ X)
    [IsImmersion g] [QuasiCompact g] : (L.pullback g).IsAmple := by
  have := hL.1
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace g
  rw [← g.toImage_imageι, pullback_comp]
  exact (hL.pullback g.imageι).pullback_of_isOpenImmersion g.toImage

set_option backward.isDefEq.respectTransparency false in
/-- Let `X` be quasi-compact and quasi-separated and `h` a function on `X` such that `L|_{D(h)}` is
ample. Then every point of `D(h)` has an affine neighbourhood `X_t ⊆ D(h)`, for a section `t` of
a positive power of `L` over `X` (the key step of EGA II 4.6.4). -/
theorem exists_of_isAmple_pullback_basicOpen [CompactSpace X] [QuasiSeparatedSpace X]
    (h : Γ(X, ⊤)) (hL : (L.pullback (X.basicOpen h).ι).IsAmple) {x : X}
    (hx : x ∈ X.basicOpen h) : ∃ (n : ℕ) (_ : 0 < n) (t : L.sections n),
      x ∈ L.nonvanishingLocus t ∧ L.nonvanishingLocus t ≤ X.basicOpen h ∧
        IsAffineOpen (L.nonvanishingLocus t) := by
  set ι := (X.basicOpen h).ι
  obtain ⟨n, hn, s', hxs', hs'a⟩ := hL.2 ⟨x, hx⟩
  obtain ⟨s₀, hs₀, hs₀e⟩ := L.exists_isSection_famPullback_eq ι s'.isSection_toFam
  have hE' : (L.pullback ι).nonvanishingLocus s' = ι ⁻¹ᵁ L.famLocus ι.opensRange s₀ := by
    rw [← sections.famLocus_toFam, ← hs₀e, famLocus_famPullback, top_inf_eq]
  have hEZ : L.famLocus ι.opensRange s₀ ≤ X.basicOpen h :=
    (famLocus_le s₀).trans (Scheme.Opens.opensRange_ι _).le
  have hEa : IsAffineOpen (L.famLocus ι.opensRange s₀) := by
    have := hs'a
    rwa [hE', ← ι.isAffineOpen_iff_of_isOpenImmersion,
      Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (famLocus_le s₀)] at this
  have hxE : x ∈ L.famLocus ι.opensRange s₀ := by
    rw [hE'] at hxs'
    exact hxs'
  have hSh := isSection_famConst (L := L) (V := ⊤) h
  have hShloc : L.famLocus ⊤ (L.famConst ⊤ h) = X.basicOpen h := famLocus_famConst h
  have hle : L.famLocus ⊤ (L.famConst ⊤ h) ≤ ι.opensRange := by
    rw [hShloc, Scheme.Opens.opensRange_ι]
  obtain ⟨k, y, hy, hyr⟩ := exists_isSection_famRes_eq (U := ⊤) isCompact_univ
    isQuasiSeparated_univ hSh (hs₀.famRes hle)
  have hT : L.IsSection (n : ℤ) ⊤ (L.famConst ⊤ h * y) := (hSh.mul hy).of_eq (by ring)
  have hloc : L.famLocus ⊤ (L.famConst ⊤ h * y) = L.famLocus ι.opensRange s₀ := by
    rw [famLocus_mul_eq hy (hs₀.famRes hle) hyr, famLocus_famRes, inf_eq_right]
    exact hEZ.trans hShloc.ge
  refine ⟨n, hn, L.sectionsOfFam _ hT, ?_, ?_, ?_⟩ <;>
    rw [nonvanishingLocus_sectionsOfFam, hloc]
  exacts [hxE, hEZ, hEa]

set_option backward.isDefEq.respectTransparency.types false in
/-- If `L|_{f⁻¹(Vⱼ)}` is ample for an affine open cover `(Vⱼ)` of `Y`, then `f` is
quasi-separated. -/
lemma quasiSeparated_of_isAmple {Y : Scheme.{u}} (f : X ⟶ Y) {κ : Type*} (V : κ → Y.Opens)
    (hV : ∀ j, IsAffineOpen (V j)) (hcov : ⨆ j, V j = ⊤)
    (hL : ∀ j, (L.pullback (f ⁻¹ᵁ V j).ι).IsAmple) : QuasiSeparated f := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top V hcov fun j ↦ ?_
  have : IsAffine (V j) := hV j
  have := (hL j).quasiSeparatedSpace
  exact (quasiSeparated_iff_quasiSeparatedSpace _).mpr this

/-- A morphism admitting a relatively ample line bundle is quasi-separated. -/
theorem IsRelativelyAmple.quasiSeparated {Y : Scheme.{u}} {f : X ⟶ Y}
    (hL : L.IsRelativelyAmple f) : QuasiSeparated f :=
  quasiSeparated_of_isAmple f (fun V : Y.affineOpens ↦ V.1) (fun V ↦ V.2)
    (iSup_affineOpens_eq_top Y) fun V ↦ hL.2 V.1 V.2

/-- A line bundle ample relative to `f` is ample relative to `f ≫ g` for `g` affine, the inverse
image under `g` of an affine open being affine. -/
theorem IsRelativelyAmple.comp {Y Z : Scheme.{u}} {f : X ⟶ Y} (hL : L.IsRelativelyAmple f)
    (g : Y ⟶ Z) [IsAffineHom g] : L.IsRelativelyAmple (f ≫ g) := by
  have := hL.1
  refine ⟨inferInstance, fun V hV ↦ ?_⟩
  rw [Scheme.Hom.comp_preimage]
  exact hL.2 _ (hV.preimage g)

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.6.4: relative ampleness is local on the base. If `f` is quasi-compact and
`L|_{f⁻¹(Vⱼ)}` is ample for an affine open cover `(Vⱼ)` of `Y`, then `L` is ample relative
to `f`. -/
theorem isRelativelyAmple_of_iSup_eq_top {Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    {κ : Type*} (V : κ → Y.Opens) (hV : ∀ j, IsAffineOpen (V j)) (hcov : ⨆ j, V j = ⊤)
    (hL : ∀ j, (L.pullback (f ⁻¹ᵁ V j).ι).IsAmple) : L.IsRelativelyAmple f := by
  have := quasiSeparated_of_isAmple f V hV hcov hL
  refine ⟨inferInstance, fun W hW ↦ ?_⟩
  set ιW := (f ⁻¹ᵁ W).ι
  have : CompactSpace (f ⁻¹ᵁ W) := isCompact_iff_compactSpace.mp (f.isCompact_preimage hW.isCompact)
  have : QuasiSeparatedSpace (f ⁻¹ᵁ W) := (isQuasiSeparated_iff_quasiSeparatedSpace _
    (f ⁻¹ᵁ W).isOpen).mp (f.isQuasiSeparated_preimage hW.isQuasiSeparated)
  refine ⟨inferInstance, fun y ↦ ?_⟩
  have hyW : f (ιW y) ∈ W := y.2
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp (hcov.ge (Set.mem_univ (f (ιW y))))
  obtain ⟨g, hgle, hyg⟩ := hW.exists_basicOpen_le (V := W ⊓ V j) ⟨f (ιW y), hyW, hj⟩ hyW
  let h : Γ(f ⁻¹ᵁ W, ⊤) := (ιW ≫ f).appLE W ⊤ (by
    rw [Scheme.Hom.comp_preimage, Scheme.Opens.ι_preimage_self]) g
  have hbo : (f ⁻¹ᵁ W).toScheme.basicOpen h = ιW ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen g := by
    rw [Scheme.basicOpen_appLE, top_inf_eq, Scheme.Hom.comp_preimage]
  have key (U : Y.Opens) (hU : Y.basicOpen g ≤ U) :
      Set.range (((f ⁻¹ᵁ U).ι ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen g).ι ≫ (f ⁻¹ᵁ U).ι) =
        f ⁻¹' (Y.basicOpen g : Set Y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
    change (f ⁻¹ᵁ U).ι '' ((f ⁻¹ᵁ U).ι ⁻¹' (f ⁻¹' (Y.basicOpen g : Set Y))) = _
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_eq_left]
    exact fun z hz ↦ hU hz
  -- `L|_{f⁻¹ D(g)}` is ample, as the restriction of `L|_{f⁻¹ Vⱼ}` to a quasi-compact open.
  set ιj := (f ⁻¹ᵁ V j).ι
  let O : (f ⁻¹ᵁ V j).toScheme.Opens := ιj ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen g
  have hO : IsCompact (O : Set (f ⁻¹ᵁ V j)) := by
    refine (ιj.isOpenEmbedding.isInducing.isCompact_preimage_iff ?_).mpr
      (f.isCompact_preimage (hW.basicOpen g).isCompact)
    rw [Scheme.Opens.range_ι]
    exact fun z hz ↦ (hgle hz).2
  have hLO := (hL j).pullback_ι hO
  let Dh : (f ⁻¹ᵁ W).toScheme.Opens := (f ⁻¹ᵁ W).toScheme.basicOpen h
  have hrange : Set.range (Dh.ι ≫ ιW) = Set.range (O.ι ≫ ιj) := by
    have e1 : Dh = ιW ⁻¹ᵁ f ⁻¹ᵁ Y.basicOpen g := hbo
    rw [e1, key W (hgle.trans inf_le_left), key (V j) (hgle.trans inf_le_right)]
  let e := IsOpenImmersion.isoOfRangeEq (Dh.ι ≫ ιW) (O.ι ≫ ιj) hrange
  have he : e.hom ≫ O.ι ≫ ιj = Dh.ι ≫ ιW := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hLDh : ((L.pullback ιW).pullback Dh.ι).IsAmple := by
    rw [← pullback_comp, ← he, pullback_comp, pullback_comp]
    exact hLO.pullback e.hom
  have hyD : y ∈ (f ⁻¹ᵁ W).toScheme.basicOpen h := by
    rw [hbo]
    exact hyg
  obtain ⟨n, hn, t, hyt, -, hta⟩ := exists_of_isAmple_pullback_basicOpen h hLDh hyD
  exact ⟨n, hn, t, hyt, hta⟩

open Limits in
set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.6.13 (iii): relative ampleness is stable under base change. If `L` is ample relative
to `f` and the square `X' ⟶ X`, `X' ⟶ Y'` over `f`, `g` is cartesian, then the inverse image of
`L` on `X'` is ample relative to `X' ⟶ Y'`. -/
theorem IsRelativelyAmple.of_isPullback {X' Y Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y}
    {fst : X' ⟶ X} {snd : X' ⟶ Y'} (H : IsPullback fst snd f g) (hL : L.IsRelativelyAmple f) :
    (L.pullback fst).IsRelativelyAmple snd := by
  have := hL.1
  have : QuasiCompact snd := MorphismProperty.of_isPullback H inferInstance
  let κ := {p : Y.affineOpens × Y'.affineOpens // p.2.1 ≤ g ⁻¹ᵁ p.1.1}
  refine isRelativelyAmple_of_iSup_eq_top snd (fun p : κ ↦ p.1.2.1) (fun p ↦ p.1.2.2) ?_
    fun p ↦ ?_
  · refine eq_top_iff.mpr fun y' _ ↦ ?_
    obtain ⟨V, hV, hgV, -⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
      (show g y' ∈ (⊤ : Y.Opens) from _root_.trivial)
    obtain ⟨V', hV', hyV', hV'le⟩ := Opens.isBasis_iff_nbhd.mp Y'.isBasis_affineOpens
      (show y' ∈ g ⁻¹ᵁ V from hgV)
    exact Opens.mem_iSup.mpr ⟨⟨(⟨V, hV⟩, ⟨V', hV'⟩), hV'le⟩, hyV'⟩
  obtain ⟨⟨⟨V, hV⟩, ⟨V', hV'⟩⟩, hle⟩ := p
  have : IsAffine V := hV
  have : IsAffine V' := hV'
  let gV : (V' : Scheme) ⟶ V := IsOpenImmersion.lift V.ι (V'.ι ≫ g) (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    rintro _ ⟨z, hz, rfl⟩
    exact hle hz)
  have hgV : gV ≫ V.ι = V'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _
  have P1 : IsPullback ((snd ⁻¹ᵁ V').ι ≫ fst) (snd ∣_ V') f (V'.ι ≫ g) :=
    (isPullback_morphismRestrict snd V').flip.paste_horiz H
  let q : (snd ⁻¹ᵁ V' : Scheme) ⟶ f ⁻¹ᵁ V :=
    IsOpenImmersion.lift (f ⁻¹ᵁ V).ι ((snd ⁻¹ᵁ V').ι ≫ fst) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      change f (fst ((snd ⁻¹ᵁ V').ι z)) ∈ V
      rw [← Scheme.Hom.comp_apply, H.w, Scheme.Hom.comp_apply]
      exact hle z.2)
  have hq : q ≫ (f ⁻¹ᵁ V).ι = (snd ⁻¹ᵁ V').ι ≫ fst := IsOpenImmersion.lift_fac _ _ _
  have P2 : IsPullback q (snd ∣_ V') (f ∣_ V) gV := by
    refine IsPullback.of_right (by rw [hq, hgV]; exact P1) ?_
      (isPullback_morphismRestrict f V).flip
    rw [← cancel_mono V.ι, Category.assoc, morphismRestrict_ι, reassoc_of% hq, H.w,
      Category.assoc, hgV, morphismRestrict_ι_assoc]
  have : IsAffineHom q := MorphismProperty.of_isPullback P2.flip inferInstance
  change (((L.pullback fst).pullback (snd ⁻¹ᵁ V').ι)).IsAmple
  rw [← pullback_comp, ← hq, pullback_comp]
  exact (hL.2 V hV).pullback q

set_option backward.isDefEq.respectTransparency false in
/-- Ampleness can be checked after pulling back along a surjective open immersion (for instance
an isomorphism, or the inclusion of `⊤`). -/
theorem isAmple_of_isAmple_pullback_of_isOpenImmersion {Z : Scheme.{u}} (f : Z ⟶ X)
    [IsOpenImmersion f] (hf : Function.Surjective f) (h : (L.pullback f).IsAmple) :
    L.IsAmple := by
  have := h.1
  refine ⟨⟨by simpa [Set.range_eq_univ.mpr hf] using isCompact_range f.continuous⟩, fun x ↦ ?_⟩
  obtain ⟨z, rfl⟩ := hf x
  obtain ⟨n, hn, t, hz, ht⟩ := h.2 z
  obtain ⟨s₀, hs₀, hs₀e⟩ := L.exists_isSection_famPullback_eq f t.isSection_toFam
  have hle : (⊤ : X.Opens) ≤ f.opensRange := fun y _ ↦ hf y
  have e : f ⁻¹ᵁ L.famLocus _ s₀ = (L.pullback f).nonvanishingLocus t := by
    rw [← sections.famLocus_toFam, ← hs₀e, famLocus_famPullback, top_inf_eq]
  refine ⟨n, hn, L.sectionsOfFam (L.famRes hle s₀) (hs₀.famRes hle), ?_, ?_⟩ <;>
    rw [nonvanishingLocus_sectionsOfFam, famLocus_famRes, top_inf_eq]
  · have : z ∈ f ⁻¹ᵁ L.famLocus _ s₀ := by rw [e]; exact hz
    exact this
  · have hr : f ''ᵁ (L.pullback f).nonvanishingLocus t = L.famLocus _ s₀ := by
      rw [← e, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (famLocus_le _)]
    rw [← hr]
    exact f.isAffineOpen_iff_of_isOpenImmersion.mpr ht

/-- A line bundle ample relative to a morphism to an affine scheme is ample. -/
theorem IsRelativelyAmple.isAmple {Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine Y]
    (hL : L.IsRelativelyAmple f) : L.IsAmple :=
  isAmple_of_isAmple_pullback_of_isOpenImmersion (f ⁻¹ᵁ ⊤).ι
    (fun x ↦ ⟨⟨x, by rw [Scheme.Hom.preimage_top]; trivial⟩, rfl⟩) (hL.2 ⊤ (isAffineOpen_top Y))

/-- An ample line bundle is ample relative to any quasi-compact morphism (EGA II 4.6.13 (ii)). -/
theorem IsAmple.isRelativelyAmple {Y : Scheme.{u}} (hL : L.IsAmple) (f : X ⟶ Y) [QuasiCompact f] :
    L.IsRelativelyAmple f :=
  ⟨inferInstance, fun _ hV ↦ hL.pullback_ι (f.isCompact_preimage hV.isCompact)⟩

end AlgebraicGeometry.Scheme.LineBundle
