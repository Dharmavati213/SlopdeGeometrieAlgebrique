/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.AlgebraicGeometry.Limits
import SGA.Foundations.Projective.AmpleDescent

/-!
# Finite subsets of schemes with an ample line bundle

- `ProjectiveSpectrum.exists_homogeneous_forall_notMem`: graded prime avoidance; finitely many
  points of `Proj A` lie in a common `D₊(f)` with `f` homogeneous of positive degree
  (Stacks 00JS).
- `Scheme.IsQuasiAffine.exists_isAffineOpen_basicOpen_of_finite`: a finite subset of a
  quasi-affine scheme is contained in an affine basic open subset.
- `Scheme.LineBundle.IsAmple.exists_isAffineOpen_of_finite`: EGA II 4.5.4: if `L` is ample, every
  finite subset of `X` is contained in an affine open subset of `X`.
-/

universe u

open CategoryTheory TopologicalSpace

namespace ProjectiveSpectrum

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] {𝒜 : ℕ → σ}
  [GradedRing 𝒜]

lemma exists_homogeneous_mem_notMem {p q : ProjectiveSpectrum 𝒜}
    (h : ¬ p ≤ q) : ∃ (i : ℕ) (z : A), z ∈ 𝒜 i ∧ z ∈ p.asHomogeneousIdeal ∧
      z ∉ q.asHomogeneousIdeal := by
  classical
  obtain ⟨a, hap, haq⟩ := Set.not_subset.mp h
  by_contra! H
  refine haq ?_
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  exact Ideal.sum_mem _ fun i _ ↦ H i _ (SetLike.coe_mem _) (p.asHomogeneousIdeal.2 i hap)

lemma exists_pos_homogeneous_notMem (q : ProjectiveSpectrum 𝒜) :
    ∃ (i : ℕ) (y : A), 0 < i ∧ y ∈ 𝒜 i ∧ y ∉ q.asHomogeneousIdeal := by
  classical
  obtain ⟨a, ha, haq⟩ := Set.not_subset.mp q.not_irrelevant_le
  by_contra! H
  refine haq ?_
  rw [← DirectSum.sum_support_decompose 𝒜 a]
  refine Ideal.sum_mem _ fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have : (DirectSum.decompose 𝒜 a 0 : A) = 0 := by
      simpa [GradedRing.proj_apply] using (HomogeneousIdeal.mem_irrelevant_iff _ _).mp ha
    rw [this]
    exact zero_mem _
  · by_contra h'
    exact h' (H i _ hi (SetLike.coe_mem _))

/-- Graded prime avoidance (Stacks 00JS), relative to an ideal `J`: if each of finitely many
points of `Proj A` avoids some homogeneous element of `J` of positive degree, then a single
homogeneous element of `J` of positive degree avoids all of them. -/
theorem exists_homogeneous_mem_forall_notMem (s : Finset (ProjectiveSpectrum 𝒜)) (J : Ideal A)
    (hJ : ∀ x ∈ s, ∃ (i : ℕ) (y : A), 0 < i ∧ y ∈ 𝒜 i ∧ y ∈ J ∧ y ∉ x.asHomogeneousIdeal) :
    ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ f ∈ J ∧ ∀ x ∈ s, f ∉ x.asHomogeneousIdeal := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨1, 0, one_pos, zero_mem _, zero_mem _, by simp⟩
  -- a minimal point `q` of `s`: the other points do not specialize to it
  obtain ⟨q, hqs, hqmin⟩ := (s : Set (ProjectiveSpectrum 𝒜)).toFinite.exists_minimal hs
  have hq : q ∈ s := hqs
  have hlt : s.erase q ⊂ s := Finset.erase_ssubset hq
  obtain ⟨b, f, hb, hf, hfJ, hfs⟩ :=
    ih _ hlt fun x hx ↦ hJ x (Finset.mem_of_mem_erase hx)
  by_cases hfq : f ∉ q.asHomogeneousIdeal
  · refine ⟨b, f, hb, hf, hfJ, fun x hx ↦ ?_⟩
    by_cases hxq : x = q
    · exact hxq ▸ hfq
    · exact hfs x (Finset.mem_erase.mpr ⟨hxq, hx⟩)
  rw [not_not] at hfq
  -- an element `z` in all the other points but not in `q`
  have hz (x : s.erase q) : ∃ (i : ℕ) (z : A), z ∈ 𝒜 i ∧ z ∈ x.1.asHomogeneousIdeal ∧
      z ∉ q.asHomogeneousIdeal := by
    refine exists_homogeneous_mem_notMem fun hxq ↦ ?_
    have hx := Finset.mem_erase.mp x.2
    exact hx.1 (le_antisymm hxq (hqmin hx.2 hxq))
  choose i z hzi hzx hzq using hz
  let Z : A := ∏ x : s.erase q, z x
  have hZ : Z ∈ 𝒜 (∑ x : s.erase q, i x) := SetLike.prod_mem_graded _ _ _ fun x _ ↦ hzi x
  have hZq : Z ∉ q.asHomogeneousIdeal := by
    have := q.isPrime
    intro h
    obtain ⟨x, -, hx⟩ := (Ideal.IsPrime.prod_mem_iff (p := q.asHomogeneousIdeal.toIdeal)).mp h
    exact hzq x hx
  have hZx (x) (hx : x ∈ s.erase q) : Z ∈ x.asHomogeneousIdeal :=
    Ideal.mem_of_dvd (I := x.asHomogeneousIdeal.toIdeal)
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ ⟨x, hx⟩)) (hzx ⟨x, hx⟩)
  obtain ⟨c, y, hc, hy, hyJ, hyq⟩ := hJ q hq
  let w := y * Z
  let a := c + ∑ x : s.erase q, i x
  have hw : w ∈ 𝒜 a := SetLike.mul_mem_graded hy hZ
  have ha : 0 < a := by omega
  have hwq : w ∉ q.asHomogeneousIdeal := fun h ↦
    (q.isPrime.mem_or_mem h).elim hyq hZq
  refine ⟨b * a, f ^ a + w ^ b, Nat.mul_pos hb ha, ?_, ?_, fun x hx ↦ ?_⟩
  · refine add_mem ?_ ?_
    · rw [mul_comm, ← smul_eq_mul]
      exact SetLike.pow_mem_graded a hf
    · rw [← smul_eq_mul]
      exact SetLike.pow_mem_graded b hw
  · exact add_mem (Ideal.pow_mem_of_mem _ hfJ a ha)
      (Ideal.pow_mem_of_mem _ (Ideal.mul_mem_right _ _ hyJ) b hb)
  by_cases hxq : x = q
  · subst hxq
    intro h
    have h' : w ^ b ∈ x.asHomogeneousIdeal.toIdeal :=
      (Ideal.add_mem_iff_right _ (Ideal.pow_mem_of_mem _ hfq a ha)).mp h
    exact hwq (x.isPrime.mem_of_pow_mem _ h')
  · have hx' : x ∈ s.erase q := Finset.mem_erase.mpr ⟨hxq, hx⟩
    intro h
    have hwx : w ∈ x.asHomogeneousIdeal.toIdeal := Ideal.mul_mem_left _ _ (hZx x hx')
    have h' : f ^ a ∈ x.asHomogeneousIdeal.toIdeal :=
      (Ideal.add_mem_iff_left _ (Ideal.pow_mem_of_mem _ hwx b hb)).mp h
    exact hfs x hx' (x.isPrime.mem_of_pow_mem _ h')

/-- Graded prime avoidance (Stacks 00JS): finitely many points of `Proj A` lie in a common basic
open subset `D₊(f)`, with `f` homogeneous of positive degree. -/
theorem exists_homogeneous_forall_notMem (s : Finset (ProjectiveSpectrum 𝒜)) :
    ∃ (d : ℕ) (f : A), 0 < d ∧ f ∈ 𝒜 d ∧ ∀ x ∈ s, f ∉ x.asHomogeneousIdeal := by
  obtain ⟨d, f, hd, hf, -, hfs⟩ := exists_homogeneous_mem_forall_notMem s ⊤ fun x _ ↦ by
    obtain ⟨i, y, hi, hy, hyx⟩ := exists_pos_homogeneous_notMem x
    exact ⟨i, y, hi, hy, Submodule.mem_top, hyx⟩
  exact ⟨d, f, hd, hf, hfs⟩

end ProjectiveSpectrum

namespace AlgebraicGeometry

open Scheme

/-- A finite subset of a quasi-affine scheme is contained in an affine basic open subset
(prime avoidance in `Γ(X, 𝒪_X)`). -/
theorem Scheme.IsQuasiAffine.exists_isAffineOpen_basicOpen_of_finite (X : Scheme.{u})
    [X.IsQuasiAffine] (F : Finset X) :
    ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ ∀ x ∈ F, x ∈ X.basicOpen r := by
  classical
  rcases F.eq_empty_or_nonempty with rfl | ⟨x₀, -⟩
  · refine ⟨0, ?_, by simp⟩
    rw [Scheme.basicOpen_zero]
    exact isAffineOpen_bot X
  -- the complement of `X` in `Spec Γ(X, 𝒪_X)` and its ideal
  let Z : Set (PrimeSpectrum Γ(X, ⊤)) := (Set.range X.toSpecΓ)ᶜ
  have hZ : IsClosed Z := by
    rw [isClosed_compl_iff]
    exact X.toSpecΓ.isOpenEmbedding.isOpen_range
  let J := PrimeSpectrum.vanishingIdeal Z
  have hJ (x : X) : ¬ J ≤ (X.toSpecΓ x).asIdeal := by
    intro h
    have : X.toSpecΓ x ∈ PrimeSpectrum.zeroLocus J := (PrimeSpectrum.mem_zeroLocus _ _).mpr h
    rw [PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hZ.closure_eq] at this
    exact this ⟨x, rfl⟩
  have hav : ¬ (J : Set Γ(X, ⊤)) ⊆ ⋃ x ∈ (F : Set X), ((X.toSpecΓ x).asIdeal : Set Γ(X, ⊤)) := by
    rw [Ideal.subset_union_prime_finite F.finite_toSet x₀ x₀ fun x _ _ _ ↦
      PrimeSpectrum.isPrime (X.toSpecΓ x)]
    rintro ⟨x, -, hx⟩
    exact hJ x hx
  obtain ⟨r, hrJ, hr⟩ := Set.not_subset.mp hav
  simp only [Set.mem_iUnion, not_exists] at hr
  have hmem (x : X) : x ∈ X.basicOpen r ↔ r ∉ (X.toSpecΓ x).asIdeal := by
    rw [← Scheme.toSpecΓ_preimage_basicOpen]
    rfl
  refine ⟨r, ?_, fun x hx ↦ (hmem x).mpr fun h ↦ hr x hx h⟩
  have hsub : (PrimeSpectrum.basicOpen r : (Spec Γ(X, ⊤)).Opens) ≤ X.toSpecΓ.opensRange := by
    intro p hp
    by_contra hpZ
    exact hp ((PrimeSpectrum.mem_vanishingIdeal _ _).mp hrJ p hpZ)
  have himg : X.toSpecΓ ''ᵁ X.basicOpen r = PrimeSpectrum.basicOpen r := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmem x).mp hx
    · intro p hp
      obtain ⟨x, rfl⟩ := hsub hp
      exact ⟨x, (hmem x).mpr hp, rfl⟩
  rw [← X.toSpecΓ.isAffineOpen_iff_of_isOpenImmersion, himg]
  exact IsAffineOpen.Spec_basicOpen r

namespace Scheme.LineBundle

variable {X : Scheme.{u}} {L : X.LineBundle}

set_option backward.isDefEq.respectTransparency false in
/-- If `L` is ample, every finite subset of `X` is contained in the non-vanishing locus `X_s` of a
section `s` of a positive power of `L`, which is quasi-affine. -/
theorem IsAmple.exists_isQuasiAffine_of_finite (hL : L.IsAmple) (F : Finset X) :
    ∃ U : X.Opens, U.toScheme.IsQuasiAffine ∧ ∀ x ∈ F, x ∈ U := by
  classical
  have hG := hL.secCovers (R := Γ(X, ⊤))
  obtain ⟨d, f, hd, hf, hF⟩ := ProjectiveSpectrum.exists_homogeneous_forall_notMem
    (F.image (L.toProjSectionRing Γ(X, ⊤) hG))
  refine ⟨L.secLocus Γ(X, ⊤) f, hL.isQuasiAffine_secLocus hf hd, fun x hx ↦ ?_⟩
  rw [← toProjSectionRing_preimage_basicOpen hG hf hd]
  exact hF _ (Finset.mem_image_of_mem _ hx)

/-- EGA II 4.5.4: if `L` is ample, every finite subset of `X` is contained in an affine open
subset of `X`. -/
theorem IsAmple.exists_isAffineOpen_of_finite (hL : L.IsAmple) (F : Finset X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U := by
  classical
  obtain ⟨W, hW, hFW⟩ := hL.exists_isQuasiAffine_of_finite F
  let F' : Finset W := F.attach.image fun x ↦ (⟨x.1, hFW x.1 x.2⟩ : W)
  obtain ⟨r, hr, hFr⟩ := IsQuasiAffine.exists_isAffineOpen_basicOpen_of_finite W F'
  refine ⟨W.ι ''ᵁ W.toScheme.basicOpen r, W.ι.isAffineOpen_iff_of_isOpenImmersion.mpr hr,
    fun x hx ↦ ?_⟩
  have := hFr ⟨x, hFW x hx⟩ (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩ : _ ∈ F')
  exact (Scheme.Hom.apply_mem_image_iff W.ι).mpr this

lemma famLocus_mul_le_right {V : X.Opens} (s t : L.Fam V) :
    L.famLocus V (s * t) ≤ L.famLocus V t :=
  iSup_mono fun i ↦ by
    rw [Pi.mul_apply, Scheme.basicOpen_mul]
    exact inf_le_right

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.5.4, strong form: if `L` is ample, every finite subset `F` of an open subset `O` of
`X` lies in the non-vanishing locus `X_t ⊆ O` of a section `t` of a positive power of `L` (graded
prime avoidance for the ideal of `Γ_*(L)` generated by the sections `s` with `X_s ⊆ O`). -/
theorem IsAmple.exists_famLocus_le_of_finite (hL : L.IsAmple) (F : Finset X) {O : X.Opens}
    (hFO : ∀ x ∈ F, x ∈ O) :
    ∃ (d : ℕ) (_ : 0 < d) (t : L.Fam ⊤), L.IsSection d ⊤ t ∧ (∀ x ∈ F, x ∈ L.famLocus ⊤ t) ∧
      L.famLocus ⊤ t ≤ O := by
  classical
  have hG := hL.secCovers (R := Γ(X, ⊤))
  let T : Set (L.sectionRing Γ(X, ⊤)) :=
    {f | ∃ d, 0 < d ∧ f ∈ L.sectionGrading Γ(X, ⊤) d ∧ L.secLocus Γ(X, ⊤) f ≤ O}
  have hT (f) (hf : f ∈ Ideal.span T) : L.secLocus Γ(X, ⊤) f ≤ O := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨-, -, -, h⟩ := hf
      exact h
    | zero => simp only [secLocus, map_zero, famLocus_zero, bot_le]
    | add f g _ _ hf hg =>
      refine le_trans ?_ (sup_le hf hg)
      simp only [secLocus, map_add]
      exact famLocus_add_le _ _
    | smul a f _ hf =>
      refine le_trans ?_ hf
      simp only [secLocus, smul_eq_mul, map_mul]
      exact famLocus_mul_le_right _ _
  obtain ⟨d, f, hd, hf, hfJ, hfF⟩ := ProjectiveSpectrum.exists_homogeneous_mem_forall_notMem
    (F.image (L.toProjSectionRing Γ(X, ⊤) hG)) (Ideal.span T) fun p hp ↦ by
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨n, hn, t, hxt, htO, -⟩ := hL.exists_nonvanishingLocus_le (hFO x hx)
      refine ⟨n, ofSections t, hn, ofSections_mem t,
        Ideal.subset_span ⟨n, hn, ofSections_mem t, by rwa [secLocus_ofSections]⟩, ?_⟩
      have : x ∈ L.secLocus Γ(X, ⊤) (ofSections t) := by rwa [secLocus_ofSections]
      rw [← toProjSectionRing_preimage_basicOpen hG (ofSections_mem t) hn] at this
      exact this
  refine ⟨d, hd, L.coeFam Γ(X, ⊤) f, isSection_coeFam hf, fun x hx ↦ ?_, hT f hfJ⟩
  change x ∈ L.secLocus Γ(X, ⊤) f
  rw [← toProjSectionRing_preimage_basicOpen hG hf hd]
  exact hfF _ (Finset.mem_image_of_mem _ hx)

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.5.4, strong form, over an open subset `U` of `X` on which `L` is ample: every finite
subset `F` of an open `O ⊆ U` lies in the non-vanishing locus `X_s ⊆ O` of a section `s` of a
positive power of `L` over `U`. -/
theorem exists_famLocus_le_of_isAmple_pullback {U : X.Opens} (hL : (L.pullback U.ι).IsAmple)
    (F : Finset X) {O : X.Opens} (hFO : ∀ x ∈ F, x ∈ O) (hOU : O ≤ U) :
    ∃ (d : ℕ) (_ : 0 < d) (s : L.Fam U), L.IsSection d U s ∧ (∀ x ∈ F, x ∈ L.famLocus U s) ∧
      L.famLocus U s ≤ O := by
  classical
  obtain ⟨d, hd, t, ht, htF, htO⟩ := hL.exists_famLocus_le_of_finite (F.subtype (· ∈ U))
    (O := U.ι ⁻¹ᵁ O) fun x hx ↦ hFO x.1 (Finset.mem_subtype.mp hx)
  obtain ⟨s, hs, hst⟩ := exists_isSection_famPullback_eq U.ι ht
  have hU : U ≤ U.ι.opensRange := (Scheme.Opens.opensRange_ι U).ge
  have key (z : U) : z ∈ (L.pullback U.ι).famLocus ⊤ t ↔ z.1 ∈ L.famLocus _ s := by
    rw [← hst, famLocus_famPullback]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨_root_.trivial, h⟩⟩
  refine ⟨d, hd, L.famRes hU s, hs.famRes hU, fun x hx ↦ ?_, fun y hy ↦ ?_⟩
  · have hxU : x ∈ U := hOU (hFO x hx)
    rw [famLocus_famRes]
    exact ⟨hxU, (key ⟨x, hxU⟩).mp (htF _ (Finset.mem_subtype.mpr hx))⟩
  · rw [famLocus_famRes] at hy
    exact htO ((key ⟨y, hy.1⟩).mpr hy.2)

set_option backward.isDefEq.respectTransparency false in
/-- EGA II 4.5.2 over an open `V` of `X`: if `V` is quasi-compact and quasi-separated and every
point of `V` lies in a quasi-affine non-vanishing locus `X_t` of a section `t` over `V` of a
positive power of `L`, then the restriction of `L` to `V` is ample. -/
theorem isAmple_pullback_of_forall_exists {V : X.Opens} [CompactSpace V] [QuasiSeparatedSpace V]
    (H : ∀ x ∈ V, ∃ (d : ℕ) (_ : 0 < d) (t : L.Fam V), L.IsSection d V t ∧
      x ∈ L.famLocus V t ∧ (L.famLocus V t).toScheme.IsQuasiAffine) :
    (L.pullback V.ι).IsAmple := by
  refine isAmple_of_forall_exists_isQuasiAffine fun z ↦ ?_
  obtain ⟨d, hd, t, ht, hzt, hqa⟩ := H z.1 z.2
  have hle : (⊤ : V.toScheme.Opens) ≤ V.ι ⁻¹ᵁ V := V.ι_preimage_self.ge
  refine ⟨d, hd, L.famPullback V.ι hle t, ht.famPullback _ _, ?_, ?_⟩
  · rw [famLocus_famPullback]
    exact ⟨_root_.trivial, hzt⟩
  · rw [famLocus_famPullback, top_inf_eq]
    have hr : Set.range ((V.ι ⁻¹ᵁ L.famLocus V t).ι ≫ V.ι) = Set.range (L.famLocus V t).ι := by
      rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
        Scheme.Opens.range_ι, Scheme.Hom.coe_preimage, Set.image_preimage_eq_inter_range,
        Scheme.Opens.range_ι, Set.inter_eq_left]
      exact famLocus_le t
    exact .of_isIso (IsOpenImmersion.isoOfRangeEq _ (L.famLocus V t).ι hr).hom

end Scheme.LineBundle

end AlgebraicGeometry
