/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import SGA.Foundations.CompleteLocalQuasiFinite
import Mathlib.RingTheory.AdicCompletion.Topology
import SGA.SGA1.ExposeIX.Submersive


/-!
# SGA 1, Exposé IX, 2.5: universally submersive morphisms over a complete local ring

IX.2.5 (`universallySubmersive_iff_forall_exists_specializes`): let `S = Spec A` with `A` a
complete noetherian local ring, and `g : S' ⟶ S` locally of finite type with finite closed fibre.
The local rings `𝒪_{S',s'}` at the points `s'` of the closed fibre are finite over `A`; let `S''`
be the sum of their spectra. Then `g` is universally submersive iff `S'' ⟶ S` is surjective, i.e.
iff every point of `S` is the image of a generization of a point of the closed fibre.

The original text reads "`S'' ⟶ S'` surjective", but its proof uses (and the statement needs) the
surjectivity of `S'' ⟶ S`: for `A` a complete discrete valuation ring with fraction field `K` and
`S' = S ⊔ Spec K`, `g` has a section, hence is universally submersive, while the point `Spec K`
does not specialize to the closed fibre. We state and prove the corrected criterion.

* `exists_opens_forall_specializes_isFinite`: for `s'` in the closed fibre, the generizations of
  `s'` form an open subset `W` of `S'` which is finite over `S` (it is `Spec 𝒪_{S',s'}`); this is
  `IsLocalRing.exists_notMem_forall_le_and_finite` (Zariski's main theorem over a complete local
  ring) on an affine neighbourhood of `s'`.
* `UniversallySubmersive.of_finite_cover`: a morphism is universally submersive as soon as
  finitely many universally closed `Zᵢ ⟶ S` factoring through it cover `S` (the sufficiency, via
  IX.2.2).
* For the necessity, SGA uses a discrete valuation ring `T` with image `{s, t}` for a point `t`
  not in the image of `S''`. We use instead the closure `T = Spec (A ⧸ 𝔭)` of a point `𝔭` which
  is closed in the complement of the image of `S''`: `A ⧸ 𝔭` is a one-dimensional local domain
  (`Ideal.IsPrime.isMaximal_of_forall_ne_bot`), which is all the argument needs.
-/

universe u

open CategoryTheory Limits IsLocalRing

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [IsAdicComplete (maximalIdeal A) A]

set_option backward.isDefEq.respectTransparency false in
/-- IX.2.5, first assertion: over the spectrum of a complete noetherian local ring `A`, let
`g : S' ⟶ Spec A` be locally of finite type with finite closed fibre, and `s'` a point of the
closed fibre. The generizations of `s'` form an open subset `W` of `S'` (namely
`Spec 𝒪_{S',s'}`), which is finite over `Spec A`. -/
theorem exists_opens_forall_specializes_isFinite {S' : Scheme.{u}} (g : S' ⟶ Spec (.of A))
    [LocallyOfFiniteType g] {y : S'} (hy : g y = closedPoint A)
    (hfin : (g ⁻¹' {closedPoint A}).Finite) :
    ∃ W : S'.Opens, y ∈ W ∧ (∀ z ∈ W, z ⤳ y) ∧ IsFinite (W.ι ≫ g) := by
  have hqf : g.QuasiFiniteAt y := by
    have : Finite (g ⁻¹' {g y}) := by rw [hy]; exact hfin.to_subtype
    have : Finite (g.fiber (g y)) := (g.fiberHomeo (g y)).finite_iff.mpr ‹_›
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
    S'.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  have hU := isAffineOpen_top (Spec (.of A))
  have hVU : V ≤ g ⁻¹ᵁ ⊤ := by simp
  -- the base ring `Γ(Spec A, ⊤) ≅ A` is complete noetherian local
  let e₀ : A ≃+* Γ(Spec (.of A), ⊤) := (Scheme.ΓSpecIso (.of A)).symm.commRingCatIsoToRingEquiv
  have : Nontrivial Γ(Spec (.of A), ⊤) := e₀.symm.toEquiv.nontrivial
  have : IsLocalRing Γ(Spec (.of A), ⊤) := .of_surjective' e₀.toRingHom e₀.surjective
  have : IsNoetherianRing Γ(Spec (.of A), ⊤) := isNoetherianRing_of_ringEquiv A e₀
  have : IsAdicComplete (maximalIdeal Γ(Spec (.of A), ⊤)) Γ(Spec (.of A), ⊤) := by
    have hm : (maximalIdeal A).map e₀ = maximalIdeal Γ(Spec (.of A), ⊤) :=
      eq_maximalIdeal (Ideal.map_isMaximal_of_equiv e₀)
    rw [← hm, IsAdicComplete.congr_ringEquiv]
    infer_instance
  let : Algebra Γ(Spec (.of A), ⊤) Γ(S', V) := (g.appLE ⊤ V hVU).hom.toAlgebra
  have : Algebra.FiniteType Γ(Spec (.of A), ⊤) Γ(S', V) := g.finiteType_appLE hU hV hVU
  let q := (hV.primeIdealOf ⟨y, hyV⟩).asIdeal
  have : Algebra.QuasiFiniteAt Γ(Spec (.of A), ⊤) q := hqf.quasiFiniteAt hV hU hVU hyV
  have : q.LiesOver (maximalIdeal Γ(Spec (.of A), ⊤)) := by
    constructor
    have h := IsAffineOpen.comap_primeIdealOf_appLE (f := g) ⊤ hU V hV hVU hyV
    have hmax : (hU.primeIdealOf ⟨g y, hVU hyV⟩).asIdeal.IsMaximal :=
      hU.primeIdealOf_isMaximal_of_isClosed _ (by rw [hy]; exact isClosed_singleton_closedPoint A)
    rw [Ideal.under, ← eq_maximalIdeal hmax, ← h]
    rfl
  obtain ⟨e, heq, hle, hfin'⟩ :=
    exists_notMem_forall_le_and_finite (A := Γ(Spec (.of A), ⊤)) q
  have hmem (z : S') (hz : z ∈ V) :
      z ∈ S'.basicOpen e ↔ e ∉ (hV.primeIdealOf ⟨z, hz⟩).asIdeal := by
    rw [← PrimeSpectrum.mem_basicOpen, ← SetLike.mem_coe, ← hV.fromSpec_preimage_basicOpen,
      SetLike.mem_coe, Scheme.Hom.mem_preimage, hV.fromSpec_primeIdealOf]
  have hWV : S'.basicOpen e ≤ V := S'.basicOpen_le e
  have hW := hV.basicOpen e
  refine ⟨S'.basicOpen e, (hmem y hyV).mpr heq, fun z hz ↦ ?_, ?_⟩
  · have hzV := hWV hz
    have hP := hle _ (hV.primeIdealOf ⟨z, hzV⟩).isPrime ((hmem z hzV).mp hz)
    have := ((PrimeSpectrum.le_iff_specializes _ _).mp hP).map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf] at this
  · have hWU : S'.basicOpen e ≤ g ⁻¹ᵁ ⊤ := by simp
    let : Algebra Γ(Spec (.of A), ⊤) Γ(S', S'.basicOpen e) :=
      (g.appLE ⊤ (S'.basicOpen e) hWU).hom.toAlgebra
    have : IsScalarTower Γ(Spec (.of A), ⊤) Γ(S', V) Γ(S', S'.basicOpen e) :=
      IsScalarTower.of_algebraMap_eq fun x ↦ by
        change (g.appLE ⊤ (S'.basicOpen e) hWU).hom x =
          (S'.presheaf.map (homOfLE hWV).op).hom ((g.appLE ⊤ V hVU).hom x)
        rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    have := hV.isLocalization_basicOpen e
    have hfinite : (g.appLE ⊤ (S'.basicOpen e) hWU).hom.Finite := hfin' _
    have : IsFinite (Spec.map (g.appLE ⊤ (S'.basicOpen e) hWU)) :=
      (IsFinite.SpecMap_iff _).mpr hfinite
    rw [← hW.isoSpec_hom_fromSpec_assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec g hU hW hWU,
      IsAffineOpen.fromSpec_top]
    infer_instance

omit [IsLocalRing A] [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] in
/-- IX.2.5, proof of sufficiency (via IX.2.2): a morphism `g : S' ⟶ S` is universally
submersive as soon as there are finitely many morphisms `hᵢ : Zᵢ ⟶ S'` with `hᵢ ≫ g` universally
closed and with images covering `S`. -/
theorem UniversallySubmersive.of_finite_cover {ι : Type*} [Finite ι] {S' S : Scheme.{u}}
    (g : S' ⟶ S) (Z : ι → Scheme.{u}) (h : ∀ i, Z i ⟶ S') [∀ i, UniversallyClosed (h i ≫ g)]
    (hcov : ∀ s : S, ∃ i, s ∈ Set.range (h i ≫ g)) : UniversallySubmersive g := by
  constructor
  intro X' Y' i₁ i₂ f' H
  let m (i : ι) : pullback (h i ≫ g) i₂ ⟶ X' :=
    H.lift (pullback.snd _ _) (pullback.fst _ _ ≫ h i) (by
      rw [Category.assoc, ← pullback.condition])
  have hm (i : ι) : m i ≫ f' = pullback.snd _ _ := H.lift_fst _ _ _
  have hsurj (y : Y') :
      ∃ i, ∃ p : ↑(pullback (h i ≫ g) i₂), pullback.snd (h i ≫ g) i₂ p = y := by
    obtain ⟨i, z, hz⟩ := hcov (i₂ y)
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback z y hz
    exact ⟨i, p, hp⟩
  refine ⟨Topology.isQuotientMap_iff_isClosed.mpr ⟨fun y ↦ ?_, fun C ↦ ⟨fun hC ↦ hC.preimage
    f'.continuous, fun hC ↦ ?_⟩⟩⟩
  · obtain ⟨i, p, rfl⟩ := hsurj y
    exact ⟨m i p, by rw [← Scheme.Hom.comp_apply, hm]⟩
  · have : C = ⋃ i, pullback.snd (h i ≫ g) i₂ '' (m i ⁻¹' (f' ⁻¹' C)) := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_preimage]
      refine ⟨fun hy ↦ ?_, ?_⟩
      · obtain ⟨i, p, rfl⟩ := hsurj y
        exact ⟨i, p, by rwa [← Scheme.Hom.comp_apply, hm], rfl⟩
      · rintro ⟨i, p, hp, rfl⟩
        rwa [← Scheme.Hom.comp_apply, hm] at hp
    rw [this]
    refine isClosed_iUnion_of_finite fun i ↦ ?_
    have : UniversallyClosed (pullback.snd (h i ≫ g) i₂) := inferInstance
    exact (pullback.snd (h i ≫ g) i₂).isClosedMap _ (hC.preimage (m i).continuous)

set_option backward.isDefEq.respectTransparency false in
/-- IX.2.5: let `A` be a complete noetherian local ring and `g : S' ⟶ Spec A` locally of finite
type with finite closed fibre. Then `g` is universally submersive iff every point of `Spec A` is
the image of a generization of a point of the closed fibre, i.e. iff the sum `S''` of the spectra
of the local rings of `S'` at the points of the closed fibre (a finite `Spec A`-scheme) maps
onto `Spec A`. (The original text has `S'' ⟶ S'` in place of `S'' ⟶ S`; see the module
docstring.) -/
theorem universallySubmersive_iff_forall_exists_specializes {S' : Scheme.{u}}
    (g : S' ⟶ Spec (.of A)) [LocallyOfFiniteType g] (hfin : (g ⁻¹' {closedPoint A}).Finite) :
    UniversallySubmersive g ↔
      ∀ t : Spec (.of A), ∃ x : S', g x = t ∧ ∃ y ∈ g ⁻¹' {closedPoint A}, x ⤳ y := by
  classical
  let ι := ↥(g ⁻¹' {closedPoint A})
  have : Finite ι := hfin.to_subtype
  choose W hyW hWsp hWfin using fun y : ι ↦ exists_opens_forall_specializes_isFinite g y.2 hfin
  have : ∀ y, UniversallyClosed ((W y).ι ≫ g) := fun y ↦ have := hWfin y; inferInstance
  have hrange (y : ι) : Set.range ((W y).ι ≫ g) = g '' (W y) := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
  refine ⟨fun hg ↦ ?_, fun H ↦ ?_⟩
  · let F : Set (Spec (.of A)) := ⋃ y : ι, g '' (W y)
    have hF : IsClosed F := isClosed_iUnion_of_finite fun y ↦ by
      rw [← hrange]; exact ((W y).ι ≫ g).isClosedMap.isClosed_range
    suffices hFu : F = Set.univ by
      intro t
      have := hFu.ge (Set.mem_univ t)
      simp only [F, Set.mem_iUnion, Set.mem_image] at this
      obtain ⟨y, x, hx, rfl⟩ := this
      exact ⟨x, rfl, y.1, y.2, hWsp y x hx⟩
    by_contra hne
    obtain ⟨t₀, ht₀⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
    -- the closed point `s` lies in `F`
    have hsF : closedPoint A ∈ F := by
      obtain ⟨y, hy⟩ := g.surjective (closedPoint A)
      exact Set.mem_iUnion.mpr ⟨⟨y, hy⟩, y, hyW _, hy⟩
    -- a closed point `u` of the open subspace `Fᶜ`
    have : CompactSpace ↥Fᶜ :=
      isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
    obtain ⟨u, -, hu⟩ := (isClosed_univ (X := ↥Fᶜ)).exists_closed_singleton ⟨⟨t₀, ht₀⟩, trivial⟩
    have hu_min (v : Spec (.of A)) (hv : v ∉ F) (huv : u.1 ⤳ v) : v = u.1 := by
      have : u ⤳ (⟨v, hv⟩ : ↥Fᶜ) := Topology.IsInducing.subtypeVal.specializes_iff.mp huv
      have h2 : (⟨v, hv⟩ : ↥Fᶜ) ∈ ({u} : Set ↥Fᶜ) := this.mem_closed hu (Set.mem_singleton u)
      exact congrArg Subtype.val h2
    obtain ⟨_, ⟨a, rfl⟩, hua, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens
      |>.exists_subset_of_mem_open u.2 hF.isOpen_compl
    let p := u.1.asIdeal
    let B := A ⧸ p
    have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr u.1.isPrime.ne_top
    have : IsLocalRing B := .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
    have hB₁ (P : Ideal B) (hP : P.IsPrime) (hP0 : P ≠ ⊥) : P.IsMaximal := by
      refine Ideal.IsPrime.isMaximal_of_forall_ne_bot (f := Ideal.Quotient.mk p a) ?_ ?_ hP hP0
      · rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hua
      · intro Q hQ hQ0
        let v : Spec (.of A) := ⟨Q.comap (Ideal.Quotient.mk p), Ideal.comap_isPrime _ _⟩
        have hpv : p ≤ v.asIdeal := fun x hx ↦ by
          simp [v, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        by_contra hav
        have hvF : v ∉ F := hsub (show v ∈ PrimeSpectrum.basicOpen a from hav)
        have hvu := hu_min v hvF ((PrimeSpectrum.le_iff_specializes _ _).mp hpv)
        apply hQ0
        rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q]
        change Ideal.map _ v.asIdeal = ⊥
        rw [hvu, Ideal.map_quotient_self]
    have hmB : maximalIdeal B ≠ ⊥ := by
      intro h
      have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective (K := maximalIdeal B)
      rw [h, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at this
      have : u.1 = closedPoint A := PrimeSpectrum.ext (eq_maximalIdeal this)
      exact u.2 (this ▸ hsF)
    let t : Spec (.of B) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p))
    have htc : t (closedPoint B) = closedPoint A := PrimeSpectrum.ext
      (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
        (K := maximalIdeal B)))
    have ht (τ : Spec (.of B)) : t τ ∈ F ↔ τ = closedPoint B := by
      refine ⟨fun hτF ↦ ?_, by rintro rfl; rw [htc]; exact hsF⟩
      by_contra hne
      have h0 : τ.asIdeal = ⊥ := by
        by_contra h0
        exact hne (PrimeSpectrum.ext (eq_maximalIdeal (hB₁ _ τ.isPrime h0)))
      have : t τ = u.1 := by
        apply PrimeSpectrum.ext
        change τ.asIdeal.comap (Ideal.Quotient.mk p) = p
        rw [h0, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact u.2 (this ▸ hτF)
    have hE : pullback.snd g t ⁻¹' {closedPoint B} =
        pullback.fst g t ⁻¹' (⋃ y : ι, (W y : Set S')) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iUnion, SetLike.mem_coe]
      have hz : g (pullback.fst g t z) = t (pullback.snd g t z) := by
        rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
      constructor
      · intro h
        have : g (pullback.fst g t z) = closedPoint A := by rw [hz, h, htc]
        exact ⟨⟨_, this⟩, hyW _⟩
      · rintro ⟨y, hy⟩
        rw [← ht, ← hz]
        exact Set.mem_iUnion.mpr ⟨y, _, hy, rfl⟩
    have hopen : IsOpen (pullback.snd g t ⁻¹' {closedPoint B}) := by
      rw [hE]
      exact (isOpen_iUnion fun y ↦ (W y).isOpen).preimage (pullback.fst g t).continuous
    exact not_isOpen_singleton_closedPoint B hmB
      ((Scheme.Hom.isQuotientMap (pullback.snd g t)).isOpen_preimage.mp hopen)
  · refine UniversallySubmersive.of_finite_cover g (fun y : ι ↦ (W y).toScheme) (fun y ↦ (W y).ι)
      fun t ↦ ?_
    obtain ⟨x, rfl, y, hy, hxy⟩ := H t
    have hx : x ∈ W ⟨y, hy⟩ := hxy.mem_open (W _).isOpen (hyW _)
    exact ⟨⟨y, hy⟩, by rw [hrange]; exact ⟨x, hx, rfl⟩⟩

end SGA.SGA1.ExposeIX
