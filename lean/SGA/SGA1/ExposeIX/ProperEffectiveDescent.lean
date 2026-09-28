/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.EtaleCoveringsClosedFibre
import SGA.SGA1.ExposeIX.FiniteEffectiveDescent

/-!
# SGA 1, Exposé IX, 4.12: proper surjective morphisms are effective descent morphisms

IX.4.12: a proper surjective morphism `g : S' ⟶ S` (of finite presentation) is an effective
descent morphism for étale coverings. We prove it when `S` is locally noetherian
(`isEffectiveDescentMorphism_of_isProper`), following SGA:

* by IX.4.5 (`DescentDatum.isEffective_iff_forall_fromSpecCompletedStalk`) one may assume that
  `S = Spec R` with `R` a complete noetherian local ring;
* the descent datum becomes effective on the closed fibre (IX.4.1), the descended étale covering
  of `Spec k` lifts to `R`, and the comparison with the given covering of `S'` lifts from the
  closed fibre because base change to the closed fibre is fully faithful on étale coverings of
  schemes proper over `R` (`existsUnique_hom_of_isPullback_of_isProper`). As SGA notes, this uses
  only the full faithfulness in IX.1.10, not the existence theorem.

The argument is that of `DescentDatum.isEffective_of_isFinite_of_lift` (IX.4.7), with finite
algebras replaced by proper schemes.
-/

universe u

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

namespace SGA.SGA1.ExposeIX

open Scheme (FiniteEtale)
open IsLocalRing

section ClosedFibre

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [IsAdicComplete (maximalIdeal R) R]

/-- `R/𝔪¹ ≅ R/𝔪`. -/
noncomputable def quotPowOneIso :
    CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)) ≅ CommRingCat.of (R ⧸ maximalIdeal R) :=
  (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).toCommRingCatIso

omit [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] in
lemma specMap_quotPowOneIso :
    Spec.map (quotPowOneIso (R := R)).hom ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) =
      specQuotient (maximalIdeal R) := by
  rw [← Spec.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- IX.1.10, full faithfulness, for a closed fibre given by any cartesian square: for
`p : Y ⟶ Spec R` proper, `R` complete noetherian local, base change along `ι : Y₀ ⟶ Y` is fully
faithful on étale coverings. -/
theorem full_and_faithful_pullback_of_isPullback {Y Y₀ : Scheme.{u}} {p : Y ⟶ Spec (.of R)}
    [IsProper p] {ι : Y₀ ⟶ Y} {q : Y₀ ⟶ Spec (.of (R ⧸ maximalIdeal R))}
    (h : IsPullback ι q p (specQuotient (maximalIdeal R))) :
    (FiniteEtale.pullback ι).Full ∧ (FiniteEtale.pullback ι).Faithful := by
  have : IsNoetherianRing (CommRingCat.of R) := ‹_›
  have : IsAdicComplete (maximalIdeal R) (CommRingCat.of R) := ‹_›
  have h' : IsPullback ι (q ≫ Spec.map (quotPowOneIso (R := R)).hom) p
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1))))) :=
    h.of_iso (Iso.refl _) (Iso.refl _) (Scheme.Spec.mapIso (quotPowOneIso (R := R)).op)
      (Iso.refl _) (by simp) (by simp) (by simp) (by simp [specMap_quotPowOneIso])
  let e := h'.isoPullback
  have he : e.hom ≫ thickening.ι (A := .of R) p (maximalIdeal R) 0 = ι :=
    h'.isoPullback_hom_fst
  have hff := CohomologyAux.full_pullback_thickening (A := .of R) (maximalIdeal R) p
    finiteEtale_h83
  have hfa := CohomologyAux.faithful_pullback_thickening (A := .of R) (maximalIdeal R) p
    finiteEtale_h83
  have : (FiniteEtale.pullback e.hom).IsEquivalence :=
    finiteEtale_h83 _ inferInstance inferInstance
  let i : FiniteEtale.pullback ι ≅
      FiniteEtale.pullback (thickening.ι (A := .of R) p (maximalIdeal R) 0) ⋙
        FiniteEtale.pullback e.hom :=
    (MorphismProperty.Over.pullbackCongr he).symm ≪≫ MorphismProperty.Over.pullbackComp _ _
  exact ⟨Functor.Full.of_iso i.symm, Functor.Faithful.of_iso i.symm⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Morphisms from a proper `Spec R`-scheme `Y` to an étale covering `β : Z ⟶ Spec R`, `R`
complete noetherian local, are determined by, and lift from, their restrictions to the closed
fibre `Y ×_{Spec R} Spec (R ⧸ 𝔪)` (given by any cartesian square). This is the full faithfulness
of IX.1.10 for `Y`, applied to the étale covering `Y ×_R Z` of `Y`. -/
theorem existsUnique_hom_of_isPullback_of_isProper {Y Y₀ Z : Scheme.{u}} {p : Y ⟶ Spec (.of R)}
    [IsProper p] {ι : Y₀ ⟶ Y} {q : Y₀ ⟶ Spec (.of (R ⧸ maximalIdeal R))}
    (h : IsPullback ι q p (specQuotient (maximalIdeal R))) (β : Z ⟶ Spec (.of R)) [IsFinite β]
    [Etale β] (f₀ : Y₀ ⟶ Z) (hf₀ : f₀ ≫ β = ι ≫ p) :
    ∃! f : Y ⟶ Z, f ≫ β = p ∧ ι ≫ f = f₀ := by
  obtain ⟨hfull, hfaith⟩ := full_and_faithful_pullback_of_isPullback h
  let E : FiniteEtale Y := MorphismProperty.Over.mk ⊤ (pullback.fst p β)
    ⟨inferInstance, inferInstance⟩
  let T : FiniteEtale Y := MorphismProperty.Over.mk ⊤ (𝟙 Y) ⟨inferInstance, inferInstance⟩
  have hcond : pullback.fst T.hom ι = pullback.snd T.hom ι ≫ ι :=
    (Category.comp_id _).symm.trans pullback.condition
  -- sections of `E` over `Y` are morphisms `Y ⟶ Z` over `Spec R`
  let toHom (f : Y ⟶ Z) (hf : f ≫ β = p) : T ⟶ E :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 Y) f ((Category.id_comp p).trans hf.symm))
      (pullback.lift_fst _ _ _)
  have htoHom (f : Y ⟶ Z) (hf : f ≫ β = p) :
      (toHom f hf).left = pullback.lift (𝟙 Y) f ((Category.id_comp p).trans hf.symm) := rfl
  have hofHom (φ : T ⟶ E) : (φ.left ≫ pullback.snd p β) ≫ β = p := by
    have hw : φ.left ≫ pullback.fst p β = 𝟙 Y := MorphismProperty.Over.w φ
    rw [Category.assoc, ← pullback.condition, reassoc_of% hw]
    exact Category.id_comp p
  -- the morphism over the closed fibre defined by `f₀`
  let φ₀l : pullback T.hom ι ⟶ pullback E.hom ι :=
    pullback.lift (pullback.lift (pullback.fst T.hom ι) (pullback.snd T.hom ι ≫ f₀)
      (by rw [Category.assoc, hf₀, hcond, Category.assoc]))
      (pullback.snd T.hom ι) ((pullback.lift_fst _ _ _).trans hcond)
  have hφ₀l : φ₀l ≫ pullback.snd E.hom ι = pullback.snd T.hom ι := pullback.lift_snd _ _ _
  let φ₀ : (FiniteEtale.pullback ι).obj T ⟶ (FiniteEtale.pullback ι).obj E :=
    MorphismProperty.Over.homMk φ₀l hφ₀l
  -- `ψ ↦ ψ.left` determines morphisms over the closed fibre
  have hmapl (f : Y ⟶ Z) (hf : f ≫ β = p) (hιf : ι ≫ f = f₀) :
      ((FiniteEtale.pullback ι).map (toHom f hf)).left = φ₀l := by
    rw [MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [φ₀l, Category.assoc, pullback.lift_fst, htoHom]
        exact Category.comp_id _
      · simp only [φ₀l, Category.assoc, pullback.lift_fst, pullback.lift_snd, htoHom]
        rw [hcond, Category.assoc, hιf]
    · simp only [φ₀l, pullback.lift_snd]
  let σ₀ : Y₀ ⟶ pullback T.hom ι :=
    pullback.lift ι (𝟙 Y₀) ((Category.comp_id ι).trans (Category.id_comp ι).symm)
  have hσ₀ : σ₀ ≫ pullback.fst T.hom ι = ι := pullback.lift_fst _ _ _
  have hσ₀' : σ₀ ≫ pullback.snd T.hom ι = 𝟙 Y₀ := pullback.lift_snd _ _ _
  obtain ⟨φ, hφ⟩ := hfull.map_surjective φ₀
  refine ⟨φ.left ≫ pullback.snd p β, ⟨hofHom φ, ?_⟩, fun f ⟨hf, hιf⟩ ↦ ?_⟩
  · have h₁ := congrArg (fun ψ ↦ σ₀ ≫ ψ.left ≫ pullback.fst E.hom ι ≫ pullback.snd p β) hφ
    simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_fst_assoc] at h₁
    change σ₀ ≫ (pullback.fst T.hom ι ≫ φ.left) ≫ pullback.snd p β =
      σ₀ ≫ φ₀l ≫ pullback.fst E.hom ι ≫ pullback.snd p β at h₁
    have e1 : σ₀ ≫ (pullback.fst T.hom ι ≫ φ.left) ≫ pullback.snd p β =
        ι ≫ φ.left ≫ pullback.snd p β := by
      rw [Category.assoc, reassoc_of% hσ₀]
    refine e1.symm.trans (h₁.trans ?_)
    simp only [φ₀l, pullback.lift_fst_assoc]
    rw [pullback.lift_snd, reassoc_of% hσ₀']
  · have hφ' : (FiniteEtale.pullback ι).map (toHom f hf) = φ₀ :=
      MorphismProperty.Over.Hom.ext (hmapl f hf hιf)
    have hφf : toHom f hf = φ := hfaith.map_injective (hφ'.trans hφ.symm)
    have h₂ := congrArg (fun ψ : T ⟶ E ↦ ψ.left ≫ pullback.snd p β) hφf
    simp only [htoHom, pullback.lift_snd] at h₂
    exact h₂

set_option backward.isDefEq.respectTransparency false in
/-- Over a local ring `R`, an étale morphism `c : Y ⟶ Z` of proper `Spec R`-schemes which becomes
an isomorphism over the closed point (given by cartesian squares over some `σ : T ⟶ Spec R`
whose image contains the closed point) is an isomorphism. -/
theorem isIso_of_isIso_closedFibre_of_isProper {R : Type u} [CommRing R] [IsLocalRing R]
    {T : Scheme.{u}} (σ : T ⟶ Spec (.of R))
    (hσ : closedPoint R ∈ Set.range σ) {Y Z Y₀ Z₀ : Scheme.{u}} (pY : Y ⟶ Spec (.of R))
    (pZ : Z ⟶ Spec (.of R)) [IsProper pY] [IsProper pZ] (c : Y ⟶ Z) (hc : c ≫ pZ = pY)
    [Etale c] {ιY : Y₀ ⟶ Y} {qY : Y₀ ⟶ T} (hY : IsPullback ιY qY pY σ)
    {ιZ : Z₀ ⟶ Z} {qZ : Z₀ ⟶ T} (hZ : IsPullback ιZ qZ pZ σ)
    (c₀ : Y₀ ⟶ Z₀) (hc₀ : c₀ ≫ ιZ = ιY ≫ c) (hq : c₀ ≫ qZ = qY) [IsIso c₀] : IsIso c := by
  have : IsProper (c ≫ pZ) := hc ▸ inferInstance
  have : IsProper c := IsProper.of_comp c pZ
  -- surjectivity
  have hsurj : Surjective c := by
    refine ⟨fun z ↦ ?_⟩
    have hU : IsClopen (Set.range c) :=
      ⟨c.isClosedMap.isClosed_range, c.isOpenMap.isOpen_range⟩
    have := eq_univ_of_isClopen_of_closedFibre_subset pZ hU (fun z hz ↦ ?_)
    · exact this.ge (Set.mem_univ z)
    · have hz' : z ∈ Set.range ιZ := by
        rw [isPullback_range_fst_eq hZ]
        change pZ z ∈ Set.range σ
        rw [Set.mem_singleton_iff.mp hz]; exact hσ
      obtain ⟨z₀, rfl⟩ := hz'
      refine ⟨ιY (inv c₀ z₀), ?_⟩
      rw [← Scheme.Hom.comp_apply, ← hc₀, ← Scheme.Hom.comp_apply, IsIso.inv_hom_id_assoc]
  -- universal injectivity, via the diagonal
  have hW : IsPullback (ιY ≫ pullback.diagonal c) qY (pullback.fst c c ≫ pY) σ := by
    refine IsPullback.of_isLimit' ⟨by simp [hY.w]⟩ (PullbackCone.IsLimit.mk _
      (fun s ↦ hY.lift (s.fst ≫ pullback.fst c c) s.snd (by simpa using s.condition))
      (fun s ↦ ?_) (fun s ↦ by simp) (fun s m h₁ h₂ ↦ hY.hom_ext (by
        have := congr_arg (· ≫ pullback.fst c c) h₁
        simpa using this) (by simpa using h₂)))
    have h₂ : (s.fst ≫ pullback.snd c c) ≫ pY = s.snd ≫ σ := by
      have hs : s.fst ≫ pullback.fst c c ≫ pY = s.snd ≫ σ := by
        simpa only [Category.assoc] using s.condition
      calc (s.fst ≫ pullback.snd c c) ≫ pY = s.fst ≫ pullback.snd c c ≫ c ≫ pZ := by
            rw [hc, Category.assoc]
        _ = s.fst ≫ pullback.fst c c ≫ c ≫ pZ := by rw [pullback.condition_assoc]
        _ = s.snd ≫ σ := by rw [hc, hs]
    have key : hY.lift (s.fst ≫ pullback.fst c c) s.snd (by simpa using s.condition) =
        hY.lift (s.fst ≫ pullback.snd c c) s.snd h₂ := by
      rw [← cancel_mono c₀]
      apply hZ.hom_ext
      · simp only [Category.assoc, hc₀, IsPullback.lift_fst_assoc, pullback.condition]
      · simp [hq]
    apply pullback.hom_ext
    · simp
    · simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
      conv_lhs => rw [key]
      simp
  have hdiag : Surjective (pullback.diagonal c) := by
    refine ⟨fun w ↦ ?_⟩
    have hU : IsClopen (Set.range (pullback.diagonal c)) :=
      ⟨(pullback.diagonal c).isClosedEmbedding.isClosed_range,
        (pullback.diagonal c).isOpenEmbedding.isOpen_range⟩
    have := eq_univ_of_isClopen_of_closedFibre_subset (pullback.fst c c ≫ pY) hU
      (fun w hw ↦ ?_)
    · exact this.ge (Set.mem_univ w)
    · have hw' : w ∈ Set.range (ιY ≫ pullback.diagonal c) := by
        rw [isPullback_range_fst_eq hW]
        change (pullback.fst c c ≫ pY) w ∈ Set.range σ
        rw [Set.mem_singleton_iff.mp hw]; exact hσ
      obtain ⟨y₀, rfl⟩ := hw'
      exact ⟨ιY y₀, rfl⟩
  have : UniversallyInjective c := (UniversallyInjective.iff_diagonal c).mpr hdiag
  exact isIso_of_etale_of_universallyInjective_of_surjective c

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.12 over a complete noetherian local base: along a proper surjective
`g : S' ⟶ Spec R`, every descent datum on a finite étale `S'`-scheme is effective, with a finite
étale descended scheme. The datum is effective on the closed fibre (IX.4.1); the descended
covering lifts to `R`, and the comparison with the given covering lifts from the closed fibre by
the full faithfulness in IX.1.10 (`existsUnique_hom_of_isPullback_of_isProper`). -/
theorem DescentDatum.isEffective_of_isProper_of_isAdicComplete {S' Y : Scheme.{u}}
    {g : S' ⟶ Spec (.of R)} [IsProper g] [Surjective g] {a : Y ⟶ S'} [IsFinite a] [Etale a]
    (D : DescentDatum g a) : D.IsEffective (@IsFinite ⊓ @Etale) := by
  let σ := specQuotient (maximalIdeal R)
  have hF : IsField (R ⧸ maximalIdeal R) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp inferInstance
  have hbot (x : PrimeSpectrum (R ⧸ maximalIdeal R)) : x.asIdeal = ⊥ := by
    refine eq_bot_iff.mpr fun r hr ↦ ?_
    by_contra h
    obtain ⟨r', hr'⟩ := hF.mul_inv_cancel h
    exact x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem hr (IsUnit.of_mul_eq_one _ hr'))
  have : Subsingleton (Spec (.of (R ⧸ maximalIdeal R))) :=
    ⟨fun x y ↦ PrimeSpectrum.ext ((hbot x).trans (hbot y).symm)⟩
  have hσ : closedPoint R ∈ Set.range σ := by
    obtain ⟨x⟩ : Nonempty (PrimeSpectrum (R ⧸ maximalIdeal R)) := inferInstance
    refine ⟨x, PrimeSpectrum.ext ?_⟩
    change x.asIdeal.comap (Ideal.Quotient.mk _) = maximalIdeal R
    refine ((maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ x.isPrime.ne_top)
      fun r hr ↦ ?_).symm
    simp [Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  -- effective descent on the closed fibre (IX.4.1)
  have ha₀ : etaleSeparatedFiniteType (pullback.snd a (pullback.fst g σ)) :=
    MorphismProperty.pullback_snd _ _ ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨X₀, b₀, v₀, hb₀, hv₀, hact₀⟩ := (D.baseChange σ).isEffective_of_flat' ha₀
  have : Etale b₀ := hb₀.1.1
  have : IsFinite b₀ :=
    of_isPullback_of_descendsAlong (P := @IsFinite) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      hv₀.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  -- lift the descended scheme to a finite étale `Spec R`-scheme
  obtain ⟨B, _, _, hBf, hBe, ιX, hX⟩ := exists_isPullback_of_finite_etale (maximalIdeal R) b₀
  let b : Spec (.of B) ⟶ Spec (.of R) := Spec.map (CommRingCat.ofHom (algebraMap R B))
  have : Etale b := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr hBe)
  have : IsFinite b := (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hBf)
  have hY := isPullback_baseChange_obj σ (g := g) (a := a)
  -- the projection `Y ⟶ Spec B`, lifting the closed fibre
  obtain ⟨v, ⟨hvb, hvι⟩, -⟩ :=
    existsUnique_hom_of_isPullback_of_isProper hY b (v₀ ≫ ιX) (by
      rw [Category.assoc, hX.w, ← Category.assoc, hv₀.w, hY.w, Category.assoc])
  -- the square is cartesian: the comparison map is an isomorphism on the closed fibres
  let c : Y ⟶ pullback b g := pullback.lift v a hvb
  have : Etale (c ≫ pullback.snd b g) := by rw [pullback.lift_snd]; infer_instance
  have : Etale c := Etale.of_comp c (pullback.snd b g)
  have hZ := isPullback_pullbackMap_of_isPullback hX (IsPullback.of_hasPullback g σ)
  have : IsIso c := isIso_of_isIso_closedFibre_of_isProper σ hσ (a ≫ g)
    (pullback.snd b g ≫ g) c (by simp [c]) hY hZ hv₀.isoPullback.hom (by
      apply pullback.hom_ext
      · simp [c, b, σ, pullback.map, hvι]
      · simp [c, b, σ, pullback.map, pullback.condition]) (by simp)
  have hv : IsPullback v a b g :=
    IsPullback.of_iso_pullback ⟨hvb⟩ (asIso c) (by simp [c]) (by simp [c])
  -- compatibility with the descent datum, checked on the closed fibre of `Y ×_{Spec R} S'`
  have hact : D.act ≫ v = pullback.fst (a ≫ g) g ≫ v := by
    have hX'' := isPullback_baseChangeAux g a σ
    obtain ⟨f, -, huniq⟩ := existsUnique_hom_of_isPullback_of_isProper hX'' b
      (DescentDatum.baseChangeAux g a σ ≫ D.act ≫ v) (by
        rw [Category.assoc, Category.assoc, hvb, reassoc_of% D.act_comp])
    have h₁ := huniq (D.act ≫ v) ⟨by rw [Category.assoc, hvb, reassoc_of% D.act_comp], rfl⟩
    have h₂ := huniq (pullback.fst (a ≫ g) g ≫ v) ⟨by
        rw [Category.assoc, hvb, pullback.condition], by
        have e₁ : DescentDatum.baseChangeAux g a σ ≫ D.act =
            (D.baseChange σ).act ≫ pullback.fst a (pullback.fst g σ) :=
          (pullback.lift_fst _ _ _).symm
        rw [reassoc_of% e₁, DescentDatum.baseChangeAux_fst_assoc, hvι, reassoc_of% hact₀]⟩
    rw [h₁, h₂]
  exact ⟨Spec (.of B), b, v, ⟨inferInstance, inferInstance⟩, hv, hact⟩

end ClosedFibre

section Noetherian

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.12 for étale coverings over a locally noetherian base: along a proper surjective
`g : S' ⟶ S`, every descent datum on a finite étale `S'`-scheme is effective, with a finite
étale descended scheme. -/
theorem DescentDatum.isEffective_etaleCovering_of_isProper [IsLocallyNoetherian S] [IsProper g]
    [Surjective g] [IsFinite a] [Etale a]
    (D : DescentDatum g a) : D.IsEffective etaleCovering := by
  have ha : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecCompletedStalk ha]
    intro x
    exact ((D.baseChange (fromSpecCompletedStalk S x)).isEffective_of_isProper_of_isAdicComplete
      ).of_le fun _ _ f h ↦ have : IsFinite f := h.1; ⟨⟨h.2, inferInstance⟩, inferInstance⟩
  obtain ⟨X, b, v, hb, hv, hact⟩ := hfp
  have : Etale b := hb.1.1
  -- `X` is finite over `S`: it is proper, since `X' = X ×_S S'` is, and quasi-finite
  have : IsProper b := (isProper_iff_of_isPullback hv.flip).mp inferInstance
  have : LocallyQuasiFinite b := locallyQuasiFinite_of_formallyUnramified b
  exact ⟨X, b, v, ⟨.of_isProper_of_locallyQuasiFinite b, inferInstance⟩, hv, hact⟩

variable (g) in
/-- **IX.4.12** (locally noetherian base): a proper surjective morphism to a locally noetherian
scheme (hence of finite presentation) is an effective descent morphism for étale coverings. -/
theorem isEffectiveDescentMorphism_of_isProper [IsLocallyNoetherian S] [IsProper g]
    [Surjective g] : IsEffectiveDescentMorphism g etaleCovering :=
  ⟨isDescentMorphism_of_isProper (g := g), fun _ a D ha ↦
    have : IsFinite a := ha.1
    have : Etale a := ha.2
    D.isEffective_etaleCovering_of_isProper⟩

end Noetherian

end SGA.SGA1.ExposeIX
