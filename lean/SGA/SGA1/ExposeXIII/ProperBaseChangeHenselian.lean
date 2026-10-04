/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Etale.ProperBaseChangeClopen
import SGA.Foundations.Limits.GeometricFiberCardIso
import SGA.SGA1.ExposeI.Fundamental
import SGA.SGA1.ExposeI.Unramified
import SGA.SGA1.ExposeIX.EtaleMorphismDescent
import SGA.SGA1.ExposeVIII.QuasiFiniteOpenInFinite

/-!
# Sections of étale schemes over a proper scheme over a henselian local ring

Used in the proof of XIII 1.4 (`SGA.SGA1.ExposeXIII.ProperBaseChangeRepresentable`). Let `A` be a
noetherian henselian local ring, `P` proper over `Spec A` with closed fibre `P₀ = P ×_A κ`, and
`E ⟶ P` étale, separated and of finite type. Every section of `E` over `P₀` extends to a section
over `P` (`exists_section_of_henselianLocalRing`; Stacks 0A3S for the sheaf represented by `E`,
noetherian case, by an argument which avoids Gabber's lemma):

* by VIII.6.4 (`ExposeVIII.exists_isOpenImmersion_isFinite_of_isNoetherian`), `E` is an open
  subscheme of a scheme `Z` finite over `P`;
* the image `C₀` of the section in the closed fibre `Z₀` of `Z` is open and closed, so it lifts to
  a clopen subset `C` of `Z`, `Z` being proper over `A`
  (`exists_isClopen_preimage_of_isPullback_of_henselianLocalRing`);
* `C ⊆ E`, since a closed subset of `Z` missing the closed fibre is empty
  (`eq_empty_of_isClosed_of_forall_ne_closedPoint`);
* `C ⟶ P` is finite étale and an isomorphism over `P₀`; its geometric number of points is locally
  constant and equal to `1` near `P₀`, hence everywhere, so it is an isomorphism
  (`AlgebraicGeometry.Scheme.Hom.isIso_of_forall_geometricFiberCard_eq_one`); its inverse is the
  section.

Consequences: morphisms from `P` into separated étale `X`-schemes extend uniquely from `P₀`
(`exists_hom_of_isPullback_closedFibre`; uniqueness is
`AlgebraicGeometry.eq_of_comp_eq_of_isPullback_closedFibre`), and the full faithfulness half of
IX.1.10 holds over a noetherian henselian local ring
(`full_pullback_closedFibre_of_henselianLocalRing`; faithfulness over any local ring,
`faithful_pullback_closedFibre_of_isLocalRing`), part of
`HenselianEtaleCoveringsOfClosedFibreStatement`. These contain the complete noetherian case
`ExposeIX.full_pullback_closedFibre`, `ExposeIX.faithful_pullback_closedFibre` (a complete local
ring is henselian, `ExposeIX.henselianLocalRing_of_isAdicComplete`), which `ExposeIX` proves
differently, through the formal completion; neither half needs to be proved a third time.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

-- As in `SGA.Foundations.Etale.Functoriality`.
set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

section Section

variable {A : CommRingCat.{u}} [HenselianLocalRing A] [IsNoetherianRing A] {P : Scheme.{u}}
  (p : P ⟶ Spec A) [IsProper p]

/-- The case of `exists_section_of_henselianLocalRing` where `E ⟶ P` is quasi-compact. -/
theorem exists_section_of_henselianLocalRing_of_quasiCompact (E : P.Etale) [IsSeparated E.hom]
    [QuasiCompact E.hom]
    (s₀ : pullback p (Spec.map (CommRingCat.ofHom (residue A))) ⟶ E.left)
    (hs₀ : s₀ ≫ E.hom = pullback.fst p (Spec.map (CommRingCat.ofHom (residue A)))) :
    ∃ s : P ⟶ E.left, s ≫ E.hom = 𝟙 P ∧
      pullback.fst p (Spec.map (CommRingCat.ofHom (residue A))) ≫ s = s₀ := by
  let r := Spec.map (CommRingCat.ofHom (residue A))
  let P₀ := pullback p r
  let i : P₀ ⟶ P := pullback.fst p r
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian P := {}
  have : IsNoetherian ((Functor.fromPUnit P).obj E.right) := inferInstanceAs (IsNoetherian P)
  -- VIII.6.4: `E` is open in some `Z` finite over `P`
  obtain ⟨Z, j, π, _, _, hjπ⟩ := ExposeVIII.exists_isOpenImmersion_isFinite_of_isNoetherian E.hom
  -- the closed fibres of `E` and `Z`, and the section `c₀` of `Z₀ ⟶ P₀`
  let Z₀ := pullback π i
  let E₀ := pullback E.hom i
  let j₀ : E₀ ⟶ Z₀ := pullback.map E.hom i π i j (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hjπ])
    (by simp)
  have hj₀fst : j₀ ≫ pullback.fst π i = pullback.fst E.hom i ≫ j := by simp [j₀]
  have hj₀snd : j₀ ≫ pullback.snd π i = pullback.snd E.hom i := by simp [j₀]
  have hj₀ : IsPullback j₀ (pullback.fst E.hom i) (pullback.fst π i) j := by
    refine IsPullback.of_right (h₁₂ := pullback.snd π i) (h₂₂ := π) (v₁₃ := i) ?_ hj₀fst
      (IsPullback.of_hasPullback π i).flip
    rw [hj₀snd, hjπ]
    exact (IsPullback.of_hasPullback E.hom i).flip
  have : IsOpenImmersion j₀ := MorphismProperty.of_isPullback hj₀.flip inferInstance
  let σ₀ : P₀ ⟶ E₀ := pullback.lift s₀ (𝟙 P₀) (by rw [hs₀, Category.id_comp])
  have hσ₀ : σ₀ ≫ pullback.snd E.hom i = 𝟙 P₀ := pullback.lift_snd _ _ _
  have : IsOpenImmersion σ₀ := ExposeI.isOpenImmersion_of_section (pullback.snd E.hom i) hσ₀
  let c₀ := σ₀ ≫ j₀
  have hc₀ : c₀ ≫ pullback.snd π i = 𝟙 P₀ := by
    rw [Category.assoc, hj₀snd, hσ₀]
  have hc₀fst : c₀ ≫ pullback.fst π i = s₀ ≫ j := by
    rw [Category.assoc, hj₀fst, ← Category.assoc]
    exact congrArg (· ≫ j) (pullback.lift_fst _ _ _)
  have : IsClosedImmersion c₀ := ExposeI.isClosedImmersion_of_section (pullback.snd π i) hc₀
  have hC₀ : IsClopen (Set.range c₀) :=
    ⟨c₀.isClosedEmbedding.isClosed_range, c₀.isOpenEmbedding.isOpen_range⟩
  -- lift the clopen subset `c₀(P₀)` of `Z₀` to a clopen subset `C` of `Z`
  have hZpb : IsPullback (pullback.fst π i) (pullback.snd π i ≫ pullback.snd p r) (π ≫ p) r :=
    (IsPullback.of_hasPullback π i).paste_vert (IsPullback.of_hasPullback p r)
  obtain ⟨C, hC, hCC₀⟩ :=
    exists_isClopen_preimage_of_isPullback_of_henselianLocalRing (π ≫ p) hZpb _ hC₀
  have hZrange := range_eq_preimage_closedPoint_of_isPullback hZpb
  have hCfibre (z : Z) (hzC : z ∈ C) (hzm : (π ≫ p) z = closedPoint A) :
      ∃ x₀, j (s₀ x₀) = z := by
    obtain ⟨z₀, rfl⟩ : z ∈ Set.range (pullback.fst π i) := hZrange ▸ hzm
    obtain ⟨x₀, rfl⟩ : z₀ ∈ Set.range c₀ := hCC₀ ▸ hzC
    refine ⟨x₀, ?_⟩
    have e := congrArg (fun φ ↦ φ x₀) hc₀fst
    simp only [Scheme.Hom.comp_apply] at e
    exact e.symm
  -- `C` lies in `E`
  have hCj : C ⊆ Set.range j := by
    have hT := eq_empty_of_isClosed_of_forall_ne_closedPoint (π ≫ p)
      (hC.1.inter j.isOpenEmbedding.isOpen_range.isClosed_compl) fun z ⟨hzC, hzj⟩ hzm ↦ by
        obtain ⟨x₀, rfl⟩ := hCfibre z hzC hzm
        exact hzj ⟨_, rfl⟩
    intro z hz
    by_contra hzj
    exact (hT ▸ ⟨hz, hzj⟩ : z ∈ (∅ : Set Z))
  -- the open subscheme `U = j⁻¹(C)` of `E`, finite étale over `P`
  let U : E.left.Opens := j ⁻¹ᵁ ⟨C, hC.isOpen⟩
  have hUC : Set.range (U.ι ≫ j) = C := by
    ext z
    constructor
    · rintro ⟨u, rfl⟩
      rw [Scheme.Hom.comp_apply]
      exact u.2
    · intro hz
      obtain ⟨e, rfl⟩ := hCj hz
      exact ⟨⟨e, hz⟩, rfl⟩
  let g : U.toScheme ⟶ P := U.ι ≫ E.hom
  have : IsClosedImmersion (U.ι ≫ j) :=
    IsClosedImmersion.of_isPreimmersion _ (hUC ▸ hC.1)
  have hg : g = (U.ι ≫ j) ≫ π := by rw [Category.assoc, hjπ]
  have : IsFinite g := hg ▸ inferInstance
  -- the section `s₀` lands in `U`
  have hs₀U : Set.range s₀ ⊆ (U : Set E.left) := by
    rintro _ ⟨x₀, rfl⟩
    change j (s₀ x₀) ∈ C
    have h₁ : pullback.fst π i (c₀ x₀) ∈ C := by
      have : c₀ x₀ ∈ (pullback.fst π i) ⁻¹' C := hCC₀ ▸ ⟨x₀, rfl⟩
      exact this
    have e := congrArg (fun φ ↦ φ x₀) hc₀fst
    simp only [Scheme.Hom.comp_apply] at e
    rwa [e] at h₁
  let s₀' := IsOpenImmersion.lift U.ι s₀ (by rwa [Scheme.Opens.range_ι])
  have hs₀' : s₀' ≫ U.ι = s₀ := IsOpenImmersion.lift_fac _ _ _
  have hs₀'g : s₀' ≫ g = i :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ E.hom) hs₀').trans hs₀)
  -- over the closed fibre, `g` is an isomorphism: its base change has a surjective section
  have hU₀ := IsPullback.of_hasPullback g i
  let τ₀ : P₀ ⟶ pullback g i := pullback.lift s₀' (𝟙 P₀) (by rw [hs₀'g, Category.id_comp])
  have hτ₀ : τ₀ ≫ pullback.snd g i = 𝟙 P₀ := pullback.lift_snd _ _ _
  have : IsOpenImmersion τ₀ := ExposeI.isOpenImmersion_of_section (pullback.snd g i) hτ₀
  have : IsClosedImmersion i :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback p r).flip
      (IsClosedImmersion.spec_of_surjective _ residue_surjective)
  have : IsLocalHom (CommRingCat.ofHom (residue A)).hom := inferInstanceAs (IsLocalHom (residue A))
  have hclosed (x : P₀) : (i ≫ p) x = closedPoint A := by
    have e := congrArg (fun φ ↦ φ x) (pullback.condition : pullback.fst p r ≫ p = _ ≫ r)
    simp only [Scheme.Hom.comp_apply] at e ⊢
    rw [e, Subsingleton.elim (pullback.snd p r x) (closedPoint _)]
    exact Spec_closedPoint
  have hsurj : Surjective τ₀ := by
    refine ⟨fun u₀ ↦ ?_⟩
    let u := pullback.fst g i u₀
    have hum : (π ≫ p) (j (U.ι u)) = closedPoint A := by
      have e₁ : (pullback.fst g i ≫ (U.ι ≫ j) ≫ π ≫ p) u₀ = (pullback.snd g i ≫ i ≫ p) u₀ := by
        congr 1
        rw [← Category.assoc (U.ι ≫ j), ← hg, pullback.condition_assoc]
      simp only [Scheme.Hom.comp_apply] at e₁ ⊢
      refine e₁.trans ?_
      have := hclosed (pullback.snd g i u₀)
      simp only [Scheme.Hom.comp_apply] at this
      exact this
    obtain ⟨x₀, hx₀⟩ := hCfibre _ (u.2 : j (U.ι u) ∈ C) hum
    have hux : u = s₀' x₀ := by
      apply U.ι.isOpenEmbedding.injective
      apply j.isOpenEmbedding.injective
      have e : U.ι (s₀' x₀) = s₀ x₀ := by
        have := congrArg (fun φ ↦ φ x₀) hs₀'
        simp only [Scheme.Hom.comp_apply] at this
        exact this
      rw [e]
      exact hx₀.symm
    refine ⟨x₀, (pullback.fst g i).isClosedEmbedding.injective ?_⟩
    have e : pullback.fst g i (τ₀ x₀) = s₀' x₀ := by
      have := congrArg (fun φ ↦ φ x₀) (pullback.lift_fst _ _ _ : τ₀ ≫ pullback.fst g i = s₀')
      simp only [Scheme.Hom.comp_apply] at this
      exact this
    rw [e]
    exact hux.symm
  have : IsIso τ₀ := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, hsurj⟩
  have : IsIso (pullback.snd g i) := by
    have : pullback.snd g i = inv τ₀ := by
      rw [← cancel_epi τ₀, hτ₀, IsIso.hom_inv_id]
    rw [this]
    infer_instance
  have hfin : ∀ y, (g ⁻¹' {y}).Finite := g.finite_preimage_singleton
  have hcard₀ (x₀ : P₀) : g.geometricFiberCard (i x₀) = 1 := by
    rw [← g.geometricFiberCard_of_isPullback hfin hU₀ x₀]
    exact Scheme.Hom.geometricFiberCard_eq_one_of_isIso _ x₀
  -- the geometric number of points of `g` is locally constant, hence `1` everywhere
  have hcard (y : P) : g.geometricFiberCard y = 1 := by
    have hT : IsClosed {y | g.geometricFiberCard y ≠ 1} :=
      (g.isLocallyConstant_geometricFiberCard.isClopen_fiber 1).isOpen.isClosed_compl
    have hempty := eq_empty_of_isClosed_of_forall_ne_closedPoint p hT fun y hy hym ↦ by
      obtain ⟨x₀, rfl⟩ :=
        (range_eq_preimage_closedPoint_of_isPullback (IsPullback.of_hasPullback p r)).ge hym
      exact hy (hcard₀ x₀)
    by_contra h
    have hy : y ∈ ({y | g.geometricFiberCard y ≠ 1} : Set P) := h
    rw [hempty] at hy
    exact hy
  have : IsIso g := Scheme.Hom.isIso_of_forall_geometricFiberCard_eq_one g hfin hcard
  refine ⟨inv g ≫ U.ι, by simp [g], ?_⟩
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ U.ι) ((IsIso.eq_comp_inv g).mpr hs₀'g).symm).trans hs₀')

/-- **Sections of separated étale schemes extend from the closed fibre over a noetherian henselian
local ring** (Stacks 0A3S for the sheaf represented by `E`; noetherian case): let `P` be proper
over `Spec A` with closed fibre `P₀ = P ×_A κ`, and `E ⟶ P` étale and separated. Every section
of `E` over `P₀` extends to a section over `P`. (The image of the section lies in a quasi-compact
open subscheme of `E`, to which `exists_section_of_henselianLocalRing_of_quasiCompact` applies.) -/
theorem exists_section_of_henselianLocalRing (E : P.Etale) [IsSeparated E.hom]
    (s₀ : pullback p (Spec.map (CommRingCat.ofHom (residue A))) ⟶ E.left)
    (hs₀ : s₀ ≫ E.hom = pullback.fst p (Spec.map (CommRingCat.ofHom (residue A)))) :
    ∃ s : P ⟶ E.left, s ≫ E.hom = 𝟙 P ∧
      pullback.fst p (Spec.map (CommRingCat.ofHom (residue A))) ≫ s = s₀ := by
  let r := Spec.map (CommRingCat.ofHom (residue A))
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : CompactSpace ↥(pullback p r) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst p r)
  -- a quasi-compact open subscheme `U` of `E` containing the image of `s₀`
  obtain ⟨t, ht⟩ := (isCompact_range s₀.continuous).elim_finite_subcover
    (fun V : E.left.affineOpens ↦ (V.1 : Set E.left)) (fun V ↦ V.1.2) fun x _ ↦
      Set.mem_iUnion.mpr (TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top E.left).ge (Set.mem_univ x)))
  let U : E.left.Opens := ⨆ V ∈ t, V.1
  have hU : IsCompact (U : Set E.left) := by
    simp only [U, TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.coe_mk]
    exact t.isCompact_biUnion fun V _ ↦ V.2.isCompact
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have hsU : Set.range s₀ ⊆ U := fun x hx ↦ by
    obtain ⟨V, hV, hxV⟩ := Set.mem_iUnion₂.mp (ht hx)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨V, TopologicalSpace.Opens.mem_iSup.mpr ⟨hV, hxV⟩⟩
  let EU : P.Etale := Scheme.Etale.mk (U.ι ≫ E.hom)
  have : IsSeparated EU.hom := inferInstanceAs (IsSeparated (U.ι ≫ E.hom))
  have : QuasiSeparatedSpace P := quasiSeparatedSpace_of_quasiSeparated p
  have : QuasiSeparatedSpace ↥((Functor.fromPUnit P).obj E.right) :=
    inferInstanceAs (QuasiSeparatedSpace P)
  have : CompactSpace U.toScheme := inferInstanceAs (CompactSpace U)
  have : QuasiCompact EU.hom := quasiCompact_of_compactSpace (U.ι ≫ E.hom)
  let s₀' := IsOpenImmersion.lift U.ι s₀ (by rwa [Scheme.Opens.range_ι])
  have hs₀' : s₀' ≫ U.ι = s₀ := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨s, hs, his⟩ := exists_section_of_henselianLocalRing_of_quasiCompact p EU s₀'
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ E.hom) hs₀').trans hs₀))
  refine ⟨s ≫ U.ι, (Category.assoc _ _ _).trans hs, ?_⟩
  rw [← Category.assoc, his, hs₀']

/-- **Morphisms into separated étale schemes extend from the closed fibre** over a noetherian
henselian local ring: for `P` proper over `Spec A` with closed fibre `ι : P₀ ⟶ P` (any cartesian
square), `π : P ⟶ X` and `E` étale and separated over `X`, every `w : P₀ ⟶ E` over `ι ≫ π` is
`ι ≫ v` for some `v : P ⟶ E` over `π` (unique by `eq_of_comp_eq_of_isPullback_closedFibre`). -/
theorem exists_hom_of_isPullback_closedFibre {P₀ X : Scheme.{u}} {ι : P₀ ⟶ P}
    {q₀ : P₀ ⟶ Spec (.of (ResidueField A))}
    (h : IsPullback ι q₀ p (Spec.map (CommRingCat.ofHom (residue A)))) (π : P ⟶ X)
    (E : X.Etale) [IsSeparated E.hom] (w : P₀ ⟶ E.left) (hw : w ≫ E.hom = ι ≫ π) :
    ∃ v : P ⟶ E.left, v ≫ E.hom = π ∧ ι ≫ v = w := by
  let e := h.isoPullback
  have he : e.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom (residue A))) = ι :=
    h.isoPullback_hom_fst
  let EP : P.Etale := Scheme.Etale.mk (pullback.snd E.hom π)
  have : IsSeparated EP.hom := inferInstanceAs (IsSeparated (pullback.snd E.hom π))
  obtain ⟨s, hs, his⟩ := exists_section_of_henselianLocalRing p EP
    (e.inv ≫ pullback.lift w ι hw) (by
      change (e.inv ≫ pullback.lift w ι hw) ≫ pullback.snd E.hom π = _
      rw [Category.assoc, pullback.lift_snd, ← he, Iso.inv_hom_id_assoc])
  refine ⟨s ≫ pullback.fst E.hom π, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    change (s ≫ EP.hom) ≫ π = π
    rw [hs, Category.id_comp]
  · rw [← he, Category.assoc, reassoc_of% his, Iso.hom_inv_id_assoc, pullback.lift_fst]

end Section

section Coverings

variable (A : Type u) [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- The closed fibre of an étale covering `Y` of `X` is a closed fibre of `Y` over `Spec A`. -/
lemma isPullback_closedFibre_comp [IsLocalRing A] {Y : Scheme.{u}} (q : Y ⟶ X) :
    IsPullback (pullback.fst q (pullback.fst f (Spec.map (CommRingCat.ofHom (residue A)))))
      (pullback.snd q (pullback.fst f (Spec.map (CommRingCat.ofHom (residue A)))) ≫
        pullback.snd f (Spec.map (CommRingCat.ofHom (residue A)))) (q ≫ f)
      (Spec.map (CommRingCat.ofHom (residue (CommRingCat.of A)))) :=
  (IsPullback.of_hasPullback _ _).paste_vert (IsPullback.of_hasPullback _ _)

/-- IX.1.10, faithfulness, over any local ring (SGA 1 states IX.1.10 for a complete noetherian
local ring; this is the faithfulness half of `HenselianEtaleCoveringsOfClosedFibreStatement`,
which holds without the henselian hypothesis): for `X` proper over `Spec A`, two morphisms of
étale coverings of `X` which agree on the closed fibre are equal. This contains
`ExposeIX.faithful_pullback_closedFibre` (complete noetherian `A`). -/
theorem faithful_pullback_closedFibre_of_isLocalRing [IsLocalRing A] [IsProper f] :
    (MorphismProperty.Over.pullback ExposeIX.etaleCovering ⊤
      (pullback.fst f (Spec.map (CommRingCat.ofHom (residue A))))).Faithful where
  map_injective {Y₁ Y₂} φ ψ hφψ := by
    have : IsFinite Y₁.hom := Y₁.prop.1
    have : IsFinite Y₂.hom := Y₂.prop.1
    have : Etale Y₂.hom := Y₂.prop.2
    let E : X.Etale := Scheme.Etale.mk Y₂.hom
    have : IsSeparated E.hom := inferInstanceAs (IsSeparated Y₂.hom)
    ext1
    refine eq_of_comp_eq_of_isPullback_closedFibre (A := CommRingCat.of A)
      (isPullback_closedFibre_comp A f Y₁.hom) E
      φ.left ψ.left ((MorphismProperty.Over.w φ).trans (MorphismProperty.Over.w ψ).symm) ?_
    have := congrArg (fun k ↦ k.left ≫ pullback.fst Y₂.hom
      (pullback.fst f (Spec.map (CommRingCat.ofHom (residue A))))) hφψ
    simp only [MorphismProperty.Over.pullback_map_left, pullback.lift_fst] at this
    exact this

/-- IX.1.10, fullness, over a noetherian henselian local ring (SGA 1 states IX.1.10 for a complete
noetherian local ring; this is the fullness half of `HenselianEtaleCoveringsOfClosedFibreStatement`
for noetherian `A`): for `X` proper over `Spec A`, every morphism between the restrictions to the
closed fibre of two étale coverings of `X` comes from a morphism of étale coverings
(`exists_hom_of_isPullback_closedFibre`). This contains `ExposeIX.full_pullback_closedFibre`
(complete noetherian `A`, `ExposeIX.henselianLocalRing_of_isAdicComplete`). -/
theorem full_pullback_closedFibre_of_henselianLocalRing [HenselianLocalRing A]
    [IsNoetherianRing A] [IsProper f] :
    (MorphismProperty.Over.pullback ExposeIX.etaleCovering ⊤
      (pullback.fst f (Spec.map (CommRingCat.ofHom (residue A))))).Full :=
  ExposeIX.full_overPullback_of_exists _ _ fun Y₁ Y₂ p q hp hq φ' hφ' ↦ by
    have : IsFinite p := hp.1
    have : IsFinite q := hq.1
    have : Etale q := hq.2
    let E : X.Etale := Scheme.Etale.mk q
    have : IsSeparated E.hom := inferInstanceAs (IsSeparated q)
    have : HenselianLocalRing (CommRingCat.of A) := ‹HenselianLocalRing A›
    have : IsNoetherianRing (CommRingCat.of A) := ‹IsNoetherianRing A›
    exact exists_hom_of_isPullback_closedFibre (A := CommRingCat.of A) (p ≫ f)
      (isPullback_closedFibre_comp A f p) p E φ' hφ'

end Coverings

end SGA.SGA1.ExposeXIII
