/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Limits.FiniteEtale
import SGA.Foundations.Limits.SpreadingOutAffine

/-!
# Spreading out schemes of finite presentation over a limit

EGA IV 8.8.2 (ii) (Stacks 01ZM): let `c.pt = lim E i` be the limit of a cofiltered diagram of
quasi-compact and quasi-separated schemes with affine transition maps. Every `c.pt`-scheme of
finite presentation is the base change of a scheme of finite presentation over some `E j`
(`AlgebraicGeometry.Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation`,
`AlgebraicGeometry.Scheme.spreadingOutStatement`).

The proof is Stacks': an affine open of `X` lying over an affine open of some `E i` descends by
the affine case (`SGA.Foundations.Limits.SpreadingOutAffine`, commutative algebra); then the
pieces of a finite affine cover are glued one at a time
(`AlgebraicGeometry.Scheme.spreadsOut_of_sup_eq_top`): if `X = U ∪ W` with `U`, `W` descended to
`U_j`, `W_j`, the quasi-compact open `U ∩ W` descends to opens of `U_k` and `W_k`, these become
isomorphic at some level `l` (EGA IV 8.8.2 (i), `Scheme.exists_iso_of_isPullback`), and `U_l`,
`W_l` are glued along them as a pushout of open immersions.

* `AlgebraicGeometry.Scheme.LimitModel c q j`: a model of `q : X ⟶ c.pt` of finite presentation
  over `E j`, i.e. a cartesian square `X ⟶ X_j`, `X_j ⟶ E j` of finite presentation.
* `AlgebraicGeometry.Scheme.SpreadsOut c q`: `q` has a model over some `E j`.

## References

* [EGA IV₃, 8.8.2][EGA4]
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
-/

universe u

open CategoryTheory Limits Topology

namespace AlgebraicGeometry

/-! ### Open covers by two open immersions -/

section TwoPieces

variable {P A₁ A₂ : Scheme.{u}} (j₁ : A₁ ⟶ P) (j₂ : A₂ ⟶ P) [IsOpenImmersion j₁]
  [IsOpenImmersion j₂]

/-- The open cover of `P` by two open immersions `j₁ : A₁ ⟶ P`, `j₂ : A₂ ⟶ P` whose ranges cover
`P`. -/
noncomputable def Scheme.openCoverOfTwo (h : ∀ z : P, z ∈ Set.range j₁ ∨ z ∈ Set.range j₂) :
    P.OpenCover :=
  Scheme.Cover.mkOfCovers Bool (fun b ↦ cond b A₁ A₂)
    (fun b ↦ Bool.casesOn (motive := fun b ↦ cond b A₁ A₂ ⟶ P) b j₂ j₁)
    (fun z ↦ by
      rcases h z with ⟨a, rfl⟩ | ⟨a, rfl⟩
      · exact ⟨true, a, rfl⟩
      · exact ⟨false, a, rfl⟩)
    (fun b ↦ by cases b <;> infer_instance)

set_option backward.isDefEq.respectTransparency false in
/-- A commutative square `X ⟶ P`, `X ⟶ B`, `P ⟶ S`, `B ⟶ S` is cartesian if `P` is covered by two
open immersions `j₁`, `j₂` over which it is cartesian: `X₁ = e⁻¹(A₁)` and `X₁ ⟶ A₁` is the base
change of `B ⟶ S` along `A₁ ⟶ S`, and the same for `A₂`. -/
theorem Scheme.isPullback_of_two_openImmersions {X B S X₁ X₂ : Scheme.{u}} {e : X ⟶ P}
    {q : X ⟶ B} {p : P ⟶ S} {g : B ⟶ S}
    (h : ∀ z : P, z ∈ Set.range j₁ ∨ z ∈ Set.range j₂) {i₁ : X₁ ⟶ X} {i₂ : X₂ ⟶ X}
    {e₁ : X₁ ⟶ A₁} {e₂ : X₂ ⟶ A₂} (h₁ : IsPullback e₁ i₁ j₁ e) (h₂ : IsPullback e₂ i₂ j₂ e)
    (s₁ : IsPullback e₁ (i₁ ≫ q) (j₁ ≫ p) g) (s₂ : IsPullback e₂ (i₂ ≫ q) (j₂ ≫ p) g) :
    IsPullback e q p g := by
  refine Scheme.isPullback_of_openCover e q p g (Scheme.openCoverOfTwo j₁ j₂ h) fun b ↦ ?_
  cases b
  · refine s₂.of_iso h₂.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id]
      exact (IsPullback.isoPullback_hom_snd h₂.flip).symm
    · simp only [Iso.refl_hom, Category.comp_id]
      change _ = _ ≫ pullback.fst e j₂ ≫ q
      rw [IsPullback.isoPullback_hom_fst_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp
  · refine s₁.of_iso h₁.flip.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id]
      exact (IsPullback.isoPullback_hom_snd h₁.flip).symm
    · simp only [Iso.refl_hom, Category.comp_id]
      change _ = _ ≫ pullback.fst e j₁ ≫ q
      rw [IsPullback.isoPullback_hom_fst_assoc]
    · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      rfl
    · simp

end TwoPieces

/-! ### Pushouts of open immersions -/

section Pushout

variable {M A B : Scheme.{u}} (f : M ⟶ A) (g : M ⟶ B) [IsOpenImmersion f] [IsOpenImmersion g]

/-- Every point of the pushout of two open immersions comes from one of the two pieces. -/
lemma Scheme.pushout_inl_or_inr (z : ↥(pushout f g)) :
    z ∈ Set.range (pushout.inl f g) ∨ z ∈ Set.range (pushout.inr f g) := by
  obtain ⟨t, x, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective (span f g) z
  rcases t with _ | _ | _
  · left
    refine ⟨f x, ?_⟩
    rw [← Scheme.Hom.comp_apply]
    exact congrArg (fun φ ↦ φ x) (colimit.w (span f g) WalkingSpan.Hom.fst)
  · exact .inl ⟨x, rfl⟩
  · exact .inr ⟨x, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Two points of the pieces of a pushout of open immersions with the same image come from the
same point of `M`. -/
lemma Scheme.exists_eq_of_pushout_inl_eq_inr {a : A} {b : B}
    (h : pushout.inl f g a = pushout.inr f g b) : ∃ m : M, f m = a ∧ g m = b := by
  obtain ⟨k, fi, fj, m, hi, hj⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff (F := span f g)
    (i := WalkingSpan.left) (j := WalkingSpan.right)).mp h
  rcases k with _ | _ | _
  · cases fi
    cases fj
    exact ⟨m, hi, hj⟩
  · cases fj
  · cases fi

end Pushout

/-! ### Quasi-separatedness of a union of two opens -/

section QuasiSeparated

/-- In a space covered by two quasi-separated open subsets `U`, `V` with `U ∩ V` compact, the
intersection of compact open subsets `A ⊆ U`, `B ⊆ V` is compact. -/
private lemma isCompact_inter_of_isQuasiSeparated {T : Type*} [TopologicalSpace T] {U V A B : Set T}
    (hU : IsQuasiSeparated U) (hV : IsQuasiSeparated V) (hUo : IsOpen U) (hVo : IsOpen V)
    (hUV : IsCompact (U ∩ V)) (hA : IsCompact A) (hAo : IsOpen A) (hAU : A ⊆ U)
    (hB : IsCompact B) (hBo : IsOpen B) (hBV : B ⊆ V) : IsCompact (A ∩ B) := by
  have h1 : IsCompact (A ∩ (U ∩ V)) :=
    hU A (U ∩ V) hAU hAo hA Set.inter_subset_left (hUo.inter hVo) hUV
  have h2 : IsCompact (A ∩ (U ∩ V) ∩ B) :=
    hV _ B (fun x hx ↦ hx.2.2) (hAo.inter (hUo.inter hVo)) h1 hBV hBo hB
  convert h2 using 1
  ext x
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨⟨ha, hAU ha, hBV hb⟩, hb⟩
  · rintro ⟨⟨ha, -⟩, hb⟩
    exact ⟨ha, hb⟩

/-- A scheme covered by the ranges of two open immersions from quasi-separated schemes, whose
intersection is quasi-compact, is quasi-separated. -/
lemma Scheme.quasiSeparatedSpace_of_two_openImmersions {P A₁ A₂ : Scheme.{u}} (j₁ : A₁ ⟶ P)
    (j₂ : A₂ ⟶ P) [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiSeparatedSpace A₁]
    [QuasiSeparatedSpace A₂] (h : ∀ z : P, z ∈ Set.range j₁ ∨ z ∈ Set.range j₂)
    (hc : IsCompact (Set.range j₁ ∩ Set.range j₂)) : QuasiSeparatedSpace P := by
  have hq₁ : IsQuasiSeparated (Set.range j₁) := by
    rw [← Set.image_univ]
    exact isQuasiSeparated_univ.image_of_isEmbedding j₁.isOpenEmbedding.isEmbedding
  have hq₂ : IsQuasiSeparated (Set.range j₂) := by
    rw [← Set.image_univ]
    exact isQuasiSeparated_univ.image_of_isEmbedding j₂.isOpenEmbedding.isEmbedding
  have ho₁ : IsOpen (Set.range j₁) := j₁.isOpenEmbedding.isOpen_range
  have ho₂ : IsOpen (Set.range j₂) := j₂.isOpenEmbedding.isOpen_range
  let B : Type u := {s : Set P // IsOpen s ∧ IsCompact s ∧ (s ⊆ Set.range j₁ ∨ s ⊆ Set.range j₂)}
  refine QuasiSeparatedSpace.of_isTopologicalBasis (b := fun s : B ↦ s.1) ?_ ?_
  · refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
    · rintro _ ⟨s, rfl⟩
      exact s.2.1
    · intro a O haO hO
      have key (r : Set P) (hr : IsOpen r) (har : a ∈ r) :
          ∃ W : P.Opens, IsAffineOpen W ∧ a ∈ W ∧ (W : Set P) ⊆ O ∩ r := by
        obtain ⟨_, ⟨W, hW, rfl⟩, haW, hWO⟩ := P.isBasis_affineOpens.exists_subset_of_mem_open
          (Set.mem_inter haO har) (hO.inter hr)
        exact ⟨W, hW, haW, hWO⟩
      rcases h a with ha | ha
      · obtain ⟨W, hW, haW, hWO⟩ := key _ ho₁ ha
        exact ⟨W, ⟨⟨W, W.2, hW.isCompact, .inl fun x hx ↦ (hWO hx).2⟩, rfl⟩, haW,
          fun x hx ↦ (hWO hx).1⟩
      · obtain ⟨W, hW, haW, hWO⟩ := key _ ho₂ ha
        exact ⟨W, ⟨⟨W, W.2, hW.isCompact, .inr fun x hx ↦ (hWO hx).2⟩, rfl⟩, haW,
          fun x hx ↦ (hWO hx).1⟩
  · rintro ⟨s, hso, hsc, hs⟩ ⟨t, hto, htc, ht⟩
    dsimp only
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact hq₁ s t hs hso hsc ht hto htc
    · exact isCompact_inter_of_isQuasiSeparated hq₁ hq₂ ho₁ ho₂ hc hsc hso hs htc hto ht
    · rw [Set.inter_comm]
      exact isCompact_inter_of_isQuasiSeparated hq₁ hq₂ ho₁ ho₂ hc htc hto ht hsc hso hs
    · exact hq₂ s t hs hso hsc ht hto htc

end QuasiSeparated

/-! ### Models over a member of the diagram -/

section Model

variable {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}}

/-- A model of `q : X ⟶ c.pt` over the member `E j` of the diagram: a scheme `X_j` of finite
presentation over `E j` (locally of finite presentation, quasi-compact and quasi-separated) with a
cartesian square `X ⟶ X_j`, `X ⟶ c.pt`, `X_j ⟶ E j`, `c.pt ⟶ E j`. -/
structure Scheme.LimitModel (c : Cone E) {X : Scheme.{u}} (q : X ⟶ c.pt) (j : I) where
  /-- The model `X_j`. -/
  obj : Scheme.{u}
  /-- The structure morphism `X_j ⟶ E j`. -/
  hom : obj ⟶ E.obj j
  /-- The projection `X ⟶ X_j`. -/
  proj : X ⟶ obj
  isPullback : IsPullback proj q hom (c.π.app j)
  locallyOfFinitePresentation : LocallyOfFinitePresentation hom := by infer_instance
  quasiCompact : QuasiCompact hom := by infer_instance
  quasiSeparated : QuasiSeparated hom := by infer_instance

attribute [instance] Scheme.LimitModel.locallyOfFinitePresentation
  Scheme.LimitModel.quasiCompact Scheme.LimitModel.quasiSeparated

variable (c : Cone E) in
/-- `q : X ⟶ c.pt` spreads out: it is the base change of a morphism of finite presentation
`X_j ⟶ E j` for some `j`. -/
def Scheme.SpreadsOut {X : Scheme.{u}} (q : X ⟶ c.pt) : Prop :=
  ∃ j, Nonempty (Scheme.LimitModel c q j)

variable {c : Cone E} {X : Scheme.{u}} {q : X ⟶ c.pt}

namespace Scheme.LimitModel

/-- The base change `X_j ×_{E j} E k` of a model to a lower level `k ⟶ j`. -/
@[simps]
noncomputable def lower {j : I} (M : Scheme.LimitModel c q j) {k : I} (g : k ⟶ j) :
    Scheme.LimitModel c q k where
  obj := pullback M.hom (E.map g)
  hom := pullback.snd _ _
  proj := (Scheme.baseChangeCone M.isPullback).π.app (Over.mk g)
  isPullback := Scheme.isPullback_baseChangeCone M.isPullback (Over.mk g)

@[reassoc (attr := simp)]
lemma lower_proj_fst {j : I} (M : Scheme.LimitModel c q j) {k : I} (g : k ⟶ j) :
    (M.lower g).proj ≫ pullback.fst M.hom (E.map g) = M.proj := by
  simp only [lower, Scheme.baseChangeCone_π_app]
  exact pullback.lift_fst _ _ _

/-- The transition morphism `X_j ×_{E j} E k ⟶ X_j` of a lowered model. -/
noncomputable def lowerFst {j : I} (M : Scheme.LimitModel c q j) {k : I} (g : k ⟶ j) :
    (M.lower g).obj ⟶ M.obj :=
  pullback.fst M.hom (E.map g)

@[reassoc (attr := simp)]
lemma lower_proj_lowerFst {j : I} (M : Scheme.LimitModel c q j) {k : I} (g : k ⟶ j) :
    (M.lower g).proj ≫ M.lowerFst g = M.proj :=
  M.lower_proj_fst g

/-- Transport of a model along an isomorphism `X' ≅ X`. -/
@[simps]
noncomputable def ofIso {j : I} (M : Scheme.LimitModel c q j) {X' : Scheme.{u}} (φ : X' ≅ X) :
    Scheme.LimitModel c (φ.hom ≫ q) j where
  obj := M.obj
  hom := M.hom
  proj := φ.hom ≫ M.proj
  isPullback := M.isPullback.of_iso φ.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simp) (by simp) (by simp)

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]

/-- A quasi-compact open of `X` is the preimage of a quasi-compact open of the model at a lower
level (Stacks 01Z4 for the diagram `k ↦ X_j ×_{E j} E k`). -/
theorem exists_preimage_eq (hc : IsLimit c) {j : I} (M : Scheme.LimitModel c q j) (O : X.Opens)
    (hO : IsCompact (O : Set X)) :
    ∃ (k : I) (g : k ⟶ j) (V : (M.lower g).obj.Opens), IsCompact (V : Set (M.lower g).obj) ∧
      (M.lower g).proj ⁻¹ᵁ V = O := by
  obtain ⟨k, V, hV, hVO⟩ := AlgebraicGeometry.exists_preimage_eq (Scheme.baseChangeDiagram E M.hom)
    (Scheme.baseChangeCone M.isPullback) (Scheme.isLimitBaseChangeCone hc M.isPullback) O hO
  exact ⟨k.left, k.hom, V, hV, hVO⟩

end Scheme.LimitModel

lemma Scheme.SpreadsOut.of_iso (h : Scheme.SpreadsOut c q) {X' : Scheme.{u}} (φ : X' ≅ X) :
    Scheme.SpreadsOut c (φ.hom ≫ q) :=
  have ⟨j, ⟨M⟩⟩ := h
  ⟨j, ⟨M.ofIso φ⟩⟩

end Model

/-! ### The gluing step -/

section Gluing

variable {I : Type u} [Category.{u} I] {E : I ⥤ Scheme.{u}} {c : Cone E}

set_option backward.isDefEq.respectTransparency false in
/-- The gluing of two models: let `X = U ∪ W`, and `L_U`, `L_W` models of `U` and `W` over `E n`
with open immersions `M ⟶ L_U`, `M ⟶ L_W` (`M` quasi-compact) agreeing over `E n`, such that
`U ∩ W ⟶ L_U` and `U ∩ W ⟶ L_W` factor through `M` and the points of `U` (resp. `W`) mapping into
`M` lie in `W` (resp. `U`). Then the pushout `L_U ⊔_M L_W` is a model of `X` over `E n`. -/
theorem Scheme.spreadsOut_of_glue [∀ i, CompactSpace (E.obj i)]
    [∀ i, QuasiSeparatedSpace (E.obj i)] {X : Scheme.{u}} (q : X ⟶ c.pt) {U W : X.Opens}
    (hUW : U ⊔ W = ⊤) {n : I} (LU : Scheme.LimitModel c (U.ι ≫ q) n)
    (LW : Scheme.LimitModel c (W.ι ≫ q) n) {M : Scheme.{u}} [CompactSpace M] (iU : M ⟶ LU.obj)
    (iW : M ⟶ LW.obj) [IsOpenImmersion iU] [IsOpenImmersion iW]
    (hs : iU ≫ LU.hom = iW ≫ LW.hom)
    (hrU : ∀ u, LU.proj u ∈ Set.range iU → U.ι u ∈ W)
    (hrW : ∀ w, LW.proj w ∈ Set.range iW → W.ι w ∈ U)
    (b : (U ⊓ W).toScheme ⟶ M) (hbU : X.homOfLE inf_le_left ≫ LU.proj = b ≫ iU)
    (hbW : X.homOfLE inf_le_right ≫ LW.proj = b ≫ iW) : Scheme.SpreadsOut c q := by
  let jU : LU.obj ⟶ pushout iU iW := pushout.inl _ _
  let jW : LW.obj ⟶ pushout iU iW := pushout.inr _ _
  have hpc : iU ≫ jU = iW ≫ jW := pushout.condition
  let p : pushout iU iW ⟶ E.obj n := pushout.desc LU.hom LW.hom hs
  have hjU : jU ≫ p = LU.hom := pushout.inl_desc _ _ _
  have hjW : jW ≫ p = LW.hom := pushout.inr_desc _ _ _
  -- the morphism `X ⟶ P`
  have hcompat : X.homOfLE inf_le_left ≫ LU.proj ≫ jU =
      X.homOfLE inf_le_right ≫ LW.proj ≫ jW := by
    rw [reassoc_of% hbU, reassoc_of% hbW, hpc]
  let 𝒰 := X.openCoverOfIsOpenCover _ (Scheme.isOpenCover_cond hUW)
  let φ : ∀ b : Bool, 𝒰.X b ⟶ pushout iU iW := fun b ↦
    Bool.casesOn (motive := fun b ↦ 𝒰.X b ⟶ pushout iU iW) b (LW.proj ≫ jW) (LU.proj ≫ jU)
  have hcompat' : X.homOfLE (inf_le_left : W ⊓ U ≤ W) ≫ LW.proj ≫ jW =
      X.homOfLE inf_le_right ≫ LU.proj ≫ jU := by
    have := congrArg (X.homOfLE (inf_comm W U).le ≫ ·) hcompat
    simpa only [Scheme.homOfLE_homOfLE_assoc] using this.symm
  have hφ : ∀ x y, pullback.fst (𝒰.f x) (𝒰.f y) ≫ φ x = pullback.snd (𝒰.f x) (𝒰.f y) ≫ φ y := by
    intro x y
    cases x <;> cases y
    · exact congrArg (· ≫ φ false) (Scheme.pullback_fst_eq_snd_ι W)
    · have hP := isPullback_opens_inf W U
      rw [← cancel_epi hP.isoPullback.hom]
      change hP.isoPullback.hom ≫ pullback.fst W.ι U.ι ≫ LW.proj ≫ jW =
        hP.isoPullback.hom ≫ pullback.snd W.ι U.ι ≫ LU.proj ≫ jU
      rw [hP.isoPullback_hom_fst_assoc, hP.isoPullback_hom_snd_assoc]
      exact hcompat'
    · have hP := isPullback_opens_inf U W
      rw [← cancel_epi hP.isoPullback.hom]
      change hP.isoPullback.hom ≫ pullback.fst U.ι W.ι ≫ LU.proj ≫ jU =
        hP.isoPullback.hom ≫ pullback.snd U.ι W.ι ≫ LW.proj ≫ jW
      rw [hP.isoPullback_hom_fst_assoc, hP.isoPullback_hom_snd_assoc]
      exact hcompat
    · exact congrArg (· ≫ φ true) (Scheme.pullback_fst_eq_snd_ι U)
  let e := 𝒰.glueMorphisms φ hφ
  have heU : U.ι ≫ e = LU.proj ≫ jU := 𝒰.ι_glueMorphisms φ hφ true
  have heW : W.ι ≫ e = LW.proj ≫ jW := 𝒰.ι_glueMorphisms φ hφ false
  -- the preimages of the two pieces of the pushout are `U` and `W`
  have hpreU : e ⁻¹ᵁ jU.opensRange = U.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    ext x
    constructor
    · intro hx
      change e x ∈ Set.range jU at hx
      obtain ⟨a, ha⟩ := hx
      by_contra hxU
      have hxW : x ∈ W := by
        have : x ∈ U ⊔ W := hUW ▸ trivial
        exact this.resolve_left hxU
      obtain ⟨w, rfl⟩ : ∃ w : W.toScheme, W.ι w = x := ⟨⟨x, hxW⟩, rfl⟩
      have h1 : jW (LW.proj w) = e (W.ι w) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heW]
      obtain ⟨z, -, hz⟩ := Scheme.exists_eq_of_pushout_inl_eq_inr iU iW (ha.trans h1.symm)
      exact hxU (hrW w ⟨z, hz⟩)
    · intro hx
      obtain ⟨u, rfl⟩ : ∃ u : U.toScheme, U.ι u = x := ⟨⟨x, hx⟩, rfl⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
      exact ⟨LU.proj u, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heU]⟩
  have hpreW : e ⁻¹ᵁ jW.opensRange = W.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    ext x
    constructor
    · intro hx
      change e x ∈ Set.range jW at hx
      obtain ⟨b, hb⟩ := hx
      by_contra hxW
      have hxU : x ∈ U := by
        have : x ∈ U ⊔ W := hUW ▸ trivial
        exact this.resolve_right hxW
      obtain ⟨u, rfl⟩ : ∃ u : U.toScheme, U.ι u = x := ⟨⟨x, hxU⟩, rfl⟩
      have h1 : jU (LU.proj u) = e (U.ι u) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heU]
      obtain ⟨z, hz, -⟩ := Scheme.exists_eq_of_pushout_inl_eq_inr iU iW (h1.trans hb.symm)
      exact hxW (hrU u ⟨z, hz⟩)
    · intro hx
      obtain ⟨w, rfl⟩ : ∃ w : W.toScheme, W.ι w = x := ⟨⟨x, hx⟩, rfl⟩
      rw [SetLike.mem_coe, Scheme.Hom.mem_preimage, Scheme.Hom.mem_opensRange]
      exact ⟨LW.proj w, by rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heW]⟩
  have hcov := Scheme.pushout_inl_or_inr iU iW
  have hQU : IsPullback LU.proj U.ι jU e := IsOpenImmersion.isPullback _ _ _ _ heU hpreU
  have hQW : IsPullback LW.proj W.ι jW e := IsOpenImmersion.isPullback _ _ _ _ heW hpreW
  have hSU : IsPullback LU.proj (U.ι ≫ q) (jU ≫ p) (c.π.app n) := by
    rw [hjU]
    exact LU.isPullback
  have hSW : IsPullback LW.proj (W.ι ≫ q) (jW ≫ p) (c.π.app n) := by
    rw [hjW]
    exact LW.isPullback
  have hpb : IsPullback e q p (c.π.app n) :=
    Scheme.isPullback_of_two_openImmersions jU jW hcov hQU hQW hSU hSW
  -- the glued scheme is of finite presentation over `E n`
  have : LocallyOfFinitePresentation p :=
    IsZariskiLocalAtSource.of_openCover (Scheme.openCoverOfTwo jU jW hcov) fun b ↦ by
      cases b
      · change LocallyOfFinitePresentation (jW ≫ p)
        rw [hjW]
        infer_instance
      · change LocallyOfFinitePresentation (jU ≫ p)
        rw [hjU]
        infer_instance
  have : CompactSpace LU.obj := QuasiCompact.compactSpace_of_compactSpace LU.hom
  have : CompactSpace LW.obj := QuasiCompact.compactSpace_of_compactSpace LW.hom
  have : CompactSpace ↥(pushout iU iW : Scheme.{u}) := by
    rw [← isCompact_univ_iff]
    have : (Set.univ : Set ↥(pushout iU iW : Scheme.{u})) = Set.range jU ∪ Set.range jW := by
      ext z
      simpa using hcov z
    rw [this]
    exact (isCompact_range jU.continuous).union (isCompact_range jW.continuous)
  have : QuasiSeparatedSpace LU.obj := quasiSeparatedSpace_of_quasiSeparated LU.hom
  have : QuasiSeparatedSpace LW.obj := quasiSeparatedSpace_of_quasiSeparated LW.hom
  have : QuasiSeparatedSpace ↥(pushout iU iW : Scheme.{u}) := by
    refine Scheme.quasiSeparatedSpace_of_two_openImmersions jU jW hcov ?_
    have : Set.range jU ∩ Set.range jW = Set.range (iU ≫ jU) := by
      ext z
      constructor
      · rintro ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩
        obtain ⟨m, hm, -⟩ := Scheme.exists_eq_of_pushout_inl_eq_inr iU iW hb.symm
        exact ⟨m, by rw [Scheme.Hom.comp_apply, hm]⟩
      · rintro ⟨m, rfl⟩
        refine ⟨⟨iU m, rfl⟩, ⟨iW m, ?_⟩⟩
        rw [← Scheme.Hom.comp_apply, ← hpc]
    rw [this]
    exact isCompact_range (iU ≫ jU).continuous
  exact ⟨n, ⟨{ obj := pushout iU iW, hom := p, proj := e, isPullback := hpb }⟩⟩

variable [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)]
  [∀ i, CompactSpace (E.obj i)] [∀ i, QuasiSeparatedSpace (E.obj i)]

set_option backward.isDefEq.respectTransparency false in
/-- The gluing step of EGA IV 8.8.2 (ii) (Stacks 01ZM): if `X = U ∪ W` with `U ∩ W`
quasi-compact, and `U ⟶ c.pt`, `W ⟶ c.pt` spread out to finite levels, then so does
`X ⟶ c.pt`. -/
theorem Scheme.spreadsOut_of_sup_eq_top (hc : IsLimit c) {X : Scheme.{u}} (q : X ⟶ c.pt)
    {U W : X.Opens} (hUW : U ⊔ W = ⊤) (hM : IsCompact ((U ⊓ W : X.Opens) : Set X))
    (hU : Scheme.SpreadsOut c (U.ι ≫ q)) (hW : Scheme.SpreadsOut c (W.ι ≫ q)) :
    Scheme.SpreadsOut c q := by
  obtain ⟨jU, ⟨MU⟩⟩ := hU
  obtain ⟨jW, ⟨MW⟩⟩ := hW
  -- the open `U ∩ W`, seen in `U` and in `W`
  have hOU : IsCompact ((U.ι ⁻¹ᵁ W : U.toScheme.Opens) : Set U.toScheme) := by
    rw [U.ι.isOpenEmbedding.isInducing.isCompact_iff]
    convert hM using 1
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxU, hxW⟩
      exact ⟨⟨x, hxU⟩, hxW, rfl⟩
  have hOW : IsCompact ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme) := by
    rw [W.ι.isOpenEmbedding.isInducing.isCompact_iff]
    convert hM using 1
    ext x
    simp only [Set.mem_image]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy, y.2⟩
    · rintro ⟨hxU, hxW⟩
      exact ⟨⟨x, hxW⟩, hxU, rfl⟩
  obtain ⟨kU, gU, VU, hVUc, hVU⟩ := MU.exists_preimage_eq hc (U.ι ⁻¹ᵁ W) hOU
  obtain ⟨kW, gW, VW, hVWc, hVW⟩ := MW.exists_preimage_eq hc (W.ι ⁻¹ᵁ U) hOW
  -- a common level `m`
  let m := IsCofiltered.min kU kW
  let NU := (MU.lower gU).lower (IsCofiltered.minToLeft kU kW)
  let NW := (MW.lower gW).lower (IsCofiltered.minToRight kU kW)
  let VU' : NU.obj.Opens := (MU.lower gU).lowerFst (IsCofiltered.minToLeft kU kW) ⁻¹ᵁ VU
  let VW' : NW.obj.Opens := (MW.lower gW).lowerFst (IsCofiltered.minToRight kU kW) ⁻¹ᵁ VW
  have hVU' : NU.proj ⁻¹ᵁ VU' = U.ι ⁻¹ᵁ W := by
    rw [← hVU, ← Scheme.Hom.comp_preimage, Scheme.LimitModel.lower_proj_lowerFst]
  have hVW' : NW.proj ⁻¹ᵁ VW' = W.ι ⁻¹ᵁ U := by
    rw [← hVW, ← Scheme.Hom.comp_preimage, Scheme.LimitModel.lower_proj_lowerFst]
  have : QuasiCompact ((MU.lower gU).lowerFst (IsCofiltered.minToLeft kU kW)) := by
    delta Scheme.LimitModel.lowerFst; infer_instance
  have : QuasiCompact ((MW.lower gW).lowerFst (IsCofiltered.minToRight kU kW)) := by
    delta Scheme.LimitModel.lowerFst; infer_instance
  have : CompactSpace VU'.toScheme := isCompact_iff_compactSpace.mp
    (((MU.lower gU).lowerFst (IsCofiltered.minToLeft kU kW)).isCompact_preimage hVUc)
  have : CompactSpace VW'.toScheme := isCompact_iff_compactSpace.mp
    (((MW.lower gW).lowerFst (IsCofiltered.minToRight kU kW)).isCompact_preimage hVWc)
  have : QuasiSeparatedSpace NU.obj := quasiSeparatedSpace_of_quasiSeparated NU.hom
  have : QuasiSeparatedSpace NW.obj := quasiSeparatedSpace_of_quasiSeparated NW.hom
  -- the overlap `Y = U ∩ W` and its maps to the opens `VU'`, `VW'`
  let iUW : (U ⊓ W).toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let iWU : (U ⊓ W).toScheme ⟶ W.toScheme := X.homOfLE inf_le_right
  have hrU : Set.range (iUW ≫ NU.proj) ⊆ Set.range VU'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change iUW y ∈ NU.proj ⁻¹ᵁ VU'
    rw [hVU']
    change (iUW ≫ U.ι) y ∈ W
    rw [Scheme.homOfLE_ι]
    exact y.2.2
  have hrW : Set.range (iWU ≫ NW.proj) ⊆ Set.range VW'.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change iWU y ∈ NW.proj ⁻¹ᵁ VW'
    rw [hVW']
    change (iWU ≫ W.ι) y ∈ U
    rw [Scheme.homOfLE_ι]
    exact y.2.1
  let aU : (U ⊓ W).toScheme ⟶ VU'.toScheme := IsOpenImmersion.lift VU'.ι (iUW ≫ NU.proj) hrU
  let aW : (U ⊓ W).toScheme ⟶ VW'.toScheme := IsOpenImmersion.lift VW'.ι (iWU ≫ NW.proj) hrW
  have hAU : IsPullback aU iUW VU'.ι NU.proj := by
    refine IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm ?_
    rw [Scheme.Opens.opensRange_ι, hVU', Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf,
      Scheme.Opens.ι_preimage_self, top_inf_eq]
  have hAW : IsPullback aW iWU VW'.ι NW.proj := by
    refine IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm ?_
    rw [Scheme.Opens.opensRange_ι, hVW', Scheme.opensRange_homOfLE, Scheme.Hom.preimage_inf,
      Scheme.Opens.ι_preimage_self, inf_top_eq]
  have h₁ : IsPullback aU ((U ⊓ W).ι ≫ q) (VU'.ι ≫ NU.hom) (c.π.app m) := by
    have := hAU.paste_vert NU.isPullback
    rwa [Scheme.homOfLE_ι_assoc] at this
  have h₂ : IsPullback aW ((U ⊓ W).ι ≫ q) (VW'.ι ≫ NW.hom) (c.π.app m) := by
    have := hAW.paste_vert NW.isPullback
    rwa [Scheme.homOfLE_ι_assoc] at this
  -- the two models of `U ∩ W` become isomorphic at some level `n`
  obtain ⟨k, θ, hθ, hθ'⟩ := Scheme.exists_iso_of_isPullback hc h₁ h₂
  let n := k.left
  let g : n ⟶ m := k.hom
  let p₁ := VU'.ι ≫ NU.hom
  let p₂ := VW'.ι ≫ NW.hom
  -- the open immersions of the overlap into the models of `U` and `W` at level `n`
  obtain ⟨iU, hiU, hiUs⟩ : ∃ iU : pullback p₁ (E.map g) ⟶ (NU.lower g).obj,
      IsPullback iU (pullback.fst p₁ (E.map g)) (NU.lowerFst g) VU'.ι ∧
        iU ≫ (NU.lower g).hom = pullback.snd p₁ (E.map g) :=
    ⟨_, IsPullback.of_right' (IsPullback.of_hasPullback p₁ (E.map g)).flip
      (IsPullback.of_hasPullback NU.hom (E.map g)).flip, IsPullback.lift_fst _ _ _ _⟩
  obtain ⟨iW, hiW, hiWs⟩ : ∃ iW : pullback p₂ (E.map g) ⟶ (NW.lower g).obj,
      IsPullback iW (pullback.fst p₂ (E.map g)) (NW.lowerFst g) VW'.ι ∧
        iW ≫ (NW.lower g).hom = pullback.snd p₂ (E.map g) :=
    ⟨_, IsPullback.of_right' (IsPullback.of_hasPullback p₂ (E.map g)).flip
      (IsPullback.of_hasPullback NW.hom (E.map g)).flip, IsPullback.lift_fst _ _ _ _⟩
  have : IsOpenImmersion iU := MorphismProperty.of_isPullback hiU.flip inferInstance
  have : IsOpenImmersion iW := MorphismProperty.of_isPullback hiW.flip inferInstance
  have : CompactSpace ↥(pullback p₁ (E.map g) : Scheme.{u}) := inferInstance
  -- the comparison maps from `U ∩ W`
  let bU := (Scheme.baseChangeCone h₁).π.app k
  let bW := (Scheme.baseChangeCone h₂).π.app k
  have hbU : iUW ≫ (NU.lower g).proj = bU ≫ iU := by
    apply pullback.hom_ext
    · change _ ≫ NU.lowerFst g = _ ≫ NU.lowerFst g
      rw [Category.assoc, Scheme.LimitModel.lower_proj_lowerFst, Category.assoc, hiU.w]
      simp only [bU, Scheme.baseChangeCone_π_app]
      erw [pullback.lift_fst_assoc]
      exact (IsOpenImmersion.lift_fac VU'.ι (iUW ≫ NU.proj) hrU).symm
    · change _ ≫ (NU.lower g).hom = _ ≫ (NU.lower g).hom
      rw [Category.assoc, Category.assoc, hiUs, (NU.lower g).isPullback.w]
      simp only [bU, Scheme.baseChangeCone_π_app, iUW, Category.assoc, Scheme.homOfLE_ι_assoc]
      exact (pullback.lift_snd _ _ _).symm
  have hbW : iWU ≫ (NW.lower g).proj = bW ≫ iW := by
    apply pullback.hom_ext
    · change _ ≫ NW.lowerFst g = _ ≫ NW.lowerFst g
      rw [Category.assoc, Scheme.LimitModel.lower_proj_lowerFst, Category.assoc, hiW.w]
      simp only [bW, Scheme.baseChangeCone_π_app]
      erw [pullback.lift_fst_assoc]
      exact (IsOpenImmersion.lift_fac VW'.ι (iWU ≫ NW.proj) hrW).symm
    · change _ ≫ (NW.lower g).hom = _ ≫ (NW.lower g).hom
      rw [Category.assoc, Category.assoc, hiWs, (NW.lower g).isPullback.w]
      simp only [bW, Scheme.baseChangeCone_π_app, iWU, Category.assoc, Scheme.homOfLE_ι_assoc]
      exact (pullback.lift_snd _ _ _).symm
  refine Scheme.spreadsOut_of_glue q hUW (NU.lower g) (NW.lower g) iU (θ.hom ≫ iW) ?_ ?_ ?_ bU
    hbU ?_
  · rw [hiUs, Category.assoc, hiWs, hθ]
  · rintro u ⟨z, hz⟩
    have hmem : NU.proj u ∈ VU' := by
      rw [← Scheme.LimitModel.lower_proj_lowerFst NU g, Scheme.Hom.comp_apply, ← hz,
        ← Scheme.Hom.comp_apply, hiU.w, Scheme.Hom.comp_apply]
      exact (pullback.fst p₁ (E.map g) z).2
    have : u ∈ NU.proj ⁻¹ᵁ VU' := hmem
    rw [hVU'] at this
    exact this
  · rintro w ⟨z, hz⟩
    have hmem : NW.proj w ∈ VW' := by
      rw [← Scheme.LimitModel.lower_proj_lowerFst NW g, Scheme.Hom.comp_apply, ← hz,
        ← Scheme.Hom.comp_apply, Category.assoc, hiW.w, ← Category.assoc, Scheme.Hom.comp_apply]
      exact ((θ.hom ≫ pullback.fst p₂ (E.map g)) z).2
    have : w ∈ NW.proj ⁻¹ᵁ VW' := hmem
    rw [hVW'] at this
    exact this
  · rw [hbW]
    exact ((Category.assoc _ _ _).trans (congrArg (· ≫ iW) hθ')).symm

end Gluing

/-! ### EGA IV 8.8.2 (ii) -/

section Main

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {E : I ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsAffineHom (E.map f)] [∀ i, CompactSpace (E.obj i)]
  [∀ i, QuasiSeparatedSpace (E.obj i)] {c : Cone E}

omit [∀ i, CompactSpace (E.obj i)] in
set_option backward.isDefEq.respectTransparency false in
/-- EGA IV 8.8.2 (ii), affine pieces: an affine scheme `Y` locally of finite presentation over
`c.pt` whose image lies in the preimage of an affine open `V` of some `E i` spreads out. -/
theorem Scheme.spreadsOut_of_isAffine (hc : IsLimit c) {Y : Scheme.{u}} [IsAffine Y]
    (q : Y ⟶ c.pt) [LocallyOfFinitePresentation q] {i : I} (V : (E.obj i).Opens)
    (hV : IsAffineOpen V) (hqV : ∀ y, c.π.app i (q y) ∈ V) : Scheme.SpreadsOut c q := by
  have : ∀ j, IsAffine ((opensDiagram E i V).obj j) := fun j ↦ hV.preimage (E.map j.hom)
  have hr : Set.range q ⊆ Set.range (c.π.app i ⁻¹ᵁ V).ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hqV y
  let q' : Y ⟶ (c.π.app i ⁻¹ᵁ V).toScheme := IsOpenImmersion.lift (c.π.app i ⁻¹ᵁ V).ι q hr
  have hq' : q' ≫ (c.π.app i ⁻¹ᵁ V).ι = q := IsOpenImmersion.lift_fac _ _ _
  have : LocallyOfFinitePresentation q' := by
    refine IsZariskiLocalAtTarget.of_isPullback (iY := (c.π.app i ⁻¹ᵁ V).ι) (iX := 𝟙 Y)
      (f := q) ?_ inferInstance
    refine (IsOpenImmersion.isPullback q' (𝟙 Y) _ q (by rw [Category.id_comp, hq']) ?_).flip
    ext y
    simp only [Scheme.Opens.opensRange_ι, Scheme.Hom.mem_preimage, SetLike.mem_coe]
    exact ⟨fun _ ↦ ⟨y, rfl⟩, fun _ ↦ hqV y⟩
  obtain ⟨j, Yj, qj, e, hYj, hqj, h⟩ :=
    Scheme.exists_isPullback_of_isLimit_of_isAffine_of_locallyOfFinitePresentation
      (c := opensCone E c i V) (isLimitOpensCone E c hc i V) q'
  have sq : IsPullback ((opensCone E c i V).π.app j) (c.π.app i ⁻¹ᵁ V).ι
      (E.map j.hom ⁻¹ᵁ V).ι (c.π.app j.left) :=
    IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp [← Scheme.Hom.comp_preimage])
  have h' := h.paste_vert sq
  rw [hq'] at h'
  exact ⟨j.left, ⟨{ obj := Yj, hom := qj ≫ (E.map j.hom ⁻¹ᵁ V).ι, proj := e, isPullback := h' }⟩⟩

private lemma iSup_fin_succ_eq_sup' {α : Type*} [CompleteLattice α] {n : ℕ}
    (f : Fin (n + 1) → α) : ⨆ k, f k = f 0 ⊔ ⨆ k : Fin n, f k.succ :=
  le_antisymm (iSup_le fun k ↦ Fin.cases le_sup_left
      (fun k ↦ le_sup_of_le_right (le_iSup (fun k : Fin n ↦ f k.succ) k)) k)
    (sup_le (le_iSup f 0) (iSup_le fun k ↦ le_iSup f k.succ))

/-- (Implementation) The gluing of EGA IV 8.8.2 (ii), by induction on the number of pieces of a
cover of `X` by quasi-compact opens which spread out. -/
theorem Scheme.spreadsOut_of_iSup_eq_top (hc : IsLimit c) (n : ℕ) :
    ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X] (q : X ⟶ c.pt) (U : Fin (n + 1) → X.Opens),
      (∀ k, IsCompact (U k : Set X)) → (∀ k, Scheme.SpreadsOut c ((U k).ι ≫ q)) →
        ⨆ k, U k = ⊤ → Scheme.SpreadsOut c q := by
  induction n with
  | zero =>
    intro X _ q U _ hU hcov
    have h0 : U 0 = ⊤ := by
      rw [← hcov]
      exact le_antisymm (le_iSup U 0) (iSup_le fun k ↦ by rw [Fin.fin_one_eq_zero k])
    have h := (hU 0).of_iso (X.topIso.symm ≪≫ X.isoOfEq h0.symm)
    have e : (X.topIso.symm ≪≫ X.isoOfEq h0.symm).hom ≫ (U 0).ι = 𝟙 X := by
      simp [Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι]
    rwa [← Category.assoc, e, Category.id_comp] at h
  | succ n ih =>
    intro X _ q U hUc hU hcov
    let W : X.Opens := ⨆ k : Fin (n + 1), U k.succ
    have hVW : U 0 ⊔ W = ⊤ := by rw [← hcov, iSup_fin_succ_eq_sup']
    have hWc : IsCompact (W : Set X) := by
      simp only [W, TopologicalSpace.Opens.coe_iSup]
      exact isCompact_iUnion fun k ↦ hUc k.succ
    have hM : IsCompact ((U 0 ⊓ W : X.Opens) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (U 0).2 (hUc 0) W.2 hWc
    have : QuasiSeparatedSpace W.toScheme :=
      QuasiSeparatedSpace.of_isOpenEmbedding W.ι.isOpenEmbedding
    have hle (k : Fin (n + 1)) : U k.succ ≤ W := le_iSup (fun k : Fin (n + 1) ↦ U k.succ) k
    refine Scheme.spreadsOut_of_sup_eq_top hc q hVW hM (hU 0) ?_
    refine ih (W.ι ≫ q) (fun k ↦ W.ι ⁻¹ᵁ U k.succ) (fun k ↦ ?_) (fun k ↦ ?_) ?_
    · rw [W.ι.isOpenEmbedding.isInducing.isCompact_iff]
      convert hUc k.succ using 1
      ext x
      simp only [Set.mem_image]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hle k hx⟩, hx, rfl⟩
    · have hr : Set.range ((W.ι ⁻¹ᵁ U k.succ).ι ≫ W.ι) = Set.range (U k.succ).ι := by
        rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
          Scheme.Opens.range_ι]
        ext x
        simp only [Set.mem_image]
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hle k hx⟩, hx, rfl⟩
      have h := (hU k.succ).of_iso (IsOpenImmersion.isoOfRangeEq _ _ hr)
      rwa [← Category.assoc, IsOpenImmersion.isoOfRangeEq_hom_fac, Category.assoc] at h
    · rw [← Scheme.Hom.preimage_iSup]
      exact Scheme.Opens.ι_preimage_self W

set_option backward.isDefEq.respectTransparency false in
/-- **EGA IV 8.8.2 (ii)** (Stacks 01ZM): let `c.pt = lim E i` be the limit of a cofiltered
diagram of quasi-compact and quasi-separated schemes with affine transition maps. Every
`c.pt`-scheme `X` of finite presentation (`q : X ⟶ c.pt` locally of finite presentation,
quasi-compact and quasi-separated) is the base change `X = X_j ×_{E j} c.pt` of an `E j`-scheme
`X_j` of finite presentation, for some `j`. -/
@[stacks 01ZM]
theorem Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation (hc : IsLimit c)
    {X : Scheme.{u}} (q : X ⟶ c.pt) [LocallyOfFinitePresentation q] [QuasiCompact q]
    [QuasiSeparated q] :
    ∃ (j : I) (Xj : Scheme.{u}) (qj : Xj ⟶ E.obj j) (e : X ⟶ Xj),
      LocallyOfFinitePresentation qj ∧ QuasiCompact qj ∧ QuasiSeparated qj ∧
        IsPullback e q qj (c.π.app j) := by
  suffices h : Scheme.SpreadsOut c q by
    obtain ⟨j, ⟨M⟩⟩ := h
    exact ⟨j, M.obj, M.hom, M.proj, inferInstance, inferInstance, inferInstance, M.isPullback⟩
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have := Scheme.compactSpace_of_isLimit E c hc
  have := isAffineHom_π_app E c hc i
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace q
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated q
  -- every point has an affine neighbourhood lying over an affine open of `E i`
  have key (x : X) : ∃ (U : X.Opens) (V : (E.obj i).Opens), IsAffineOpen U ∧ IsAffineOpen V ∧
      x ∈ U ∧ ∀ y, c.π.app i ((U.ι ≫ q) y) ∈ V := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ := (E.obj i).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (c.π.app i (q x))) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (a := x) (u := (q ≫ c.π.app i) ⁻¹ᵁ V) hxV ((q ≫ c.π.app i) ⁻¹ᵁ V).2
    exact ⟨U, V, hU, hV, hxU, fun y ↦ hUV y.2⟩
  choose U V hU hV hxU hUV using key
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ (U x : Set X))
    (fun x ↦ (U x).2) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hxU x⟩)
  let φ := s.equivFin
  let P : Fin (s.card + 1) → X.Opens := Fin.cons ⊥ fun k ↦ U (φ.symm k)
  refine Scheme.spreadsOut_of_iSup_eq_top hc _ q P (fun k ↦ ?_) (fun k ↦ ?_) ?_
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · simp [P]
    · exact (hU (φ.symm k)).isCompact
  · refine Fin.cases ?_ (fun k ↦ ?_) k
    · have : IsEmpty (P 0).toScheme := ⟨fun x ↦ by
        obtain ⟨y, hy⟩ := x
        change y ∈ (⊥ : X.Opens) at hy
        simp at hy⟩
      have : IsAffine (P 0).toScheme := isAffine_of_isEmpty
      exact Scheme.spreadsOut_of_isAffine hc _ (i := i) ⊥ (isAffineOpen_bot _) fun x ↦ isEmptyElim x
    · have : IsAffine (P k.succ).toScheme := hU (φ.symm k)
      exact Scheme.spreadsOut_of_isAffine hc _ (V (φ.symm k)) (hV (φ.symm k)) (hUV (φ.symm k))
  · refine top_le_iff.mp fun x _ ↦ ?_
    have hx := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [TopologicalSpace.Opens.mem_iSup]
    exact ⟨(φ ⟨y, hy⟩).succ, by simpa [P] using hxy⟩

/-- **EGA IV 8.8.2 (ii)** holds: `Scheme.SpreadingOutStatement`. -/
theorem Scheme.spreadingOutStatement : Scheme.SpreadingOutStatement.{u} :=
  fun _ _ _ _ _ _ _ _ hc _ q _ _ _ ↦
    Scheme.exists_isPullback_of_isLimit_of_locallyOfFinitePresentation hc q

end Main

end AlgebraicGeometry
