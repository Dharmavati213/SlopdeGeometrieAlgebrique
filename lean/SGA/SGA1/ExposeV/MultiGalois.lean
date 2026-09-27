/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroupFunctoriality
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# SGA 1, Exposé V, §9: non-connected schemes and multi-Galois categories

V.9: if `(S_i)` are the connected components of `S`, the category of étale coverings of `S` is
equivalent to the product of the categories of étale coverings of the `S_i`, each of which is a
Galois category (V.7). SGA calls a category equivalent to a product of Galois categories a
*multi-Galois category* (`IsMultiGalois`) and leaves the details to the reader.

* `FEt.restrictFamily U`: restriction of étale coverings to the members of a family of opens
  `U i`; for a finite family of pairwise disjoint opens covering `S` it is an equivalence
  `FEt S ≌ ∀ i, FEt (U i)` (`FEt.equivPiOfDisjoint`): faithful and full by gluing morphisms
  along the open cover `X ×_S U i` of a covering `X`, and essentially surjective since
  `∐ Z_i → S` is an étale covering whose restriction to `U j` is `Z_j`.
* `FEt.isMultiGalois`: if `S` has finitely many connected components (e.g. `S` noetherian),
  `FEt S` is a multi-Galois category, the product of the Galois categories `FEt S_i`.

SGA states V.9 for locally noetherian `S`, whose connected components are open; the case of
infinitely many components and the description by functors on the groupoid of geometric
points (the generalization of V.5.8) are not formalized.
-/

universe u₁ u₂ u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeV

/-- V.9: a *multi-Galois category* is a category equivalent to a product of Galois categories
(of categories `𝒞(π_i)`, V.5.1), one for each "connected component". -/
def IsMultiGalois (C : Type u₁) [Category.{u₂} C] : Prop :=
  ∃ (ι : Type u₂) (D : ι → Type u₁) (_ : ∀ i, Category.{u₂} (D i))
    (_ : ∀ i, GaloisCategory (D i)), Nonempty (C ≌ ∀ i, D i)

section Decomposition

variable {S : Scheme.{u}} {ι : Type u} (U : ι → S.Opens)

/-- V.9: restriction of étale coverings of `S` to the members of a family of open subschemes. -/
noncomputable def FEt.restrictFamily : FEt S ⥤ ∀ i, FEt (U i) :=
  Functor.pi' fun i ↦ FEt.pullback (U i).ι

variable {U}

lemma FEt.mem_of_pullback (X : FEt S) (i : ι) (w : ↥(Limits.pullback X.hom (U i).ι)) :
    X.hom (pullback.fst X.hom (U i).ι w) ∈ U i := by
  rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  exact (pullback.snd X.hom (U i).ι w).2

/-- The open cover of (the source of) an étale covering `X` of `S` by its restrictions
`X ×_S U i`, for a family of opens covering `S`. -/
noncomputable def FEt.openCoverOfISupEqTop (hU : iSup U = ⊤) (X : FEt S) : X.left.OpenCover where
  I₀ := ι
  X i := Limits.pullback X.hom (U i).ι
  f i := pullback.fst X.hom (U i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    have hx : X.hom x ∈ iSup U := hU ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    rw [IsOpenImmersion.range_pullbackFst]
    simpa using hi

lemma FEt.pullback_map_left_fst {X Y : FEt S} (φ : X ⟶ Y) (i : ι) :
    ((FEt.pullback (U i).ι).map φ).left ≫ pullback.fst Y.hom (U i).ι =
      pullback.fst X.hom (U i).ι ≫ φ.left := by
  simp only [FEt.pullback, MorphismProperty.Over.pullback_map_left]
  exact pullback.lift_fst _ _ _

lemma FEt.pullback_map_left_snd {X Y : FEt S} (φ : X ⟶ Y) (i : ι) :
    ((FEt.pullback (U i).ι).map φ).left ≫ pullback.snd Y.hom (U i).ι =
      pullback.snd X.hom (U i).ι := by
  simp only [FEt.pullback, MorphismProperty.Over.pullback_map_left]
  exact pullback.lift_snd _ _ _

/-- V.9: for a family of opens covering `S`, restriction of étale coverings is faithful. -/
lemma FEt.restrictFamily_faithful (hU : iSup U = ⊤) : (FEt.restrictFamily U).Faithful where
  map_injective {X Y} f g h := by
    have hi (i : ι) : ((FEt.pullback (U i).ι).map f).left = ((FEt.pullback (U i).ι).map g).left :=
      congrArg (fun φ : (FEt.restrictFamily U).obj X ⟶ (FEt.restrictFamily U).obj Y ↦ (φ i).left)
        h
    apply MorphismProperty.Over.Hom.ext
    refine (FEt.openCoverOfISupEqTop hU X).hom_ext _ _ fun (i : ι) ↦ ?_
    change pullback.fst X.hom (U i).ι ≫ f.left = pullback.fst X.hom (U i).ι ≫ g.left
    rw [← FEt.pullback_map_left_fst (U := U) f i, ← FEt.pullback_map_left_fst (U := U) g i, hi i]

-- The objects `((FEt.restrictFamily U).obj X i).left` and `pullback X.hom (U i).ι` are only
-- defeq after unfolding `Functor.pi'` and `MorphismProperty.Over.pullback`.
set_option backward.isDefEq.respectTransparency false in
/-- V.9: for a family of pairwise disjoint opens covering `S`, restriction of étale coverings is
full (morphisms glue). -/
lemma FEt.restrictFamily_full (hU : iSup U = ⊤) (hd : Pairwise (Function.onFun Disjoint U)) :
    (FEt.restrictFamily U).Full where
  map_surjective {X Y} φ := by
    let g (i : ι) : Limits.pullback X.hom (U i).ι ⟶ Y.left :=
      (φ i).left ≫ pullback.fst Y.hom (U i).ι
    have hw (i : ι) : (φ i).left ≫ pullback.snd Y.hom (U i).ι = pullback.snd X.hom (U i).ι :=
      MorphismProperty.Over.w (φ i)
    have hg (i j : ι) :
        pullback.fst (pullback.fst X.hom (U i).ι) (pullback.fst X.hom (U j).ι) ≫ g i =
          pullback.snd (pullback.fst X.hom (U i).ι) (pullback.fst X.hom (U j).ι) ≫ g j := by
      by_cases hij : i = j
      · subst hij
        have : pullback.fst (pullback.fst X.hom (U i).ι) (pullback.fst X.hom (U i).ι) =
            pullback.snd (pullback.fst X.hom (U i).ι) (pullback.fst X.hom (U i).ι) := by
          rw [← cancel_mono (pullback.fst X.hom (U i).ι), pullback.condition]
        rw [this]
      · have : IsEmpty ↥(Limits.pullback (pullback.fst X.hom (U i).ι)
            (pullback.fst X.hom (U j).ι)) := ⟨fun z ↦ by
          have h₁ := FEt.mem_of_pullback X i
            (pullback.fst (pullback.fst X.hom (U i).ι) (pullback.fst X.hom (U j).ι) z)
          have h₂ := FEt.mem_of_pullback X j
            (pullback.snd (pullback.fst X.hom (U i).ι) (pullback.fst X.hom (U j).ι) z)
          have e := congrArg (fun h ↦ X.hom (h z))
            (pullback.condition (f := pullback.fst X.hom (U i).ι) (g := pullback.fst X.hom (U j).ι))
          simp only [Scheme.Hom.comp_apply] at e
          rw [e] at h₁
          have h₃ : _ ∈ U i ⊓ U j := ⟨h₁, h₂⟩
          rw [disjoint_iff.mp (hd hij)] at h₃
          simp at h₃⟩
        exact AlgebraicGeometry.isInitialOfIsEmpty.hom_ext _ _
    let F : X.left ⟶ Y.left := Scheme.Cover.glueMorphisms (FEt.openCoverOfISupEqTop hU X) g hg
    have hFi (i : ι) : pullback.fst X.hom (U i).ι ≫ F = g i :=
      Scheme.Cover.ι_glueMorphisms (FEt.openCoverOfISupEqTop hU X) g hg i
    have hF : F ≫ Y.hom = X.hom :=
      Scheme.Cover.hom_ext (FEt.openCoverOfISupEqTop hU X) _ _ fun (i : ι) ↦ by
        change pullback.fst X.hom (U i).ι ≫ F ≫ Y.hom = pullback.fst X.hom (U i).ι ≫ X.hom
        rw [← Category.assoc, hFi i]
        change ((φ i).left ≫ pullback.fst Y.hom (U i).ι) ≫ Y.hom = _
        rw [Category.assoc, pullback.condition, ← Category.assoc, hw i, ← pullback.condition]
    refine ⟨MorphismProperty.Over.homMk F hF, ?_⟩
    funext i
    apply MorphismProperty.Over.Hom.ext
    change ((FEt.pullback (U i).ι).map (MorphismProperty.Over.homMk F hF)).left = (φ i).left
    apply pullback.hom_ext
    · rw [FEt.pullback_map_left_fst (U := U) _ i]
      exact hFi i
    · rw [FEt.pullback_map_left_snd (U := U) _ i, hw i]

/-- The restriction to `U j` of `∐ Z_i → S` is `Z_j`. -/
lemma FEt.isPullback_sigmaι (hd : Pairwise (Function.onFun Disjoint U)) (Z : ∀ i, FEt (U i))
    (j : ι) : IsPullback (Z j).hom (Sigma.ι (fun i ↦ (Z i).left) j) (U j).ι
      (Sigma.desc fun i ↦ (Z i).hom ≫ (U i).ι) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  ext x
  obtain ⟨⟨k, z⟩, rfl⟩ := (sigmaMk fun i ↦ (Z i).left).surjective x
  have hfx : (Sigma.desc fun i ↦ (Z i).hom ≫ (U i).ι) (Sigma.ι (fun i ↦ (Z i).left) k z) =
      (U k).ι ((Z k).hom z) := by
    rw [← Scheme.Hom.comp_apply, Sigma.ι_desc, Scheme.Hom.comp_apply]
  change (Sigma.desc fun i ↦ (Z i).hom ≫ (U i).ι) (sigmaMk (fun i ↦ (Z i).left) ⟨k, z⟩) ∈
      (U j).ι.opensRange ↔
    sigmaMk (fun i ↦ (Z i).left) ⟨k, z⟩ ∈ Set.range (Sigma.ι (fun i ↦ (Z i).left) j)
  rw [sigmaMk_mk, hfx, Scheme.Opens.opensRange_ι]
  have hk : (U k).ι ((Z k).hom z) ∈ U k := ((Z k).hom z).2
  constructor
  · intro h
    by_cases hkj : k = j
    · subst hkj
      exact ⟨z, rfl⟩
    · have h₃ : _ ∈ U k ⊓ U j := ⟨hk, h⟩
      rw [disjoint_iff.mp (hd hkj)] at h₃
      simp at h₃
  · rintro ⟨w, hw⟩
    obtain rfl : j = k := by
      by_contra hjk
      have := (sigmaι_eq_iff (fun i ↦ (Z i).left) j k w z).mp hw
      exact hjk (congrArg Sigma.fst this)
    exact hk

/-- The open cover of `S` by a family of opens with supremum `⊤`. -/
noncomputable def openCoverOfISupEqTop' (hU : iSup U = ⊤) : S.OpenCover where
  I₀ := ι
  X i := U i
  f i := (U i).ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
    have hx : x ∈ iSup U := hU ▸ trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact ⟨i, by simpa using hi⟩

-- Needed to find `IsZariskiLocalAtTarget @IsFinite` (from `HasAffineProperty`).
set_option backward.isDefEq.respectTransparency false in
/-- V.9: for a finite family `U` of pairwise disjoint opens covering `S` and étale coverings
`Z_i` of the `U i`, `∐ Z_i → S` is an étale covering. -/
lemma FEt.finiteEtale_sigmaDesc [Finite ι] (hU : iSup U = ⊤)
    (hd : Pairwise (Function.onFun Disjoint U)) (Z : ∀ i, FEt (U i)) :
    finiteEtaleHom (Sigma.desc fun i ↦ (Z i).hom ≫ (U i).ι) := by
  refine ⟨?_, IsZariskiLocalAtSource.sigmaDesc fun i ↦ inferInstance⟩
  rw [IsZariskiLocalAtTarget.iff_of_openCover (P := (@IsFinite : MorphismProperty Scheme.{u}))
    (openCoverOfISupEqTop' hU)]
  intro j
  have h := (FEt.isPullback_sigmaι hd Z j).flip
  have e : Arrow.mk (Z j).hom ≅ Arrow.mk ((openCoverOfISupEqTop' hU).pullbackHom
      (Sigma.desc fun i ↦ (Z i).hom ≫ (U i).ι) j) :=
    Arrow.isoMk h.isoPullback (Iso.refl _) (by
      simp [openCoverOfISupEqTop', Scheme.Cover.pullbackHom])
  exact (MorphismProperty.arrow_mk_iso_iff @IsFinite e).mp (inferInstanceAs (IsFinite (Z j).hom))

/-- V.9: for a finite family of pairwise disjoint opens covering `S`, restriction of étale
coverings is essentially surjective: a family `Z_i` of étale coverings of the `U i` is the
restriction of `∐ Z_i → S`. -/
lemma FEt.restrictFamily_essSurj [Finite ι] (hU : iSup U = ⊤)
    (hd : Pairwise (Function.onFun Disjoint U)) : (FEt.restrictFamily U).EssSurj where
  mem_essImage Z := by
    let X : FEt S := MorphismProperty.Over.mk ⊤ (Sigma.desc fun i ↦ (Z i).hom ≫ (U i).ι)
      (FEt.finiteEtale_sigmaDesc hU hd Z)
    refine ⟨X, ⟨Pi.isoMk fun j ↦ MorphismProperty.Over.isoMk
      (FEt.isPullback_sigmaι hd Z j).flip.isoPullback.symm ?_⟩⟩
    exact (FEt.isPullback_sigmaι hd Z j).flip.isoPullback_inv_snd

/-- V.9: for a finite family `U` of pairwise disjoint opens covering `S`, the étale coverings of
`S` are equivalent to the product of the categories of étale coverings of the `U i`, by
restriction. -/
noncomputable def FEt.equivPiOfDisjoint [Finite ι] (hU : iSup U = ⊤)
    (hd : Pairwise (Function.onFun Disjoint U)) : FEt S ≌ ∀ i, FEt (U i) :=
  have := FEt.restrictFamily_faithful hU
  have := FEt.restrictFamily_full hU hd
  have := FEt.restrictFamily_essSurj hU hd
  have : (FEt.restrictFamily U).IsEquivalence := { }
  (FEt.restrictFamily U).asEquivalence

end Decomposition

section Components

variable (S : Scheme.{u})

/-- A connected component of a scheme with finitely many connected components, as an open
subscheme. -/
def connectedComponentOpens [Finite (ConnectedComponents S)] (c : ConnectedComponents S) :
    S.Opens :=
  ⟨ConnectedComponents.mk ⁻¹' {c},
    (isClopen_discrete {c}).isOpen.preimage ConnectedComponents.continuous_coe⟩

variable [Finite (ConnectedComponents S)]

lemma iSup_connectedComponentOpens : iSup (connectedComponentOpens S) = ⊤ := by
  ext x
  simp only [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion, TopologicalSpace.Opens.coe_top,
    Set.mem_univ, iff_true]
  exact ⟨ConnectedComponents.mk x, rfl⟩

lemma pairwise_disjoint_connectedComponentOpens :
    Pairwise (Function.onFun Disjoint (connectedComponentOpens S)) := by
  intro c d hcd
  rw [Function.onFun, disjoint_iff]
  ext x
  simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, TopologicalSpace.Opens.coe_bot,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro hc hd
  exact hcd ((Set.mem_singleton_iff.mp hc).symm.trans (Set.mem_singleton_iff.mp hd))

instance (c : ConnectedComponents S) : ConnectedSpace (connectedComponentOpens S c) := by
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  have h : ((connectedComponentOpens S (ConnectedComponents.mk x) : S.Opens) : Set S) =
      connectedComponent x :=
    connectedComponents_preimage_singleton
  have := isConnected_connectedComponent (x := x)
  rw [← h] at this
  exact isConnected_iff_connectedSpace.mp this

/-- V.9: the étale coverings of a scheme `S` with finitely many connected components `S_i` are
equivalent to the product of the categories of étale coverings of the `S_i`. -/
noncomputable def FEt.equivPiConnectedComponents :
    FEt S ≌ ∀ c : ConnectedComponents S, FEt (connectedComponentOpens S c) :=
  FEt.equivPiOfDisjoint (iSup_connectedComponentOpens S)
    (pairwise_disjoint_connectedComponentOpens S)

/-- V.9: if `S` has finitely many connected components (e.g. `S` is noetherian), the category of
étale coverings of `S` is a multi-Galois category: it is equivalent to the product of the Galois
categories of étale coverings of the connected components of `S` (V.7). -/
theorem FEt.isMultiGalois : IsMultiGalois (FEt S) :=
  ⟨ConnectedComponents S, fun c ↦ FEt (connectedComponentOpens S c), fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, ⟨FEt.equivPiConnectedComponents S⟩⟩

end Components

/-- A noetherian topological space has finitely many connected components: each lies in the
connected component of any point of an irreducible component containing it. -/
lemma finite_connectedComponents_of_noetherianSpace (X : Type*) [TopologicalSpace X]
    [TopologicalSpace.NoetherianSpace X] : Finite (ConnectedComponents X) := by
  have : Finite (irreducibleComponents X) :=
    (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)).to_subtype
  let f : irreducibleComponents X → ConnectedComponents X := fun Z ↦
    ConnectedComponents.mk Z.2.1.nonempty.some
  refine Finite.of_surjective f fun c ↦ ?_
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
  refine ⟨⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩, ?_⟩
  apply ConnectedComponents.coe_eq_coe.mpr
  have hsub : irreducibleComponent x ⊆ connectedComponent x :=
    isIrreducible_irreducibleComponent.isPreirreducible.isPreconnected.subset_connectedComponent
      mem_irreducibleComponent
  exact connectedComponent_eq (hsub (Set.Nonempty.some_mem _)) |>.symm

/-- V.9 for a noetherian scheme (e.g. locally noetherian and quasi-compact): the category of
étale coverings is a multi-Galois category, the product of the Galois categories of étale
coverings of the (finitely many) connected components. -/
theorem FEt.isMultiGalois_of_isNoetherian (S : Scheme.{u}) [IsNoetherian S] :
    IsMultiGalois (FEt S) :=
  have := finite_connectedComponents_of_noetherianSpace S
  FEt.isMultiGalois S

end SGA.SGA1.ExposeV
