/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import SGA.Foundations.QuasiCoherent.Local

/-!
# Inverse images of quasi-coherent modules

For a morphism of schemes `f : X ⟶ Y`, the inverse image functor
`Scheme.Modules.pullback f : Y.Modules ⥤ X.Modules` sends `𝒪_Y` to `𝒪_X`
(`Scheme.Modules.pullbackObjUnitIso`), and, being a left adjoint, sends presentations to
presentations. Since it commutes with restriction to open subschemes
(`Scheme.Modules.restrictPullbackIso`), it preserves quasi-coherence, finite type, finite
presentation and local freeness ([Stacks, Tag 01BG], [Stacks, Tag 01BJ], [Stacks, Tag 01BO],
[Stacks, Tag 01C7]).
-/

universe u

open CategoryTheory Limits TopologicalSpace

namespace CategoryTheory.Functor

/-- A functor isomorphic to a functor identifying `u` and `v` identifies them. -/
lemma map_eq_map_of_iso {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) {X Y : C} {u v : X ⟶ Y} (h : G.map u = G.map v) :
    F.map u = F.map v := by
  rw [← cancel_mono (e.hom.app Y), e.hom.naturality, e.hom.naturality, h]

/-- If `a'` and `b'` are conjugate to `a` and `b` by the same isomorphisms and `F` identifies
`a'` and `b'`, then it identifies `a` and `b`. -/
lemma map_eq_map_of_conj {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') {a b : X ⟶ Y} {a' b' : X' ⟶ Y'}
    (ha : a' = eX.inv ≫ a ≫ eY.hom) (hb : b' = eX.inv ≫ b ≫ eY.hom) (h : F.map a' = F.map b') :
    F.map a = F.map b := by
  have ha' : a = eX.hom ≫ a' ≫ eY.inv := by rw [ha]; simp
  have hb' : b = eX.hom ≫ b' ≫ eY.inv := by rw [hb]; simp
  rw [ha', hb', F.map_comp, F.map_comp, F.map_comp, F.map_comp, h]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules

section Unit

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
  (pullbackPushforwardAdjunction f).isRightAdjoint

instance isIso_pullbackObjUnitToUnit : IsIso (pullbackObjUnitToUnit.{u} f.toRingCatSheafHom) :=
  have : (Opens.map f.base).Final := inferInstance
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-- The inverse image of `𝒪_Y` along `f : X ⟶ Y` is `𝒪_X`. -/
noncomputable def pullbackObjUnitIso :
    (pullback f).obj (unit Y.ringCatSheaf) ≅ unit X.ringCatSheaf :=
  @asIso _ _ _ _ (pullbackObjUnitToUnit.{u} f.toRingCatSheafHom) (isIso_pullbackObjUnitToUnit f)

end Unit

section Presentation

variable {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}

/-- The inverse image of a presentation. -/
noncomputable def presentationPullback (P : M.Presentation) :
    ((pullback f).obj M).Presentation :=
  P.mapOfAdjunction (pullbackPushforwardAdjunction f) (pullbackObjUnitIso f).symm

instance (P : M.Presentation) [hP : P.IsFinite] : (presentationPullback f P).IsFinite :=
  ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

/-- The inverse images of generating sections. -/
noncomputable def generatingSectionsPullback (σ : M.GeneratingSections) :
    ((pullback f).obj M).GeneratingSections :=
  σ.mapOfAdjunction (pullbackPushforwardAdjunction f) (pullbackObjUnitIso f).symm

instance (σ : M.GeneratingSections) [hσ : σ.IsFiniteType] :
    (generatingSectionsPullback f σ).IsFiniteType :=
  ⟨hσ.finite⟩

instance (σ : M.GeneratingSections) [hσ : IsIso σ.π] :
    IsIso (generatingSectionsPullback f σ).π :=
  GeneratingSections.isIso_mapOfAdjunction_π σ (pullbackPushforwardAdjunction f) _

end Presentation

section Restrict

variable {X Y V W : Scheme.{u}} (f : X ⟶ Y) (i : V ⟶ X) [IsOpenImmersion i] (j : W ⟶ Y)
  [IsOpenImmersion j] (f' : V ⟶ W) (h : f' ≫ j = i ≫ f)

/-- Inverse images commute with restriction to open subschemes: given a commutative square
`f' ≫ j = i ≫ f` where `i` and `j` are open immersions, `(f^* M)|_V ≅ f'^* (M|_W)`. -/
noncomputable def restrictPullbackIso (M : Y.Modules) :
    ((pullback f).obj M).restrict i ≅ (pullback f').obj (M.restrict j) :=
  (restrictFunctorIsoPullback i).app _ ≪≫ (pullbackComp i f).app M ≪≫
    (pullbackCongr h.symm).app M ≪≫ ((pullbackComp f' j).app M).symm ≪≫
    (pullback f').mapIso ((restrictFunctorIsoPullback j).app M).symm

end Restrict

section Properties

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)

/-- The inverse image of a quasi-coherent module is quasi-coherent. -/
@[stacks 01BG]
instance isQuasicoherent_pullback [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent := by
  obtain ⟨ι, U, P, hU, -⟩ := M.exists_isOpenCover_presentation
  exact isQuasicoherent_of_isOpenCover (U := fun i ↦ f ⁻¹ᵁ U i) (hU.comap f.base.hom) fun i ↦
    (presentationPullback (f ∣_ U i) (P i)).ofIso
      (restrictPullbackIso f _ _ _ (morphismRestrict_ι f (U i)) M).symm

/-- The inverse image of a module of finite type is of finite type. -/
@[stacks 01BJ]
instance isFiniteType_pullback [M.IsFiniteType] : ((pullback f).obj M).IsFiniteType := by
  obtain ⟨ι, U, σ, hU, hσ⟩ := exists_isOpenCover_generatingSections M
  exact isFiniteType_of_isOpenCover (U := fun i ↦ f ⁻¹ᵁ U i) (hU.comap f.base.hom)
    (fun i ↦ (generatingSectionsPullback (f ∣_ U i) (σ i)).ofIso
      (restrictPullbackIso f _ _ _ (morphismRestrict_ι f (U i)) M).symm)
    (hσ := fun i ↦ ⟨(hσ i).finite⟩)

/-- The inverse image of a module of finite presentation is of finite presentation. -/
@[stacks 01BO]
instance isFinitePresentation_pullback [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation := by
  obtain ⟨ι, U, P, hU, hP⟩ := exists_isOpenCover_finitePresentation M
  exact isFinitePresentation_of_isOpenCover (U := fun i ↦ f ⁻¹ᵁ U i) (hU.comap f.base.hom)
    (fun i ↦ (presentationPullback (f ∣_ U i) (P i)).ofIso
      (restrictPullbackIso f _ _ _ (morphismRestrict_ι f (U i)) M).symm)
    (hP := fun i ↦ ⟨⟨(hP i).isFiniteType_generators.finite⟩,
      ⟨(hP i).isFiniteType_relations.finite⟩⟩)

/-- The inverse image of a locally free module is locally free. -/
@[stacks 01C7]
instance isLocallyFree_pullback [M.IsLocallyFree] : ((pullback f).obj M).IsLocallyFree := by
  obtain ⟨ι, U, σ, hU, hσ⟩ := exists_isOpenCover_basis M
  exact isLocallyFree_of_isOpenCover (U := fun i ↦ f ⁻¹ᵁ U i) (hU.comap f.base.hom)
    (fun i ↦ (generatingSectionsPullback (f ∣_ U i) (σ i)).ofIso
      (restrictPullbackIso f _ _ _ (morphismRestrict_ι f (U i)) M).symm)
    (hσ := fun i ↦ GeneratingSections.isIso_ofIso_π _ _ (hσ :=
      GeneratingSections.isIso_mapOfAdjunction_π _ _ _ (hσ := hσ i)))

variable {X : Scheme.{u}} (U : X.Opens) (M : X.Modules)

instance isQuasicoherent_restrict [M.IsQuasicoherent] : (M.restrict U.ι).IsQuasicoherent :=
  isQuasicoherent_of_iso ((restrictFunctorIsoPullback U.ι).app M).symm

instance isFiniteType_restrict [M.IsFiniteType] : (M.restrict U.ι).IsFiniteType :=
  isFiniteType_of_iso ((restrictFunctorIsoPullback U.ι).app M).symm

instance isFinitePresentation_restrict [M.IsFinitePresentation] :
    (M.restrict U.ι).IsFinitePresentation :=
  isFinitePresentation_of_iso ((restrictFunctorIsoPullback U.ι).app M).symm

instance isLocallyFree_restrict [M.IsLocallyFree] : (M.restrict U.ι).IsLocallyFree :=
  isLocallyFree_of_iso ((restrictFunctorIsoPullback U.ι).app M).symm

end Properties

section HomExt

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Morphisms of `𝒪_X`-modules which agree on the members of an open cover are equal. -/
lemma hom_ext_of_isOpenCover {ι : Type*} {U : ι → X.Opens} (hU : IsOpenCover U) {u v : M ⟶ N}
    (h : ∀ i, (restrictFunctor (U i).ι).map u = (restrictFunctor (U i).ι).map v) : u = v := by
  ext V s
  let W (i : ι) : X.Opens := (U i).ι ''ᵁ ((U i).ι ⁻¹ᵁ V)
  have hW (i : ι) : W i ≤ V := (U i).ι.image_preimage_le V
  have hcov : V ≤ ⨆ i, W i := by
    intro x hx
    obtain ⟨i, hi⟩ := hU.exists_mem x
    exact Opens.mem_iSup.mpr ⟨i, ⟨⟨x, hi⟩, hx, rfl⟩⟩
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ W V (fun i ↦ homOfLE (hW i))
    hcov _ _ fun i ↦ ?_
  have hu := congr($(u.mapPresheaf.naturality (homOfLE (hW i)).op) s)
  have hv := congr($(v.mapPresheaf.naturality (homOfLE (hW i)).op) s)
  have := congr($(congrArg (fun w ↦ Hom.app w ((U i).ι ⁻¹ᵁ V)) (h i))
    (M.presheaf.map (homOfLE (hW i)).op s))
  simp only [mapPresheaf_app] at hu hv
  exact hu.symm.trans (this.trans hv)

end HomExt

section OpenImmersion

variable {X V : Scheme.{u}}

/-- The restriction of `M` to the image of an open immersion `g : V ⟶ X` corresponds to `g^* M`
under the isomorphism `V ≅ g.opensRange`. -/
noncomputable def restrictOpensRangeIso (g : V ⟶ X) [IsOpenImmersion g] (M : X.Modules) :
    M.restrict g.opensRange.ι ≅ (pullback g.isoOpensRange.inv).obj ((pullback g).obj M) :=
  (restrictFunctorIsoPullback g.opensRange.ι).app M ≪≫
    (pullbackCongr g.isoOpensRange_inv_comp.symm).app M ≪≫
    ((pullbackComp g.isoOpensRange.inv g).app M).symm

/-- `restrictOpensRangeIso` as a natural isomorphism. -/
noncomputable def restrictOpensRangeNatIso (g : V ⟶ X) [IsOpenImmersion g] :
    restrictFunctor g.opensRange.ι ≅ pullback g ⋙ pullback g.isoOpensRange.inv :=
  restrictFunctorIsoPullback _ ≪≫ pullbackCongr g.isoOpensRange_inv_comp.symm ≪≫
    (pullbackComp _ _).symm

/-- If `g = k ≫ U.ι` factors through an open subscheme `U`, then `g^* M ≅ k^* (M|_U)`. -/
noncomputable def pullbackIsoOfFac {U : X.Opens} (g : V ⟶ X) (k : V ⟶ U) (h : k ≫ U.ι = g)
    (M : X.Modules) : (pullback g).obj M ≅ (pullback k).obj (M.restrict U.ι) :=
  (pullbackCongr h.symm).app M ≪≫ ((pullbackComp k U.ι).app M).symm ≪≫
    (pullback k).mapIso ((restrictFunctorIsoPullback U.ι).app M).symm

variable {ι : Type u} {V : ι → Scheme.{u}} (g : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (g i)]
  (hg : ∀ x : X, ∃ i, x ∈ Set.range (g i)) {M : X.Modules}

include hg in
lemma isOpenCover_opensRange : IsOpenCover fun i ↦ (g i).opensRange := by
  refine IsOpenCover.of_sets (fun i ↦ (g i).opensRange.2) ?_
  refine Set.eq_univ_of_forall fun x ↦ ?_
  obtain ⟨i, hi⟩ := hg x
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

include hg in
/-- A module whose inverse images along a jointly surjective family of open immersions have
presentations is quasi-coherent. -/
lemma isQuasicoherent_of_pullback_presentation
    (P : ∀ i, ((pullback (g i)).obj M).Presentation) : M.IsQuasicoherent :=
  isQuasicoherent_of_isOpenCover (isOpenCover_opensRange g hg) fun i ↦
    (presentationPullback (g i).isoOpensRange.inv (P i)).ofIso
      (restrictOpensRangeIso (g i) M).symm

include hg in
/-- A module whose inverse images along a jointly surjective family of open immersions have
finite presentations is of finite presentation. -/
lemma isFinitePresentation_of_pullback_presentation
    (P : ∀ i, ((pullback (g i)).obj M).Presentation) [hP : ∀ i, (P i).IsFinite] :
    M.IsFinitePresentation :=
  isFinitePresentation_of_isOpenCover (isOpenCover_opensRange g hg)
    (fun i ↦ (presentationPullback (g i).isoOpensRange.inv (P i)).ofIso
      (restrictOpensRangeIso (g i) M).symm)
    (hP := fun i ↦ ⟨⟨(hP i).isFiniteType_generators.finite⟩,
      ⟨(hP i).isFiniteType_relations.finite⟩⟩)

include hg in
/-- A module whose inverse images along a jointly surjective family of open immersions are
generated by finitely many global sections is of finite type. -/
lemma isFiniteType_of_pullback_generatingSections
    (σ : ∀ i, ((pullback (g i)).obj M).GeneratingSections) [hσ : ∀ i, (σ i).IsFiniteType] :
    M.IsFiniteType :=
  isFiniteType_of_isOpenCover (isOpenCover_opensRange g hg)
    (fun i ↦ (generatingSectionsPullback (g i).isoOpensRange.inv (σ i)).ofIso
      (restrictOpensRangeIso (g i) M).symm)
    (hσ := fun i ↦ ⟨(hσ i).finite⟩)

include hg in
/-- A module whose inverse images along a jointly surjective family of open immersions are
free is locally free. -/
lemma isLocallyFree_of_pullback_generatingSections
    (σ : ∀ i, ((pullback (g i)).obj M).GeneratingSections) [hσ : ∀ i, IsIso (σ i).π] :
    M.IsLocallyFree :=
  isLocallyFree_of_isOpenCover (isOpenCover_opensRange g hg)
    (fun i ↦ (generatingSectionsPullback (g i).isoOpensRange.inv (σ i)).ofIso
      (restrictOpensRangeIso (g i) M).symm)
    (hσ := fun i ↦ GeneratingSections.isIso_ofIso_π _ _ (hσ :=
      GeneratingSections.isIso_mapOfAdjunction_π _ _ _ (hσ := hσ i)))

include hg in
/-- Morphisms of modules which agree after inverse image along a jointly surjective family of
open immersions are equal. -/
lemma hom_ext_of_pullback {N : X.Modules} {u v : M ⟶ N}
    (h : ∀ i, (pullback (g i)).map u = (pullback (g i)).map v) : u = v :=
  hom_ext_of_isOpenCover (isOpenCover_opensRange g hg) fun i ↦ by
    rw [← cancel_mono ((restrictOpensRangeNatIso (g i)).hom.app N),
      NatTrans.naturality, NatTrans.naturality, Functor.comp_map, Functor.comp_map, h i]

omit [∀ i, IsOpenImmersion (g i)] in
include hg in
/-- Composing a family of open immersions with open covers of their sources. -/
private lemma exists_mem_range_comp {κ : ι → Type u} (W : ∀ i, κ i → (V i).Opens)
    (hW : ∀ i, IsOpenCover (W i)) (x : X) :
    ∃ j : Σ i, κ i, x ∈ Set.range ((W j.1 j.2).ι ≫ g j.1) := by
  obtain ⟨i, y, rfl⟩ := hg x
  obtain ⟨k, hk⟩ := (hW i).exists_mem y
  exact ⟨⟨i, k⟩, ⟨⟨y, hk⟩, rfl⟩⟩

include hg in
/-- Quasi-coherence is local for open immersions. -/
lemma isQuasicoherent_of_forall_pullback
    (h : ∀ i, ((pullback (g i)).obj M).IsQuasicoherent) : M.IsQuasicoherent := by
  choose κ W P hW _ using fun i ↦ ((pullback (g i)).obj M).exists_isOpenCover_presentation
  refine isQuasicoherent_of_pullback_presentation (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ g j.1)
    (exists_mem_range_comp g hg W hW) fun j ↦ (P j.1 j.2).ofIso ?_
  exact ((restrictFunctorIsoPullback _).app _ ≪≫ (pullbackComp _ _).app M)

include hg in
/-- Finite type is local for open immersions. -/
lemma isFiniteType_of_forall_pullback
    (h : ∀ i, ((pullback (g i)).obj M).IsFiniteType) : M.IsFiniteType := by
  choose κ W σ hW hσ using fun i ↦ exists_isOpenCover_generatingSections ((pullback (g i)).obj M)
  exact isFiniteType_of_pullback_generatingSections (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ g j.1)
    (exists_mem_range_comp g hg W hW)
    (fun j ↦ (σ j.1 j.2).ofIso ((restrictFunctorIsoPullback _).app _ ≪≫ (pullbackComp _ _).app M))
    (hσ := fun j ↦ ⟨(hσ j.1 j.2).finite⟩)

include hg in
/-- Finite presentation is local for open immersions. -/
lemma isFinitePresentation_of_forall_pullback
    (h : ∀ i, ((pullback (g i)).obj M).IsFinitePresentation) : M.IsFinitePresentation := by
  choose κ W P hW hP using fun i ↦
    exists_isOpenCover_finitePresentation ((pullback (g i)).obj M)
  exact isFinitePresentation_of_pullback_presentation
    (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ g j.1) (exists_mem_range_comp g hg W hW)
    (fun j ↦ (P j.1 j.2).ofIso ((restrictFunctorIsoPullback _).app _ ≪≫ (pullbackComp _ _).app M))
    (hP := fun j ↦ ⟨⟨(hP j.1 j.2).isFiniteType_generators.finite⟩,
      ⟨(hP j.1 j.2).isFiniteType_relations.finite⟩⟩)

include hg in
/-- Local freeness is local for open immersions. -/
lemma isLocallyFree_of_forall_pullback
    (h : ∀ i, ((pullback (g i)).obj M).IsLocallyFree) : M.IsLocallyFree := by
  choose κ W σ hW hσ using fun i ↦ exists_isOpenCover_basis ((pullback (g i)).obj M)
  exact isLocallyFree_of_pullback_generatingSections (fun j : Σ i, κ i ↦ (W j.1 j.2).ι ≫ g j.1)
    (exists_mem_range_comp g hg W hW)
    (fun j ↦ (σ j.1 j.2).ofIso ((restrictFunctorIsoPullback _).app _ ≪≫ (pullbackComp _ _).app M))
    (hσ := fun j ↦ GeneratingSections.isIso_ofIso_π _ _ (hσ := hσ j.1 j.2))

end OpenImmersion

section Global

variable {X : Scheme.{u}} {M : X.Modules}

/-- A module generated by finitely many global sections is of finite type. -/
lemma isFiniteType_of_generatingSections (σ : M.GeneratingSections) [hσ : σ.IsFiniteType] :
    M.IsFiniteType :=
  isFiniteType_of_pullback_generatingSections (fun _ : PUnit.{u + 1} ↦ 𝟙 X)
    (fun x ↦ ⟨.unit, x, rfl⟩) (fun _ ↦ generatingSectionsPullback (𝟙 X) σ)
    (hσ := fun _ ↦ ⟨hσ.finite⟩)

/-- A module with a finite global presentation is of finite presentation. -/
lemma isFinitePresentation_of_presentation (P : M.Presentation) [hP : P.IsFinite] :
    M.IsFinitePresentation :=
  isFinitePresentation_of_pullback_presentation (fun _ : PUnit.{u + 1} ↦ 𝟙 X)
    (fun x ↦ ⟨.unit, x, rfl⟩) (fun _ ↦ presentationPullback (𝟙 X) P)
    (hP := fun _ ↦ ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩)

/-- A free module is locally free. -/
lemma isLocallyFree_of_generatingSections (σ : M.GeneratingSections) [hσ : IsIso σ.π] :
    M.IsLocallyFree :=
  isLocallyFree_of_pullback_generatingSections (fun _ : PUnit.{u + 1} ↦ 𝟙 X)
    (fun x ↦ ⟨.unit, x, rfl⟩) (fun _ ↦ generatingSectionsPullback (𝟙 X) σ)
    (hσ := fun _ ↦ GeneratingSections.isIso_mapOfAdjunction_π _ _ _ (hσ := hσ))

end Global

end AlgebraicGeometry.Scheme.Modules
