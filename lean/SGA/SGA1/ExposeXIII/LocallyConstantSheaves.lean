/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Etale.RepresentableGluing
import SGA.SGA1.ExposeIX.EffectiveGluing
import SGA.SGA1.ExposeIX.QuasiAffineDescent
import SGA.SGA1.ExposeVIII.MorphismDescent
import SGA.SGA1.ExposeV.QuotientDescent
import SGA.SGA1.ExposeV.QuotientHasQuotients

/-!
# SGA 1, Exposé XIII: locally constant sheaves of finite sets and étale coverings

XIII 2.3 a) uses that a locally constant constructible sheaf of sets on the étale site of a
scheme is representable by an étale covering (SGA 4 IX 2.2). We prove this, and the resulting
equivalences of categories.

* A descent datum from a representing object (`descentDatum`). Let `g : S' ⟶ S` be étale and
  `X'` an étale `S'`-scheme representing the restriction of a sheaf `G` on `S_et` to `S'`. Then
  `X'` carries a descent datum relative to `g` in the sense of IX.3: the point `x'·s'` of
  `X'` classifies the section of `G` given by `x'`, seen over `s'`.
* If `g` is surjective and this datum is effective with descended étale scheme `X`, then `X`
  represents `G` (`nonempty_etaleYoneda_iso_of_descent`).
* Over an affine base (`exists_etaleYoneda_iso_of_isAffine`): finitely many affine étale
  neighbourhoods trivialize a locally constant sheaf of finite sets `F`. Their disjoint union
  is faithfully flat and quasi-compact over the base, and `F` restricted to it is represented by
  a finite disjoint union of constant schemes (`Scheme.nonempty_etaleYoneda_sigma_iso`). The
  datum is effective by IX.4.1, and the descended scheme is finite by fpqc descent of finiteness
  (VIII.5.7).
* In general (`exists_etaleYoneda_iso`, SGA 4 IX 2.2): the representing objects over the affine
  opens of `S` glue by IX.4.3, since the covering `∐ U ⟶ S` has a section over each `U`.
* `fetEquivLocallyConstantFiniteSheaf`: the functor sending an étale covering to the sheaf it
  represents is an equivalence between étale coverings of `S` and locally constant sheaves of
  finite sets on `S_et`. It is fully faithful by `Scheme.finiteEtaleSheafFullyFaithful`.
* `contActionEquivLocallyConstantFiniteSheaf`: for `S` connected, with a geometric point `s̄`,
  locally constant sheaves of finite sets are equivalent to finite continuous `π₁(S, s̄)`-sets
  (V.7).
-/

universe u

open CategoryTheory Limits Opposite AlgebraicGeometry
open Scheme (etaleYoneda etaleRestrict etaleRepresentsEquiv etaleRepresentsEquiv_comp
  etaleRepresentsEquiv_apply)

set_option backward.isDefEq.respectTransparency false

namespace SGA.SGA1.ExposeXIII

section DescentDatum

variable {S S' : Scheme.{u}} (g : S' ⟶ S) [Etale g] {G : Sheaf S.smallEtaleTopology (Type u)}
  {X' : S'.Etale} (φ : (etaleYoneda S').obj X' ≅ (etaleRestrict g).obj G)

/-- The `S'`-scheme `X' ×_S S'`, over `S'` by the second projection. -/
noncomputable abbrev actSource (X' : S'.Etale) : S'.Etale :=
  Scheme.Etale.mk (pullback.snd (X'.hom ≫ g) g)

/-- The first projection `X' ×_S S' ⟶ X'`, as a morphism of étale `S`-schemes. -/
noncomputable def actFst (X' : S'.Etale) :
    (Scheme.Etale.map g).obj (actSource g X') ⟶ (Scheme.Etale.map g).obj X' :=
  MorphismProperty.Over.homMk (pullback.fst _ _) pullback.condition trivial

/-- The universal section of `G` over `X'`. -/
noncomputable abbrev univSection : G.obj.obj (op ((Scheme.Etale.map g).obj X')) :=
  etaleRepresentsEquiv g φ X' (𝟙 X')

/-- The action `X' ×_S S' ⟶ X'` of the descent datum: it classifies the inverse image of the
universal section along the first projection. -/
noncomputable def actHom : actSource g X' ⟶ X' :=
  (etaleRepresentsEquiv g φ _).symm (G.obj.map (actFst g X').op (univSection g φ))

lemma etaleRepresentsEquiv_actHom :
    etaleRepresentsEquiv g φ _ (actHom g φ) = G.obj.map (actFst g X').op (univSection g φ) :=
  Equiv.apply_symm_apply _ _

lemma map_actHom_univSection :
    G.obj.map ((Scheme.Etale.map g).map (actHom g φ)).op (univSection g φ) =
      G.obj.map (actFst g X').op (univSection g φ) := by
  rw [← etaleRepresentsEquiv_apply, etaleRepresentsEquiv_actHom]

/-- The descent datum relative to `g` on an étale `S'`-scheme `X'` representing the restriction
of `G` to `S'`: `(x', s') ↦ x'·s'` is the point of `X'` over `s'` corresponding to the section of
`G` given by `x'`. -/
noncomputable def descentDatum : ExposeIX.DescentDatum g X'.hom where
  act := (actHom g φ).left
  act_comp := MorphismProperty.Over.w (actHom g φ)
  unit := by
    let l : X' ⟶ actSource g X' :=
      MorphismProperty.Over.homMk (pullback.lift (𝟙 _) X'.hom (by simp)) (pullback.lift_snd _ _ _)
        trivial
    have hl : (Scheme.Etale.map g).map l ≫ actFst g X' = 𝟙 _ :=
      MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
    have : l ≫ actHom g φ = 𝟙 X' := by
      apply (etaleRepresentsEquiv g φ X').injective
      rw [etaleRepresentsEquiv_comp, etaleRepresentsEquiv_actHom, ← Functor.map_comp_apply,
        ← op_comp, hl, op_id, CategoryTheory.Functor.map_id]
      rfl
    exact congrArg (fun k ↦ k.left) this
  assoc := by
    let Q : S'.Etale := Scheme.Etale.mk (pullback.snd (pullback.snd (X'.hom ≫ g) g ≫ g) g)
    have hact : (actHom g φ).left ≫ X'.hom = pullback.snd (X'.hom ≫ g) g :=
      MorphismProperty.Over.w (actHom g φ)
    let k₁ : Q ⟶ actSource g X' := MorphismProperty.Over.homMk
      (pullback.lift (pullback.fst _ _ ≫ (actHom g φ).left) (pullback.snd _ _)
        (by rw [Category.assoc, reassoc_of% hact, pullback.condition]))
      (pullback.lift_snd _ _ _) trivial
    let k₂ : Q ⟶ actSource g X' := MorphismProperty.Over.homMk
      (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _)
        (by rw [Category.assoc, pullback.condition, pullback.condition]))
      (pullback.lift_snd _ _ _) trivial
    let m : (Scheme.Etale.map g).obj Q ⟶ (Scheme.Etale.map g).obj (actSource g X') :=
      MorphismProperty.Over.homMk (pullback.fst _ _) pullback.condition trivial
    have h₁ : (Scheme.Etale.map g).map k₁ ≫ actFst g X' =
        m ≫ (Scheme.Etale.map g).map (actHom g φ) :=
      MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
    have h₂ : (Scheme.Etale.map g).map k₂ ≫ actFst g X' = m ≫ actFst g X' :=
      MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
    have : k₁ ≫ actHom g φ = k₂ ≫ actHom g φ := by
      apply (etaleRepresentsEquiv g φ Q).injective
      rw [etaleRepresentsEquiv_comp, etaleRepresentsEquiv_comp, etaleRepresentsEquiv_actHom,
        ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, h₁, h₂,
        op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
        map_actHom_univSection]
    exact congrArg (fun k ↦ k.left) this

lemma descentDatum_act : (descentDatum g φ).act = (actHom g φ).left := rfl

variable {g φ} {X : Scheme.{u}} {b : X ⟶ S} [Etale b] {v : X'.left ⟶ X}
  (hv : IsPullback v X'.hom b g) (hact : (descentDatum g φ).act ≫ v = pullback.fst _ _ ≫ v)

/-- The morphism `X' ⟶ X` over `S`, for a descent `X` of the datum. -/
noncomputable def descentMap : (Scheme.Etale.map g).obj X' ⟶ Scheme.Etale.mk b :=
  MorphismProperty.Over.homMk v hv.w trivial

include hact in
lemma map_univSection_eq {Z : S.Etale} (p₁ p₂ : Z ⟶ (Scheme.Etale.map g).obj X')
    (h : p₁ ≫ descentMap hv = p₂ ≫ descentMap hv) :
    G.obj.map p₁.op (univSection g φ) = G.obj.map p₂.op (univSection g φ) := by
  have h₁ : p₁.left ≫ X'.hom ≫ g = Z.hom := MorphismProperty.Over.w p₁
  have h₂ : p₂.left ≫ X'.hom ≫ g = Z.hom := MorphismProperty.Over.w p₂
  have hvv : p₁.left ≫ v = p₂.left ≫ v := congrArg (fun k ↦ k.left) h
  let k : Z.left ⟶ pullback (X'.hom ≫ g) g :=
    pullback.lift p₁.left (p₂.left ≫ X'.hom) (by rw [h₁, Category.assoc, h₂])
  let k' : Z ⟶ (Scheme.Etale.map g).obj (actSource g X') :=
    MorphismProperty.Over.homMk k (by
      change k ≫ pullback.snd _ _ ≫ g = Z.hom
      rw [pullback.lift_snd_assoc, Category.assoc, h₂]) trivial
  have hk₁ : k' ≫ actFst g X' = p₁ := MorphismProperty.Over.Hom.ext (pullback.lift_fst _ _ _)
  have hact' : (actHom g φ).left ≫ X'.hom = pullback.snd (X'.hom ≫ g) g :=
    MorphismProperty.Over.w (actHom g φ)
  have hk₂ : k' ≫ (Scheme.Etale.map g).map (actHom g φ) = p₂ := by
    apply MorphismProperty.Over.Hom.ext
    change k ≫ (actHom g φ).left = p₂.left
    apply hv.hom_ext
    · rw [Category.assoc, ← descentDatum_act, hact, pullback.lift_fst_assoc, hvv]
    · rw [Category.assoc, hact', pullback.lift_snd]
  rw [← hk₁, ← hk₂, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    map_actHom_univSection]

include hact in
/-- The section of `G` over the descended scheme `X` which restricts to the universal section
over `X'`. -/
lemma exists_section_descent [Surjective g] :
    ∃ s : G.obj.obj (op (Scheme.Etale.mk b)),
      G.obj.map (descentMap hv).op s = univSection g φ := by
  have hG := (isSheaf_iff_isSheaf_of_type _ _).1 G.property
  have hsurj : Surjective v := MorphismProperty.of_isPullback hv.flip inferInstance
  have hcov : Sieve.generate (Presieve.singleton (descentMap hv)) ∈
      S.smallEtaleTopology (Scheme.Etale.mk b) := by
    rw [Scheme.mem_smallEtaleTopology_iff]
    intro x
    obtain ⟨y, rfl⟩ := v.surjective x
    exact ⟨_, descentMap hv, y, ⟨_, 𝟙 _, _, Presieve.singleton.mk, Category.id_comp _⟩, rfl⟩
  obtain ⟨s, hs, -⟩ := Presieve.isSheafFor_singleton.1
    ((Presieve.isSheafFor_iff_generate _).2 (hG _ hcov)) (univSection g φ)
    (fun p₁ p₂ h ↦ map_univSection_eq hv hact p₁ p₂ h)
  exact ⟨s, hs⟩

include hv hact in
/-- If the descent datum defined by a representing object `X'` of `G|S'` is effective, with
descended étale `S`-scheme `X`, then `X` represents `G`. -/
theorem nonempty_etaleYoneda_iso_of_descent [Surjective g] :
    Nonempty ((etaleYoneda S).obj (Scheme.Etale.mk b) ≅ G) := by
  obtain ⟨s, hs⟩ := exists_section_descent hv hact
  have : IsIso (S.smallEtaleTopology.yonedaEquiv.symm s) :=
    Scheme.isIso_of_forall_isIso_etaleRestrict (fun _ : Unit ↦ g)
      (fun x ↦ ⟨(), g.surjective x⟩) _ fun _ ↦
        Scheme.isIso_etaleRestrict_map_yonedaEquiv_symm (φ := φ) (descentMap hv) hv hs
  exact ⟨asIso (S.smallEtaleTopology.yonedaEquiv.symm s)⟩

end DescentDatum

section Representability

open Scheme (etalePullback etalePullbackComp etalePullbackIsoRestrict etalePullbackConstantSheafIso
  constantSheafIsoYoneda IsLocallyConstantFiniteSheaf)

variable {S : Scheme.{u}} {F : Sheaf S.smallEtaleTopology (Type u)}

/-- A locally constant sheaf with finite values becomes constant on affine étale neighbourhoods
of every point. -/
lemma exists_affine_trivialization (hF : IsLocallyConstantFiniteSheaf F) (x : S) :
    ∃ (A : Scheme.{u}) (_ : IsAffine A) (e : A ⟶ S) (_ : Etale e) (a : A) (E : Type u)
      (_ : Finite E), e a = x ∧
        Nonempty ((etalePullback e).obj F ≅
          (constantSheaf A.smallEtaleTopology (Type u)).obj E) := by
  obtain ⟨W, e, _, w, hw, E, hE, ⟨i⟩⟩ := hF x
  obtain ⟨_, ⟨A, hA, rfl⟩, hwA, -⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ w) isOpen_univ
  change W.Opens at A
  have : IsAffine A := hA
  refine ⟨A, inferInstance, A.ι ≫ e, inferInstance, ⟨w, hwA⟩, E, hE, by simpa using hw, ⟨?_⟩⟩
  exact ((etalePullbackComp A.ι e).app F).symm ≪≫ (etalePullback A.ι).mapIso i ≪≫
    (etalePullbackConstantSheafIso A.ι).app E

/-- The identification `(ιᵢ)^! g^! F ≅ eᵢ^* F` for `eᵢ = ιᵢ ≫ g`. -/
noncomputable def etaleRestrictRestrictIso {W S' : Scheme.{u}} (ι : W ⟶ S') (g : S' ⟶ S) [Etale ι]
    [Etale g] {e : W ⟶ S} (h : ι ≫ g = e) :
    (etaleRestrict ι).obj ((etaleRestrict g).obj F) ≅ (etalePullback e).obj F :=
  ((etalePullbackIsoRestrict ι).app _).symm ≪≫
    (etalePullback ι).mapIso ((etalePullbackIsoRestrict g).app F).symm ≪≫
    (etalePullbackComp ι g).app F ≪≫ eqToIso (by rw [h])

instance (A : Scheme.{u}) (E : Type u) [Finite E] : IsFinite (Scheme.constantSchemeHom A E) :=
  ExposeV.isFinite_sigmaDesc _ fun _ ↦ inferInstance

/-- SGA 4 IX 2.2 over an affine base: a locally constant sheaf of finite sets on the small étale
site of an affine scheme is represented by a finite étale scheme. The trivializing étale
neighbourhoods can be chosen affine and finite in number; their disjoint union `S'` is
faithfully flat and quasi-compact over `S`, the restriction of `F` to `S'` is represented by a
finite disjoint union of constant schemes, and this finite étale `S'`-scheme descends
(IX.4.1). -/
theorem exists_etaleYoneda_iso_of_isAffine [IsAffine S] (hF : IsLocallyConstantFiniteSheaf F) :
    ∃ (V : S.Etale) (_ : IsFinite V.hom), Nonempty ((etaleYoneda S).obj V ≅ F) := by
  choose A hA e he a E hE hae i using exists_affine_trivialization hF
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ Set.range (e x))
    (fun x ↦ (e x).isOpenMap.isOpen_range) (fun x _ ↦ Set.mem_iUnion.2 ⟨x, a x, hae x⟩)
  let W : t → Scheme.{u} := fun x ↦ A x.1
  let g : ∐ W ⟶ S := Sigma.desc fun x ↦ e x.1
  have : Etale g := IsZariskiLocalAtSource.sigmaDesc fun x ↦ he x.1
  have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ <| by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨x, hx⟩, hy⟩
  have : QuasiCompact g := by
    rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]
    exact (sigmaMk W).compactSpace
  let X : ∀ x : t, (W x).Etale := fun x ↦ Scheme.Etale.constant (W x) (E x.1)
  let φ : ∀ x, (etaleYoneda (W x)).obj (X x) ≅
      (etaleRestrict (Sigma.ι W x)).obj ((etaleRestrict g).obj F) := fun x ↦
    (constantSheafIsoYoneda (W x) (E x.1)).symm ≪≫ (i x.1).some.symm ≪≫
      (etaleRestrictRestrictIso (Sigma.ι W x) g (Sigma.ι_desc _ _)).symm
  obtain ⟨ψ⟩ := Scheme.nonempty_etaleYoneda_sigma_iso φ
  have : ∀ x, IsFinite (X x).hom := fun x ↦
    inferInstanceAs (IsFinite (Scheme.constantSchemeHom _ _))
  have ha : ExposeIX.etaleSeparatedFiniteType (Scheme.Etale.sigma W X).hom :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  obtain ⟨Xd, b, v, hb, hv, hact⟩ := (descentDatum g ψ).isEffective_of_flat' ha
  have : Etale b := hb.1.1
  have : IsFinite b := ExposeVIII.isFinite_descendsAlong_fpqc.of_isPullback hv.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  exact ⟨Scheme.Etale.mk b, this, nonempty_etaleYoneda_iso_of_descent hv hact⟩

/-- SGA 4 IX 2.2: a locally constant sheaf of finite sets on the small étale site of a scheme `S`
is represented by a finite étale `S`-scheme. By the affine case, it is represented on every affine
open `U` by a finite étale `U`-scheme `X_U`; the disjoint union of the `X_U` represents the
restriction of `F` to `∐ U`, and the corresponding descent datum along `∐ U ⟶ S` is effective by
IX.4.3, since over each `U` the covering has a section. -/
theorem exists_etaleYoneda_iso (hF : IsLocallyConstantFiniteSheaf F) :
    ∃ (V : S.Etale) (_ : IsFinite V.hom), Nonempty ((etaleYoneda S).obj V ≅ F) := by
  let W : S.affineOpens → Scheme.{u} := fun U ↦ U.1
  have hW : ∀ U, IsAffine (W U) := fun U ↦ U.2
  choose X hX hiso using fun U : S.affineOpens ↦
    exists_etaleYoneda_iso_of_isAffine (S := W U) (hF.etalePullback U.1.ι)
  let g : ∐ W ⟶ S := Sigma.desc fun U ↦ U.1.ι
  have : Etale g := IsZariskiLocalAtSource.sigmaDesc fun _ ↦ inferInstance
  have : Surjective g := Surjective.sigmaDesc_of_union_range_eq_univ <| by
    refine Set.eq_univ_of_forall fun y ↦ ?_
    obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ :=
      S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    exact Set.mem_iUnion.2 ⟨⟨U, hU⟩, by rw [Scheme.Opens.range_ι]; exact hyU⟩
  let φ : ∀ U, (etaleYoneda (W U)).obj (X U) ≅
      (etaleRestrict (Sigma.ι W U)).obj ((etaleRestrict g).obj F) := fun U ↦
    (hiso U).some ≪≫ (etaleRestrictRestrictIso (Sigma.ι W U) g (Sigma.ι_desc _ _)).symm
  obtain ⟨ψ⟩ := Scheme.nonempty_etaleYoneda_sigma_iso φ
  have hD : (descentDatum g ψ).IsEffective @Etale := by
    rw [ExposeIX.DescentDatum.isEffective_iff_forall_baseChange (fun U : S.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top S)]
    intro U
    have hσ : pullback.lift (Sigma.ι W U) (𝟙 _) (by simp [g, W]) ≫ pullback.snd g U.1.ι =
        𝟙 _ :=
      pullback.lift_snd _ _ _
    exact ((descentDatum g ψ).baseChange U.1.ι).isEffective_of_section hσ @Etale inferInstance
  obtain ⟨Xd, b, v, hb, hv, hact⟩ := hD
  have : Etale b := hb
  have : IsFinite b := by
    refine IsZariskiLocalAtTarget.of_iSup_eq_top (fun U : S.affineOpens ↦ U.1)
      (iSup_affineOpens_eq_top S) fun U ↦ ?_
    have h₁ : IsPullback ((Scheme.Etale.sigmaι W X U).left ≫ v) (X U).hom b U.1.ι := by
      have := (Scheme.isPullback_etaleSigmaι W X U).paste_horiz hv
      rwa [Sigma.ι_desc] at this
    have h₂ := (isPullback_morphismRestrict b U.1).flip
    have := hX U
    have he : (h₁.isoIsPullback _ _ h₂).hom ≫ b ∣_ U.1 = (X U).hom :=
      IsPullback.isoIsPullback_hom_snd _ _ _ _
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsFinite (h₁.isoIsPullback _ _ h₂).hom, he]
    infer_instance
  exact ⟨Scheme.Etale.mk b, this, nonempty_etaleYoneda_iso_of_descent hv hact⟩

end Representability

section Equivalence

variable (S : Scheme.{u})

/-- The category of locally constant sheaves of finite sets on the small étale site of `S`. -/
abbrev LocallyConstantFiniteSheaf : Type _ :=
  ObjectProperty.FullSubcategory
    (Scheme.IsLocallyConstantFiniteSheaf : ObjectProperty (Sheaf S.smallEtaleTopology (Type u)))

/-- The sheaf represented by an étale covering of `S`, as a locally constant sheaf of finite
sets. -/
noncomputable def fetToSheaf : ExposeV.FEt S ⥤ LocallyConstantFiniteSheaf S :=
  ObjectProperty.lift _ (Scheme.finiteEtaleSheaf S)
    Scheme.isLocallyConstantFiniteSheaf_finiteEtaleSheaf

/-- `fetToSheaf` is fully faithful. -/
noncomputable def fetToSheafFullyFaithful : (fetToSheaf S).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    (Scheme.finiteEtaleSheafFullyFaithful S)

instance : (fetToSheaf S).Full := (fetToSheafFullyFaithful S).full

instance : (fetToSheaf S).Faithful := (fetToSheafFullyFaithful S).faithful

instance : (fetToSheaf S).EssSurj where
  mem_essImage F := by
    obtain ⟨V, hV, ⟨i⟩⟩ := exists_etaleYoneda_iso F.property
    exact ⟨⟨V.toComma, ⟨hV, V.prop⟩⟩, ⟨ObjectProperty.isoMk _ i⟩⟩

instance : (fetToSheaf S).IsEquivalence where

/-- SGA 4 IX 2.2: étale coverings of `S` are equivalent to locally constant sheaves of finite
sets on the small étale site of `S`, by sending an étale covering to the sheaf it represents. -/
noncomputable def fetEquivLocallyConstantFiniteSheaf :
    ExposeV.FEt S ≌ LocallyConstantFiniteSheaf S :=
  (fetToSheaf S).asEquivalence

open scoped FintypeCatDiscrete in
/-- For `S` connected with a geometric point `s̄`, locally constant sheaves of finite sets on
`S_et` are equivalent to finite sets with a continuous action of `π₁(S, s̄)` (SGA 1 V.7 and
SGA 4 IX 2.2). -/
noncomputable def contActionEquivLocallyConstantFiniteSheaf [ConnectedSpace S] (Ω : Type u)
    [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ S) :
    ContAction FintypeCat (ExposeV.etaleFundamentalGroup Ω s) ≌ LocallyConstantFiniteSheaf S :=
  (ExposeV.FEt.equivContActionOfHasQuotients Ω s).symm.trans
    (fetEquivLocallyConstantFiniteSheaf S)

end Equivalence

end SGA.SGA1.ExposeXIII
