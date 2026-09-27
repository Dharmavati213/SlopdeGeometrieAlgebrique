/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIX.EtaleEffectiveDescent

/-!
# SGA 1, Exposé IX, §4: effectiveness of descent data of étale schemes is local

Let `g : S' ⟶ S` be universally submersive and `D` a descent datum on an `S'`-scheme `X'`.
An open subset `W` of `X'` is *stable* if `x'·s' ∈ W ↔ x' ∈ W`; `D` then restricts to a descent
datum on `W`. We prove that effectiveness of descent data for étale schemes is local:

* on `X'`: if `X'` is covered by stable opens on which the datum is effective (with étale
  descended schemes), it is effective (`DescentDatum.isEffective_of_iSup_eq_top`). The descended
  schemes are glued along the open subschemes descending the intersections, using the descent of
  morphisms IX.3.3 for the gluing maps and the cocycle condition;
* on `S`: this gives IX.4.3 (`DescentDatum.isEffective_iff_forall_baseChange`).
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc pullback.condition pullback.condition_assoc

/-- The class of étale morphisms, as a `MorphismProperty` (a named constant of this type is
easier to rewrite with than `@Etale`). -/
def etale : MorphismProperty Scheme.{u} := @Etale

lemma etale_iff {X Y : Scheme.{u}} (f : X ⟶ Y) : etale f ↔ Etale f := Iff.rfl

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

namespace DescentDatum

variable (D : DescentDatum g a)

/-- An open subset `W` of `X'` is *stable* under a descent datum if `x'·s' ∈ W ↔ x' ∈ W`. -/
def IsStable (W : X'.Opens) : Prop :=
  D.act ⁻¹ᵁ W = pullback.fst (a ≫ g) g ⁻¹ᵁ W

variable {D}

/-- The inclusion `W ×_S S' ⟶ X' ×_S S'` for an open subset `W` of `X'`. -/
noncomputable abbrev restrictMap (W : X'.Opens) :
    pullback ((W.ι ≫ a) ≫ g) g ⟶ pullback (a ≫ g) g :=
  pullback.map _ _ _ _ W.ι (𝟙 _) (𝟙 _) (by simp) (by simp)

lemma range_restrictMap_act_subset {W : X'.Opens} (hW : D.IsStable W) :
    Set.range (restrictMap W ≫ D.act) ⊆ Set.range W.ι := by
  rintro _ ⟨e, rfl⟩
  have h₁ : restrictMap W e ∈ pullback.fst (a ≫ g) g ⁻¹ᵁ W := by
    change pullback.fst (a ≫ g) g (restrictMap W e) ∈ W
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (pullback.fst ((W.ι ≫ a) ≫ g) g e).2
  rw [← hW] at h₁
  rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
  exact h₁

variable (D) in
/-- The descent datum induced on a stable open subset `W` of `X'`. -/
noncomputable def restrict (W : X'.Opens) (hW : D.IsStable W) : DescentDatum g (W.ι ≫ a) where
  act := IsOpenImmersion.lift W.ι (restrictMap W ≫ D.act) (range_restrictMap_act_subset hW)
  act_comp := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]
    simp only [Category.assoc, D.act_comp]
    simp
  unit := by
    rw [← cancel_mono W.ι, Category.assoc, IsOpenImmersion.lift_fac]
    simp only [Category.id_comp]
    have : pullback.lift (f := (W.ι ≫ a) ≫ g) (g := g) (𝟙 W.toScheme) (W.ι ≫ a) (by simp) ≫
        restrictMap W = W.ι ≫ pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a (by simp) := by
      apply pullback.hom_ext <;> simp
    rw [reassoc_of% this, D.unit, Category.comp_id]
  assoc := by
    rw [← cancel_mono W.ι]
    simp only [Category.assoc, IsOpenImmersion.lift_fac]
    have key := D.act_lift_act
      (pullback.fst (pullback.snd ((W.ι ≫ a) ≫ g) g ≫ g) g ≫ restrictMap W)
      (pullback.snd (pullback.snd ((W.ι ≫ a) ≫ g) g ≫ g) g) (by simp)
    convert key using 1
    · rw [← Category.assoc]
      congr 1
      apply pullback.hom_ext
      · simp [IsOpenImmersion.lift_fac]
      · simp
    · rw [← Category.assoc]
      congr 1
      apply pullback.hom_ext <;> simp

@[reassoc (attr := simp)]
lemma restrict_act_ι (W : X'.Opens) (hW : D.IsStable W) :
    (D.restrict W hW).act ≫ W.ι = restrictMap W ≫ D.act :=
  IsOpenImmersion.lift_fac _ _ _

lemma IsStable.inf {V W : X'.Opens} (hV : D.IsStable V) (hW : D.IsStable W) :
    D.IsStable (V ⊓ W) := by
  simp only [IsStable, Scheme.Hom.preimage_inf] at hV hW ⊢
  rw [hV, hW]

/-- The inclusion `V ×_S S' ⟶ W ×_S S'` for opens `V ≤ W` of `X'`. -/
noncomputable abbrev restrictMapLE {V W : X'.Opens} (h : V ≤ W) :
    pullback ((V.ι ≫ a) ≫ g) g ⟶ pullback ((W.ι ≫ a) ≫ g) g :=
  pullback.map _ _ _ _ (X'.homOfLE h) (𝟙 _) (𝟙 _) (by simp) (by simp)

@[reassoc (attr := simp)]
lemma restrictMapLE_restrictMap {V W : X'.Opens} (h : V ≤ W) :
    restrictMapLE (a := a) (g := g) h ≫ restrictMap W = restrictMap V := by
  apply pullback.hom_ext <;> simp

@[reassoc]
lemma restrict_act_homOfLE {V W : X'.Opens} (hV : D.IsStable V) (hW : D.IsStable W)
    (h : V ≤ W) :
    (D.restrict V hV).act ≫ X'.homOfLE h = restrictMapLE h ≫ (D.restrict W hW).act := by
  rw [← cancel_mono W.ι]
  simp

/-- An effective descent of a descent datum `D` in the class `P`: an `S`-scheme `b : X ⟶ S` with
`P b` and a cartesian square `X' ⟶ X` over `g`, compatible with the descent datum. -/
structure Descent (D : DescentDatum g a) (P : MorphismProperty Scheme.{u}) where
  /-- The descended scheme. -/
  X : Scheme.{u}
  /-- Its structure morphism. -/
  b : X ⟶ S
  /-- The projection `X' ⟶ X`. -/
  v : X' ⟶ X
  prop : P b
  isPullback : IsPullback v a b g
  act_v : D.act ≫ v = pullback.fst (a ≫ g) g ≫ v

lemma isEffective_iff_nonempty_descent (P : MorphismProperty Scheme.{u}) :
    D.IsEffective P ↔ Nonempty (D.Descent P) :=
  ⟨fun ⟨X, b, v, hb, hv, hact⟩ ↦ ⟨⟨X, b, v, hb, hv, hact⟩⟩,
    fun ⟨E⟩ ↦ ⟨E.X, E.b, E.v, E.prop, E.isPullback, E.act_v⟩⟩

variable {P : MorphismProperty Scheme.{u}}

/-- The kernel pair of the projection of an effective descent is `X' ×_S S'`. -/
lemma Descent.isPullback_act (E : D.Descent P) :
    IsPullback D.act (pullback.fst (a ≫ g) g) E.v E.v :=
  DescentDatum.isPullback_act E.isPullback E.act_v

/-- The projection of an effective descent along a universally submersive morphism is universally
submersive. -/
lemma Descent.universallySubmersive_v [UniversallySubmersive g] (E : D.Descent P) :
    UniversallySubmersive E.v :=
  MorphismProperty.of_isPullback E.isPullback.flip ‹_›

/-- A stable open subset of `X'` is the preimage of an open subset of the descended scheme. -/
lemma Descent.exists_opens_preimage_eq [UniversallySubmersive g] (E : D.Descent P)
    {V : X'.Opens} (hV : D.IsStable V) : ∃ O : E.X.Opens, E.v ⁻¹ᵁ O = V := by
  have : UniversallySubmersive E.v := MorphismProperty.of_isPullback E.isPullback.flip ‹_›
  have hK := E.isPullback_act
  have hsat : pullback.fst E.v E.v ⁻¹ᵁ V = pullback.snd E.v E.v ⁻¹ᵁ V := by
    ext z
    obtain ⟨e, rfl⟩ : ∃ e, hK.isoPullback.hom e = z :=
      ⟨hK.isoPullback.inv z, by rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl⟩
    have h₁ := congrArg (fun φ ↦ φ e) hK.isoPullback_hom_fst
    have h₂ := congrArg (fun φ ↦ φ e) hK.isoPullback_hom_snd
    simp only [Scheme.Hom.comp_apply] at h₁ h₂
    change pullback.fst E.v E.v _ ∈ V ↔ pullback.snd E.v E.v _ ∈ V
    rw [h₁, h₂]
    exact SetLike.ext_iff.mp hV e
  obtain ⟨O, hO, -⟩ := exists_unique_opens_preimage_eq E.v V hsat
  exact ⟨O, hO⟩

/-- The open subset of the descended scheme whose preimage is a given stable open. -/
noncomputable def Descent.descOpens [UniversallySubmersive g] (E : D.Descent P) {V : X'.Opens}
    (hV : D.IsStable V) : E.X.Opens :=
  (E.exists_opens_preimage_eq hV).choose

@[simp]
lemma Descent.preimage_descOpens [UniversallySubmersive g] (E : D.Descent P) {V : X'.Opens}
    (hV : D.IsStable V) : E.v ⁻¹ᵁ E.descOpens hV = V :=
  (E.exists_opens_preimage_eq hV).choose_spec

lemma IsStable.restrict {V W : X'.Opens} (hV : D.IsStable V) (hW : D.IsStable W) :
    (D.restrict W hW).IsStable (W.ι ⁻¹ᵁ V) := by
  simp only [IsStable, ← Scheme.Hom.comp_preimage, restrict_act_ι] at hV ⊢
  rw [Scheme.Hom.comp_preimage, hV, ← Scheme.Hom.comp_preimage]
  congr 1
  simp

/-- An effective descent (for étale schemes) of the datum on a stable open `W` restricts to one
on every stable open `V ≤ W`: the descended scheme is the open subscheme of the one of `W`
whose preimage is `V`. -/
noncomputable def Descent.restrictLE [UniversallySubmersive g] {V W : X'.Opens}
    (hV : D.IsStable V) (hW : D.IsStable W) (h : V ≤ W) (E : (D.restrict W hW).Descent etale) :
    (D.restrict V hV).Descent etale :=
  let O := E.descOpens (hV.restrict hW)
  have hO : E.v ⁻¹ᵁ O = W.ι ⁻¹ᵁ V := E.preimage_descOpens _
  have : Etale E.b := E.prop
  have hrange : Set.range (X'.homOfLE h ≫ E.v) ⊆ Set.range O.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change X'.homOfLE h x ∈ E.v ⁻¹ᵁ O
    rw [hO]
    change W.ι (X'.homOfLE h x) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
    exact x.2
  { X := O
    b := O.ι ≫ E.b
    v := IsOpenImmersion.lift O.ι (X'.homOfLE h ≫ E.v) hrange
    prop := (etale_iff _).mpr inferInstance
    isPullback := by
      have h₁ : IsPullback (IsOpenImmersion.lift O.ι (X'.homOfLE h ≫ E.v) hrange)
          (X'.homOfLE h) O.ι E.v :=
        IsOpenImmersion.isPullback _ _ _ _ (IsOpenImmersion.lift_fac _ _ _).symm
          (by rw [Scheme.Opens.opensRange_ι, hO, Scheme.opensRange_homOfLE])
      have := h₁.paste_vert E.isPullback
      simpa using this
    act_v := by
      rw [← cancel_mono O.ι]
      simp only [Category.assoc, IsOpenImmersion.lift_fac]
      rw [restrict_act_homOfLE_assoc hV hW h, E.act_v]
      simp }

@[reassoc (attr := simp)]
lemma Descent.restrictLE_v_ι [UniversallySubmersive g] {V W : X'.Opens}
    (hV : D.IsStable V) (hW : D.IsStable W) (h : V ≤ W) (E : (D.restrict W hW).Descent etale) :
    (E.restrictLE hV hW h).v ≫ (E.descOpens (hV.restrict hW)).ι = X'.homOfLE h ≫ E.v :=
  IsOpenImmersion.lift_fac (E.descOpens (hV.restrict hW)).ι _ _

/-- The comparison `V ×_S S' ⟶ X' ×_S S'` is the base change of the inclusion `V ⟶ X'` along
the first projection. -/
lemma isPullback_restrictMap (V : X'.Opens) :
    IsPullback (restrictMap V) (pullback.fst ((V.ι ≫ a) ≫ g) g) (pullback.fst (a ≫ g) g)
      V.ι := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (a ≫ g) g) (v₁₃ := g) (h₂₂ := a ≫ g) ?_
    (by simp) (IsPullback.of_hasPullback (a ≫ g) g).flip
  simpa using (IsPullback.of_hasPullback ((V.ι ≫ a) ≫ g) g).flip

section Transition

variable [UniversallySubmersive g] {V V' : X'.Opens} {hV : D.IsStable V} {hV' : D.IsStable V'}
  (E : (D.restrict V hV).Descent etale) (E' : (D.restrict V' hV').Descent etale) (h : V ≤ V')

lemma Descent.existsUnique_homOfLE :
    ∃! t : E.X ⟶ E'.X, t ≫ E'.b = E.b ∧ E.v ≫ t = X'.homOfLE h ≫ E'.v := by
  have : Etale E'.b := E'.prop
  refine DescentDatum.existsUnique_hom E.isPullback E.act_v E'.b (X'.homOfLE h ≫ E'.v) ?_ ?_
  · rw [Category.assoc, E'.isPullback.w, E.isPullback.w]
    simp
  · rw [restrict_act_homOfLE_assoc hV hV' h, E'.act_v]
    simp

/-- The morphism between descended schemes induced by an inclusion `V ≤ V'` of stable opens. -/
noncomputable def Descent.homOfLE : E.X ⟶ E'.X :=
  (E.existsUnique_homOfLE E' h).exists.choose

@[reassoc (attr := simp)]
lemma Descent.homOfLE_b : E.homOfLE E' h ≫ E'.b = E.b :=
  (E.existsUnique_homOfLE E' h).exists.choose_spec.1

@[reassoc (attr := simp)]
lemma Descent.v_homOfLE : E.v ≫ E.homOfLE E' h = X'.homOfLE h ≫ E'.v :=
  (E.existsUnique_homOfLE E' h).exists.choose_spec.2

lemma Descent.eq_homOfLE {t : E.X ⟶ E'.X} (ht₁ : t ≫ E'.b = E.b)
    (ht₂ : E.v ≫ t = X'.homOfLE h ≫ E'.v) : t = E.homOfLE E' h :=
  (E.existsUnique_homOfLE E' h).unique ⟨ht₁, ht₂⟩
    ⟨E.homOfLE_b E' h, E.v_homOfLE E' h⟩

lemma Descent.isPullback_homOfLE :
    IsPullback (X'.homOfLE h) E.v E'.v (E.homOfLE E' h) := by
  refine IsPullback.of_right (h₁₂ := V'.ι ≫ a) (v₁₃ := g) (h₂₂ := E'.b) ?_
    (E.v_homOfLE E' h).symm E'.isPullback.flip
  simpa using E.isPullback.flip

instance Descent.isOpenImmersion_homOfLE : IsOpenImmersion (E.homOfLE E' h) := by
  have : Etale E.b := E.prop
  have : Etale E'.b := E'.prop
  have : Etale (E.homOfLE E' h ≫ E'.b) := by rw [E.homOfLE_b]; infer_instance
  have : Etale (E.homOfLE E' h) := Etale.of_comp _ E'.b
  have : Surjective E'.v := MorphismProperty.of_isPullback E'.isPullback.flip inferInstance
  have : UniversallyInjective (E.homOfLE E' h) :=
    of_isPullback_of_descendsAlong (P := @UniversallyInjective) (Q := @Surjective)
      (E.isPullback_homOfLE E' h) inferInstance inferInstance
  exact isOpenImmersion_of_etale_of_universallyInjective _

lemma Descent.preimage_range_homOfLE :
    E'.v ⁻¹' Set.range (E.homOfLE E' h) = Set.range (X'.homOfLE h) := by
  have := Scheme.image_preimage_eq_of_isPullback (E.isPullback_homOfLE E' h).flip Set.univ
  simpa [Set.image_univ] using this.symm

end Transition

section Gluing

variable [UniversallySubmersive g] {ι : Type*} (W : ι → X'.Opens) (hs : ∀ i, D.IsStable (W i))
  (E : ∀ i, (D.restrict (W i) (hs i)).Descent etale)

variable (D) in
/-- (Implementation) The index category for gluing: the stable opens contained in some `W i`,
ordered by inclusion. -/
abbrev GluingIndex : Type u := {V : X'.Opens // D.IsStable V ∧ ∃ i, V ≤ W i}

/-- (Implementation) The chosen descents over the stable opens of `GluingIndex`. -/
noncomputable def gluingDescent (V : GluingIndex D W) : (D.restrict V.1 V.2.1).Descent etale :=
  (E V.2.2.choose).restrictLE V.2.1 (hs _) V.2.2.choose_spec

/-- (Implementation) The diagram of descended schemes, to be glued. -/
@[simps]
noncomputable abbrev gluingFunctor : GluingIndex D W ⥤ Scheme.{u} where
  obj V := (gluingDescent W hs E V).X
  map {V V'} f := (gluingDescent W hs E V).homOfLE (gluingDescent W hs E V') (leOfHom f)
  map_id V := ((gluingDescent W hs E V).eq_homOfLE _ _ (by simp) (by simp)).symm
  map_comp f f' := ((gluingDescent W hs E _).eq_homOfLE _ _ (by simp) (by simp)).symm

instance {V V' : GluingIndex D W} (f : V ⟶ V') :
    IsOpenImmersion ((gluingFunctor W hs E).map f) :=
  Descent.isOpenImmersion_homOfLE _ _ _

/-- (Implementation) The inf of two elements of `GluingIndex`. -/
abbrev GluingIndex.inf (V V' : GluingIndex D W) : GluingIndex D W :=
  ⟨V.1 ⊓ V'.1, V.2.1.inf V'.2.1, V.2.2.choose, inf_le_left.trans V.2.2.choose_spec⟩

lemma gluingDescent_v_homOfLE {V V' : GluingIndex D W} (f : V ⟶ V') :
    (gluingDescent W hs E V).v ≫ (gluingFunctor W hs E).map f =
      X'.homOfLE (leOfHom f) ≫ (gluingDescent W hs E V').v :=
  Descent.v_homOfLE _ _ _

lemma preimage_range_gluingFunctor_map {V V' : GluingIndex D W} (f : V ⟶ V') :
    (gluingDescent W hs E V').v ⁻¹' Set.range ((gluingFunctor W hs E).map f) =
      Set.range (X'.homOfLE (leOfHom f)) :=
  Descent.preimage_range_homOfLE _ _ _

instance : (gluingFunctor W hs E ⋙ Scheme.forget).IsLocallyDirected where
  cond := by
    intro V₁ V₂ V₃ f₁ f₂ x₁ x₂ hx
    change (gluingFunctor W hs E).map f₁ x₁ = (gluingFunctor W hs E).map f₂ x₂ at hx
    change ∃ V₄ f₄₁ f₄₂ x, (gluingFunctor W hs E).map f₄₁ x = x₁ ∧
      (gluingFunctor W hs E).map f₄₂ x = x₂
    have := (gluingDescent W hs E V₃).universallySubmersive_v
    obtain ⟨w, hw⟩ := (gluingDescent W hs E V₃).v.surjective ((gluingFunctor W hs E).map f₁ x₁)
    have hw₁ : w ∈ (gluingDescent W hs E V₃).v ⁻¹' Set.range ((gluingFunctor W hs E).map f₁) :=
      ⟨x₁, hw.symm⟩
    have hw₂ : w ∈ (gluingDescent W hs E V₃).v ⁻¹' Set.range ((gluingFunctor W hs E).map f₂) :=
      ⟨x₂, (hw.trans hx).symm⟩
    rw [preimage_range_gluingFunctor_map] at hw₁ hw₂
    obtain ⟨w₁, rfl⟩ := hw₁
    obtain ⟨w₂, hw₂⟩ := hw₂
    have e₁ : V₃.1.ι (X'.homOfLE (leOfHom f₁) w₁) = w₁.1 := by
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    have e₂ : V₃.1.ι (X'.homOfLE (leOfHom f₂) w₂) = w₂.1 := by
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    have hw₁₂ : w₁.1 = w₂.1 := by rw [← e₁, ← hw₂, e₂]
    let V₄ := GluingIndex.inf W V₁ V₂
    let w₄ : V₄.1.toScheme := ⟨w₁.1, w₁.2, hw₁₂ ▸ w₂.2⟩
    have h₄₁ : X'.homOfLE (inf_le_left : V₄.1 ≤ V₁.1) w₄ = w₁ := by
      apply V₁.1.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      rfl
    have h₄₂ : X'.homOfLE (inf_le_right : V₄.1 ≤ V₂.1) w₄ = w₂ := by
      apply V₂.1.ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
      exact hw₁₂
    have k (V V' : GluingIndex D W) (f : V ⟶ V') (y : V.1.toScheme) :
        (gluingFunctor W hs E).map f ((gluingDescent W hs E V).v y) =
          (gluingDescent W hs E V').v (X'.homOfLE (leOfHom f) y) := by
      have := congrArg (fun φ ↦ φ y) (gluingDescent_v_homOfLE W hs E f)
      exact this
    refine ⟨V₄, homOfLE (show V₄.1 ≤ V₁.1 from inf_le_left),
      homOfLE (show V₄.1 ≤ V₂.1 from inf_le_right),
      (gluingDescent W hs E V₄).v w₄, ?_, ?_⟩
    · rw [k, h₄₁]
      apply ((gluingFunctor W hs E).map f₁).isOpenEmbedding.injective
      rw [k, hw]
    · rw [k, h₄₂]
      apply ((gluingFunctor W hs E).map f₂).isOpenEmbedding.injective
      rw [k, hw₂, ← hx, hw]

/-- (Implementation) The glued scheme. -/
noncomputable abbrev gluedX : Scheme.{u} := colimit (gluingFunctor W hs E)

/-- (Implementation) The structure morphism of the glued scheme. -/
noncomputable def gluedB : gluedX W hs E ⟶ S :=
  colimit.desc _
    { pt := S
      ι :=
        { app V := (gluingDescent W hs E V).b
          naturality V V' f := by
            simp only [Descent.homOfLE_b, Functor.const_obj_map,
              Category.comp_id, Functor.const_obj_obj] } }

@[reassoc (attr := simp)]
lemma ι_gluedB (V : GluingIndex D W) :
    colimit.ι (gluingFunctor W hs E) V ≫ gluedB W hs E = (gluingDescent W hs E V).b :=
  colimit.ι_desc _ _

lemma homOfLE_v_ι {V V' : GluingIndex D W} (h : V.1 ≤ V'.1) :
    X'.homOfLE h ≫ (gluingDescent W hs E V').v ≫ colimit.ι (gluingFunctor W hs E) V' =
      (gluingDescent W hs E V).v ≫ colimit.ι (gluingFunctor W hs E) V := by
  rw [← Category.assoc, ← gluingDescent_v_homOfLE W hs E (homOfLE h : V ⟶ V'), Category.assoc,
    colimit.w]

variable (hW : ⨆ i, W i = ⊤)

omit [UniversallySubmersive g] in
include hs hW in
lemma isOpenCover_gluingIndex : TopologicalSpace.IsOpenCover (fun V : GluingIndex D W ↦ V.1) :=
  eq_top_iff.mpr (hW.symm.trans_le (iSup_le fun i ↦ le_iSup_of_le ⟨W i, hs i, i, le_rfl⟩ le_rfl))

lemma gluedV_compat (V V' : GluingIndex D W) :
    pullback.fst V.1.ι V'.1.ι ≫ (gluingDescent W hs E V).v ≫ colimit.ι (gluingFunctor W hs E) V =
      pullback.snd V.1.ι V'.1.ι ≫ (gluingDescent W hs E V').v ≫
        colimit.ι (gluingFunctor W hs E) V' := by
  have hP := isPullback_opens_inf V.1 V'.1
  rw [← cancel_epi hP.isoPullback.hom, hP.isoPullback_hom_fst_assoc,
    hP.isoPullback_hom_snd_assoc]
  exact (homOfLE_v_ι W hs E (V' := V) (V := GluingIndex.inf W V V') inf_le_left).trans
    (homOfLE_v_ι W hs E (V' := V') (V := GluingIndex.inf W V V') inf_le_right).symm

/-- (Implementation) The projection `X' ⟶ glued`, glued from the projections of the pieces. -/
noncomputable def gluedV : X' ⟶ gluedX W hs E :=
  (X'.openCoverOfIsOpenCover _ (isOpenCover_gluingIndex W hs hW)).glueMorphisms
    (fun V ↦ (gluingDescent W hs E V).v ≫ colimit.ι (gluingFunctor W hs E) V)
    (fun V V' ↦ gluedV_compat W hs E V V')

@[reassoc (attr := simp)]
lemma ι_gluedV (V : GluingIndex D W) :
    V.1.ι ≫ gluedV W hs E hW =
      (gluingDescent W hs E V).v ≫ colimit.ι (gluingFunctor W hs E) V :=
  Scheme.Cover.ι_glueMorphisms (X'.openCoverOfIsOpenCover _ (isOpenCover_gluingIndex W hs hW)) _ _ V

lemma preimage_opensRange_ι_gluedV (V : GluingIndex D W) :
    gluedV W hs E hW ⁻¹ᵁ (colimit.ι (gluingFunctor W hs E) V).opensRange = V.1 := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨i, hi⟩ : ∃ i, x ∈ W i := by
      have : x ∈ ⨆ i, W i := hW.symm ▸ trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using this
    let V₀ : GluingIndex D W := ⟨W i, hs i, i, le_rfl⟩
    have hx : gluedV W hs E hW x =
        colimit.ι (gluingFunctor W hs E) V₀ ((gluingDescent W hs E V₀).v ⟨x, hi⟩) :=
      congrArg (fun φ ↦ φ ⟨x, hi⟩) (ι_gluedV W hs E hW V₀)
    rw [hx] at hy
    obtain ⟨k, fk, fk₀, z, -, hz₀⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff (gluingFunctor W hs E)).mp hy
    have hmem : (⟨x, hi⟩ : V₀.1.toScheme) ∈
        (gluingDescent W hs E V₀).v ⁻¹' Set.range ((gluingFunctor W hs E).map fk₀) :=
      ⟨z, hz₀⟩
    rw [preimage_range_gluingFunctor_map] at hmem
    obtain ⟨w, hw⟩ := hmem
    have : x = w.1 := by
      have := congrArg V₀.1.ι hw
      rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι] at this
      exact this.symm
    rw [this]
    exact leOfHom fk w.2
  · intro hx
    exact ⟨(gluingDescent W hs E V).v ⟨x, hx⟩,
      (congrArg (fun φ ↦ φ ⟨x, hx⟩) (ι_gluedV W hs E hW V)).symm⟩

lemma isPullback_v_ι_gluedV (V : GluingIndex D W) :
    IsPullback (gluingDescent W hs E V).v V.1.ι (colimit.ι (gluingFunctor W hs E) V)
      (gluedV W hs E hW) :=
  IsOpenImmersion.isPullback _ _ _ _ (ι_gluedV W hs E hW V)
    (by rw [preimage_opensRange_ι_gluedV, Scheme.Opens.opensRange_ι])

lemma isPullback_gluedV : IsPullback (gluedV W hs E hW) a (gluedB W hs E) g := by
  refine Scheme.isPullback_of_openCover _ _ _ _
    (Scheme.IsLocallyDirected.openCover (gluingFunctor W hs E)) fun (V : GluingIndex D W) ↦ ?_
  change IsPullback (pullback.snd (gluedV W hs E hW) (colimit.ι (gluingFunctor W hs E) V))
    (pullback.fst (gluedV W hs E hW) (colimit.ι (gluingFunctor W hs E) V) ≫ a)
    (colimit.ι (gluingFunctor W hs E) V ≫ gluedB W hs E) g
  have h3 := (isPullback_v_ι_gluedV W hs E hW V).flip
  refine (gluingDescent W hs E V).isPullback.of_iso h3.isoPullback (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact (ι_gluedB W hs E V).symm
  · simp

lemma act_gluedV :
    D.act ≫ gluedV W hs E hW = pullback.fst (a ≫ g) g ≫ gluedV W hs E hW := by
  refine Scheme.hom_ext_of_forall _ _ fun e ↦ ?_
  obtain ⟨i, hi⟩ : ∃ i, pullback.fst (a ≫ g) g e ∈ W i := by
    have : pullback.fst (a ≫ g) g e ∈ ⨆ i, W i := hW.symm ▸ trivial
    simpa [TopologicalSpace.Opens.mem_iSup] using this
  let V : GluingIndex D W := ⟨W i, hs i, i, le_rfl⟩
  refine ⟨pullback.fst (a ≫ g) g ⁻¹ᵁ V.1, hi, ?_⟩
  have hP := (isPullback_morphismRestrict (pullback.fst (a ≫ g) g) V.1).flip
  obtain ⟨φ, hφ⟩ : ∃ φ, (pullback.fst (a ≫ g) g ⁻¹ᵁ V.1).ι = φ ≫ restrictMap V.1 :=
    ⟨_, (hP.isoIsPullback_hom_fst _ _ (isPullback_restrictMap V.1)).symm⟩
  rw [hφ]
  simp only [Category.assoc]
  congr 1
  rw [← restrict_act_ι_assoc V.1 V.2.1, ι_gluedV,
    reassoc_of% (gluingDescent W hs E V).act_v, ← ι_gluedV W hs E hW V]
  simp

set_option backward.isDefEq.respectTransparency false in
lemma etale_gluedB : Etale (gluedB W hs E) := by
  refine IsZariskiLocalAtSource.of_openCover
    (Scheme.IsLocallyDirected.openCover (gluingFunctor W hs E)) fun V ↦ ?_
  change Etale (colimit.ι (gluingFunctor W hs E) V ≫ gluedB W hs E)
  rw [ι_gluedB]
  exact (gluingDescent W hs E V).prop

/-- (Implementation) The descent obtained by gluing. -/
noncomputable def gluedDescent : D.Descent etale where
  X := gluedX W hs E
  b := gluedB W hs E
  v := gluedV W hs E hW
  prop := etale_gluedB W hs E
  isPullback := isPullback_gluedV W hs E hW
  act_v := act_gluedV W hs E hW

end Gluing

section OpenBase

variable (U : S.Opens)

lemma isStable_preimage : D.IsStable ((a ≫ g) ⁻¹ᵁ U) := by
  simp only [IsStable, ← Scheme.Hom.comp_preimage]
  congr 1
  rw [reassoc_of% D.act_comp]
  simp

variable {U} {W : X'.Opens} (hW : W = (a ≫ g) ⁻¹ᵁ U)
include hW

lemma isStable_of_eq_preimage : D.IsStable W := hW ▸ D.isStable_preimage U

lemma range_ι_comp_subset : Set.range (W.ι ≫ a ≫ g) ⊆ Set.range U.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  have : x.1 ∈ (a ≫ g) ⁻¹ᵁ U := hW ▸ x.2
  exact this

/-- (Implementation) The morphism `W ⟶ U` induced by `a ≫ g`. -/
noncomputable def restrictToOpen : W.toScheme ⟶ U :=
  IsOpenImmersion.lift U.ι (W.ι ≫ a ≫ g) (range_ι_comp_subset hW)

@[reassoc (attr := simp)]
lemma restrictToOpen_ι : restrictToOpen hW ≫ U.ι = W.ι ≫ a ≫ g :=
  IsOpenImmersion.lift_fac _ _ _

/-- (Implementation) The isomorphism `W = (a ≫ g)⁻¹ U ≅ X' ×_{S'} (S' ×_S U)`. -/
noncomputable def preimageToPullback : W.toScheme ⟶ pullback a (pullback.fst g U.ι) :=
  pullback.lift W.ι (pullback.lift (W.ι ≫ a) (restrictToOpen hW) (by simp)) (by simp)

@[reassoc (attr := simp)]
lemma preimageToPullback_fst :
    preimageToPullback hW ≫ pullback.fst a (pullback.fst g U.ι) = W.ι := by
  simp [preimageToPullback]

@[reassoc (attr := simp)]
lemma preimageToPullback_snd_fst :
    preimageToPullback hW ≫ pullback.snd a (pullback.fst g U.ι) ≫ pullback.fst g U.ι =
      W.ι ≫ a := by
  simp [preimageToPullback]

@[reassoc (attr := simp)]
lemma preimageToPullback_snd_snd :
    preimageToPullback hW ≫ pullback.snd a (pullback.fst g U.ι) ≫ pullback.snd g U.ι =
      restrictToOpen hW := by
  simp [preimageToPullback]

instance : IsIso (preimageToPullback hW) := by
  have hr : Set.range (pullback.fst a (pullback.fst g U.ι)) ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι, hW]
    change (pullback.fst a (pullback.fst g U.ι) ≫ a ≫ g) x ∈ U
    rw [pullback.condition_assoc, pullback.condition, ← Category.assoc, Scheme.Hom.comp_apply]
    exact (_ : U.toScheme).2
  refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
  · rw [← cancel_mono W.ι]
    simp
  · apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext
      · simp [pullback.condition]
      · rw [← cancel_mono U.ι]
        simp [pullback.condition]

/-- (Implementation) Comparison of `W ×_S S'` with the corresponding object of the base-changed
datum. -/
noncomputable def preimageToPullbackAct :
    pullback ((W.ι ≫ a) ≫ g) g ⟶
      pullback (pullback.snd a (pullback.fst g U.ι) ≫ pullback.snd g U.ι) (pullback.snd g U.ι) :=
  pullback.lift (pullback.fst _ _ ≫ preimageToPullback hW)
    (pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ restrictToOpen hW) (by
      have := pullback.condition (f := (W.ι ≫ a) ≫ g) (g := g)
      simp only [Category.assoc] at this ⊢
      rw [restrictToOpen_ι, this]))
    (by simp)

lemma preimageToPullbackAct_baseChangeAux :
    preimageToPullbackAct hW ≫ baseChangeAux g a U.ι = restrictMap W := by
  apply pullback.hom_ext
  · simp [preimageToPullbackAct, baseChangeAux_fst]
  · simp [preimageToPullbackAct, baseChangeAux_snd]

lemma preimageToPullbackAct_act :
    preimageToPullbackAct hW ≫ (D.baseChange U.ι).act =
      (D.restrict _ (D.isStable_of_eq_preimage hW)).act ≫ preimageToPullback hW := by
  apply pullback.hom_ext
  · have h₁ : (D.baseChange U.ι).act ≫ pullback.fst a (pullback.fst g U.ι) =
        baseChangeAux g a U.ι ≫ D.act := pullback.lift_fst _ _ _
    simp only [Category.assoc]
    rw [h₁, reassoc_of% preimageToPullbackAct_baseChangeAux, preimageToPullback_fst,
      restrict_act_ι]
  · have h₂ : (D.baseChange U.ι).act ≫ pullback.snd a (pullback.fst g U.ι) =
        pullback.snd _ _ := (D.baseChange U.ι).act_comp
    simp only [Category.assoc]
    rw [h₂]
    apply pullback.hom_ext
    · simp only [preimageToPullbackAct, Category.assoc, pullback.lift_snd_assoc,
        pullback.lift_fst, preimageToPullback_snd_fst, restrict_act_ι_assoc, D.act_comp]
      simp
    · rw [← cancel_mono U.ι]
      simp only [preimageToPullbackAct, Category.assoc, pullback.lift_snd,
        preimageToPullback_snd_snd_assoc, restrictToOpen_ι, restrict_act_ι_assoc,
        reassoc_of% D.act_comp]
      simpa using pullback.condition (f := (W.ι ≫ a) ≫ g) (g := g)

lemma preimageToPullbackAct_fst :
    preimageToPullbackAct hW ≫ pullback.fst _ _ = pullback.fst _ _ ≫ preimageToPullback hW :=
  pullback.lift_fst _ _ _

/-- Effectiveness over an open `U` of `S` (for the base-changed datum) gives effectiveness of the
induced datum on the stable open `W = (a ≫ g)⁻¹ U` of `X'`. -/
lemma isEffective_restrict_of_isEffective_baseChange
    (h : (D.baseChange U.ι).IsEffective @Etale) :
    (D.restrict _ (D.isStable_of_eq_preimage hW)).IsEffective @Etale := by
  obtain ⟨XU, bU, vU, hb, hv, hact⟩ := h
  have : Etale bU := hb
  have hv' : IsPullback vU (pullback.snd a (pullback.fst g U.ι) ≫ pullback.fst g U.ι)
      (bU ≫ U.ι) g :=
    hv.paste_vert (IsPullback.of_hasPullback g U.ι).flip
  refine ⟨XU, bU ≫ U.ι, preimageToPullback hW ≫ vU, (inferInstance : Etale (bU ≫ U.ι)), ?_, ?_⟩
  · refine hv'.of_iso (asIso (preimageToPullback hW)).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ?_ ?_ ?_ ?_
    · simp
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv, IsIso.eq_inv_comp]
      exact preimageToPullback_snd_fst hW
    · simp
    · simp
  · rw [← reassoc_of% (preimageToPullbackAct_act hW), hact,
      reassoc_of% (preimageToPullbackAct_fst hW)]

end OpenBase

/-- Effectiveness of descent data for étale schemes is local on `X'`: if `X'` is covered by
stable opens `W i` such that the induced descent data are effective (with étale descended
schemes), then the descent datum is effective. The descended scheme is glued from the descended
schemes of the stable opens contained in some `W i`. -/
theorem isEffective_of_iSup_eq_top [UniversallySubmersive g] {ι : Type*} (W : ι → X'.Opens)
    (hW : ⨆ i, W i = ⊤) (hs : ∀ i, D.IsStable (W i))
    (hE : ∀ i, (D.restrict (W i) (hs i)).IsEffective @Etale) : D.IsEffective @Etale :=
  (isEffective_iff_nonempty_descent (D := D) etale).mpr
    ⟨gluedDescent W hs (fun i ↦ ((isEffective_iff_nonempty_descent etale).mp (hE i)).some) hW⟩

/-! ### Quasi-compactness and separation of the descended scheme -/

set_option backward.isDefEq.respectTransparency false in
/-- Quasi-separatedness descends along surjective quasi-compact morphisms. -/
instance quasiSeparated_descendsAlong :
    DescendsAlong @QuasiSeparated (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) := by
  have := quasiCompact_descendsAlong.{u}
  rw [quasiSeparated_eq_diagonal_is_quasiCompact]
  exact instDescendsAlongDiagonalOfRespectsIsoOfIsStableUnderBaseChange _ _

/-- Along a surjective quasi-compact `g`, if `X'` is étale of finite presentation over `S'`, an
effective descent with étale descended scheme is effective for étale morphisms of finite
presentation. -/
lemma isEffective_etaleFinitePresentation_of_etale [Surjective g] [QuasiCompact g]
    (ha : etaleFinitePresentation a) (h : D.IsEffective @Etale) :
    D.IsEffective etaleFinitePresentation := by
  obtain ⟨X, b, v, hb, hv, hact⟩ := h
  obtain ⟨⟨-, ha₁⟩, ha₂⟩ := ha
  have hg : (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g := ⟨‹_›, ‹_›⟩
  exact ⟨X, b, v, ⟨⟨hb, quasiCompact_descendsAlong.of_isPullback hv.flip hg ha₁⟩,
    quasiSeparated_descendsAlong.of_isPullback hv.flip hg ha₂⟩, hv, hact⟩

lemma isEffective_etaleFinitePresentation_iff [Surjective g] [QuasiCompact g]
    (ha : etaleFinitePresentation a) :
    D.IsEffective etaleFinitePresentation ↔ D.IsEffective @Etale :=
  ⟨fun ⟨X, b, v, hb, hv, hact⟩ ↦ ⟨X, b, v, hb.1.1, hv, hact⟩,
    isEffective_etaleFinitePresentation_of_etale ha⟩

/-- Along a universally submersive quasi-compact `g`, if `X'` is étale, separated and of finite
type over `S'`, an effective descent with étale descended scheme is effective for étale separated
morphisms of finite type. -/
lemma isEffective_etaleSeparatedFiniteType_of_etale [UniversallySubmersive g] [QuasiCompact g]
    (ha : etaleSeparatedFiniteType a) (h : D.IsEffective @Etale) :
    D.IsEffective etaleSeparatedFiniteType := by
  obtain ⟨X, b, v, hb, hv, hact⟩ := h
  obtain ⟨⟨-, ha₁⟩, ha₂⟩ := ha
  have hg : (@Surjective ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) g := ⟨inferInstance, ‹_›⟩
  exact ⟨X, b, v, ⟨⟨hb, isSeparated_descendsAlong.of_isPullback hv.flip ‹_› ha₁⟩,
    quasiCompact_descendsAlong.of_isPullback hv.flip hg ha₂⟩, hv, hact⟩

lemma isEffective_etaleSeparatedFiniteType_iff [UniversallySubmersive g] [QuasiCompact g]
    (ha : etaleSeparatedFiniteType a) :
    D.IsEffective etaleSeparatedFiniteType ↔ D.IsEffective @Etale :=
  ⟨fun ⟨X, b, v, hb, hv, hact⟩ ↦ ⟨X, b, v, hb.1.1, hv, hact⟩,
    isEffective_etaleSeparatedFiniteType_of_etale ha⟩

/-- IX.4.3: let `g : S' ⟶ S` be universally submersive, `X'` an `S'`-scheme with a descent datum
relative to `g`, and `(Sᵢ)` an open cover of `S`. The datum is effective (for étale schemes) if
and only if, for every `i`, the induced datum on `X' ×_S Sᵢ` relative to `S' ×_S Sᵢ ⟶ Sᵢ` is.
(SGA assumes `X'` étale over `S'`; this is not needed, since the descended schemes are required
to be étale.) -/
theorem isEffective_iff_forall_baseChange [UniversallySubmersive g] {ι : Type*}
    (U : ι → S.Opens) (hU : ⨆ i, U i = ⊤) :
    D.IsEffective @Etale ↔ ∀ i, (D.baseChange (U i).ι).IsEffective @Etale := by
  refine ⟨fun h i ↦ h.baseChange _, fun h ↦ ?_⟩
  refine D.isEffective_of_iSup_eq_top (fun i ↦ (a ≫ g) ⁻¹ᵁ U i) ?_
    (fun i ↦ D.isStable_preimage (U i))
    (fun i ↦ D.isEffective_restrict_of_isEffective_baseChange rfl (h i))
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]

/-- The "inverse" `(x', s') ↦ (x'·s', a(x'))` of the groupoid action. -/
noncomputable def swapAct : pullback (a ≫ g) g ⟶ pullback (a ≫ g) g :=
  pullback.lift D.act (pullback.fst (a ≫ g) g ≫ a) (by
    rw [reassoc_of% D.act_comp, Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma swapAct_fst : D.swapAct ≫ pullback.fst (a ≫ g) g = D.act := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma swapAct_snd : D.swapAct ≫ pullback.snd (a ≫ g) g = pullback.fst (a ≫ g) g ≫ a :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
lemma swapAct_act : D.swapAct ≫ D.act = pullback.fst (a ≫ g) g := by
  have := D.act_lift_act (𝟙 _) (pullback.fst (a ≫ g) g ≫ a) (by simp)
  simp only [Category.id_comp] at this
  have h₁ : D.swapAct = pullback.lift (f := a ≫ g) (g := g) D.act (pullback.fst (a ≫ g) g ≫ a)
      (by rw [reassoc_of% D.act_comp, Category.assoc, pullback.condition]) := rfl
  rw [h₁, this]
  have h₂ : pullback.lift (f := a ≫ g) (g := g) (pullback.fst (a ≫ g) g)
      (pullback.fst (a ≫ g) g ≫ a) (by simp) =
      pullback.fst (a ≫ g) g ≫ pullback.lift (f := a ≫ g) (g := g) (𝟙 X') a (by simp) := by
    apply pullback.hom_ext <;> simp
  rw [h₂, Category.assoc, D.unit, Category.comp_id]

lemma swapAct_swapAct : D.swapAct ≫ D.swapAct = 𝟙 _ := by
  apply pullback.hom_ext
  · simp
  · simp [D.act_comp]

instance : IsIso D.swapAct := ⟨D.swapAct, D.swapAct_swapAct, D.swapAct_swapAct⟩

/-- The action is quasi-compact if `g` is: it is the first projection composed with the
isomorphism `swapAct`. -/
instance [QuasiCompact g] : QuasiCompact D.act := by
  rw [← D.swapAct_fst]
  infer_instance

/-! ### Radicial morphisms: every open subset is stable -/

set_option backward.isDefEq.respectTransparency.types false in
/-- If `g` is radicial, the action of a descent datum is the first projection on points: the
first projection `X' ×_S S' ⟶ X'` is injective, and `x'·a(x') = x'`. -/
lemma act_apply_eq_fst_apply [UniversallyInjective g] (e : ↥(pullback (a ≫ g) g)) :
    D.act e = pullback.fst (a ≫ g) g e := by
  have : UniversallyInjective (pullback.fst (a ≫ g) g) := MorphismProperty.pullback_fst _ _ ‹_›
  set x' := pullback.fst (a ≫ g) g e
  have he : diag g a x' = e := (pullback.fst (a ≫ g) g).injective (by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl)
  rw [← he, ← Scheme.Hom.comp_apply, D.unit]
  rfl

/-- VIII.7.5, key step (used in IX.4.10, IX.4.11): if `g` is radicial, every open subset of `X'`
is stable under any descent datum. -/
lemma isStable_of_universallyInjective [UniversallyInjective g] (W : X'.Opens) : D.IsStable W := by
  ext e
  change D.act e ∈ W ↔ pullback.fst (a ≫ g) g e ∈ W
  rw [act_apply_eq_fst_apply]

end DescentDatum

/-! ### IX.4.10 and IX.4.11 from IX.4.7 and IX.4.1 -/

set_option backward.isDefEq.respectTransparency false in
/-- The reduction in the proofs of IX.4.10 and IX.4.11: let `g` be radicial and universally
submersive, and suppose that for every affine open `U` of `S`, every descent datum relative to
`S' ×_S U ⟶ U` on an affine étale `S' ×_S U`-scheme is effective. Then every descent datum on an
étale `S'`-scheme is effective. (Every open subset is stable since `g` is radicial, so one glues
the descents of affine pieces, first over `X'` and then over `S`.) -/
theorem DescentDatum.isEffective_of_universallyInjective_of_affine {S' S X' : Scheme.{u}}
    {g : S' ⟶ S} [UniversallyInjective g] [UniversallySubmersive g] {a : X' ⟶ S'} [Etale a]
    (D : DescentDatum g a)
    (H : ∀ (U : S.affineOpens) ⦃W : Scheme.{u}⦄ [IsAffine W] (w : W ⟶ pullback g U.1.ι) [Etale w]
      (E : DescentDatum (pullback.snd g U.1.ι) w), E.IsEffective @Etale) :
    D.IsEffective @Etale := by
  refine (D.isEffective_iff_forall_baseChange (fun U : S.affineOpens ↦ U.1)
    (iSup_affineOpens_eq_top S)).mpr fun U ↦ ?_
  set DU := D.baseChange U.1.ι
  have : UniversallyInjective (pullback.snd g U.1.ι) := MorphismProperty.pullback_snd _ _ ‹_›
  refine DU.isEffective_of_iSup_eq_top (fun V : (pullback a (pullback.fst g U.1.ι)).affineOpens ↦
    V.1) (iSup_affineOpens_eq_top _) (fun V ↦ DU.isStable_of_universallyInjective V.1)
    fun V ↦ ?_
  have : IsAffine V.1 := V.2
  exact H U _ (DU.restrict V.1 _)

end SGA.SGA1.ExposeIX
