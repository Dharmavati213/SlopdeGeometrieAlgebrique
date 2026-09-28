/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeIX.EffectiveGluing
import SGA.Foundations.SpecStalkLimit
import SGA.Foundations.EtaleSpreadingOut

/-!
# SGA 1, Exposé IX, 4.4 and 4.5: effectiveness near a point

IX.4.4 (`DescentDatum.exists_isEffective_baseChange_iff`): for `g : S' ⟶ S` of finite
presentation and universally submersive, and `X'` étale of finite presentation over `S'` with a
descent datum, the datum is effective over a neighbourhood of `x ∈ S` iff it is effective over
`Spec 𝒪_{S,x}`. IX.4.5, first assertion (`DescentDatum.isEffective_iff_forall_fromSpecStalk`): the
datum is effective iff it is effective over every `Spec 𝒪_{S,x}`.

The proof spreads out the descended scheme over `Spec 𝒪_{S,x}` to a neighbourhood of `x`
("an easy general sorites on preschemes defined over an inductive limit of rings", EGA IV 8):
`Spec 𝒪_{S,x}` is the limit of the affine open neighbourhoods of `x`
(`AlgebraicGeometry.Scheme.isLimitPreimageConeOfIsPullback`), affine étale schemes spread out
(`AlgebraicGeometry.Scheme.exists_etale_isPullback_fromSpecStalkOfMem`), and so do morphisms and
their equalities (mathlib's `Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation`,
`Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType`) and quasi-compact opens
(`exists_preimage_eq`, `exists_map_preimage_eq_map_preimage`, `exists_map_eq_top`).

* `DescentDatum.exists_isEffective_restrict_of_isAffine`: the case of an affine descended scheme:
  the projection, the inverse of the comparison map `X' ⟶ X ×_S S'`, and the compatibility with
  the descent datum spread out.
* `DescentDatum.exists_isEffective_piece`: for an affine open `Y` of the descended scheme, the
  stable open `v⁻¹(Y)` spreads out to a stable open of `X'` near `x` on which the datum is
  effective (reduction to the affine case).
* `DescentDatum.exists_isEffective_restrict_preimage`: the pieces are glued.

We also prove transport lemmas for effective descents: along isomorphisms of descent data,
between nested restrictions, and between restriction and base change.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc pullback.condition pullback.condition_assoc

/-- A cartesian square stays cartesian after composing both lower maps with a monomorphism. -/
lemma isPullback_comp_mono {C : Type*} [Category C] {P X Y Z W : C} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (m : Z ⟶ W) [Mono m] :
    IsPullback fst snd (f ≫ m) (g ≫ m) :=
  IsPullback.of_isLimit' ⟨by rw [reassoc_of% h.w]⟩ (PullbackCone.IsLimit.mk _
    (fun s ↦ h.lift s.fst s.snd (by rw [← cancel_mono m]; simpa using s.condition))
    (fun s ↦ by simp) (fun s ↦ by simp)
    (fun s l h₁ h₂ ↦ h.hom_ext (by simpa using h₁) (by simpa using h₂)))

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

/-! ### Transport of effective descents -/

namespace DescentDatum

section Transport

variable {X₁ X₂ : Scheme.{u}} {a₁ : X₁ ⟶ S'} {a₂ : X₂ ⟶ S'} {D₁ : DescentDatum g a₁}
  {D₂ : DescentDatum g a₂} {P : MorphismProperty Scheme.{u}}

/-- An isomorphism of `S'`-schemes compatible with descent data transports effective descents. -/
noncomputable def Descent.ofIso (E : D₂.Descent P) (e : X₁ ≅ X₂) (he : e.hom ≫ a₂ = a₁)
    (hact : D₁.act ≫ e.hom = pullback.map (a₁ ≫ g) g (a₂ ≫ g) g e.hom (𝟙 _) (𝟙 _)
      (by simp [← he]) (by simp) ≫ D₂.act) :
    D₁.Descent P where
  X := E.X
  b := E.b
  v := e.hom ≫ E.v
  prop := E.prop
  isPullback := E.isPullback.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
    (by simp [← he]) (by simp) (by simp)
  act_v := by
    simp only [← Category.assoc]
    rw [hact]
    simp [E.act_v]

/-- Effectiveness is invariant under isomorphisms of descent data. -/
lemma isEffective_iff_of_iso (e : X₁ ≅ X₂) (he : e.hom ≫ a₂ = a₁)
    (hact : D₁.act ≫ e.hom = pullback.map (a₁ ≫ g) g (a₂ ≫ g) g e.hom (𝟙 _) (𝟙 _)
      (by simp [← he]) (by simp) ≫ D₂.act) :
    D₁.IsEffective P ↔ D₂.IsEffective P := by
  constructor
  · intro h
    obtain ⟨E⟩ := (isEffective_iff_nonempty_descent P).mp h
    have he' : e.inv ≫ a₁ = a₂ := by rw [← he, Iso.inv_hom_id_assoc]
    refine (isEffective_iff_nonempty_descent P).mpr ⟨E.ofIso e.symm he' ?_⟩
    have hm : pullback.map (a₂ ≫ g) g (a₁ ≫ g) g e.inv (𝟙 _) (𝟙 _) (by simp [← he'])
        (by simp) ≫ pullback.map (a₁ ≫ g) g (a₂ ≫ g) g e.hom (𝟙 _) (𝟙 _) (by simp [← he])
        (by simp) = 𝟙 _ := by
      apply pullback.hom_ext <;> simp
    change D₂.act ≫ e.inv = _
    rw [← Category.id_comp D₂.act, ← hm, Category.assoc, Category.assoc, ← reassoc_of% hact,
      Iso.hom_inv_id]
    simp only [Category.comp_id]
    rfl
  · intro h
    obtain ⟨E⟩ := (isEffective_iff_nonempty_descent P).mp h
    exact (isEffective_iff_nonempty_descent P).mpr ⟨E.ofIso e he hact⟩

end Transport

variable (D : DescentDatum g a)

/-- The restriction of an effective descent to the stable open `v⁻¹(Y)`, for an open `Y` of the
descended scheme; the descended scheme is `Y`. -/
lemma Descent.isStable_preimage {P : MorphismProperty Scheme.{u}} (E : D.Descent P)
    (Y : E.X.Opens) : D.IsStable (E.v ⁻¹ᵁ Y) := by
  simp only [IsStable, ← Scheme.Hom.comp_preimage, E.act_v]

/-- The restriction of an effective étale descent to the stable open `v⁻¹(Y)`, for an open `Y`
of the descended scheme; the descended scheme is `Y`. -/
noncomputable def Descent.restrictOpen (E : D.Descent etale) (Y : E.X.Opens) :
    (D.restrict (E.v ⁻¹ᵁ Y) (Descent.isStable_preimage D E Y)).Descent etale where
  X := Y
  b := Y.ι ≫ E.b
  v := E.v ∣_ Y
  prop := have : Etale E.b := E.prop; (etale_iff _).mpr inferInstance
  isPullback := by
    simpa using (isPullback_morphismRestrict E.v Y).paste_vert E.isPullback
  act_v := by
    rw [← cancel_mono Y.ι]
    simp only [Category.assoc, morphismRestrict_ι, restrict_act_ι_assoc, E.act_v]
    simp

variable {D} in
/-- (Implementation) The isomorphism `W₀.ι⁻¹ W ≅ W` for opens `W ≤ W₀`. -/
noncomputable def nestedIso {W W₀ : X'.Opens} (hle : W ≤ W₀) :
    (W₀.ι ⁻¹ᵁ W).toScheme ≅ W.toScheme :=
  IsOpenImmersion.isoOfRangeEq ((W₀.ι ⁻¹ᵁ W).ι ≫ W₀.ι) W.ι (by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι,
      Scheme.Opens.range_ι]
    exact Set.image_preimage_eq_of_subset
      (by rw [Scheme.Opens.range_ι]; exact SetLike.coe_subset_coe.mpr hle))

@[reassoc (attr := simp)]
lemma nestedIso_hom_ι {W W₀ : X'.Opens} (hle : W ≤ W₀) :
    (nestedIso hle).hom ≫ W.ι = (W₀.ι ⁻¹ᵁ W).ι ≫ W₀.ι :=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

lemma nestedIso_act {W W₀ : X'.Opens} (hW : D.IsStable W) (hW₀ : D.IsStable W₀)
    (hle : W ≤ W₀) :
    ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ W) (hW.restrict hW₀)).act ≫ (nestedIso hle).hom =
      pullback.map _ g _ g (nestedIso hle).hom (𝟙 _) (𝟙 _) (by simp) (by simp) ≫
        (D.restrict W hW).act := by
  rw [← cancel_mono W.ι]
  simp only [Category.assoc, nestedIso_hom_ι, restrict_act_ι, restrict_act_ι_assoc]
  simp only [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

/-- The restriction of a restriction is a restriction. -/
lemma isEffective_nestedRestrict_iff {P : MorphismProperty Scheme.{u}} {W W₀ : X'.Opens}
    (hW : D.IsStable W) (hW₀ : D.IsStable W₀) (hle : W ≤ W₀) :
    ((D.restrict W₀ hW₀).restrict (W₀.ι ⁻¹ᵁ W) (hW.restrict hW₀)).IsEffective P ↔
      (D.restrict W hW).IsEffective P :=
  isEffective_iff_of_iso (nestedIso hle) (by simp) (D.nestedIso_act hW hW₀ hle)

section BaseChangeRestrict

variable {T : Scheme.{u}} (t : T ⟶ S) (O : X'.Opens)

/-- (Implementation) The map `O ×_{S'} (S' ×_S T) ⟶ (X' ×_S T) ∩ pr⁻¹(O)`. -/
noncomputable def baseChangeRestrictHom :
    pullback (O.ι ≫ a) (pullback.fst g t) ⟶
      (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).toScheme :=
  IsOpenImmersion.lift (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι
    (pullback.map (O.ι ≫ a) (pullback.fst g t) a (pullback.fst g t) O.ι (𝟙 _) (𝟙 _)
      (by simp) (by simp)) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (_ ≫ pullback.fst a (pullback.fst g t)) y ∈ O
      rw [pullback.lift_fst, Scheme.Hom.comp_apply]
      exact (pullback.fst (O.ι ≫ a) (pullback.fst g t) y).2)

@[reassoc (attr := simp)]
lemma baseChangeRestrictHom_ι :
    baseChangeRestrictHom t O ≫ (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι =
      pullback.map (O.ι ≫ a) (pullback.fst g t) a (pullback.fst g t) O.ι (𝟙 _) (𝟙 _)
        (by simp) (by simp) :=
  IsOpenImmersion.lift_fac _ _ _

/-- (Implementation) The map `(X' ×_S T) ∩ pr⁻¹(O) ⟶ O`. -/
noncomputable def baseChangeRestrictToO :
    (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).toScheme ⟶ O.toScheme :=
  IsOpenImmersion.lift O.ι ((pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι ≫
    pullback.fst a (pullback.fst g t)) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact y.2)

@[reassoc (attr := simp)]
lemma baseChangeRestrictToO_ι :
    baseChangeRestrictToO t O ≫ O.ι = (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι ≫
      pullback.fst a (pullback.fst g t) :=
  IsOpenImmersion.lift_fac _ _ _

/-- (Implementation) The isomorphism `O ×_{S'} (S' ×_S T) ≅ (X' ×_S T) ∩ pr⁻¹(O)`. -/
noncomputable def baseChangeRestrictIso :
    pullback (O.ι ≫ a) (pullback.fst g t) ≅
      (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).toScheme where
  hom := baseChangeRestrictHom t O
  inv := pullback.lift (baseChangeRestrictToO t O)
    ((pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι ≫ pullback.snd a (pullback.fst g t)) (by
      rw [baseChangeRestrictToO_ι_assoc]
      simp [pullback.condition])
  hom_inv_id := by
    apply pullback.hom_ext
    · rw [← cancel_mono O.ι]
      simp
    · simp
  inv_hom_id := by
    rw [← cancel_mono (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι]
    apply pullback.hom_ext
    · simp
    · simp

variable {O} (hO : D.IsStable O)
include hO

/-- The preimage in `X' ×_S T` of a stable open subset of `X'` is stable. -/
lemma isStable_baseChange_preimage :
    (D.baseChange t).IsStable (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O) := by
  have h₁ : (D.baseChange t).act ≫ pullback.fst a (pullback.fst g t) =
      baseChangeAux g a t ≫ D.act := pullback.lift_fst _ _ _
  have h₂ := baseChangeAux_fst (g := g) (a := a) t
  simp only [IsStable, ← Scheme.Hom.comp_preimage, h₁, ← h₂] at hO ⊢
  rw [Scheme.Hom.comp_preimage, hO, ← Scheme.Hom.comp_preimage]

lemma baseChangeRestrictIso_act :
    ((D.restrict O hO).baseChange t).act ≫ (baseChangeRestrictIso t O).hom =
      pullback.map _ _ _ _ (baseChangeRestrictIso t O).hom (𝟙 _) (𝟙 _)
        (by simp [baseChangeRestrictIso]) (by simp) ≫
        ((D.baseChange t).restrict (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O)
          (D.isStable_baseChange_preimage t hO)).act := by
  rw [← cancel_mono (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O).ι]
  apply pullback.hom_ext
  · have h₁ : ((D.restrict O hO).baseChange t).act ≫ pullback.fst (O.ι ≫ a)
        (pullback.fst g t) = baseChangeAux g (O.ι ≫ a) t ≫ (D.restrict O hO).act :=
      pullback.lift_fst _ _ _
    have h₂ : (D.baseChange t).act ≫ pullback.fst a (pullback.fst g t) =
        baseChangeAux g a t ≫ D.act := pullback.lift_fst _ _ _
    simp only [baseChangeRestrictIso, Category.assoc, baseChangeRestrictHom_ι_assoc,
      pullback.lift_fst, restrict_act_ι_assoc, h₂]
    simp only [← Category.assoc, h₁]
    simp only [Category.assoc, restrict_act_ι]
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [baseChangeAux]
  · have h₃ := ((D.restrict O hO).baseChange t).act_comp
    have h₄ := ((D.baseChange t).restrict (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O)
      (D.isStable_baseChange_preimage t hO)).act_comp
    simp only [baseChangeRestrictIso, Category.assoc, baseChangeRestrictHom_ι_assoc,
      pullback.lift_snd, Category.comp_id, h₃, h₄]

/-- Base change commutes with restriction to stable opens: an effective descent of the restriction
of `D.baseChange t` to the preimage of `O` gives one of the base change of the restriction of `D`
to `O`. -/
noncomputable def Descent.ofBaseChangeRestrict {P : MorphismProperty Scheme.{u}}
    (E : ((D.baseChange t).restrict (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O)
      (D.isStable_baseChange_preimage t hO)).Descent P) :
    ((D.restrict O hO).baseChange t).Descent P :=
  E.ofIso (baseChangeRestrictIso t O) (by simp [baseChangeRestrictIso])
    (D.baseChangeRestrictIso_act t hO)

/-- Base change commutes with restriction to stable opens. -/
lemma isEffective_baseChange_restrict_iff {P : MorphismProperty Scheme.{u}} :
    ((D.restrict O hO).baseChange t).IsEffective P ↔
      ((D.baseChange t).restrict (pullback.fst a (pullback.fst g t) ⁻¹ᵁ O)
        (D.isStable_baseChange_preimage t hO)).IsEffective P :=
  isEffective_iff_of_iso (baseChangeRestrictIso t O) (by simp [baseChangeRestrictIso])
    (D.baseChangeRestrictIso_act t hO)

end BaseChangeRestrict



/-- Transport of a descent along an equality of stable opens. -/
noncomputable def Descent.congrOpen {P : MorphismProperty Scheme.{u}} {W W' : X'.Opens}
    (hW : D.IsStable W) (hW' : D.IsStable W') (h : W = W') (E : (D.restrict W hW).Descent P) :
    (D.restrict W' hW').Descent P := by
  subst h
  exact E

lemma Descent.congrOpen_X {P : MorphismProperty Scheme.{u}} {W W' : X'.Opens}
    (hW : D.IsStable W) (hW' : D.IsStable W') (h : W = W') (E : (D.restrict W hW).Descent P) :
    (Descent.congrOpen D hW hW' h E).X = E.X := by
  subst h
  rfl

/-- The restriction to the whole of `X'` is the datum itself. -/
lemma isEffective_restrict_top_iff {P : MorphismProperty Scheme.{u}} (hT : D.IsStable ⊤) :
    (D.restrict ⊤ hT).IsEffective P ↔ D.IsEffective P :=
  isEffective_iff_of_iso X'.topIso rfl (by
      change (D.restrict ⊤ hT).act ≫ (⊤ : X'.Opens).ι = _
      rw [restrict_act_ι]
      congr 1)

variable {D} in
lemma isEffective_restrict_congr {P : MorphismProperty Scheme.{u}} {W W' : X'.Opens}
    (hW : D.IsStable W) (h : W = W') :
    (D.restrict W hW).IsEffective P ↔ (D.restrict W' (h ▸ hW)).IsEffective P := by
  subst h
  rfl

/-- Effectiveness is local on stable open subsets: if a stable open `W₀` is covered by stable
opens on which the datum is effective (with étale descended schemes), it is effective on `W₀`. -/
theorem isEffective_restrict_of_iSup_eq [UniversallySubmersive g] {ι : Type*} {W₀ : X'.Opens}
    (h₀ : D.IsStable W₀) (W : ι → X'.Opens) (hW : ⨆ i, W i = W₀) (hs : ∀ i, D.IsStable (W i))
    (hE : ∀ i, (D.restrict (W i) (hs i)).IsEffective @Etale) :
    (D.restrict W₀ h₀).IsEffective @Etale := by
  have hle (i : ι) : W i ≤ W₀ := hW ▸ le_iSup W i
  refine (D.restrict W₀ h₀).isEffective_of_iSup_eq_top (fun i ↦ W₀.ι ⁻¹ᵁ W i) ?_
    (fun i ↦ (hs i).restrict h₀)
    (fun i ↦ (D.isEffective_nestedRestrict_iff (hs i) h₀ (hle i)).mpr (hE i))
  rw [← Scheme.Hom.preimage_iSup, hW]
  exact eq_top_iff.mpr fun x _ ↦ x.2

end DescentDatum

section Squares

variable {T : Scheme.{u}} (t : T ⟶ S)

/-- `X' ×_{S'} (S' ×_S T)` is `X' ×_S T`. -/
lemma isPullback_baseChange_obj :
    IsPullback (pullback.fst a (pullback.fst g t))
      (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (a ≫ g) t :=
  (IsPullback.of_hasPullback a (pullback.fst g t)).paste_vert (IsPullback.of_hasPullback g t)

variable (g a) in
/-- The object `X'' = X' ×_S S'` of the base-changed datum is `X'' ×_S T`. -/
lemma isPullback_baseChangeAux :
    IsPullback (DescentDatum.baseChangeAux g a t)
      (pullback.snd (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t) ≫
        pullback.snd g t)
      (pullback.snd (a ≫ g) g ≫ g) t := by
  -- `X''_T = X'_T ×_T S'_T = S' ×_S X'_T`
  have h₁ : IsPullback
      (pullback.snd (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t) ≫
        pullback.fst g t)
      (pullback.fst (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t)) g
      ((pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) ≫ t) :=
    (IsPullback.of_hasPullback (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t)
      (pullback.snd g t)).flip.paste_horiz (IsPullback.of_hasPullback g t)
  -- hence the square over `X'_T ⟶ X'` is cartesian
  have h₂ : IsPullback (DescentDatum.baseChangeAux g a t)
      (pullback.fst (pullback.snd a (pullback.fst g t) ≫ pullback.snd g t) (pullback.snd g t))
      (pullback.fst (a ≫ g) g) (pullback.fst a (pullback.fst g t)) := by
    refine IsPullback.of_right (h₁₂ := pullback.snd (a ≫ g) g) (v₁₃ := g) (h₂₂ := a ≫ g) ?_
      (by simp [DescentDatum.baseChangeAux]) (IsPullback.of_hasPullback (a ≫ g) g).flip
    convert h₁ using 1
    · simp [DescentDatum.baseChangeAux]
    · simp [pullback.condition]
  have h₃ := h₂.paste_vert (isPullback_baseChange_obj t (g := g) (a := a))
  convert h₃ using 1
  · simp [pullback.condition]
  · simp [pullback.condition]

end Squares

set_option backward.isDefEq.respectTransparency false in
/-- If the descent datum is effective on the stable open `(a ≫ g)⁻¹(U)` of `X'`, its base change
along any `t : T ⟶ S` with image in `U` is effective. -/
lemma DescentDatum.isEffective_baseChange_of_isEffective_restrict (D : DescentDatum g a)
    {T : Scheme.{u}} (t : T ⟶ S) (U : S.Opens)
    (ht : ∀ z, t z ∈ U)
    (h : (D.restrict ((a ≫ g) ⁻¹ᵁ U) (D.isStable_preimage U)).IsEffective @Etale) :
    (D.baseChange t).IsEffective @Etale := by
  have h₁ := h.baseChange t
  have h₂ := (D.isEffective_baseChange_restrict_iff t (D.isStable_preimage U)).mp h₁
  have htop : pullback.fst a (pullback.fst g t) ⁻¹ᵁ ((a ≫ g) ⁻¹ᵁ U) = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    change (pullback.fst a (pullback.fst g t) ≫ a ≫ g) z ∈ U
    rw [(isPullback_baseChange_obj t (g := g) (a := a)).w, Scheme.Hom.comp_apply]
    exact ht _
  have h₃ := (DescentDatum.isEffective_restrict_congr _ htop).mp h₂
  exact (DescentDatum.isEffective_restrict_top_iff _ _).mp h₃

section Stability

variable [QuasiCompact g]

set_option backward.isDefEq.respectTransparency false in
/-- If a quasi-compact open `O` of `X'` has a stable preimage in `X' ×_S Spec 𝒪_{S,x}`, then
`O ∩ (a ≫ g)⁻¹(V)` is stable for some affine neighbourhood `V` of `x`. -/
lemma DescentDatum.exists_isStable_inf (D : DescentDatum g a) (x : S) {O : X'.Opens}
    {i : S.AffineNhds x} (hO : IsCompact (O : Set X')) (hOi : O ≤ (a ≫ g) ⁻¹ᵁ i.1)
    (hst : (D.baseChange (S.fromSpecStalk x)).IsStable
      (pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ⁻¹ᵁ O)) :
    ∃ V : S.AffineNhds x, V.1 ≤ i.1 ∧ D.IsStable (O ⊓ (a ≫ g) ⁻¹ᵁ V.1) := by
  have hX'' := isPullback_baseChangeAux g a (S.fromSpecStalk x)
  have hlim := Scheme.isLimitPreimageConeOfIsPullback hX''
  let R : (pullback (a ≫ g) g).Opens := (pullback.snd (a ≫ g) g ≫ g) ⁻¹ᵁ i.1
  have hA' : IsCompact (D.act ⁻¹' (O : Set X')) :=
    QuasiCompact.isCompact_preimage (f := D.act) _ O.2 hO
  have hB' : IsCompact (pullback.fst (a ≫ g) g ⁻¹' (O : Set X')) :=
    QuasiCompact.isCompact_preimage (f := pullback.fst (a ≫ g) g) _ O.2 hO
  have hAR : D.act ⁻¹' (O : Set X') ⊆ Set.range R.ι := by
    intro e he
    rw [Scheme.Opens.range_ι]
    change (pullback.snd (a ≫ g) g ≫ g) e ∈ i.1
    rw [← reassoc_of% D.act_comp, Scheme.Hom.comp_apply]
    exact hOi he
  have hBR : pullback.fst (a ≫ g) g ⁻¹' (O : Set X') ⊆ Set.range R.ι := by
    intro e he
    rw [Scheme.Opens.range_ι]
    change (pullback.snd (a ≫ g) g ≫ g) e ∈ i.1
    rw [← pullback.condition, Scheme.Hom.comp_apply]
    exact hOi he
  have hA : IsCompact ((R.ι ⁻¹ᵁ (D.act ⁻¹ᵁ O) : R.toScheme.Opens) : Set R.toScheme) :=
    (R.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff hAR).mpr hA'
  have hB : IsCompact ((R.ι ⁻¹ᵁ (pullback.fst (a ≫ g) g ⁻¹ᵁ O) : R.toScheme.Opens) :
      Set R.toScheme) :=
    (R.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff hBR).mpr hB'
  have hAB : (Scheme.preimageConeOfIsPullback x _ hX'').π.app i ⁻¹ᵁ
      (R.ι ⁻¹ᵁ (D.act ⁻¹ᵁ O)) = (Scheme.preimageConeOfIsPullback x _ hX'').π.app i ⁻¹ᵁ
      (R.ι ⁻¹ᵁ (pullback.fst (a ≫ g) g ⁻¹ᵁ O)) := by
    simp only [← Scheme.Hom.comp_preimage]
    rw [Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX'',
      Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX'']
    have h₁ : DescentDatum.baseChangeAux g a (S.fromSpecStalk x) ≫ D.act =
        (D.baseChange (S.fromSpecStalk x)).act ≫
          pullback.fst a (pullback.fst g (S.fromSpecStalk x)) :=
      (pullback.lift_fst _ _ _).symm
    rw [h₁, DescentDatum.baseChangeAux_fst, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage]
    exact hst
  obtain ⟨j, f, hj⟩ := exists_map_preimage_eq_map_preimage _ _ hlim hA hB hAB
  refine ⟨j, leOfHom f, ?_⟩
  ext e
  change D.act e ∈ O ⊓ (a ≫ g) ⁻¹ᵁ j.1 ↔ pullback.fst (a ≫ g) g e ∈ O ⊓ (a ≫ g) ⁻¹ᵁ j.1
  have hpe : (a ≫ g) (D.act e) = (pullback.snd (a ≫ g) g ≫ g) e := by
    rw [← Scheme.Hom.comp_apply, reassoc_of% D.act_comp]
  have hpe' : (a ≫ g) (pullback.fst (a ≫ g) g e) = (pullback.snd (a ≫ g) g ≫ g) e := by
    rw [← Scheme.Hom.comp_apply, pullback.condition]
  by_cases he : (pullback.snd (a ≫ g) g ≫ g) e ∈ j.1
  · have key := SetLike.ext_iff.mp hj ⟨e, he⟩
    have hmap : R.ι ((S.preimageDiagram x (pullback.snd (a ≫ g) g ≫ g)).map f ⟨e, he⟩) = e := by
      rw [← Scheme.Hom.comp_apply, Scheme.preimageDiagram_map, Scheme.homOfLE_ι]
      rfl
    change (S.preimageDiagram x _).map f ⟨e, he⟩ ∈ R.ι ⁻¹ᵁ (D.act ⁻¹ᵁ O) ↔
      (S.preimageDiagram x _).map f ⟨e, he⟩ ∈ R.ι ⁻¹ᵁ (pullback.fst (a ≫ g) g ⁻¹ᵁ O) at key
    change D.act (R.ι _) ∈ O ↔ pullback.fst (a ≫ g) g (R.ι _) ∈ O at key
    rw [hmap] at key
    change D.act e ∈ O ∧ (a ≫ g) (D.act e) ∈ j.1 ↔
      pullback.fst (a ≫ g) g e ∈ O ∧ (a ≫ g) (pullback.fst (a ≫ g) g e) ∈ j.1
    rw [hpe, hpe', key]
  · change D.act e ∈ O ∧ (a ≫ g) (D.act e) ∈ j.1 ↔
      pullback.fst (a ≫ g) g e ∈ O ∧ (a ≫ g) (pullback.fst (a ≫ g) g e) ∈ j.1
    rw [hpe, hpe']
    exact ⟨fun h ↦ absurd h.2 he, fun h ↦ absurd h.2 he⟩

end Stability

section AffineCase

variable [LocallyOfFinitePresentation g] [QuasiCompact g] [QuasiSeparated g] [Etale a]

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.4, sufficiency, when the descended scheme over `Spec 𝒪_{S,x}` is affine: the descended
scheme spreads out to an affine open neighbourhood `V` of `x`, and so do the projection
`X' ⟶ X`, the inverse of the comparison map `X' ⟶ X ×_S S'` (making the square cartesian) and the
compatibility with the descent datum. (Universal submersiveness of `g` is not needed here.)
The quasi-compactness of `X'` is only required over some affine neighbourhood `W₀` of `x`. -/
theorem DescentDatum.exists_isEffective_restrict_of_isAffine (D : DescentDatum g a) (x : S)
    (W₀ : S.AffineNhds x)
    (hc : ∀ V : S.AffineNhds x, V.1 ≤ W₀.1 → IsCompact (((a ≫ g) ⁻¹ᵁ V.1 : X'.Opens) : Set X'))
    (hq : QuasiSeparatedSpace ((a ≫ g) ⁻¹ᵁ W₀.1).toScheme)
    (E : (D.baseChange (S.fromSpecStalk x)).Descent etale) [IsAffine E.X] :
    ∃ V : S.AffineNhds x, V.1 ≤ W₀.1 ∧
      (D.restrict ((a ≫ g) ⁻¹ᵁ V.1) (D.isStable_preimage V.1)).IsEffective @Etale := by
  have hEb : Etale E.b := E.prop
  -- spread out the descended scheme
  obtain ⟨U₀, Z, qZ, e, hZa, hqZ, hZ⟩ := Scheme.exists_etale_isPullback_fromSpecStalkOfMem x E.b
  let f : Z ⟶ S := qZ ≫ U₀.1.ι
  have hZ' : IsPullback e E.b f (S.fromSpecStalk x) := by
    have := isPullback_comp_mono hZ U₀.1.ι
    rwa [Scheme.Opens.fromSpecStalkOfMem_ι] at this
  -- the limit square for `X'`
  have hX := isPullback_baseChange_obj (S.fromSpecStalk x) (g := g) (a := a)
  have hqX : E.v ≫ E.b = pullback.snd a (pullback.fst g (S.fromSpecStalk x)) ≫
      pullback.snd g (S.fromSpecStalk x) :=
    E.isPullback.w
  -- work over the neighbourhoods contained in `W₁ ≤ W₀, U₀`
  obtain ⟨W₁, hW₁₀, hW₁U⟩ := exists_le_le W₀ U₀
  have hlimX : IsLimit ((Scheme.preimageConeOfIsPullback x (a ≫ g) hX).whisker
      (Over.forget W₁)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget W₁) _).symm
      (Scheme.isLimitPreimageConeOfIsPullback hX)
  have _ (j : Over W₁) : CompactSpace ((Over.forget W₁ ⋙ S.preimageDiagram x (a ≫ g)).obj j) :=
    isCompact_iff_compactSpace.mp (hc j.left ((leOfHom j.hom).trans hW₁₀))
  have _ (j : Over W₁) :
      QuasiSeparatedSpace ((Over.forget W₁ ⋙ S.preimageDiagram x (a ≫ g)).obj j) :=
    (X'.homOfLE ((a ≫ g).preimage_mono
      ((leOfHom j.hom).trans hW₁₀))).isOpenEmbedding.quasiSeparatedSpace
  have _ {j₁ j₂ : Over W₁} (φ : j₁ ⟶ j₂) :
      IsAffineHom ((Over.forget W₁ ⋙ S.preimageDiagram x (a ≫ g)).map φ) :=
    inferInstanceAs (IsAffineHom ((S.preimageDiagram x (a ≫ g)).map ((Over.forget W₁).map φ)))
  have hvf : (E.v ≫ e) ≫ f = pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ≫ a ≫ g := by
    rw [Category.assoc E.v e f, hZ'.w, reassoc_of% hqX]
    simp [hX.w]
  -- spreading out `v`
  obtain ⟨j₁, v₁, hv₁, hv₁f⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over.forget W₁ ⋙ S.preimageDiagram x (a ≫ g))
    (Functor.whiskerLeft (Over.forget W₁) (S.preimageDiagramTo x (a ≫ g) (a ≫ g))) f _ hlimX
    (E.v ≫ e) (by
      ext V
      simp only [NatTrans.comp_app, Cone.whisker_π, Functor.whiskerLeft_app,
        Scheme.preimageDiagramTo_app, Functor.const_obj_obj, Functor.const_map_app]
      rw [Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX, hvf])
  let V₁ := j₁.left
  have hv₁ : (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₁ ≫ v₁ = E.v ≫ e := hv₁
  have hv₁f : v₁ ≫ f = ((a ≫ g) ⁻¹ᵁ V₁.1).ι ≫ a ≫ g := hv₁f
  -- the limit square for `Q = Z ×_S S'`
  let pQ : pullback f g ⟶ S := pullback.fst f g ≫ f
  let kQ : pullback a (pullback.fst g (S.fromSpecStalk x)) ⟶ pullback f g :=
    pullback.lift (E.v ≫ e) (pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ≫ a)
      (by rw [hvf, Category.assoc])
  have hQ : IsPullback kQ (pullback.snd a (pullback.fst g (S.fromSpecStalk x)) ≫
      pullback.snd g (S.fromSpecStalk x)) pQ (S.fromSpecStalk x) := by
    have h₁ : IsPullback kQ E.v (pullback.fst f g) e := by
      refine IsPullback.of_right (h₁₂ := pullback.snd f g) (v₁₃ := g) (h₂₂ := f) ?_
        (by simp [kQ]) (IsPullback.of_hasPullback f g).flip
      have := E.isPullback.flip.paste_horiz (IsPullback.of_hasPullback g (S.fromSpecStalk x))
      convert this using 1
      · simp [kQ, pullback.condition]
      · exact hZ'.w
    have := h₁.paste_vert hZ'
    rwa [hqX] at this
  -- spreading out the inverse `Q ⟶ X'`
  have hlimQ : IsLimit ((Scheme.preimageConeOfIsPullback x pQ hQ).whisker (Over.forget W₁)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget W₁) _).symm
      (Scheme.isLimitPreimageConeOfIsPullback hQ)
  have hQaff (j : Over W₁) : IsAffineOpen (qZ ⁻¹ᵁ (U₀.1.ι ⁻¹ᵁ j.left.1)) := by
    have hV : IsAffineOpen (U₀.1.ι ⁻¹ᵁ j.left.1) := by
      rw [← Scheme.opensRange_homOfLE ((leOfHom j.hom).trans hW₁U)]
      exact isAffineOpen_opensRange _
    exact hV.preimage qZ
  have _ (j : Over W₁) : CompactSpace ((Over.forget W₁ ⋙ S.preimageDiagram x pQ).obj j) :=
    isCompact_iff_compactSpace.mp (QuasiCompact.isCompact_preimage (f := pullback.fst f g) _
      (qZ ⁻¹ᵁ (U₀.1.ι ⁻¹ᵁ j.left.1)).2 (hQaff j).isCompact)
  have _ (j : Over W₁) :
      QuasiSeparatedSpace ((Over.forget W₁ ⋙ S.preimageDiagram x pQ).obj j) :=
    quasiSeparatedSpace_of_quasiSeparated (pQ ∣_ j.left.1)
  have _ {j₁ j₂ : Over W₁} (φ : j₁ ⟶ j₂) :
      IsAffineHom ((Over.forget W₁ ⋙ S.preimageDiagram x pQ).map φ) :=
    inferInstanceAs (IsAffineHom ((S.preimageDiagram x pQ).map ((Over.forget W₁).map φ)))
  obtain ⟨j₂, χ, hχ, hχa⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (Over.forget W₁ ⋙ S.preimageDiagram x pQ)
    (Functor.whiskerLeft (Over.forget W₁) (S.preimageDiagramTo x pQ (pullback.snd f g))) a _
    hlimQ (pullback.fst a (pullback.fst g (S.fromSpecStalk x))) (by
      ext j
      simp only [NatTrans.comp_app, Cone.whisker_π, Functor.whiskerLeft_app,
        Scheme.preimageDiagramTo_app, Functor.const_obj_obj, Functor.const_map_app]
      rw [Scheme.preimageConeOfIsPullback_π_app_ι_assoc hQ]
      simp [kQ])
  -- the maps `c : W ⟶ Q` and `χ : Q ⟶ W` at a common level `V₃`
  obtain ⟨V₃, h31, h32⟩ := exists_le_le V₁ j₂.left
  have hV₃W : V₃.1 ≤ W₁.1 := h31.trans (leOfHom j₁.hom)
  let W₃ : X'.Opens := (a ≫ g) ⁻¹ᵁ V₃.1
  let QV₃ : (pullback f g).Opens := pQ ⁻¹ᵁ V₃.1
  let v₃ : W₃.toScheme ⟶ Z := X'.homOfLE ((a ≫ g).preimage_mono h31) ≫ v₁
  have hv₃f : v₃ ≫ f = W₃.ι ≫ a ≫ g := by
    simp only [v₃, Category.assoc, hv₁f, Scheme.homOfLE_ι_assoc]
  have hπv₃ : (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₃ ≫ v₃ = E.v ≫ e := by
    rw [← hv₁, ← (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).w (homOfLE h31)]
    simp [v₃]
  let c₃ : W₃.toScheme ⟶ pullback f g := pullback.lift v₃ (W₃.ι ≫ a) (by rw [hv₃f, Category.assoc])
  have hc₃ : c₃ ≫ pQ = W₃.ι ≫ a ≫ g := by simp [c₃, pQ]
  have hπc₃ : (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₃ ≫ c₃ = kQ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, c₃, kQ, pullback.lift_fst]
      exact hπv₃
    · simp only [Category.assoc, c₃, kQ, pullback.lift_snd]
      rw [← Category.assoc, Scheme.preimageConeOfIsPullback_π_app_ι hX]
  let χ₃ : QV₃.toScheme ⟶ X' := (pullback f g).homOfLE (pQ.preimage_mono h32) ≫ χ
  have hχ₃a : χ₃ ≫ a = QV₃.ι ≫ pullback.snd f g := by
    simp only [χ₃, Category.assoc, hχa, Functor.whiskerLeft_app, Scheme.preimageDiagramTo_app]
    simp
  have hπχ₃ : (Scheme.preimageConeOfIsPullback x pQ hQ).π.app V₃ ≫ χ₃ =
      pullback.fst a (pullback.fst g (S.fromSpecStalk x)) := by
    have hχ' : (Scheme.preimageConeOfIsPullback x pQ hQ).π.app j₂.left ≫ χ =
        pullback.fst a (pullback.fst g (S.fromSpecStalk x)) := hχ
    rw [← hχ', ← (Scheme.preimageConeOfIsPullback x pQ hQ).w (homOfLE h32), Category.assoc]
  have hχ₃ag : χ₃ ≫ a ≫ g = QV₃.ι ≫ pQ := by
    rw [reassoc_of% hχ₃a, ← pullback.condition]
  let c₃' : W₃.toScheme ⟶ QV₃.toScheme := IsOpenImmersion.lift QV₃.ι c₃ (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (c₃ ≫ pQ) w ∈ V₃.1
    rw [hc₃]
    exact w.2)
  have hc₃' : c₃' ≫ QV₃.ι = c₃ := IsOpenImmersion.lift_fac _ _ _
  let χ₃' : QV₃.toScheme ⟶ W₃.toScheme := IsOpenImmersion.lift W₃.ι χ₃ (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (χ₃ ≫ a ≫ g) y ∈ V₃.1
    rw [hχ₃ag]
    exact y.2)
  have hχ₃' : χ₃' ≫ W₃.ι = χ₃ := IsOpenImmersion.lift_fac _ _ _
  have hπc₃' : (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₃ ≫ c₃' =
      (Scheme.preimageConeOfIsPullback x pQ hQ).π.app V₃ := by
    rw [← cancel_mono QV₃.ι, Category.assoc, hc₃', hπc₃,
      Scheme.preimageConeOfIsPullback_π_app_ι hQ]
  have hπχ₃' : (Scheme.preimageConeOfIsPullback x pQ hQ).π.app V₃ ≫ χ₃' =
      (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₃ := by
    rw [← cancel_mono W₃.ι, Category.assoc, hχ₃', hπχ₃,
      Scheme.preimageConeOfIsPullback_π_app_ι hX]
  -- `χ ∘ c = id` near `x`
  obtain ⟨j₄, h43, h4⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (Over.forget W₁ ⋙ S.preimageDiagram x (a ≫ g))
    (Functor.whiskerLeft (Over.forget W₁) (S.preimageDiagramTo x (a ≫ g) a)) a _ hlimX
    (i := Over.mk (homOfLE hV₃W))
    (c₃' ≫ χ₃) W₃.ι
    (by
      rw [Category.assoc, hχ₃a, reassoc_of% hc₃']
      simp only [c₃, pullback.lift_snd]
      rfl)
    rfl
    (by
      change (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₃ ≫ c₃' ≫ χ₃ =
        (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₃ ≫ W₃.ι
      rw [reassoc_of% hπc₃', hπχ₃, Scheme.preimageConeOfIsPullback_π_app_ι hX])
  let V₄ := j₄.left
  -- `c ∘ χ = id` near `x`
  obtain ⟨j₅, h53, h5⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (Over.forget W₁ ⋙ S.preimageDiagram x pQ)
    (Functor.whiskerLeft (Over.forget W₁) (S.preimageDiagramTo x pQ pQ)) pQ _ hlimQ
    (i := Over.mk (homOfLE hV₃W))
    (χ₃' ≫ c₃) QV₃.ι
    (by
      change QV₃.ι ≫ pQ = (χ₃' ≫ c₃) ≫ pQ
      rw [Category.assoc, hc₃, reassoc_of% hχ₃', hχ₃ag])
    (by rfl)
    (by
      change (Scheme.preimageConeOfIsPullback x pQ hQ).π.app V₃ ≫ χ₃' ≫ c₃ =
        (Scheme.preimageConeOfIsPullback x pQ hQ).π.app V₃ ≫ QV₃.ι
      rw [reassoc_of% hπχ₃', hπc₃, Scheme.preimageConeOfIsPullback_π_app_ι hQ])
  -- compatibility with the descent datum, through `X'' = X' ×_S S'`
  obtain ⟨V₆, h64, h65⟩ := exists_le_le V₄ j₅.left
  have hX'' := isPullback_baseChangeAux g a (S.fromSpecStalk x)
  have hlimX'' : IsLimit ((Scheme.preimageConeOfIsPullback x _ hX'').whisker (Over.forget W₁)) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget W₁) _).symm
      (Scheme.isLimitPreimageConeOfIsPullback hX'')
  have _ (j : Over W₁) : CompactSpace
      ((Over.forget W₁ ⋙ S.preimageDiagram x (pullback.snd (a ≫ g) g ≫ g)).obj j) := by
    have h := QuasiCompact.isCompact_preimage (f := pullback.fst (a ≫ g) g) _
      ((a ≫ g) ⁻¹ᵁ j.left.1).2 (hc j.left ((leOfHom j.hom).trans hW₁₀))
    have e : (pullback.snd (a ≫ g) g ≫ g) ⁻¹ᵁ j.left.1 =
        pullback.fst (a ≫ g) g ⁻¹ᵁ ((a ≫ g) ⁻¹ᵁ j.left.1) := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition]
    change CompactSpace ((pullback.snd (a ≫ g) g ≫ g) ⁻¹ᵁ j.left.1).toScheme
    rw [e]
    exact isCompact_iff_compactSpace.mp h
  have _ {j₁ j₂ : Over W₁} (φ : j₁ ⟶ j₂) :
      IsAffineHom ((Over.forget W₁ ⋙ S.preimageDiagram x (pullback.snd (a ≫ g) g ≫ g)).map φ) :=
    inferInstanceAs (IsAffineHom ((S.preimageDiagram x (pullback.snd (a ≫ g) g ≫ g)).map
      ((Over.forget W₁).map φ)))
  let R₆ : (pullback (a ≫ g) g).Opens := (pullback.snd (a ≫ g) g ≫ g) ⁻¹ᵁ V₆.1
  let W₆ : X'.Opens := (a ≫ g) ⁻¹ᵁ V₆.1
  have hV₆₁ : V₆.1 ≤ V₁.1 := h64.trans ((leOfHom h43.left).trans h31)
  let v₆ : W₆.toScheme ⟶ Z := X'.homOfLE ((a ≫ g).preimage_mono hV₆₁) ≫ v₁
  have hv₆f : v₆ ≫ f = W₆.ι ≫ a ≫ g := by
    simp only [v₆, Category.assoc, hv₁f, Scheme.homOfLE_ι_assoc]
  have hπv₆ : (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₆ ≫ v₆ = E.v ≫ e := by
    rw [← hv₁, ← (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).w (homOfLE hV₆₁)]
    simp [v₆]
  let act₆ : R₆.toScheme ⟶ W₆.toScheme := IsOpenImmersion.lift W₆.ι (R₆.ι ≫ D.act) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (R₆.ι ≫ D.act ≫ a ≫ g) y ∈ V₆.1
    rw [reassoc_of% D.act_comp]
    exact y.2)
  have hact₆ : act₆ ≫ W₆.ι = R₆.ι ≫ D.act := IsOpenImmersion.lift_fac _ _ _
  let fst₆ : R₆.toScheme ⟶ W₆.toScheme :=
    IsOpenImmersion.lift W₆.ι (R₆.ι ≫ pullback.fst (a ≫ g) g) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (R₆.ι ≫ pullback.fst (a ≫ g) g ≫ a ≫ g) y ∈ V₆.1
      rw [pullback.condition]
      exact y.2)
  have hfst₆ : fst₆ ≫ W₆.ι = R₆.ι ≫ pullback.fst (a ≫ g) g := IsOpenImmersion.lift_fac _ _ _
  have hV₆W : V₆.1 ≤ W₁.1 := h64.trans ((leOfHom h43.left).trans hV₃W)
  obtain ⟨j₇, h76, h7⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (Over.forget W₁ ⋙ S.preimageDiagram x (pullback.snd (a ≫ g) g ≫ g))
    (Functor.whiskerLeft (Over.forget W₁)
      (S.preimageDiagramTo x (pullback.snd (a ≫ g) g ≫ g) (pullback.snd (a ≫ g) g ≫ g))) f _
    hlimX'' (i := Over.mk (homOfLE hV₆W)) (act₆ ≫ v₆) (fst₆ ≫ v₆)
    (by
      rw [Category.assoc, hv₆f, reassoc_of% hact₆, reassoc_of% D.act_comp]
      rfl)
    (by
      rw [Category.assoc, hv₆f, reassoc_of% hfst₆, pullback.condition]
      rfl)
    (by
      have h₁ : (Scheme.preimageConeOfIsPullback x _ hX'').π.app V₆ ≫ act₆ =
          (D.baseChange (S.fromSpecStalk x)).act ≫
            (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₆ := by
        rw [← cancel_mono W₆.ι, Category.assoc, hact₆, Category.assoc,
          Scheme.preimageConeOfIsPullback_π_app_ι hX,
          Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX'']
        exact (pullback.lift_fst _ _ _).symm
      have h₂ : (Scheme.preimageConeOfIsPullback x _ hX'').π.app V₆ ≫ fst₆ =
          pullback.fst _ _ ≫ (Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app V₆ := by
        rw [← cancel_mono W₆.ι, Category.assoc, hfst₆, Category.assoc,
          Scheme.preimageConeOfIsPullback_π_app_ι hX,
          Scheme.preimageConeOfIsPullback_π_app_ι_assoc hX'']
        exact DescentDatum.baseChangeAux_fst (S.fromSpecStalk x)
      change (Scheme.preimageConeOfIsPullback x _ hX'').π.app V₆ ≫ act₆ ≫ v₆ =
        (Scheme.preimageConeOfIsPullback x _ hX'').π.app V₆ ≫ fst₆ ≫ v₆
      rw [reassoc_of% h₁, reassoc_of% h₂, hπv₆, reassoc_of% E.act_v])
  let V₇ := j₇.left
  -- the descent over the neighbourhood `V₇`
  have hV₇₆ : V₇.1 ≤ V₆.1 := leOfHom h76.left
  have hV₇₄ : V₇.1 ≤ V₄.1 := hV₇₆.trans h64
  have hV₇₃ : V₇.1 ≤ V₃.1 := hV₇₄.trans (leOfHom h43.left)
  have hV₇₁ : V₇.1 ≤ V₁.1 := hV₇₃.trans h31
  have hV₇₅ : V₇.1 ≤ j₅.left.1 := hV₇₆.trans h65
  let W : X'.Opens := (a ≫ g) ⁻¹ᵁ V₇.1
  let ZV : Z.Opens := f ⁻¹ᵁ V₇.1
  let QV : (pullback f g).Opens := pullback.fst f g ⁻¹ᵁ ZV
  let v₇ : W.toScheme ⟶ Z := X'.homOfLE ((a ≫ g).preimage_mono hV₇₁) ≫ v₁
  have hv₇f : v₇ ≫ f = W.ι ≫ a ≫ g := by
    simp only [v₇, Category.assoc, hv₁f, Scheme.homOfLE_ι_assoc]
  let cfull : W.toScheme ⟶ pullback f g :=
    pullback.lift v₇ (W.ι ≫ a) (by rw [hv₇f, Category.assoc])
  have hcfull : X'.homOfLE ((a ≫ g).preimage_mono hV₇₃) ≫ c₃ = cfull := by
    apply pullback.hom_ext
    · simp [c₃, cfull, v₃, v₇]
    · simp only [c₃, cfull, Category.assoc, pullback.lift_snd]
      exact Scheme.homOfLE_ι_assoc _ _ _
  let c : W.toScheme ⟶ QV.toScheme := IsOpenImmersion.lift QV.ι cfull (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (cfull ≫ pullback.fst f g ≫ f) w ∈ V₇.1
    rw [pullback.lift_fst_assoc, hv₇f]
    exact w.2)
  have hc : c ≫ QV.ι = cfull := IsOpenImmersion.lift_fac _ _ _
  have hQV₃ : QV ≤ QV₃ := pQ.preimage_mono hV₇₃
  let χ' : QV.toScheme ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι ((pullback f g).homOfLE hQV₃ ≫ χ₃) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      change ((pullback f g).homOfLE hQV₃ ≫ χ₃ ≫ a ≫ g) y ∈ V₇.1
      rw [hχ₃ag, Scheme.homOfLE_ι_assoc]
      exact y.2)
  have hχ' : χ' ≫ W.ι = (pullback f g).homOfLE hQV₃ ≫ χ₃ := IsOpenImmersion.lift_fac _ _ _
  have hcχ : c ≫ χ' = 𝟙 _ := by
    have e₁ : c ≫ (pullback f g).homOfLE hQV₃ =
        X'.homOfLE ((a ≫ g).preimage_mono hV₇₃) ≫ c₃' := by
      rw [← cancel_mono QV₃.ι, Category.assoc, Scheme.homOfLE_ι, hc, Category.assoc, hc₃',
        hcfull]
    have h4' : X'.homOfLE ((a ≫ g).preimage_mono (leOfHom h43.left)) ≫ c₃' ≫ χ₃ =
        X'.homOfLE ((a ≫ g).preimage_mono (leOfHom h43.left)) ≫ W₃.ι := h4
    rw [← cancel_mono W.ι, Category.assoc, hχ', reassoc_of% e₁, Category.id_comp,
      ← X'.homOfLE_homOfLE ((a ≫ g).preimage_mono hV₇₄)
        ((a ≫ g).preimage_mono (leOfHom h43.left)), Category.assoc, h4',
      Scheme.homOfLE_homOfLE_assoc]
    exact Scheme.homOfLE_ι _ _
  have hχc : χ' ≫ c = 𝟙 _ := by
    have e₁ : χ' ≫ X'.homOfLE ((a ≫ g).preimage_mono hV₇₃) =
        (pullback f g).homOfLE hQV₃ ≫ χ₃' := by
      rw [← cancel_mono W₃.ι, Category.assoc, Scheme.homOfLE_ι, hχ', Category.assoc, hχ₃']
    have h5' : (pullback f g).homOfLE (pQ.preimage_mono (leOfHom h53.left)) ≫ χ₃' ≫ c₃ =
        (pullback f g).homOfLE (pQ.preimage_mono (leOfHom h53.left)) ≫ QV₃.ι := h5
    rw [← cancel_mono QV.ι, Category.assoc, hc, Category.id_comp, ← hcfull,
      reassoc_of% e₁, ← (pullback f g).homOfLE_homOfLE (pQ.preimage_mono hV₇₅)
        (pQ.preimage_mono (leOfHom h53.left)), Category.assoc,
      h5', Scheme.homOfLE_homOfLE_assoc]
    exact Scheme.homOfLE_ι _ _
  have hQVι : QV.ι = χ' ≫ cfull := by rw [← hc, ← Category.assoc, hχc, Category.id_comp]
  let v : W.toScheme ⟶ ZV.toScheme := IsOpenImmersion.lift ZV.ι v₇ (by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (v₇ ≫ f) w ∈ V₇.1
    rw [hv₇f]
    exact w.2)
  have hv : v ≫ ZV.ι = v₇ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨V₇, (leOfHom j₇.hom).trans hW₁₀, ZV, ZV.ι ≫ f, v, inferInstanceAs (Etale (ZV.ι ≫ f)),
    ?_, ?_⟩
  · -- the square is cartesian: `W ≅ Z_V ×_S S'`
    let eW : W.toScheme ≅ QV.toScheme := ⟨c, χ', hcχ, hχc⟩
    have SQ := (isPullback_morphismRestrict (pullback.fst f g) ZV).paste_vert
      (IsPullback.of_hasPullback f g)
    refine SQ.of_iso eW.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, eW]
      rw [← cancel_mono ZV.ι, morphismRestrict_ι, Category.assoc, hv, hQVι, Category.assoc]
      simp [cfull]
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, eW]
      rw [hQVι, Category.assoc]
      simp [cfull]
      rfl
  · -- compatibility with the descent datum
    have hW₆ : W ≤ W₆ := (a ≫ g).preimage_mono hV₇₆
    let R₇ : (pullback (a ≫ g) g).Opens := (pullback.snd (a ≫ g) g ≫ g) ⁻¹ᵁ V₇.1
    have hR : R₇ ≤ R₆ := (pullback.snd (a ≫ g) g ≫ g).preimage_mono hV₇₆
    let m : pullback ((W.ι ≫ a) ≫ g) g ⟶ R₇.toScheme :=
      IsOpenImmersion.lift R₇.ι (restrictMap W) (by
        rintro _ ⟨y, rfl⟩
        rw [Scheme.Opens.range_ι]
        change (restrictMap W ≫ pullback.snd (a ≫ g) g ≫ g) y ∈ V₇.1
        have : restrictMap W ≫ pullback.snd (a ≫ g) g ≫ g =
            pullback.fst ((W.ι ≫ a) ≫ g) g ≫ W.ι ≫ a ≫ g := by
          have h := pullback.condition (f := (W.ι ≫ a) ≫ g) (g := g)
          simp only [Category.assoc] at h
          simp [h]
        rw [this, Scheme.Hom.comp_apply]
        exact (pullback.fst ((W.ι ≫ a) ≫ g) g y).2)
    have hm : m ≫ R₇.ι = restrictMap W := IsOpenImmersion.lift_fac _ _ _
    have e₁ : (D.restrict W (D.isStable_preimage V₇.1)).act ≫ X'.homOfLE hW₆ =
        m ≫ (pullback (a ≫ g) g).homOfLE hR ≫ act₆ := by
      rw [← cancel_mono W₆.ι]
      simp only [Category.assoc]
      rw [Scheme.homOfLE_ι, restrict_act_ι, hact₆, Scheme.homOfLE_ι_assoc, reassoc_of% hm]
    have e₂ : pullback.fst ((W.ι ≫ a) ≫ g) g ≫ X'.homOfLE hW₆ =
        m ≫ (pullback (a ≫ g) g).homOfLE hR ≫ fst₆ := by
      rw [← cancel_mono W₆.ι]
      simp only [Category.assoc]
      rw [Scheme.homOfLE_ι, hfst₆, Scheme.homOfLE_ι_assoc, reassoc_of% hm]
      simp
    have h7' : (pullback (a ≫ g) g).homOfLE hR ≫ act₆ ≫ v₆ =
        (pullback (a ≫ g) g).homOfLE hR ≫ fst₆ ≫ v₆ := h7
    have hv₇₆ : v₇ = X'.homOfLE hW₆ ≫ v₆ := by simp [v₇, v₆]
    rw [← cancel_mono ZV.ι]
    simp only [Category.assoc]
    rw [hv, hv₇₆, reassoc_of% e₁, reassoc_of% e₂, h7']

end AffineCase

section GeneralCase

variable [UniversallySubmersive g] [LocallyOfFinitePresentation g] [QuasiCompact g]
  [QuasiSeparated g] [Etale a] [QuasiCompact a] [QuasiSeparated a]

omit [UniversallySubmersive g] in
set_option backward.isDefEq.respectTransparency false in
/-- (Implementation) The pieces in the proof of IX.4.4: the preimage `v⁻¹(Y)` of an affine open `Y`
of the descended scheme over `Spec 𝒪_{S,x}` spreads out to an open `O` of `X'` on which the
descent datum becomes effective near `x`. -/
lemma DescentDatum.exists_isEffective_piece (D : DescentDatum g a) (x : S)
    (E : (D.baseChange (S.fromSpecStalk x)).Descent etale) (Y : E.X.Opens) (hY : IsAffineOpen Y) :
    ∃ O : X'.Opens, pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ⁻¹ᵁ O = E.v ⁻¹ᵁ Y ∧
      ∃ (V : S.AffineNhds x) (hV : D.IsStable (O ⊓ (a ≫ g) ⁻¹ᵁ V.1)),
        (D.restrict _ hV).IsEffective @Etale := by
  have hX := isPullback_baseChange_obj (S.fromSpecStalk x) (g := g) (a := a)
  have hlimX := Scheme.isLimitPreimageConeOfIsPullback hX
  have : QuasiCompact (pullback.snd g (S.fromSpecStalk x)) := inferInstance
  have : QuasiCompact E.v := MorphismProperty.of_isPullback E.isPullback.flip inferInstance
  have hWc : IsCompact (E.v ⁻¹' (Y : Set E.X)) :=
    QuasiCompact.isCompact_preimage _ Y.2 hY.isCompact
  obtain ⟨i, O', hO'c, hO'⟩ := exists_preimage_eq _ _ hlimX (E.v ⁻¹ᵁ Y) hWc
  let O : X'.Opens := ((a ≫ g) ⁻¹ᵁ i.1).ι ''ᵁ O'
  have hOi : O ≤ (a ≫ g) ⁻¹ᵁ i.1 := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have hOc : IsCompact (O : Set X') := hO'c.image (Scheme.Hom.continuous _)
  have hkO : pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ⁻¹ᵁ O = E.v ⁻¹ᵁ Y := by
    have e := Scheme.preimageConeOfIsPullback_π_app_ι hX i
    rw [← hO']
    calc pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ⁻¹ᵁ O
        = ((Scheme.preimageConeOfIsPullback x (a ≫ g) hX).π.app i ≫
            ((a ≫ g) ⁻¹ᵁ i.1).ι) ⁻¹ᵁ O := by rw [e]
      _ = _ := by rw [Scheme.Hom.comp_preimage, Scheme.Hom.preimage_image_eq]
  have hst := Descent.isStable_preimage (D.baseChange _) E Y
  rw [← hkO] at hst
  obtain ⟨V, hVi, hstab⟩ := D.exists_isStable_inf x hOc hOi hst
  have htop : pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ⁻¹ᵁ ((a ≫ g) ⁻¹ᵁ V.1) = ⊤ := by
    refine eq_top_iff.mpr fun z _ ↦ ?_
    obtain ⟨w, hw⟩ := Scheme.range_subset_of_isPullback hX V ⟨z, rfl⟩
    change pullback.fst a (pullback.fst g (S.fromSpecStalk x)) z ∈ (a ≫ g) ⁻¹ᵁ V.1
    rw [← hw]
    exact w.2
  have hkO'' : pullback.fst a (pullback.fst g (S.fromSpecStalk x)) ⁻¹ᵁ
      (O ⊓ (a ≫ g) ⁻¹ᵁ V.1) = E.v ⁻¹ᵁ Y := by
    rw [Scheme.Hom.preimage_inf, hkO, htop, inf_top_eq]
  -- the descent over `Spec 𝒪_{S,x}` of the restriction to `O ⊓ (a ≫ g)⁻¹ V`, with affine
  -- descended scheme `Y`
  let E₂ := Descent.ofBaseChangeRestrict D (S.fromSpecStalk x) hstab
    (Descent.congrOpen _ _ _ hkO''.symm (Descent.restrictOpen (D.baseChange _) E Y))
  have : IsAffine E₂.X := by
    change IsAffine
      (Descent.congrOpen _ _ _ hkO''.symm (Descent.restrictOpen (D.baseChange _) E Y)).X
    rw [Descent.congrOpen_X]
    exact hY
  -- quasi-compactness over `V`
  have hsq : IsQuasiSeparated (((a ≫ g) ⁻¹ᵁ i.1 : X'.Opens) : Set X') :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ ((a ≫ g) ⁻¹ᵁ i.1).2).mpr
      (quasiSeparatedSpace_of_quasiSeparated ((a ≫ g) ∣_ i.1))
  let O'' := O ⊓ (a ≫ g) ⁻¹ᵁ V.1
  have hc (V₂ : S.AffineNhds x) (h₂ : V₂.1 ≤ V.1) :
      IsCompact ((((O''.ι ≫ a) ≫ g) ⁻¹ᵁ V₂.1 : O''.toScheme.Opens) : Set O''.toScheme) := by
    have hV₂c : IsCompact (((a ≫ g) ⁻¹ᵁ V₂.1 : X'.Opens) : Set X') :=
      QuasiCompact.isCompact_preimage _ V₂.1.2 V₂.isAffineOpen.isCompact
    have hK := hsq _ _ hOi O.2 hOc ((a ≫ g).preimage_mono (h₂.trans hVi))
      ((a ≫ g) ⁻¹ᵁ V₂.1).2 hV₂c
    have hKe : (O : Set X') ∩ ((a ≫ g) ⁻¹ᵁ V₂.1 : X'.Opens) =
        (O'' : Set X') ∩ ((a ≫ g) ⁻¹ᵁ V₂.1 : X'.Opens) := by
      ext z
      simp only [Set.mem_inter_iff, O'', TopologicalSpace.Opens.coe_inf]
      exact ⟨fun h ↦ ⟨⟨h.1, (a ≫ g).preimage_mono h₂ h.2⟩, h.2⟩, fun h ↦ ⟨h.1.1, h.2⟩⟩
    rw [hKe] at hK
    have := (O''.ι.isOpenEmbedding.isInducing.isCompact_preimage_iff
      (K := (O'' : Set X') ∩ ((a ≫ g) ⁻¹ᵁ V₂.1 : X'.Opens))
      (by rw [Scheme.Opens.range_ι]; exact Set.inter_subset_left)).mpr hK
    convert this using 1
    ext z
    simp
  have hq : QuasiSeparatedSpace (((O''.ι ≫ a) ≫ g) ⁻¹ᵁ V.1).toScheme := by
    have hemb := ((((O''.ι ≫ a) ≫ g) ⁻¹ᵁ V.1).ι ≫ O''.ι).isOpenEmbedding
    rw [← isQuasiSeparated_univ_iff, hemb.isQuasiSeparated_iff]
    refine hsq.of_subset ?_
    rintro _ ⟨z, -, rfl⟩
    exact hOi ((((O''.ι ≫ a) ≫ g) ⁻¹ᵁ V.1).ι z).2.1
  obtain ⟨V', hV'V, hE⟩ := (D.restrict O'' hstab).exists_isEffective_restrict_of_isAffine x V hc
    hq E₂
  -- back to an open of `X'`
  have hst' : D.IsStable (O'' ⊓ (a ≫ g) ⁻¹ᵁ V'.1) := hstab.inf (D.isStable_preimage V'.1)
  have hopen : O''.ι ⁻¹ᵁ (O'' ⊓ (a ≫ g) ⁻¹ᵁ V'.1) = ((O''.ι ≫ a) ≫ g) ⁻¹ᵁ V'.1 := by
    ext z
    simp
  have hOO : O'' ⊓ (a ≫ g) ⁻¹ᵁ V'.1 = O ⊓ (a ≫ g) ⁻¹ᵁ V'.1 := by
    ext z
    simp only [O'', TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, (a ≫ g).preimage_mono hV'V h.2⟩, h.2⟩⟩
  have hE' := (isEffective_restrict_congr (D := D.restrict O'' hstab) _ hopen.symm).mp hE
  have hE'' := (D.isEffective_nestedRestrict_iff hst' hstab inf_le_left).mp hE'
  exact ⟨O, hkO, V', hOO ▸ hst', (isEffective_restrict_congr hst' hOO).mp hE''⟩

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.4, sufficiency: if the descent datum becomes effective (with étale descended scheme) over
`Spec 𝒪_{S,x}`, it is effective over some affine open neighbourhood `V` of `x`, in the sense that
its restriction to the stable open `X' ×_S V = (a ≫ g)⁻¹(V)` is effective. The descended scheme
over `Spec 𝒪_{S,x}` is covered by finitely many affine opens; each spreads out to a neighbourhood
of `x` together with the corresponding stable open of `X'` (`exists_isEffective_piece`), and the
pieces are glued. -/
theorem DescentDatum.exists_isEffective_restrict_preimage (D : DescentDatum g a) (x : S)
    (h : (D.baseChange (S.fromSpecStalk x)).IsEffective @Etale) :
    ∃ V : S.AffineNhds x,
      (D.restrict ((a ≫ g) ⁻¹ᵁ V.1) (D.isStable_preimage V.1)).IsEffective @Etale := by
  obtain ⟨E⟩ := (isEffective_iff_nonempty_descent etale).mp h
  have hX := isPullback_baseChange_obj (S.fromSpecStalk x) (g := g) (a := a)
  have hlimX := Scheme.isLimitPreimageConeOfIsPullback hX
  -- the descended scheme is quasi-compact
  have : CompactSpace (pullback a (pullback.fst g (S.fromSpecStalk x)) : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd a (pullback.fst g (S.fromSpecStalk x)) ≫ pullback.snd g (S.fromSpecStalk x))
  have : UniversallySubmersive E.v := E.universallySubmersive_v
  have : CompactSpace E.X := E.v.surjective.compactSpace E.v.continuous
  -- a finite affine open cover of the descended scheme, and the corresponding pieces
  obtain ⟨Us, hUsB, hUsf, hUs⟩ :=
    E.X.isBasis_affineOpens.exists_finite_of_isCompact (U := ⊤) isCompact_univ
  have : Finite Us := hUsf
  choose O hO V hV hE using fun Y : Us ↦ D.exists_isEffective_piece x E Y.1 (hUsB Y.2)
  -- the pieces cover `X'` near `x`
  obtain ⟨i₀⟩ : Nonempty (S.AffineNhds x) := inferInstance
  obtain ⟨j, f, hj⟩ := exists_map_eq_top _ _ hlimX (i := i₀)
    (((a ≫ g) ⁻¹ᵁ i₀.1).ι ⁻¹ᵁ ⨆ Y, O Y) (by
      rw [← Scheme.Hom.comp_preimage, Scheme.preimageConeOfIsPullback_π_app_ι hX,
        Scheme.Hom.preimage_iSup]
      simp only [hO]
      rw [← Scheme.Hom.preimage_iSup, ← sSup_eq_iSup', ← hUs]
      rfl)
  have hcov (z : X') (hz : z ∈ (a ≫ g) ⁻¹ᵁ j.1) : ∃ Y, z ∈ O Y := by
    have h₁ : (⟨z, hz⟩ : ((a ≫ g) ⁻¹ᵁ j.1).toScheme) ∈
        (S.preimageDiagram x (a ≫ g)).map f ⁻¹ᵁ (((a ≫ g) ⁻¹ᵁ i₀.1).ι ⁻¹ᵁ ⨆ Y, O Y) := by
      rw [hj]
      trivial
    change ((S.preimageDiagram x (a ≫ g)).map f ≫ ((a ≫ g) ⁻¹ᵁ i₀.1).ι) ⟨z, hz⟩ ∈ ⨆ Y, O Y
      at h₁
    rw [Scheme.preimageDiagram_map, Scheme.homOfLE_ι] at h₁
    exact TopologicalSpace.Opens.mem_iSup.mp h₁
  obtain ⟨M, hM⟩ := Finite.exists_ge V
  obtain ⟨W, hWM, hWj⟩ := exists_le_le M j
  refine ⟨W, D.isEffective_restrict_of_iSup_eq _
    (fun Y ↦ (O Y ⊓ (a ≫ g) ⁻¹ᵁ (V Y).1) ⊓ (a ≫ g) ⁻¹ᵁ W.1) ?_
    (fun Y ↦ (hV Y).inf (D.isStable_preimage W.1)) fun Y ↦ ?_⟩
  · refine le_antisymm (iSup_le fun Y ↦ inf_le_right) fun z hz ↦ ?_
    obtain ⟨Y, hY⟩ := hcov z ((a ≫ g).preimage_mono hWj hz)
    exact TopologicalSpace.Opens.mem_iSup.mpr
      ⟨Y, ⟨hY, (a ≫ g).preimage_mono (hWM.trans (hM Y)) hz⟩, hz⟩
  · obtain ⟨EY⟩ := (isEffective_iff_nonempty_descent etale).mp (hE Y)
    exact (isEffective_iff_nonempty_descent etale).mpr
      ⟨EY.restrictLE ((hV Y).inf (D.isStable_preimage W.1)) (hV Y) inf_le_left⟩

end GeneralCase

section Statements

variable [UniversallySubmersive g] [LocallyOfFinitePresentation g] [QuasiCompact g]
  [QuasiSeparated g]

lemma range_fromSpecStalk_subset (x : S) (U : S.Opens) (hx : x ∈ U)
    (z : Spec (S.presheaf.stalk x)) : S.fromSpecStalk x z ∈ U := by
  have h := Set.mem_range_self (f := S.fromSpecStalk x) z
  rw [Scheme.range_fromSpecStalk] at h
  exact Specializes.mem_open h U.2 hx

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.4: let `g : S' ⟶ S` be universally submersive and of finite presentation, `X'` étale of
finite presentation over `S'` with a descent datum, and `x ∈ S`. The datum is effective over some
open neighbourhood `U` of `x` (i.e. for `X' ×_S U` relative to `S' ×_S U ⟶ U`) iff it is effective
over `Spec 𝒪_{S,x}`. -/
theorem DescentDatum.exists_isEffective_baseChange_iff (D : DescentDatum g a) (x : S)
    (ha : etaleFinitePresentation a) :
    (∃ U : S.Opens, x ∈ U ∧ (D.baseChange U.ι).IsEffective etaleFinitePresentation) ↔
      (D.baseChange (S.fromSpecStalk x)).IsEffective etaleFinitePresentation := by
  obtain ⟨⟨ha₁, ha₂⟩, ha₃⟩ := ha
  have : Etale a := ha₁
  have : QuasiCompact a := ha₂
  have : QuasiSeparated a := ha₃
  have hle : etaleFinitePresentation.{u} ≤ @Etale := fun _ _ _ h ↦ h.1.1
  have hup {T : Scheme.{u}} (t : T ⟶ S) (h : (D.baseChange t).IsEffective @Etale) :
      (D.baseChange t).IsEffective etaleFinitePresentation :=
    (D.baseChange t).isEffective_etaleFinitePresentation_of_etale
      (MorphismProperty.pullback_snd _ _ ⟨⟨ha₁, ha₂⟩, ha₃⟩) h
  constructor
  · rintro ⟨U, hxU, h⟩
    have h₁ := D.isEffective_restrict_of_isEffective_baseChange rfl (h.of_le hle)
    exact hup _ (D.isEffective_baseChange_of_isEffective_restrict _ U
      (range_fromSpecStalk_subset x U hxU) h₁)
  · intro h
    obtain ⟨V, hV⟩ := D.exists_isEffective_restrict_preimage x (h.of_le hle)
    exact ⟨V.1, V.2.2, hup _ (D.isEffective_baseChange_of_isEffective_restrict _ V.1
      (fun z ↦ z.2) hV)⟩

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.5, first assertion: under the hypotheses of IX.4.4, a descent datum is effective iff it
is effective over `Spec 𝒪_{S,x}` for every `x ∈ S`. -/
theorem DescentDatum.isEffective_iff_forall_fromSpecStalk (D : DescentDatum g a)
    (ha : etaleFinitePresentation a) :
    D.IsEffective etaleFinitePresentation ↔
      ∀ x : S, (D.baseChange (S.fromSpecStalk x)).IsEffective etaleFinitePresentation := by
  have : Etale a := ha.1.1
  have : QuasiCompact a := ha.1.2
  have : QuasiSeparated a := ha.2
  refine ⟨fun h x ↦ h.baseChange _, fun h ↦ ?_⟩
  choose V hV using fun x ↦ D.exists_isEffective_restrict_preimage x ((h x).of_le
    fun _ _ _ h ↦ h.1.1)
  refine D.isEffective_etaleFinitePresentation_of_etale ha
    (D.isEffective_of_iSup_eq_top (fun x ↦ (a ≫ g) ⁻¹ᵁ (V x).1) ?_
      (fun x ↦ D.isStable_preimage (V x).1) hV)
  refine eq_top_iff.mpr fun z _ ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨(a ≫ g) z, ?_⟩
  exact (V ((a ≫ g) z)).2.2

end Statements

end SGA.SGA1.ExposeIX
