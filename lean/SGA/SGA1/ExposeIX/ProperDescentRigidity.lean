/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIX.FiniteEtaleEffectiveDescent

/-!
# SGA 1, Exposé IX, 6.7: rigidity of descent data along morphisms with connected fibres

Let `f : X ⟶ S` be proper with geometrically connected fibres and `Y` an étale covering of `X`. A
descent datum on `Y` relative to `f` (in the form of IX.4: an action `(y, x') ↦ y·x'` of the
groupoid `X ×_S X ⇉ X`) is determined by the unit condition `y·π(y) = y`, and the associativity
condition is automatic: the points `(y, x')` with a fixed `y` form the fibre `X_{f(π y)} ⊗ κ(y)`,
which is connected, and two morphisms from a connected scheme to an étale scheme which agree at one
point agree (`eq_of_isSection_of_geometricallyConnected`). Hence (IX.6.7, the gluing step) such
actions glue: if every point of `S` has a neighbourhood over which `Y` carries an action, `Y` has a
global action, hence comes from an étale covering of `S` by effective descent (IX.4.12)
(`mem_essImage_of_forall_exists_localAct`).
-/

universe u

open CategoryTheory Limits AlgebraicGeometry MorphismProperty

namespace SGA.SGA1.ExposeIX

local notation "FEt" => (SGA.SGA1.ExposeV.finiteEtaleHom : MorphismProperty Scheme)
local notation "pb" => MorphismProperty.Over.pullback FEt ⊤

section Rigidity

variable {P E C : Scheme.{u}} (e : E ⟶ C) [FormallyUnramified e] [LocallyOfFiniteType e]
  [IsSeparated e] {u₁ u₂ : P ⟶ E} (h : u₁ ≫ e = u₂ ≫ e)

omit [IsSeparated e] in
include h in
/-- The equalizer of two morphisms to an unramified separated scheme: if the open and closed
immersion `pullback Δ (u₁, u₂) ⟶ P` is surjective, `u₁ = u₂`. -/
lemma eq_of_surjective_equalizer
    (hs : Function.Surjective (pullback.snd (pullback.diagonal e) (pullback.lift u₁ u₂ h))) :
    u₁ = u₂ := by
  let d := pullback.diagonal e
  let v : P ⟶ pullback e e := pullback.lift u₁ u₂ h
  let q := pullback.snd d v
  have : IsOpenImmersion q := MorphismProperty.pullback_snd _ _ inferInstance
  have : Surjective q := ⟨hs⟩
  have : IsIso q := (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have hv : v = inv q ≫ pullback.fst d v ≫ d := by
    rw [pullback.condition]
    exact (IsIso.inv_hom_id_assoc q v).symm
  have h₁ : u₁ = v ≫ pullback.fst e e := (pullback.lift_fst _ _ _).symm
  have h₂ : u₂ = v ≫ pullback.snd e e := (pullback.lift_snd _ _ _).symm
  rw [h₁, h₂, hv]
  simp [d]

omit [FormallyUnramified e] [LocallyOfFiniteType e] [IsSeparated e] in
include h in
/-- The points of `P` through which `u₁` and `u₂` agree on some scheme lie in the equalizer. -/
lemma mem_range_equalizer {W : Scheme.{u}} (z : W ⟶ P) (hz : z ≫ u₁ = z ≫ u₂) (w : W) :
    z w ∈ Set.range (pullback.snd (pullback.diagonal e) (pullback.lift u₁ u₂ h)) := by
  have hzv : z ≫ pullback.lift u₁ u₂ h = (z ≫ u₁) ≫ pullback.diagonal e := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.assoc, pullback.diagonal_fst,
        Category.comp_id]
    · rw [Category.assoc, pullback.lift_snd, Category.assoc, pullback.diagonal_snd,
        Category.comp_id, hz]
  refine ⟨pullback.lift (z ≫ u₁) z hzv.symm w, ?_⟩
  rw [← Scheme.Hom.comp_apply, pullback.lift_snd]

omit [IsSeparated e] in
include h in
/-- Rigidity, pointwise form: two morphisms to an unramified separated `E ⟶ C` which agree over
`C`, and agree on schemes passing through every point, are equal. -/
theorem eq_of_forall_exists_mem_range
    (hp : ∀ p : P, ∃ (W : Scheme.{u}) (z : W ⟶ P), p ∈ Set.range z ∧ z ≫ u₁ = z ≫ u₂) :
    u₁ = u₂ := by
  refine eq_of_surjective_equalizer e h fun p ↦ ?_
  obtain ⟨W, z, ⟨w, rfl⟩, hz⟩ := hp p
  exact mem_range_equalizer e h z hz w

include h in
/-- Rigidity: two morphisms from a connected scheme to an unramified separated `E ⟶ C` which agree
over `C` and at one point are equal (the locus where they agree is open and closed). -/
theorem eq_of_connectedSpace [ConnectedSpace P] {W : Scheme.{u}} [Nonempty W] (z : W ⟶ P)
    (hz : z ≫ u₁ = z ≫ u₂) : u₁ = u₂ := by
  refine eq_of_surjective_equalizer e h fun p ↦ ?_
  let q := pullback.snd (pullback.diagonal e) (pullback.lift u₁ u₂ h)
  have : IsOpenImmersion q := MorphismProperty.pullback_snd _ _ inferInstance
  have : IsClosedImmersion q := inferInstance
  have hclopen : IsClopen (Set.range q) :=
    ⟨q.isClosedEmbedding.isClosed_range, q.isOpenEmbedding.isOpen_range⟩
  obtain ⟨w⟩ := ‹Nonempty W›
  have hne : (Set.range q).Nonempty := ⟨z w, mem_range_equalizer e h z hz w⟩
  have hp : p ∈ Set.range q := by
    rw [hclopen.eq_univ hne]
    trivial
  exact hp

include h in
/-- Rigidity along a family with connected fibres: let `q : P ⟶ B` have geometrically connected
fibres and a section `σ`. Two morphisms `P ⟶ E` to an unramified separated `E ⟶ C` which agree over
`C` and along `σ` are equal. -/
theorem eq_of_isSection_of_geometricallyConnected {B : Scheme.{u}} (q : P ⟶ B)
    [GeometricallyConnected q] (σ : B ⟶ P) (hσ : σ ≫ q = 𝟙 B) (hσu : σ ≫ u₁ = σ ≫ u₂) :
    u₁ = u₂ := by
  refine eq_of_forall_exists_mem_range e h fun p ↦ ?_
  let b := q p
  let w₀ : Spec (B.residueField b) ⟶ q.fiber b :=
    pullback.lift (B.fromSpecResidueField b ≫ σ) (𝟙 _)
      (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hw₀ : w₀ ≫ q.fiberι b = B.fromSpecResidueField b ≫ σ := pullback.lift_fst _ _ _
  refine ⟨q.fiber b, q.fiberι b, ?_, ?_⟩
  · rw [Scheme.Hom.range_fiberι]
    rfl
  · refine eq_of_connectedSpace e (by rw [Category.assoc, Category.assoc, h]) w₀ ?_
    rw [reassoc_of% hw₀, reassoc_of% hw₀, hσu]

end Rigidity

section Action

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)

/-- The diagonal section `y ↦ (y, π(y))` of `Y ×_S X ⟶ Y`. -/
noncomputable abbrev actDiag : Y.left ⟶ pullback (Y.hom ≫ f) f :=
  pullback.lift (𝟙 _) Y.hom (by simp)

variable [GeometricallyConnected f]

/-- IX.6.7, uniqueness: an action `(y, x') ↦ y·x'` of `X ×_S X ⇉ X` on an étale covering `Y` of
`X` is determined by the unit law `y·π(y) = y`, since the points `(y, x')` with fixed `y` form a
connected scheme. -/
theorem act_eq_of_unit {act act' : pullback (Y.hom ≫ f) f ⟶ Y.left}
    (h : act ≫ Y.hom = pullback.snd _ _) (h' : act' ≫ Y.hom = pullback.snd _ _)
    (hu : actDiag f Y ≫ act = 𝟙 _) (hu' : actDiag f Y ≫ act' = 𝟙 _) : act = act' := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  exact eq_of_isSection_of_geometricallyConnected Y.hom (h.trans h'.symm)
    (pullback.fst (Y.hom ≫ f) f) (actDiag f Y) (pullback.lift_fst _ _ _) (hu.trans hu'.symm)

/-- IX.6.7: an action satisfying the unit law is a descent datum; the associativity law is
automatic (rigidity along the connected fibres of `(y, x₁, x₂) ↦ (y, x₁)`). -/
noncomputable def descentDatumOfAct (act : pullback (Y.hom ≫ f) f ⟶ Y.left)
    (h : act ≫ Y.hom = pullback.snd _ _) (hu : actDiag f Y ≫ act = 𝟙 _) :
    DescentDatum f Y.hom where
  act := act
  act_comp := h
  unit := hu
  assoc := by
    have : IsFinite Y.hom := Y.prop.1
    have : Etale Y.hom := Y.prop.2
    let q := pullback.fst (pullback.snd (Y.hom ≫ f) f ≫ f) f
    obtain ⟨σ, hσq, hσs⟩ : ∃ σ : pullback (Y.hom ≫ f) f ⟶
        pullback (pullback.snd (Y.hom ≫ f) f ≫ f) f, σ ≫ q = 𝟙 _ ∧
          σ ≫ pullback.snd (pullback.snd (Y.hom ≫ f) f ≫ f) f = pullback.snd (Y.hom ≫ f) f :=
      ⟨pullback.lift (𝟙 _) (pullback.snd _ _) (by rw [Category.id_comp]),
        pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hlift : pullback.lift (f := Y.hom ≫ f) (g := f) act (pullback.snd _ _)
        (by rw [reassoc_of% h]) = act ≫ actDiag f Y := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, Category.comp_id]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, h]
    refine eq_of_isSection_of_geometricallyConnected Y.hom ?_ q σ hσq ?_
    · simp only [Category.assoc, h, pullback.lift_snd]
    · have e₁ : σ ≫ pullback.lift (f := Y.hom ≫ f) (g := f) (q ≫ act)
          (pullback.snd (pullback.snd (Y.hom ≫ f) f ≫ f) f)
          (by rw [Category.assoc, reassoc_of% h]; exact pullback.condition) =
          pullback.lift (f := Y.hom ≫ f) (g := f) act (pullback.snd _ _)
            (by rw [reassoc_of% h]) := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, reassoc_of% hσq]
        · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hσs]
      have e₂ : σ ≫ pullback.lift (f := Y.hom ≫ f) (g := f) (q ≫ pullback.fst (Y.hom ≫ f) f)
          (pullback.snd (pullback.snd (Y.hom ≫ f) f ≫ f) f)
          (by rw [Category.assoc, pullback.condition]; exact pullback.condition) = 𝟙 _ := by
        apply pullback.hom_ext
        · rw [Category.assoc, pullback.lift_fst, reassoc_of% hσq, Category.id_comp]
        · rw [Category.assoc, pullback.lift_snd, hσs, Category.id_comp]
      have hmid : pullback.lift (f := Y.hom ≫ f) (g := f) act (pullback.snd _ _)
          (by rw [reassoc_of% h]) ≫ act = 𝟙 _ ≫ act := by
        rw [hlift, Category.assoc, hu, Category.comp_id, Category.id_comp]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ act) e₁).trans
        (hmid.trans ((congrArg (· ≫ act) e₂).symm.trans (Category.assoc _ _ _))))

/-- IX.4.12 in the form used for IX.6.7: an étale covering of `X` with an action satisfying the unit
law comes from an étale covering of `S` (`f` proper and surjective, `S` locally noetherian). -/
theorem mem_essImage_of_act [IsLocallyNoetherian S] [IsProper f]
    (act : pullback (Y.hom ≫ f) f ⟶ Y.left)
    (h : act ≫ Y.hom = pullback.snd _ _) (hu : actDiag f Y ≫ act = 𝟙 _) :
    (pb f).essImage Y := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  obtain ⟨Xw, b, v, hb, hv, -⟩ := (isEffectiveDescentMorphism_of_isProper f).2 Y.hom
    (descentDatumOfAct f Y act h hu) ⟨inferInstance, inferInstance⟩
  have hb' : FEt b := hb
  exact ⟨MorphismProperty.Over.mk ⊤ b hb',
    ⟨(MorphismProperty.Over.isoMk hv.isoPullback hv.isoPullback_hom_snd).symm⟩⟩

end Action

section LocalAct

variable {X S : Scheme.{u}} (f : X ⟶ S) (Y : MorphismProperty.Over FEt ⊤ X)

lemma actDiag_preimage_fst_preimage (U : Y.left.Opens) :
    actDiag f Y ⁻¹ᵁ (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ U) = U := by
  rw [← Scheme.Hom.comp_preimage, pullback.lift_fst, Scheme.Hom.id_preimage]

/-- The section `y ↦ (y, π(y))` over an open `V ⊆ S`. -/
noncomputable abbrev actDiagRes (V : S.Opens) :
    ((Y.hom ≫ f) ⁻¹ᵁ V).toScheme ⟶
      (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme :=
  (actDiag f Y).resLE _ _ (actDiag_preimage_fst_preimage f Y _).ge

/-- An action over an open `V ⊆ S`: a morphism `b : (Y ×_S X)|_V ⟶ Y` over `X` satisfying the
unit law `y·π(y) = y`. -/
def IsLocalAct (V : S.Opens)
    (b : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶ Y.left) : Prop :=
  b ≫ Y.hom = Scheme.Opens.ι _ ≫ pullback.snd (Y.hom ≫ f) f ∧
    actDiagRes f Y V ≫ b = ((Y.hom ≫ f) ⁻¹ᵁ V).ι

lemma actDiagRes_comp_morphismRestrict (V : S.Opens) :
    actDiagRes f Y V ≫ (pullback.fst (Y.hom ≫ f) f ∣_ ((Y.hom ≫ f) ⁻¹ᵁ V)) = 𝟙 _ := by
  rw [← cancel_mono ((Y.hom ≫ f) ⁻¹ᵁ V).ι, Category.assoc, morphismRestrict_ι,
    ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, pullback.lift_fst,
    Category.comp_id, Category.id_comp]

variable [GeometricallyConnected f]

/-- IX.6.7, uniqueness over an open: two actions over `V` coincide. -/
theorem IsLocalAct.eq {V : S.Opens}
    {b b' : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶ Y.left}
    (hb : IsLocalAct f Y V b) (hb' : IsLocalAct f Y V b') : b = b' := by
  have : IsFinite Y.hom := Y.prop.1
  have : Etale Y.hom := Y.prop.2
  exact eq_of_isSection_of_geometricallyConnected Y.hom (hb.1.trans hb'.1.symm)
    (pullback.fst (Y.hom ≫ f) f ∣_ ((Y.hom ≫ f) ⁻¹ᵁ V)) (actDiagRes f Y V)
    (actDiagRes_comp_morphismRestrict f Y V) (hb.2.trans hb'.2.symm)

omit [GeometricallyConnected f] in
/-- The restriction of an action over `V` to a smaller open `V'`. -/
lemma IsLocalAct.restrict {V V' : S.Opens} (hVV' : V' ≤ V)
    {b : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶ Y.left}
    (hb : IsLocalAct f Y V b) :
    IsLocalAct f Y V'
      ((pullback (Y.hom ≫ f) f).homOfLE
        ((pullback.fst (Y.hom ≫ f) f).preimage_mono ((Y.hom ≫ f).preimage_mono hVV')) ≫ b) := by
  refine ⟨by rw [Category.assoc, hb.1, Scheme.homOfLE_ι_assoc], ?_⟩
  have hσ : actDiagRes f Y V' ≫ (pullback (Y.hom ≫ f) f).homOfLE
      ((pullback.fst (Y.hom ≫ f) f).preimage_mono ((Y.hom ≫ f).preimage_mono hVV')) =
      Y.left.homOfLE ((Y.hom ≫ f).preimage_mono hVV') ≫ actDiagRes f Y V := by
    rw [← cancel_mono (Scheme.Opens.ι _), Category.assoc, Scheme.homOfLE_ι,
      Scheme.Hom.resLE_comp_ι, Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.homOfLE_ι_assoc]
  rw [reassoc_of% hσ, hb.2, Scheme.homOfLE_ι]

/-- IX.6.7, gluing: actions defined near every point of `S` glue to a global action. -/
theorem exists_act_of_forall_exists_localAct
    (hloc : ∀ s : S, ∃ (V : S.Opens) (b : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ
      ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶ Y.left), s ∈ V ∧ IsLocalAct f Y V b) :
    ∃ act : pullback (Y.hom ≫ f) f ⟶ Y.left,
      act ≫ Y.hom = pullback.snd _ _ ∧ actDiag f Y ≫ act = 𝟙 _ := by
  choose V b hs hb using hloc
  let O : S → (pullback (Y.hom ≫ f) f).Opens :=
    fun s ↦ pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ V s)
  have hO : TopologicalSpace.IsOpenCover O := by
    refine eq_top_iff.mpr fun a _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
      ⟨(pullback.fst (Y.hom ≫ f) f ≫ Y.hom ≫ f) a, ?_⟩
    exact hs ((pullback.fst (Y.hom ≫ f) f ≫ Y.hom ≫ f) a)
  let 𝒰 := (pullback (Y.hom ≫ f) f).openCoverOfIsOpenCover O hO
  have hf : ∀ s t : S, pullback.fst (O s).ι (O t).ι ≫ b s =
      pullback.snd (O s).ι (O t).ι ≫ b t := by
    intro s t
    let M := V s ⊓ V t
    have hMs : M ≤ V s := inf_le_left
    have hMt : M ≤ V t := inf_le_right
    have hrange : Set.range (pullback.fst (O s).ι (O t).ι ≫ (O s).ι) ⊆
        Set.range (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ M)).ι := by
      rintro _ ⟨p, rfl⟩
      rw [Scheme.Opens.range_ι]
      refine ⟨((pullback.fst (O s).ι (O t).ι) p).2, ?_⟩
      have := ((pullback.snd (O s).ι (O t).ι) p).2
      change (pullback.fst (O s).ι (O t).ι ≫ (O s).ι) p ∈ O t
      rw [show pullback.fst (O s).ι (O t).ι ≫ (O s).ι =
        pullback.snd (O s).ι (O t).ι ≫ (O t).ι from pullback.condition]
      exact this
    let k := IsOpenImmersion.lift (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ M)).ι
      (pullback.fst (O s).ι (O t).ι ≫ (O s).ι) hrange
    have hk : k ≫ (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ ((Y.hom ≫ f) ⁻¹ᵁ M)).ι =
        pullback.fst (O s).ι (O t).ι ≫ (O s).ι := IsOpenImmersion.lift_fac _ _ _
    have hks : pullback.fst (O s).ι (O t).ι = k ≫ (pullback (Y.hom ≫ f) f).homOfLE
        ((pullback.fst (Y.hom ≫ f) f).preimage_mono ((Y.hom ≫ f).preimage_mono hMs)) := by
      rw [← cancel_mono (O s).ι, Category.assoc, Scheme.homOfLE_ι, hk]
    have hkt : pullback.snd (O s).ι (O t).ι = k ≫ (pullback (Y.hom ≫ f) f).homOfLE
        ((pullback.fst (Y.hom ≫ f) f).preimage_mono ((Y.hom ≫ f).preimage_mono hMt)) := by
      rw [← cancel_mono (O t).ι, Category.assoc, Scheme.homOfLE_ι, hk]
      exact (pullback.condition (f := (O s).ι) (g := (O t).ι)).symm
    rw [hks, hkt, Category.assoc, Category.assoc,
      ((hb s).restrict f Y hMs).eq f Y ((hb t).restrict f Y hMt)]
  obtain ⟨act, hact⟩ : ∃ act : pullback (Y.hom ≫ f) f ⟶ Y.left, ∀ s : S, (O s).ι ≫ act = b s :=
    ⟨𝒰.glueMorphisms (fun s ↦ b s) hf, fun s ↦ 𝒰.ι_glueMorphisms (fun s ↦ b s) hf s⟩
  refine ⟨act, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun s ↦ ?_
    change (O s).ι ≫ act ≫ Y.hom = (O s).ι ≫ _
    rw [reassoc_of% hact s, (hb s).1]
  · let 𝒱 := Y.left.openCoverOfIsOpenCover (fun s ↦ (Y.hom ≫ f) ⁻¹ᵁ V s) (by
      refine eq_top_iff.mpr fun y _ ↦ TopologicalSpace.Opens.mem_iSup.mpr
        ⟨(Y.hom ≫ f) y, hs _⟩)
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun s ↦ ?_
    change ((Y.hom ≫ f) ⁻¹ᵁ V s).ι ≫ actDiag f Y ≫ act = ((Y.hom ≫ f) ⁻¹ᵁ V s).ι ≫ 𝟙 _
    have hσ : ((Y.hom ≫ f) ⁻¹ᵁ V s).ι ≫ actDiag f Y = actDiagRes f Y (V s) ≫ (O s).ι :=
      (Scheme.Hom.resLE_comp_ι _ _).symm
    rw [reassoc_of% hσ, hact s, (hb s).2, Category.comp_id]

/-- **IX.6.7, gluing and effective descent**: if every point of `S` has a neighbourhood over which
the étale covering `Y` of `X` carries an action satisfying the unit law, `Y` comes from an étale
covering of `S` (`f` proper with geometrically connected fibres, `S` locally noetherian). -/
theorem mem_essImage_of_forall_exists_localAct [IsLocallyNoetherian S] [IsProper f]
    (hloc : ∀ s : S, ∃ (V : S.Opens) (b : (pullback.fst (Y.hom ≫ f) f ⁻¹ᵁ
      ((Y.hom ≫ f) ⁻¹ᵁ V)).toScheme ⟶ Y.left), s ∈ V ∧ IsLocalAct f Y V b) :
    (pb f).essImage Y := by
  obtain ⟨act, h, hu⟩ := exists_act_of_forall_exists_localAct f Y hloc
  exact mem_essImage_of_act f Y act h hu

end LocalAct

end SGA.SGA1.ExposeIX
