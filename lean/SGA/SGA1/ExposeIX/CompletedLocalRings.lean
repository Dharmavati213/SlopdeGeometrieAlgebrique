/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import SGA.SGA1.ExposeIX.FlatBaseChange

/-!
# SGA 1, Exposé IX, 4.5: effectiveness over the completed local rings

IX.4.5, second assertion (`DescentDatum.isEffective_iff_forall_fromSpecCompletedStalk`): let
`g : S' ⟶ S` be universally submersive, of finite presentation, with `S` locally noetherian, and
let `X'` be étale, separated and of finite presentation over `S'` with a descent datum. The datum
is effective iff it is effective over `Spec 𝒪̂_{S,x}` for every `x ∈ S`.

As in SGA, this follows from the first assertion of IX.4.5 (effectiveness over the local rings
`𝒪_{S,x}`, in `SGA.SGA1.ExposeIX.EffectiveNearPoint`) and IX.4.2 (in
`SGA.SGA1.ExposeIX.FlatBaseChange`), since `𝒪_{S,x} ⟶ 𝒪̂_{S,x}` is faithfully flat. Along the way:

* `DescentDatum.isEffective_iff_of_isoOver`: effectiveness is invariant under isomorphisms of
  descent data lying over an isomorphism of the bases;
* `DescentDatum.isEffective_baseChange_baseChange_iff`: base change of descent data is
  transitive, `(D ×_S T₁) ×_{T₁} T₂ ≅ D ×_S T₂`.
-/

universe u

open CategoryTheory Limits MorphismProperty

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

attribute [local simp] pullback.lift_fst pullback.lift_snd pullback.lift_fst_assoc
  pullback.lift_snd_assoc pullback.condition pullback.condition_assoc

namespace DescentDatum

section TransportOver

variable {T S'₁ S'₂ X₁ X₂ : Scheme.{u}} {g₁ : S'₁ ⟶ T} {g₂ : S'₂ ⟶ T} {a₁ : X₁ ⟶ S'₁}
  {a₂ : X₂ ⟶ S'₂} {D₁ : DescentDatum g₁ a₁} {D₂ : DescentDatum g₂ a₂}
  {P : MorphismProperty Scheme.{u}}

/-- Transport of an effective descent along an isomorphism of descent data lying over an
isomorphism `S'₁ ≅ S'₂` of `T`-schemes. -/
noncomputable def Descent.ofIsoOver (E : D₂.Descent P) (σ : S'₁ ≅ S'₂) (hσ : σ.hom ≫ g₂ = g₁)
    (e : X₁ ≅ X₂) (he : e.hom ≫ a₂ = a₁ ≫ σ.hom)
    (hact : D₁.act ≫ e.hom = pullback.map (a₁ ≫ g₁) g₁ (a₂ ≫ g₂) g₂ e.hom σ.hom (𝟙 _)
      (by simp [reassoc_of% he, hσ]) (by simp [hσ]) ≫ D₂.act) :
    D₁.Descent P where
  X := E.X
  b := E.b
  v := e.hom ≫ E.v
  prop := E.prop
  isPullback := E.isPullback.of_iso e.symm (Iso.refl _) σ.symm (Iso.refl _) (by simp)
    (by simp [Iso.eq_inv_comp, reassoc_of% he]) (by simp) (by simp [← hσ])
  act_v := by
    rw [reassoc_of% hact, E.act_v]
    simp

/-- Effectiveness is invariant under isomorphisms of descent data lying over an isomorphism
`S'₁ ≅ S'₂` of `T`-schemes. -/
lemma isEffective_iff_of_isoOver (σ : S'₁ ≅ S'₂) (hσ : σ.hom ≫ g₂ = g₁)
    (e : X₁ ≅ X₂) (he : e.hom ≫ a₂ = a₁ ≫ σ.hom)
    (hact : D₁.act ≫ e.hom = pullback.map (a₁ ≫ g₁) g₁ (a₂ ≫ g₂) g₂ e.hom σ.hom (𝟙 _)
      (by simp [reassoc_of% he, hσ]) (by simp [hσ]) ≫ D₂.act) :
    D₁.IsEffective P ↔ D₂.IsEffective P := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨E⟩ := (isEffective_iff_nonempty_descent P).mp h
    have hσ' : σ.inv ≫ g₁ = g₂ := by rw [← hσ, Iso.inv_hom_id_assoc]
    have he' : e.inv ≫ a₁ = a₂ ≫ σ.inv := by
      rw [Iso.inv_comp_eq, reassoc_of% he, Iso.hom_inv_id, Category.comp_id]
    refine (isEffective_iff_nonempty_descent P).mpr ⟨E.ofIsoOver σ.symm hσ' e.symm he' ?_⟩
    change D₂.act ≫ e.inv = _
    rw [Iso.comp_inv_eq, Category.assoc, hact, ← Category.assoc]
    convert (Category.id_comp D₂.act).symm using 2
    apply pullback.hom_ext <;> simp
  · obtain ⟨E⟩ := (isEffective_iff_nonempty_descent P).mp h
    exact (isEffective_iff_nonempty_descent P).mpr ⟨E.ofIsoOver σ hσ e he hact⟩

end TransportOver

section Transitivity

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'} (D : DescentDatum g a)
  {T₁ T₂ : Scheme.{u}} (t₁ : T₁ ⟶ S) (t₂ : T₂ ⟶ T₁)

/-- (Implementation) `(X' ×_S T₁) ×_{T₁} T₂ ≅ X' ×_S T₂`. -/
noncomputable def baseChangeCompIso :
    pullback (pullback.snd a (pullback.fst g t₁)) (pullback.fst (pullback.snd g t₁) t₂) ≅
      pullback a (pullback.fst g (t₂ ≫ t₁)) where
  hom := pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _)
    (pullback.snd _ _ ≫ (pullbackLeftPullbackSndIso g t₁ t₂).hom) (by
      simp [pullback.condition_assoc, pullbackLeftPullbackSndIso_hom_fst])
  inv := pullback.lift (pullback.lift (pullback.fst _ _)
      (pullback.snd _ _ ≫ (pullbackLeftPullbackSndIso g t₁ t₂).inv ≫ pullback.fst _ _) (by
        simp [pullback.condition]))
    (pullback.snd _ _ ≫ (pullbackLeftPullbackSndIso g t₁ t₂).inv) (by simp)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp
      · simp [pullback.condition]
    · simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · simp

/-- Base change of descent data is transitive up to isomorphism: the base change of `D` to `T₁`
and then to `T₂` is effective iff the base change of `D` to `T₂` is. -/
lemma isEffective_baseChange_baseChange_iff {P : MorphismProperty Scheme.{u}} :
    ((D.baseChange t₁).baseChange t₂).IsEffective P ↔ (D.baseChange (t₂ ≫ t₁)).IsEffective P := by
  refine isEffective_iff_of_isoOver (pullbackLeftPullbackSndIso g t₁ t₂)
    (pullbackLeftPullbackSndIso_hom_snd _ _ _) (baseChangeCompIso t₁ t₂)
    (by simp [baseChangeCompIso]) ?_
  apply pullback.hom_ext
  · simp only [baseChange, baseChangeAux, baseChangeCompIso, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc]
    simp only [← Category.assoc]
    congr 1
    apply pullback.hom_ext <;> simp [pullbackLeftPullbackSndIso_hom_fst]
  · simp [baseChangeCompIso, baseChange]

end Transitivity

end DescentDatum

section CompletedStalks

variable {S' S X' : Scheme.{u}} {g : S' ⟶ S} {a : X' ⟶ S'}

open IsLocalRing in
/-- For `S` locally noetherian, `Spec 𝒪̂_{S,x} ⟶ Spec 𝒪_{S,x}` is faithfully flat. -/
lemma flat_and_surjective_specMap_completion [IsLocallyNoetherian S] (x : S) :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x))))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x))))) := by
  rw [flat_and_surjective_SpecMap_iff]
  have : Module.FaithfullyFlat (S.presheaf.stalk x)
      (AdicCompletion (maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x)) :=
    .of_flat_of_isLocalHom
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr ‹_›

variable [UniversallySubmersive g] [LocallyOfFinitePresentation g] [QuasiCompact g]
  [QuasiSeparated g]

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.5, second assertion: under the hypotheses of IX.4.4, if moreover `S` is locally
noetherian and `X'` is separated over `S'`, a descent datum is effective iff it is effective over
the spectrum `Spec 𝒪̂_{S,x}` of every completed local ring. -/
theorem DescentDatum.isEffective_iff_forall_fromSpecCompletedStalk [IsLocallyNoetherian S]
    (D : DescentDatum g a) (ha : etaleFinitePresentation a) [IsSeparated a] :
    D.IsEffective etaleFinitePresentation ↔
      ∀ x : S, (D.baseChange (fromSpecCompletedStalk S x)).IsEffective
        etaleFinitePresentation := by
  refine ⟨fun h x ↦ h.baseChange _, fun h ↦ ?_⟩
  rw [D.isEffective_iff_forall_fromSpecStalk ha]
  intro x
  obtain ⟨hflat, hsurj⟩ := flat_and_surjective_specMap_completion x
  let t := Spec.map (CommRingCat.ofHom (algebraMap (S.presheaf.stalk x)
    (AdicCompletion (IsLocalRing.maximalIdeal (S.presheaf.stalk x)) (S.presheaf.stalk x))))
  have : Flat t := hflat
  have : Surjective t := hsurj
  have hax : etaleSeparatedFiniteType
      (pullback.snd a (pullback.fst g (S.fromSpecStalk x))) :=
    MorphismProperty.pullback_snd _ _ ⟨⟨ha.1.1, ‹_›⟩, ha.1.2⟩
  have hx : ((D.baseChange (S.fromSpecStalk x)).baseChange t).IsEffective
      etaleFinitePresentation :=
    (DescentDatum.isEffective_baseChange_baseChange_iff D _ t).mpr (h x)
  have hx' := ((D.baseChange (S.fromSpecStalk x)).baseChange
    t).isEffective_etaleSeparatedFiniteType_of_etale (MorphismProperty.pullback_snd _ _ hax)
    (hx.of_le fun _ _ _ h ↦ h.1.1)
  have hx'' := (D.baseChange (S.fromSpecStalk x)).isEffective_of_isEffective_baseChange_of_flat
    t hax hx'
  exact (D.baseChange (S.fromSpecStalk x)).isEffective_etaleFinitePresentation_of_etale
    (MorphismProperty.pullback_snd _ _ ha) (hx''.of_le etaleSeparatedFiniteType_le_etale)

end CompletedStalks

end SGA.SGA1.ExposeIX
