/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA1.ExposeIX.FiniteEffectiveDescent


/-!
# SGA 1, Exposé IX, 4.8: descent along universally submersive quasi-finite morphisms

IX.4.8 (`isEffectiveDescentMorphism_of_locallyQuasiFinite`): over a locally noetherian `S`, a
universally submersive, quasi-finite morphism of finite type `g : S' ⟶ S` is an effective descent
morphism for étale separated schemes of finite type.

Following SGA: by IX.4.5 one may assume `S = Spec R` with `R` a complete noetherian local ring.
By IX.2.5 (`universallySubmersive_iff_forall_exists_specializes`,
`exists_opens_forall_specializes_isFinite`) there is a finite surjective `T ⟶ Spec R` factoring
through `S'` (a finite sum of spectra of local rings of `S'` at points of the closed fibre).
The base change of the descent datum to `T` is effective, since `S' ×_S T ⟶ T` has a section
(`isEffective_of_section`); `T ⟶ Spec R` is an effective descent morphism by IX.4.7
(`isEffectiveDescentMorphism_of_isFinite`), and the "sorites of descent" in the form
`DescentDatum.isEffective_of_isEffective_baseChange` conclude.
-/

universe u

open CategoryTheory Limits MorphismProperty IsLocalRing

namespace SGA.SGA1.ExposeIX

open AlgebraicGeometry

/-- Finitely many finite morphisms `Zᵢ ⟶ S` factoring through `S'` combine to one finite
morphism `Z ⟶ S` factoring through `S'` whose image contains theirs. -/
lemma exists_isFinite_of_finset {ι : Type*} {S' S : Scheme.{u}} (g : S' ⟶ S)
    (Z : ι → Scheme.{u}) (h : ∀ i, Z i ⟶ S') (hf : ∀ i, IsFinite (h i ≫ g)) (s : Finset ι)
    (hs : s.Nonempty) :
    ∃ (T : Scheme.{u}) (φ : T ⟶ S'), IsFinite (φ ≫ g) ∧
      ∀ i ∈ s, Set.range (h i ≫ g) ⊆ Set.range (φ ≫ g) := by
  classical
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i => exact ⟨Z i, h i, hf i, by simp⟩
  | cons i s hi hs ih =>
    obtain ⟨T, φ, hφ, hsub⟩ := ih
    have := hf i
    refine ⟨Z i ⨿ T, coprod.desc (h i) φ, ?_, fun j hj ↦ ?_⟩
    · rw [coprod.desc_comp]; infer_instance
    · rcases Finset.mem_cons.mp hj with rfl | hj
      · rintro _ ⟨z, rfl⟩
        exact ⟨(coprod.inl : Z j ⟶ Z j ⨿ T) z, by
          rw [← Scheme.Hom.comp_apply, coprod.inl_desc_assoc]⟩
      · rintro _ ⟨z, rfl⟩
        obtain ⟨t, ht⟩ := hsub j hj ⟨z, rfl⟩
        exact ⟨(coprod.inr : T ⟶ Z i ⨿ T) t, by
          rw [← Scheme.Hom.comp_apply, coprod.inr_desc_assoc, ht]⟩

variable {S' S X' : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.8 over a complete noetherian local base: by IX.2.5, a universally submersive
quasi-finite `g : S' ⟶ Spec R` is dominated by a finite surjective `T ⟶ Spec R` factoring
through `S'`; the base change of the datum to `T` has a section, hence is effective, and one
concludes by IX.4.7 and the sorites of descent. -/
theorem DescentDatum.isEffective_of_locallyQuasiFinite_of_isAdicComplete {R : Type u}
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    {g : S' ⟶ Spec (.of R)} [UniversallySubmersive g] [LocallyOfFiniteType g] [QuasiCompact g]
    [LocallyQuasiFinite g] {a : X' ⟶ S'} (D : DescentDatum g a)
    (ha : etaleSeparatedFiniteType a) : D.IsEffective etaleSeparatedFiniteType := by
  classical
  have hfin : (g ⁻¹' {closedPoint R}).Finite := g.finite_preimage_singleton _
  let ι := ↥(g ⁻¹' {closedPoint R})
  have : Fintype ι := hfin.fintype
  choose W hyW hWsp hWfin using fun y : ι ↦ exists_opens_forall_specializes_isFinite g y.2 hfin
  have hcov := (universallySubmersive_iff_forall_exists_specializes g hfin).mp inferInstance
  obtain ⟨x₀, hx₀⟩ := g.surjective (closedPoint R)
  obtain ⟨T, φ, hφ, hsub⟩ := exists_isFinite_of_finset g (fun y : ι ↦ (W y).toScheme)
    (fun y ↦ (W y).ι) hWfin Finset.univ ⟨⟨x₀, hx₀⟩, Finset.mem_univ _⟩
  have : Surjective (φ ≫ g) := ⟨fun t ↦ by
    obtain ⟨x, rfl, y, hy, hxy⟩ := hcov t
    have hx : x ∈ W ⟨y, hy⟩ := hxy.mem_open (W _).isOpen (hyW _)
    exact hsub ⟨y, hy⟩ (Finset.mem_univ _) ⟨⟨x, hx⟩, rfl⟩⟩
  -- the base change of `g` to `T` has a section
  have hsec : pullback.lift φ (𝟙 T) (by simp) ≫ pullback.snd g (φ ≫ g) = 𝟙 T :=
    pullback.lift_snd _ _ _
  have hT := (D.baseChange (φ ≫ g)).isEffective_of_section hsec etaleSeparatedFiniteType
    (MorphismProperty.pullback_snd _ _ ha)
  exact D.isEffective_of_isEffective_baseChange (φ ≫ g) isEffectiveDescentMorphism_of_isFinite
    ha hT

set_option backward.isDefEq.respectTransparency false in
/-- IX.4.8: over a locally noetherian `S`, a universally submersive, quasi-finite morphism of
finite type is an effective descent morphism for étale separated schemes of finite type. -/
theorem isEffectiveDescentMorphism_of_locallyQuasiFinite [IsLocallyNoetherian S] (g : S' ⟶ S)
    [UniversallySubmersive g] [LocallyOfFiniteType g] [QuasiCompact g] [LocallyQuasiFinite g] :
    IsEffectiveDescentMorphism g etaleSeparatedFiniteType := by
  refine ⟨isDescentMorphism_of_le_etale etaleSeparatedFiniteType_le_etale,
    fun X' a D ha ↦ ?_⟩
  have := LocallyOfFiniteType.isLocallyNoetherian g
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := ha
  have : Etale a := h₁
  have : IsSeparated a := h₂
  have : QuasiCompact a := h₃
  have ha' : etaleFinitePresentation a := ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  have hfp : D.IsEffective etaleFinitePresentation := by
    rw [D.isEffective_iff_forall_fromSpecCompletedStalk ha']
    intro x
    exact (DescentDatum.isEffective_of_locallyQuasiFinite_of_isAdicComplete
      (D.baseChange (fromSpecCompletedStalk S x))
      (MorphismProperty.pullback_snd _ _ ⟨⟨h₁, h₂⟩, h₃⟩)).of_le fun _ _ f h ↦
        have : IsSeparated f := h.1.2; ⟨⟨h.1.1, h.2⟩, inferInstance⟩
  exact D.isEffective_etaleSeparatedFiniteType_of_etale ⟨⟨h₁, h₂⟩, h₃⟩
    (hfp.of_le fun _ _ _ h ↦ h.1.1)

end SGA.SGA1.ExposeIX
