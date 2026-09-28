/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.FiniteEtaleExistence

/-!
# Étale coverings of a scheme proper over a complete base

Let `A` be a noetherian `I`-adically complete ring, `f : X ⟶ Spec A` proper and
`X₀ = X ×_A A / I`. We assume SGA 1 I.8.3 in the form of the hypothesis `h83`: base change along a
surjective closed immersion is an equivalence on étale coverings (as in
`Scheme.FormalFiniteEtale.isEquivalence_toZero`).

* `formalCompletionFunctor`: `Y ↦ (Y ×_X X_n)_n`, from étale coverings of `X` to étale coverings
  of the formal completion (`Scheme.FormalFiniteEtale (thickeningDiagram I f)`);
* `faithful_pullback_thickening`, `full_pullback_thickening`: `Y ↦ Y ×_X X₀` is fully faithful on
  étale coverings (`X` proper), from `eq_of_forall_pullback_thickening_comp_eq` and
  `exists_hom_of_forall_pullback_thickening` and the equivalence of the formal side with `X₀`;
* `essSurj_pullback_thickening`: for `X` closed in `ℙ(τ; Spec A)`, it is essentially surjective
  (`exists_finiteEtale_of_formalFiniteEtale`);
* `isEquivalence_pullback_thickening`: hence an equivalence (SGA 1 IX.1.10, X.2.1, projective case);
* `isEquivalence_pullback_closedFibre`: the same for a complete noetherian local ring `A` and the
  closed fibre `X ×_A k`, with étale coverings `MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤`.
-/

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme (FiniteEtale FormalFiniteEtale)

section FormalCompletionFunctor

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

lemma thickeningDiagram_map_ι (n : ℕ) :
    thickening.ι f I n = (thickeningDiagram I f).map (homOfLE n.le_succ) ≫
      thickening.ι f I (n + 1) := by
  rw [thickeningDiagram_map]
  exact (thickening.transition_ι f I n).symm

/-- The comparison `(Y ×_X X_{n+1}) ×_{X_{n+1}} X_n ≅ Y ×_X X_n` of étale coverings. -/
abbrev formalCompletionIso (n : ℕ) :=
  MorphismProperty.Over.pullbackComp (P := Scheme.finiteEtaleHom.{u}) (Q := ⊤)
    ((thickeningDiagram I f).map (homOfLE n.le_succ)) (thickening.ι f I (n + 1))
    (thickening.ι f I n) (thickeningDiagram_map_ι I f n)

/-- **The formal completion of étale coverings**: `Y ↦ (Y ×_X X_n)_n`, from étale coverings of
`X` to étale coverings of the formal completion of `X` along `f⁻¹ V(I)`. -/
def formalCompletionFunctor : X.FiniteEtale ⥤ FormalFiniteEtale (thickeningDiagram I f) where
  obj Y :=
    { obj := fun n ↦ (FiniteEtale.pullback (thickening.ι f I n)).obj Y
      iso := fun n ↦ ((formalCompletionIso I f n).app Y).symm }
  map {Y Y'} u :=
    { app := fun n ↦ (FiniteEtale.pullback (thickening.ι f I n)).map u
      comm := fun n ↦ (formalCompletionIso I f n).inv.naturality u }
  map_id Y := by
    ext n : 1
    exact (FiniteEtale.pullback (thickening.ι f I n)).map_id Y
  map_comp u v := by
    ext n : 1
    exact (FiniteEtale.pullback (thickening.ι f I n)).map_comp u v

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
lemma formalCompletion_iso_inv_left_fst (Y : X.FiniteEtale) (n : ℕ) :
    (((formalCompletionFunctor I f).obj Y).iso n).inv.left ≫ pullback.fst _ _ =
      thickeningPullbackMap I f Y.hom n := by
  apply pullback.hom_ext
  · simp [formalCompletionFunctor, thickeningPullbackMap]
  · simp [formalCompletionFunctor, thickeningPullbackMap]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma finiteEtale_pullback_map_left_fst {X' : Scheme.{u}} (g : X' ⟶ X) {Y Y' : X.FiniteEtale}
    (u : Y ⟶ Y') :
    ((FiniteEtale.pullback g).map u).left ≫ pullback.fst Y'.hom g =
      pullback.fst Y.hom g ≫ u.left := by
  simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc]
lemma finiteEtale_pullback_map_left_snd {X' : Scheme.{u}} (g : X' ⟶ X) {Y Y' : X.FiniteEtale}
    (u : Y ⟶ Y') :
    ((FiniteEtale.pullback g).map u).left ≫ pullback.snd Y'.hom g = pullback.snd Y.hom g := by
  simp

end FormalCompletionFunctor

section Equivalence

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]
  (h83 : ∀ ⦃X Y : Scheme.{u}⦄ (i : X ⟶ Y), IsClosedImmersion i → Surjective i →
    (FiniteEtale.pullback i).IsEquivalence)

instance finiteEtale_isFinite_hom {S : Scheme.{u}} (Y : S.FiniteEtale) : IsFinite Y.hom :=
  ((Scheme.finiteEtaleHom_iff _).mp Y.prop).1

instance finiteEtale_etale_hom {S : Scheme.{u}} (Y : S.FiniteEtale) : Etale Y.hom :=
  ((Scheme.finiteEtaleHom_iff _).mp Y.prop).2

omit [IsNoetherianRing A] [IsAdicComplete I A] [IsProper f] in
include h83 in
lemma isEquivalence_formalToZero :
    (FormalFiniteEtale.toZero (thickeningDiagram I f)).IsEquivalence :=
  FormalFiniteEtale.isEquivalence_toZero _ h83

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include h83 in
/-- **Faithfulness on étale coverings** (SGA 1 IX.1.10): over a complete noetherian base, two
morphisms of étale coverings of `X` proper over `Spec A` which agree over `X₀` are equal. -/
theorem faithful_pullback_thickening :
    (FiniteEtale.pullback (thickening.ι f I 0)).Faithful := by
  have := isEquivalence_formalToZero I f h83
  refine ⟨fun {Y Y'} u v huv ↦ ?_⟩
  have hΦ : (formalCompletionFunctor I f).map u = (formalCompletionFunctor I f).map v :=
    (FormalFiniteEtale.toZero (thickeningDiagram I f)).map_injective huv
  ext
  refine eq_of_forall_pullback_thickening_comp_eq I f (MorphismProperty.Over.w u)
    (MorphismProperty.Over.w v) fun n ↦ ?_
  have h := congrArg (fun w : (formalCompletionFunctor I f).obj Y ⟶
    (formalCompletionFunctor I f).obj Y' ↦ (TowerLimit.Hom.app w n).left) hΦ
  simp only [formalCompletionFunctor] at h
  rw [← finiteEtale_pullback_map_left_fst, ← finiteEtale_pullback_map_left_fst, h]

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include h83 in
/-- **Fullness on étale coverings** (SGA 1 IX.1.10): over a complete noetherian base, every
morphism over `X₀` of the restrictions of étale coverings of `X` proper over `Spec A` comes from
a morphism of étale coverings. -/
theorem full_pullback_thickening :
    (FiniteEtale.pullback (thickening.ι f I 0)).Full := by
  have := isEquivalence_formalToZero I f h83
  refine ⟨fun {Y Y'} φ₀ ↦ ?_⟩
  obtain ⟨h, hh⟩ := (FormalFiniteEtale.toZero (thickeningDiagram I f)).map_surjective
    (X := (formalCompletionFunctor I f).obj Y) (Y := (formalCompletionFunctor I f).obj Y') φ₀
  let ψ : ∀ n, pullback Y.hom (thickening.ι f I n) ⟶ Y'.left := fun n ↦
    (h.app n).left ≫ pullback.fst Y'.hom (thickening.ι f I n)
  have hsnd : ∀ n, (h.app n).left ≫ pullback.snd Y'.hom (thickening.ι f I n) =
      pullback.snd Y.hom (thickening.ι f I n) := fun n ↦ MorphismProperty.Over.w (h.app n)
  have hψ : ∀ n, ψ n ≫ Y'.hom = pullback.fst Y.hom (thickening.ι f I n) ≫ Y.hom := fun n ↦ by
    simp only [ψ, Category.assoc, pullback.condition]
    rw [reassoc_of% hsnd n]
  have hc : ∀ n, thickeningPullbackMap I f Y.hom n ≫ ψ (n + 1) = ψ n := fun n ↦ by
    have hcomm : ((Scheme.finiteEtaleTower (thickeningDiagram I f) n).map (h.app (n + 1))).left ≫
        (((formalCompletionFunctor I f).obj Y').iso n).hom.left =
          (((formalCompletionFunctor I f).obj Y).iso n).hom.left ≫ (h.app n).left := by
      rw [← MorphismProperty.Comma.comp_left, ← MorphismProperty.Comma.comp_left, h.comm n]
    have hinv : ∀ Z : X.FiniteEtale, (((formalCompletionFunctor I f).obj Z).iso n).inv.left ≫
        (((formalCompletionFunctor I f).obj Z).iso n).hom.left = 𝟙 _ := fun Z ↦ by
      rw [← MorphismProperty.Comma.comp_left, Iso.inv_hom_id]
      rfl
    have hinv' : ∀ Z : X.FiniteEtale, (((formalCompletionFunctor I f).obj Z).iso n).hom.left ≫
        (((formalCompletionFunctor I f).obj Z).iso n).inv.left = 𝟙 _ := fun Z ↦ by
      rw [← MorphismProperty.Comma.comp_left, Iso.hom_inv_id]
      rfl
    have k : pullback.fst ((FiniteEtale.pullback (thickening.ι f I (n + 1))).obj Y').hom
          ((thickeningDiagram I f).map (homOfLE n.le_succ)) ≫
        pullback.fst Y'.hom (thickening.ι f I (n + 1)) =
          (((formalCompletionFunctor I f).obj Y').iso n).hom.left ≫
            pullback.fst Y'.hom (thickening.ι f I n) := by
      rw [← thickeningPullbackMap_fst I f Y'.hom n, ← formalCompletion_iso_inv_left_fst I f Y' n,
        ← Category.assoc, reassoc_of% hinv' Y']
      rfl
    rw [← formalCompletion_iso_inv_left_fst I f Y n]
    simp only [ψ, Category.assoc]
    rw [← finiteEtale_pullback_map_left_fst_assoc]
    erw [k]
    rw [reassoc_of% hcomm, reassoc_of% hinv Y]
  obtain ⟨w, hw, hwn⟩ := exists_hom_of_forall_pullback_thickening I f ψ hψ
    (thickeningPullbackMap I f Y.hom) (thickeningPullbackMap_fst I f Y.hom) hc
  refine ⟨MorphismProperty.Over.homMk w hw, ?_⟩
  rw [← hh]
  ext : 1
  apply pullback.hom_ext
  · rw [finiteEtale_pullback_map_left_fst]
    exact hwn 0
  · rw [finiteEtale_pullback_map_left_snd]
    exact (hsnd 0).symm

omit [IsProper f] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
include h83 in
/-- **Essential surjectivity on étale coverings, projective case** (SGA 1 IX.1.10; EGA III 5.4.5):
over a complete noetherian base, every étale covering of `X₀` extends to an étale covering of `X`
closed in `ℙ(τ; Spec A)`. -/
theorem essSurj_pullback_thickening {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A))
    [IsClosedImmersion κ] (hf : f = κ ≫ ℙ(τ; Spec A) ↘ Spec A) :
    (FiniteEtale.pullback (thickening.ι f I 0)).EssSurj := by
  have := isEquivalence_formalToZero I f h83
  refine ⟨fun Y₀ ↦ ?_⟩
  let 𝒴 := (FormalFiniteEtale.toZero (thickeningDiagram I f)).objPreimage Y₀
  obtain ⟨Y, p, hfin, het, e, he⟩ := exists_finiteEtale_of_formalFiniteEtale I κ f hf 𝒴
  refine ⟨MorphismProperty.Over.mk ⊤ p ⟨hfin, het⟩, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk e he ≪≫
    (FormalFiniteEtale.toZero (thickeningDiagram I f)).objObjPreimageIso Y₀

include h83 in
/-- **Grothendieck's theorem on étale coverings over a complete base, projective case**
(SGA 1 IX.1.10, X.2.1; EGA III 5.4.5 and SGA 1 I.8.3): let `A` be a noetherian `I`-adically
complete ring and `X` a closed subscheme of `ℙ(τ; Spec A)`, `X₀ = X ×_A A / I`. Assuming SGA 1
I.8.3 (base change along a surjective closed immersion is an equivalence on étale coverings,
the hypothesis `h83`), `Y ↦ Y ×_X X₀` is an equivalence from étale coverings of `X` to étale
coverings of `X₀`. -/
theorem isEquivalence_pullback_thickening {τ : Type u} [Finite τ] (κ : X ⟶ ℙ(τ; Spec A))
    [IsClosedImmersion κ] (hf : f = κ ≫ ℙ(τ; Spec A) ↘ Spec A) :
    (FiniteEtale.pullback (thickening.ι f I 0)).IsEquivalence where
  faithful := faithful_pullback_thickening I f h83
  full := full_pullback_thickening I f h83
  essSurj := essSurj_pullback_thickening I f h83 κ hf

end Equivalence

section ClosedFibre

open IsLocalRing in
set_option backward.isDefEq.respectTransparency false in
/-- **Grothendieck's theorem on étale coverings of a projective scheme over a complete local
ring** (SGA 1 IX.1.10 and X.2.1 in the projective case; EGA III 5.4.5): let `A` be a complete
noetherian local ring with residue field `k`, `X` a closed subscheme of `ℙ(τ; Spec A)` and
`X₀ = X ×_A k` the closed fibre. Assuming SGA 1 I.8.3 (the hypothesis `h83`), base change
`Y ↦ Y ×_X X₀` is an equivalence from finite étale `X`-schemes to finite étale `X₀`-schemes. -/
theorem isEquivalence_pullback_closedFibre (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsAdicComplete (maximalIdeal A) A] {X : Scheme.{u}} {τ : Type u}
    [Finite τ] (κ : X ⟶ ℙ(τ; Spec (.of A))) [IsClosedImmersion κ]
    (h83 : ∀ ⦃X Y : Scheme.{u}⦄ (i : X ⟶ Y), IsClosedImmersion i → Surjective i →
      (FiniteEtale.pullback i).IsEquivalence) :
    (MorphismProperty.Over.pullback (@IsFinite ⊓ @Etale) ⊤
      (pullback.fst (κ ≫ ℙ(τ; Spec (.of A)) ↘ Spec (.of A))
        (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A)))))).IsEquivalence := by
  have : IsNoetherianRing (CommRingCat.of A) := ‹_›
  have : IsAdicComplete (maximalIdeal A) (CommRingCat.of A) := ‹_›
  let f := κ ≫ ℙ(τ; Spec (.of A)) ↘ Spec (.of A)
  have hmain := isEquivalence_pullback_thickening (A := .of A) (maximalIdeal A) f h83 κ rfl
  let e : CommRingCat.of (A ⧸ maximalIdeal A ^ (0 + 1)) ≅ CommRingCat.of (ResidueField A) :=
    (Ideal.quotEquivOfEq (by rw [zero_add, pow_one])).toCommRingCatIso
  have he : CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal A ^ (0 + 1))) ≫ e.hom =
      CommRingCat.ofHom (algebraMap A (ResidueField A)) := by
    ext a
    rfl
  let j : pullback f (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField A)))) ⟶
      thickening f (maximalIdeal A) 0 :=
    pullback.map _ _ _ _ (𝟙 X) (Spec.map e.hom) (𝟙 _) (by simp)
      (by rw [← he, Spec.map_comp, Category.comp_id])
  have hj : j ≫ thickening.ι f (maximalIdeal A) 0 = pullback.fst _ _ := by
    simp [j, thickening.ι]
  have hjeq : (FiniteEtale.pullback j).IsEquivalence := h83 j inferInstance inferInstance
  have hcomp : (FiniteEtale.pullback (thickening.ι f (maximalIdeal A) 0) ⋙
      FiniteEtale.pullback j).IsEquivalence := inferInstance
  have h₁ := Functor.isEquivalence_of_iso
    (MorphismProperty.Over.pullbackComp (P := Scheme.finiteEtaleHom.{u}) (Q := ⊤) j
      (thickening.ι f (maximalIdeal A) 0)).symm
  have h₂ := Functor.isEquivalence_of_iso
    (MorphismProperty.Over.pullbackCongr (P := Scheme.finiteEtaleHom.{u}) (Q := ⊤) hj)
  exact h₂

end ClosedFibre

end AlgebraicGeometry.CohomologyAux
