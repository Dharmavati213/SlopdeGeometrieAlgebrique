/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.CohomologicalComparison
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Extending degree-zero comparisons by injective dimension shifting

For two cohomological sequences with natural boundaries and vanishing on
injectives, a degree-zero natural isomorphism extends to natural isomorphisms
in every degree. The maps are constructed from cokernels of the actual
boundaries on injective presentations; no higher comparison is assumed.
-/

noncomputable section

universe u v u' v' w

open CategoryTheory Limits

namespace SGA.SGA2.ExposeII.ConnectingSequence

set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Naturality of the genuine boundary under maps of short exact sequences. -/
def BoundaryNatural (F : ConnectingSequence C D) : Prop :=
  ∀ {S T : ShortComplex C} (φ : S ⟶ T) (hS : S.ShortExact) (hT : T.ShortExact) (n : ℕ),
    F.δ S hS n ≫ (F.obj (n + 1)).map φ.τ₁ =
      (F.obj n).map φ.τ₃ ≫ F.δ T hT n

/-- The actual derived-category Ext functors and coefficient boundaries. -/
def extSequence [HasExt.{w} C] (A : C) :
    ConnectingSequence C AddCommGrpCat.{w} where
  obj := Abelian.extFunctorObj A
  δ S hS n := AddCommGrpCat.ofHom (hS.extClass.postcomp A rfl)
  map_δ S hS n := by
    ext x
    exact Abelian.Ext.comp_assoc_of_second_deg_zero x (Abelian.Ext.mk₀ S.g) hS.extClass rfl
      |>.trans (by rw [hS.comp_extClass, Abelian.Ext.comp_zero]; rfl)
  δ_map S hS n := by
    ext x
    exact Abelian.Ext.comp_assoc_of_third_deg_zero x hS.extClass (Abelian.Ext.mk₀ S.f) rfl
      |>.trans (by rw [hS.extClass_comp, Abelian.Ext.comp_zero]; rfl)
  exact_left S hS n := Abelian.Ext.covariant_sequence_exact₃' A hS n (n + 1) rfl
  exact_right S hS n := Abelian.Ext.covariant_sequence_exact₁' A hS n (n + 1) rfl

theorem extSequence_boundaryNatural [HasExt.{w} C] (A : C) :
    (extSequence A).BoundaryNatural := by
  intro S T φ hS hT n
  ext x
  change (x.comp hS.extClass rfl).comp (Abelian.Ext.mk₀ φ.τ₁) (add_zero (n + 1)) =
    (x.comp (Abelian.Ext.mk₀ φ.τ₃) (add_zero n)).comp hT.extClass rfl
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.comp_assoc_of_second_deg_zero, hS.extClass_naturality hT φ]

section Precompose

variable {E : Type*} [Category* E] [Abelian E]

/-- Precompose a coefficient sequence with a functor preserving short exact sequences. -/
def precompose (F : ConnectingSequence D E) (L : C ⥤ D) [L.PreservesZeroMorphisms]
    (hL : ∀ {S : ShortComplex C}, S.ShortExact → (S.map L).ShortExact) :
    ConnectingSequence C E where
  obj n := L ⋙ F.obj n
  δ S hS n := F.δ (S.map L) (hL hS) n
  map_δ S hS n := F.map_δ (S.map L) (hL hS) n
  δ_map S hS n := F.δ_map (S.map L) (hL hS) n
  exact_left S hS n := F.exact_left (S.map L) (hL hS) n
  exact_right S hS n := F.exact_right (S.map L) (hL hS) n

theorem precompose_boundaryNatural (F : ConnectingSequence D E) (L : C ⥤ D)
    [L.PreservesZeroMorphisms]
    (hL : ∀ {S : ShortComplex C}, S.ShortExact → (S.map L).ShortExact)
    (hF : F.BoundaryNatural) : (precompose F L hL).BoundaryNatural := by
  intro S T φ hS hT n
  exact hF (L.mapShortComplex.map φ) (hL hS) (hL hT) n

end Precompose

section Postcompose

variable {E : Type*} [Category* E] [Abelian E]

/-- An exact additive functor preserves a cohomological sequence. -/
def postcompose (F : ConnectingSequence C D) (L : D ⥤ E)
    [L.Additive] [L.PreservesHomology] : ConnectingSequence C E where
  obj n := F.obj n ⋙ L
  δ S hS n := L.map (F.δ S hS n)
  map_δ S hS n := by
    dsimp only [Functor.comp_map]
    rw [← L.map_comp, F.map_δ, L.map_zero]
  δ_map S hS n := by
    dsimp only [Functor.comp_map]
    rw [← L.map_comp, F.δ_map, L.map_zero]
  exact_left S hS n := (F.exact_left S hS n).map L
  exact_right S hS n := (F.exact_right S hS n).map L

theorem postcompose_boundaryNatural (F : ConnectingSequence C D) (L : D ⥤ E)
    [L.Additive] [L.PreservesHomology] (hF : F.BoundaryNatural) :
    (postcompose F L).BoundaryNatural := by
  intro S T φ hS hT n
  dsimp only [postcompose, Functor.comp_map]
  rw [← L.map_comp, ← L.map_comp, hF φ hS hT n]

theorem postcompose_vanishesOnInjectives (F : ConnectingSequence C D) (L : D ⥤ E)
    [L.Additive] [L.PreservesHomology] (hF : F.VanishesOnInjectives) :
    (postcompose F L).VanishesOnInjectives := by
  intro X hX n
  exact L.map_isZero (hF X n)

end Postcompose

variable [EnoughInjectives C]

/-- A fixed injective presentation of an object, including its cokernel. -/
abbrev injectiveSequence (X : C) := ShortComplex.cokernelSequence (Injective.ι X)

theorem injectiveSequence_shortExact (X : C) : (injectiveSequence X).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact _
    mono_f := by change Mono (Injective.ι X); infer_instance
    epi_g := by change Epi (cokernel.π (Injective.ι X)); infer_instance }

/-- Every coefficient morphism extends to a morphism of the fixed injective
presentations; no functorial choice of injective embeddings is required. -/
def injectiveSequenceMap {X Y : C} (f : X ⟶ Y) :
    injectiveSequence X ⟶ injectiveSequence Y where
  τ₁ := f
  τ₂ := show Injective.under X ⟶ Injective.under Y from
    Injective.factorThru (f ≫ Injective.ι Y) (Injective.ι X)
  τ₃ := cokernel.map _ _ f
    (Injective.factorThru (f ≫ Injective.ι Y) (Injective.ι X)) (by simp)
  comm₁₂ := by simp
  comm₂₃ := by simp

/-- Embed any short exact sequence in the fixed injective presentation of
its first object, leaving that first object unchanged. -/
def toInjectiveSequence (S : ShortComplex C) (hS : S.ShortExact) :
    S ⟶ injectiveSequence S.X₁ := by
  have := hS.mono_f
  have := hS.epi_g
  let t := Injective.factorThru (Injective.ι S.X₁) S.f
  have ht : S.f ≫ t = Injective.ι S.X₁ := Injective.comp_factorThru _ _
  have hw : S.f ≫ (t ≫ cokernel.π (Injective.ι S.X₁)) = 0 := by
    rw [← Category.assoc, ht, cokernel.condition]
  refine
    { τ₁ := 𝟙 S.X₁
      τ₂ := t
      τ₃ := hS.exact.gIsCokernel.desc (CokernelCofork.ofπ _ hw)
      comm₁₂ := by simpa using ht.symm
      comm₂₃ := ?_ }
  exact (hS.exact.gIsCokernel.fac
    (CokernelCofork.ofπ (t ≫ cokernel.π (Injective.ι S.X₁)) hw) WalkingParallelPair.one).symm

variable (F G : ConnectingSequence C D)

theorem injectiveBoundary_epi (hF : F.VanishesOnInjectives) (X : C) (n : ℕ) :
    Epi (F.δ (injectiveSequence X) (injectiveSequence_shortExact X) n) := by
  have hz : (F.obj (n + 1)).map (injectiveSequence X).f = 0 :=
    (hF (Injective.under X) n).eq_of_tgt _ _
  exact (ShortComplex.exact_iff_epi _ hz).mp
    (F.exact_right (injectiveSequence X) (injectiveSequence_shortExact X) n)

/-- The boundary onto the next degree is the cokernel of the preceding map
when the middle term is injective. -/
def injectiveBoundaryIsCokernel (hF : F.VanishesOnInjectives) (X : C) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (F.δ (injectiveSequence X) (injectiveSequence_shortExact X) n)
      (F.map_δ (injectiveSequence X) (injectiveSequence_shortExact X) n)) := by
  have := injectiveBoundary_epi F hF X n
  exact (F.exact_left (injectiveSequence X) (injectiveSequence_shortExact X) n).gIsCokernel

set_option backward.isDefEq.respectTransparency false in
/-- Extend a degree-`n` comparison to degree `n + 1` on an individual object. -/
def successorMap (hF : F.VanishesOnInjectives) {n : ℕ}
    (α : F.obj n ⟶ G.obj n) (X : C) :
    (F.obj (n + 1)).obj X ⟶ (G.obj (n + 1)).obj X :=
  (injectiveBoundaryIsCokernel F hF X n).desc
    (CokernelCofork.ofπ
      (α.app (injectiveSequence X).X₃ ≫
        G.δ (injectiveSequence X) (injectiveSequence_shortExact X) n)
      (by rw [α.naturality_assoc, G.map_δ, comp_zero]))

@[reassoc]
theorem δ_successorMap (hF : F.VanishesOnInjectives) {n : ℕ}
    (α : F.obj n ⟶ G.obj n) (X : C) :
    F.δ (injectiveSequence X) (injectiveSequence_shortExact X) n ≫
      successorMap F G hF α X =
    α.app (injectiveSequence X).X₃ ≫
      G.δ (injectiveSequence X) (injectiveSequence_shortExact X) n :=
  (injectiveBoundaryIsCokernel F hF X n).fac _ WalkingParallelPair.one

/-- The constructed successor comparison respects every coefficient boundary,
not just the boundaries of the chosen injective presentations. -/
@[reassoc]
theorem δ_successorMap_general (hF : F.VanishesOnInjectives)
    (natF : F.BoundaryNatural) (natG : G.BoundaryNatural) {n : ℕ}
    (α : F.obj n ⟶ G.obj n) (S : ShortComplex C) (hS : S.ShortExact) :
    F.δ S hS n ≫ successorMap F G hF α S.X₁ = α.app S.X₃ ≫ G.δ S hS n := by
  let φ := toInjectiveSequence S hS
  have hFφ : F.δ S hS n = (F.obj n).map φ.τ₃ ≫
      F.δ (injectiveSequence S.X₁) (injectiveSequence_shortExact S.X₁) n := by
    calc
      _ = F.δ S hS n ≫ (F.obj (n + 1)).map (𝟙 S.X₁) := by simp
      _ = _ := natF φ hS (injectiveSequence_shortExact S.X₁) n
  have hGφ : G.δ S hS n = (G.obj n).map φ.τ₃ ≫
      G.δ (injectiveSequence S.X₁) (injectiveSequence_shortExact S.X₁) n := by
    calc
      _ = G.δ S hS n ≫ (G.obj (n + 1)).map (𝟙 S.X₁) := by simp
      _ = _ := natG φ hS (injectiveSequence_shortExact S.X₁) n
  rw [hFφ, Category.assoc, δ_successorMap, α.naturality_assoc, ← hGφ]

set_option backward.isDefEq.respectTransparency false in
/-- Boundary naturality makes the recursively constructed comparison natural. -/
def successorNatTrans (hF : F.VanishesOnInjectives)
    (natF : F.BoundaryNatural) (natG : G.BoundaryNatural) {n : ℕ}
    (α : F.obj n ⟶ G.obj n) : F.obj (n + 1) ⟶ G.obj (n + 1) where
  app := successorMap F G hF α
  naturality {X Y} f := by
    have := injectiveBoundary_epi F hF X n
    apply (cancel_epi (F.δ (injectiveSequence X) (injectiveSequence_shortExact X) n)).mp
    let φ := injectiveSequenceMap f
    have hFφ := natF φ (injectiveSequence_shortExact X) (injectiveSequence_shortExact Y) n
    have hGφ := natG φ (injectiveSequence_shortExact X) (injectiveSequence_shortExact Y) n
    change F.δ _ _ n ≫ (F.obj (n + 1)).map φ.τ₁ ≫ successorMap F G hF α Y =
      F.δ _ _ n ≫ successorMap F G hF α X ≫ (G.obj (n + 1)).map φ.τ₁
    rw [← Category.assoc, hFφ, Category.assoc, δ_successorMap,
      α.naturality_assoc, ← hGφ, ← δ_successorMap_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem successorMap_isIso (hF : F.VanishesOnInjectives) (hG : G.VanishesOnInjectives)
    {n : ℕ} (e : F.obj n ≅ G.obj n) (X : C) :
    IsIso (successorMap F G hF e.hom X) := by
  let S := injectiveSequence X
  let hS := injectiveSequence_shortExact X
  let ψ : ComposableArrows.mk₂ ((F.obj n).map S.g) (F.δ S hS n) ⟶
      ComposableArrows.mk₂ ((G.obj n).map S.g) (G.δ S hS n) :=
    ComposableArrows.homMk₂ (e.hom.app S.X₂) (e.hom.app S.X₃)
      (successorMap F G hF e.hom X) (e.hom.naturality S.g) (δ_successorMap F G hF e.hom X)
  exact Abelian.isIso_of_epi_of_isIso ψ
    (F.exact_left S hS n).exact_toComposableArrows
    (G.exact_left S hS n).exact_toComposableArrows
    (injectiveBoundary_epi F hF X n) (injectiveBoundary_epi G hG X n)
    (show Epi (e.hom.app S.X₂) from inferInstance)
    (show IsIso (e.hom.app S.X₃) from inferInstance)

/-- Dimension shifting extends a natural isomorphism by one degree. -/
def successorNatIso (hF : F.VanishesOnInjectives) (hG : G.VanishesOnInjectives)
    (natF : F.BoundaryNatural) (natG : G.BoundaryNatural) {n : ℕ}
    (e : F.obj n ≅ G.obj n) : F.obj (n + 1) ≅ G.obj (n + 1) := by
  let α := successorNatTrans F G hF natF natG e.hom
  have (X : C) : IsIso (α.app X) := successorMap_isIso F G hF hG e X
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact asIso α

/-- Two injective-acyclic cohomological sequences agreeing naturally in degree
zero agree naturally in every degree. Higher comparisons are constructed. -/
def extendNatIso (hF : F.VanishesOnInjectives) (hG : G.VanishesOnInjectives)
    (natF : F.BoundaryNatural) (natG : G.BoundaryNatural)
    (e₀ : F.obj 0 ≅ G.obj 0) : ∀ n : ℕ, F.obj n ≅ G.obj n
  | 0 => e₀
  | n + 1 => successorNatIso F G hF hG natF natG
      (extendNatIso hF hG natF natG e₀ n)

/-- The all-degree natural isomorphism commutes with all genuine coefficient
boundaries, so it is a comparison of cohomological sequences. -/
@[reassoc]
theorem extendNatIso_comm (hF : F.VanishesOnInjectives) (hG : G.VanishesOnInjectives)
    (natF : F.BoundaryNatural) (natG : G.BoundaryNatural)
    (e₀ : F.obj 0 ≅ G.obj 0) (S : ShortComplex C) (hS : S.ShortExact) (n : ℕ) :
    F.δ S hS n ≫ (extendNatIso F G hF hG natF natG e₀ (n + 1)).hom.app S.X₁ =
      (extendNatIso F G hF hG natF natG e₀ n).hom.app S.X₃ ≫ G.δ S hS n :=
  δ_successorMap_general F G hF natF natG
    (extendNatIso F G hF hG natF natG e₀ n).hom S hS

/-- The constructed extension as a morphism of cohomological sequences. -/
def extendHom (hF : F.VanishesOnInjectives) (hG : G.VanishesOnInjectives)
    (natF : F.BoundaryNatural) (natG : G.BoundaryNatural)
    (e₀ : F.obj 0 ≅ G.obj 0) : Hom F G where
  app n := (extendNatIso F G hF hG natF natG e₀ n).hom
  comm := extendNatIso_comm F G hF hG natF natG e₀

/-- A boundary-compatible comparison out of an injective-acyclic sequence
is uniquely determined by its degree-zero component. -/
theorem Hom.app_eq_of_degree_zero (hF : F.VanishesOnInjectives)
    (φ ψ : Hom F G) (hzero : φ.app 0 = ψ.app 0) (n : ℕ) : φ.app n = ψ.app n := by
  induction n with
  | zero => exact hzero
  | succ n hn =>
    apply NatTrans.ext
    funext X
    have := injectiveBoundary_epi F hF X n
    apply (cancel_epi (F.δ (injectiveSequence X) (injectiveSequence_shortExact X) n)).mp
    erw [φ.comm (injectiveSequence X) (injectiveSequence_shortExact X),
      ψ.comm (injectiveSequence X) (injectiveSequence_shortExact X), hn]

end SGA.SGA2.ExposeII.ConnectingSequence
