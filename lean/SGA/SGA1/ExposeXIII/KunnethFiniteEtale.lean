/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA1.ExposeV.FundamentalGroupCovering
import SGA.SGA1.ExposeXIII.KunnethMain

/-!
# SGA 1, XIII.4.6: invariance under algebraically closed base change passes to étale coverings

Let `k` be algebraically closed. If a `k`-scheme `X` has the invariance property
(`HasAlgClosedBaseChangeInvariance`, X.1.8 for `X`: `FEt(X) ≌ FEt(X ⊗ₖ k')` for every
algebraically closed `k' ⊇ k`), so does every connected étale covering `C` of `X`
(`HasAlgClosedBaseChangeInvariance.of_isFinite_of_etale`). Surjectivity of
`π₁(C ⊗ₖ k') → π₁(C)` holds in general (`ExposeX.surjective_map_pullback_fst_of_isAlgClosed`).
For injectivity we argue with the coverings: an étale covering `Y` of `C ⊗ₖ k'` is also an étale
covering of `X ⊗ₖ k'`, hence of the form `E ⊗ₖ k'`, and its graph embeds `Y` into
`(E ×_X C) ⊗ₖ k'`; an automorphism of the fibre functor which is trivial on the latter is trivial
on `Y` (`hom_app_eq_id_of_mono`).

This is used in the resolution-free route to XIII.4.6 in characteristic `0`: the smooth affine
curves of the transcendence-degree induction can be chosen étale over open subsets of `𝔸¹`
(`exists_le_fg_invariance_of_trdeg_le_one`).

We also record a domination criterion (`hasAlgClosedBaseChangeInvariance_of_forall_exists_hom`):
`X` has the invariance property as soon as every connected étale covering of `X ⊗ₖ k'` receives
a morphism from `E ⊗ₖ k'` for a connected étale covering `E` of `X`. This is the form in which the
case of the open subsets of `𝔸¹` (`AffineLineOpenInvarianceStatement`) is expected to be proved:
a covering `W` of `U ⊗ₖ k'` pulled back to a suitable Kummer covering `V` of `U` extends, by
Abhyankar's lemma, to the smooth compactification of `V ⊗ₖ k'`, where X.1.8 applies.
-/

universe u

open CategoryTheory Limits AlgebraicGeometry PreGaloisCategory

namespace SGA.SGA1.ExposeXIII

/-- An automorphism `σ` of a functor `G` preserving monomorphisms (e.g. a fibre functor of a
Galois category) which is the identity at `B` is the identity at every subobject `A ↪ B`. -/
lemma hom_app_eq_id_of_mono {C D : Type*} [Category C] [Category D] {G : C ⥤ D}
    [G.PreservesMonomorphisms] (σ : G ≅ G) {A B : C} (g : A ⟶ B) [Mono g]
    (h : σ.hom.app B = 𝟙 _) : σ.hom.app A = 𝟙 _ := by
  have := σ.hom.naturality g
  rw [h, Category.comp_id] at this
  rw [← cancel_mono (G.map g), Category.id_comp]
  exact this.symm

/-- An automorphism `σ` of a functor `G` preserving epimorphisms (e.g. a fibre functor of a
Galois category) which is the identity at `A` is the identity at every quotient `A ↠ B`. -/
lemma hom_app_eq_id_of_epi {C D : Type*} [Category C] [Category D] {G : C ⥤ D}
    [G.PreservesEpimorphisms] (σ : G ≅ G) {A B : C} (g : A ⟶ B) [Epi g]
    (h : σ.hom.app A = 𝟙 _) : σ.hom.app B = 𝟙 _ := by
  have := σ.hom.naturality g
  rw [h, Category.id_comp] at this
  rw [← cancel_epi (G.map g), Category.comp_id]
  exact this

variable {k : Type u} [Field k] [IsAlgClosed k]

set_option backward.isDefEq.respectTransparency false in
/-- The invariance of étale coverings under algebraically closed base change (X.1.8 for `X`)
passes to connected étale coverings: if `X` has the invariance property over the algebraically
closed field `k` and `p : C ⟶ X` is finite étale with `C` connected, then `C` (over `k` through
`p`) has it. -/
theorem HasAlgClosedBaseChangeInvariance.of_isFinite_of_etale {X C : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : HasAlgClosedBaseChangeInvariance sX) (p : C ⟶ X) [IsFinite p]
    [Etale p] [ConnectedSpace C] {sC : C ⟶ Spec (.of k)} (w : p ≫ sX = sC) :
    HasAlgClosedBaseChangeInvariance sC := by
  subst w
  intro k' _ _ _
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let πC := pullback.fst (p ≫ sX) ρ
  let πX := pullback.fst sX ρ
  -- the base change `q : C ⊗ₖ k' ⟶ X ⊗ₖ k'` of `p`
  let q : pullback (p ≫ sX) ρ ⟶ pullback sX ρ :=
    pullback.lift (πC ≫ p) (pullback.snd _ _) (by rw [Category.assoc, pullback.condition])
  have hq : IsPullback πC q p πX := by
    refine IsPullback.of_bot ?_ (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback sX ρ)
    rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (p ≫ sX) ρ
  have : IsFinite q := MorphismProperty.of_isPullback hq ‹_›
  have : Etale q := MorphismProperty.of_isPullback hq ‹_›
  have hqfe : ExposeV.finiteEtaleHom q := ⟨inferInstance, inferInstance⟩
  have := hX k'
  -- fibre functors
  have : ConnectedSpace (Spec (.of k')) := inferInstance
  have : ConnectedSpace ↥(pullback (p ≫ sX) ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace (p ≫ sX) ρ
  obtain ⟨z⟩ : Nonempty ↥(pullback (p ≫ sX) ρ) := inferInstance
  let Ω := AlgebraicClosure ((pullback (p ≫ sX) ρ).residueField z)
  let x : Spec (.of Ω) ⟶ pullback (p ≫ sX) ρ := ExposeX.geometricPoint _ z
  let F' := ExposeV.FEt.fiber Ω x
  have : FiberFunctor (ExposeV.FEt.pullback πC ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω πC x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (ExposeV.FEt.pullback πC ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (ExposeV.FEt.pullback πC) F']
  refine ⟨(injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_, ?_⟩
  · apply Iso.ext
    refine NatTrans.ext (funext fun Y ↦ ?_)
    have hσE : ∀ E : ExposeV.FEt C, σ.hom.app ((ExposeV.FEt.pullback πC).obj E) = 𝟙 _ :=
      fun E ↦ congrArg (fun τ : Aut (ExposeV.FEt.pullback πC ⋙ F') ↦ τ.hom.app E) hσ
    change σ.hom.app Y = 𝟙 _
    -- `Y` as an étale covering of `X ⊗ₖ k'` comes from an étale covering `E` of `X`
    let Y' := (ExposeV.FEt.postcomp q hqfe).obj Y
    let E := (ExposeV.FEt.pullback πX).objPreimage Y'
    let e : (ExposeV.FEt.pullback πX).obj E ≅ Y' := (ExposeV.FEt.pullback πX).objObjPreimageIso Y'
    -- `σ` is trivial on `q^* Y' ≅ q^* πX^* E ≅ πC^* p^* E`
    have h₁ : σ.hom.app ((ExposeV.FEt.pullback q).obj Y') = 𝟙 _ :=
      ExposeV.aut_app_eq_id_of_iso σ ((ExposeV.FEt.pullback q).mapIso e)
        (hom_app_pullback_pullback_eq_id σ πC p q πX hq.w E (hσE _))
    -- the graph of `Y ⟶ C ⊗ₖ k'` embeds `Y` into `q^* Y'`
    let γ : Y ⟶ (ExposeV.FEt.pullback q).obj Y' :=
      MorphismProperty.Over.homMk (pullback.lift (𝟙 Y.left) Y.hom (by simp [Y']))
        (pullback.lift_snd _ _ _)
    have : Mono γ := by
      have : Mono γ.left := by
        have : IsSplitMono γ.left := ⟨⟨pullback.fst _ _, pullback.lift_fst _ _ _⟩⟩
        infer_instance
      exact (MorphismProperty.Over.forget _ _ _ ⋙ Over.forget _).mono_of_mono_map this
    exact hom_app_eq_id_of_mono σ γ h₁
  · -- surjectivity: connected coverings of `C` stay connected over `k'`
    have hsurj := ExposeX.surjective_map_pullback_fst_of_isAlgClosed (p ≫ sX) k' Ω x
    rwa [ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.Surjective.of_comp_iff' (MulEquiv.bijective _)] at hsurj

set_option backward.isDefEq.respectTransparency false in
/-- A domination criterion for the invariance property: let `X` be connected over the
algebraically closed field `k`. If for every algebraically closed `k' ⊇ k`, every connected
étale covering `W` of `X ⊗ₖ k'` receives a morphism from `E ⊗ₖ k'` for some connected étale
covering `E` of `X`, then `X` has the invariance property (`HasAlgClosedBaseChangeInvariance`).
(The morphism is an epimorphism since `W` is connected, so an automorphism of the fibre functor
trivial on the coverings coming from `X` is trivial on `W`; every covering is a sum of connected
ones.) -/
theorem hasAlgClosedBaseChangeInvariance_of_forall_exists_hom {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} [ConnectedSpace X]
    (h : ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] [Algebra k k']
      (W : ExposeV.FEt (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k k'))))),
      IsConnected W → ∃ (E : ExposeV.FEt X) (_ : IsConnected E),
        Nonempty ((ExposeV.FEt.pullback
          (pullback.fst sX (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj E ⟶ W)) :
    HasAlgClosedBaseChangeInvariance sX := by
  intro k' _ _ _
  let ρ := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let π := pullback.fst sX ρ
  have : ConnectedSpace (Spec (.of k')) := inferInstance
  have : ConnectedSpace ↥(pullback sX ρ) :=
    connectedSpace_pullback_of_isAlgClosed_of_connectedSpace sX ρ
  obtain ⟨z⟩ : Nonempty ↥(pullback sX ρ) := inferInstance
  let Ω := AlgebraicClosure ((pullback sX ρ).residueField z)
  let x : Spec (.of Ω) ⟶ pullback sX ρ := ExposeX.geometricPoint _ z
  let F' := ExposeV.FEt.fiber Ω x
  have : FiberFunctor (ExposeV.FEt.pullback π ⋙ F') :=
    ExposeV.fiberFunctor_of_iso (ExposeV.FEt.pullbackFiberIso Ω π x).symm
  have := ExposeV.galoisCategory_of_fiberFunctor F'
  have := ExposeV.galoisCategory_of_fiberFunctor (ExposeV.FEt.pullback π ⋙ F')
  rw [← ExposeIX.bijective_autMap_iff (ExposeV.FEt.pullback π) F']
  refine ⟨(injective_iff_map_eq_one _).mpr fun σ hσ ↦ ?_, ?_⟩
  · have hσE : ∀ E : ExposeV.FEt X, σ.hom.app ((ExposeV.FEt.pullback π).obj E) = 𝟙 _ :=
      fun E ↦ congrArg (fun τ : Aut (ExposeV.FEt.pullback π ⋙ F') ↦ τ.hom.app E) hσ
    -- `σ` is trivial on every connected covering
    have hconn : ∀ W : ExposeV.FEt (pullback sX ρ), IsConnected W → σ.hom.app W = 𝟙 _ := by
      intro W hW
      obtain ⟨E, hE, ⟨f⟩⟩ := h k' W hW
      have : Nonempty (F'.obj ((ExposeV.FEt.pullback π).obj E)) :=
        (nonempty_fiber_of_isConnected (ExposeV.FEt.pullback π ⋙ F') E)
      have : Epi f := epi_of_nonempty_of_isConnected F' f
      exact hom_app_eq_id_of_epi σ f (hσE E)
    -- every covering is a sum of connected ones
    apply Iso.ext
    refine NatTrans.ext (funext fun Y ↦ ?_)
    change σ.hom.app Y = 𝟙 _
    ext a
    obtain ⟨W, i, b, rfl, hW, -⟩ := fiber_in_connected_component F' Y a
    have hnat := ConcreteCategory.congr_hom (σ.hom.naturality i) b
    rw [hconn W hW] at hnat
    simpa using hnat
  · -- surjectivity: connected coverings of `X` stay connected over `k'`
    have hsurj := ExposeX.surjective_map_pullback_fst_of_isAlgClosed sX k' Ω x
    rwa [ExposeV.etaleFundamentalGroup.map, ExposeIX.autMap_eq_conjAut_comp,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.Surjective.of_comp_iff' (MulEquiv.bijective _)] at hsurj

end SGA.SGA1.ExposeXIII
