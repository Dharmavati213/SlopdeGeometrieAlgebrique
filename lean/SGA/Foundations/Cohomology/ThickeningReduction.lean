/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Cohomology.RelativeSpecFunctoriality
import SGA.Foundations.Cohomology.ExistenceFullyFaithful
import SGA.Foundations.Cohomology.ExistenceLocallyFree
import SGA.Foundations.Cohomology.ClosedFibre
import SGA.Foundations.Formal.EtaleCovering
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Direct images of finite schemes modulo powers of `I`

Let `f : X ⟶ Spec A`, `I ⊆ A` and `X_n = X ×_A A / I^{n+1}` (`thickening f I n`).

* `thickeningDiagram I f : ℕ ⥤ Scheme`, the sequence `X₀ ⟶ X₁ ⟶ ⋯`, a thickening sequence in the
  sense of `Scheme.IsThickeningSequence` (`range_thickening_ι`: all `X_n` have underlying set
  `f⁻¹ V(I)`);
* for `p : Y ⟶ X` affine, `reductionMap I f p n : p_* 𝒪_Y ⟶ (Y ×_X X_n ⟶ X)_* 𝒪` is surjective on
  affine opens with kernel `I^{n+1} p_* 𝒪_Y` (affine base change,
  `reductionMap_app_surjective_and`), hence induces `reductionIso`:
  `p_* 𝒪_Y / I^{n+1} ≅ (Y ×_X X_n ⟶ X)_* 𝒪`, compatibly with the transitions
  (`quotientIdealPowMap_reductionIso`);
* `isIso_descQuotientIdealPow`: a morphism of quasi-coherent modules, surjective on affine opens
  with kernel `I^{n+1} M`, induces `M / I^{n+1} M ≅ N`;
* `isCoherent_pushforwardUnit`, `projective_pushforwardUnit_sections`: for `p` finite (étale),
  `p_* 𝒪_Y` is coherent (with projective sections over affine opens).
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules

section ThickeningDiagram

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A)

/-- The thickenings `X₀ ⟶ X₁ ⟶ ⋯` of `X` along `f⁻¹ V(I)`, as a functor `ℕ ⥤ Scheme` (whose
objects are reducibly the `thickening f I n`). -/
abbrev thickeningDiagram : ℕ ⥤ Scheme.{u} where
  obj n := thickening f I n
  map {m n} h := (𝟙 (thickening f I m) ≫ (Functor.ofSequence (thickening.transition f I)).map h ≫
    𝟙 (thickening f I n) : thickening f I m ⟶ thickening f I n)
  map_id n := by
    simp only [Category.id_comp]
    exact (Functor.ofSequence (thickening.transition f I)).map_id n
  map_comp g h := by
    simp only [Category.id_comp]
    exact (Functor.ofSequence (thickening.transition f I)).map_comp g h

lemma thickeningDiagram_obj (n : ℕ) : (thickeningDiagram I f).obj n = thickening f I n := rfl

lemma thickeningDiagram_map (n : ℕ) :
    (thickeningDiagram I f).map (homOfLE n.le_succ) = thickening.transition f I n := by
  simp only [Category.id_comp]
  exact Functor.ofSequence_map_homOfLE_succ (thickening.transition f I) n

/-- The underlying set of `X_n` is `f⁻¹ V(I)`. -/
lemma range_thickening_ι (n : ℕ) :
    Set.range (thickening.ι f I n) = zeroLocusPreimage I f := by
  have h := range_pullback_fst_of_surjective (I ^ (n + 1)) f
    (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) Ideal.Quotient.mk_surjective
    (Ideal.mk_ker)
  refine h.trans (Set.ext fun x ↦ ?_)
  rw [mem_zeroLocusPreimage_iff, mem_zeroLocusPreimage_iff]
  have := (f x).isPrime
  exact Ideal.IsPrime.pow_le_iff (Nat.succ_ne_zero n)

instance isClosedImmersion_thickening_transition (n : ℕ) :
    IsClosedImmersion (thickening.transition f I n) := by
  have : IsClosedImmersion (thickening.transition f I n ≫ thickening.ι f I (n + 1)) := by
    rw [thickening.transition_ι]
    infer_instance
  exact IsClosedImmersion.of_comp _ (thickening.ι f I (n + 1))

instance surjective_thickening_transition (n : ℕ) :
    Surjective (thickening.transition f I n) := by
  refine ⟨fun x ↦ ?_⟩
  have hx : thickening.ι f I (n + 1) x ∈ Set.range (thickening.ι f I n) := by
    rw [range_thickening_ι, ← range_thickening_ι I f (n + 1)]
    exact ⟨x, rfl⟩
  obtain ⟨y, hy⟩ := hx
  refine ⟨y, (thickening.ι f I (n + 1)).isClosedEmbedding.injective ?_⟩
  rw [← Scheme.Hom.comp_apply, thickening.transition_ι, hy]

instance : Scheme.IsThickeningSequence (thickeningDiagram I f) where
  isClosedImmersion n := by
    rw [thickeningDiagram_map]
    exact isClosedImmersion_thickening_transition I f n
  surjective n := by
    rw [thickeningDiagram_map]
    exact surjective_thickening_transition I f n

end ThickeningDiagram

section Reduction

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A) {Y : Scheme.{u}}
  (p : Y ⟶ X)

/-- The reduction `p_* 𝒪_Y ⟶ (Y ×_X X_n → X)_* 𝒪` modulo `I^{n+1}`. -/
def reductionMap (n : ℕ) :
    pushforwardUnit p ⟶ pushforwardUnit (pullback.fst p (thickening.ι f I n) ≫ p) :=
  pushforwardUnitMap (pullback.fst p (thickening.ι f I n)) rfl

set_option backward.isDefEq.respectTransparency false in
lemma reductionMap_app_surjective_and [IsAffineHom p] (n : ℕ) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Function.Surjective ((reductionMap I f p n).app U) ∧
      ∀ x, (reductionMap I f p n).app U x = 0 ↔
        x ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(pushforwardUnit p, U)) := by
  have H := IsPullback.of_hasPullback p (thickening.ι f I n)
  obtain ⟨hs, hk⟩ := app_surjective_ker_of_isPullback H hU (hU.preimage p)
    (hU.preimage (thickening.ι f I n)) ((thickening.ι f I n).app_surjective U hU)
  rw [ker_thickening_app I f n hU, AdicSystem.idealV_eq_pow] at hk
  have happ : ∀ x : Γ(pushforwardUnit p, U), pushforwardUnitEquiv _ ((reductionMap I f p n).app U x)
      = (pullback.fst p (thickening.ι f I n)).app (p ⁻¹ᵁ U) (pushforwardUnitEquiv p x) := by
    intro x
    rw [reductionMap, pushforwardUnitMap_app, Scheme.Hom.app_eq_appLE]
    rfl
  refine ⟨fun y ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨x, hx⟩ := hs (pushforwardUnitEquiv _ y)
    exact ⟨(pushforwardUnitEquiv p).symm x, (happ _).trans hx⟩
  · rw [mem_smul_top_pushforwardUnit_iff, ← hk, RingHom.mem_ker, ← happ]
    rfl

end Reduction

section DescIso

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A)

/-- A morphism `ρ : M ⟶ N` of quasi-coherent modules, surjective on sections over affine opens
with kernel `I^{n+1} M` there, induces `M / I^{n+1} M ≅ N`. -/
lemma isIso_descQuotientIdealPow {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (n : ℕ) (ρ : M ⟶ N)
    (hρ : ∀ {U : X.Opens} (_ : IsAffineOpen U), Function.Surjective (ρ.app U) ∧
      ∀ x, ρ.app U x = 0 ↔ x ∈ (idealV f I U 1 ^ (n + 1) • ⊤ : Submodule Γ(X, U) Γ(M, U)))
    (hN : ∀ a ∈ I ^ (n + 1), smulA N f a = 0) :
    IsIso (descQuotientIdealPow I f n ρ hN) := by
  refine isIso_of_bijective_app_affine _ fun U hU ↦ ⟨fun y y' hyy' ↦ ?_, fun z ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := toQuotientIdealPow_app_surjective I f n hU (M := M) y
    obtain ⟨x', rfl⟩ := toQuotientIdealPow_app_surjective I f n hU (M := M) y'
    rw [← Scheme.Modules.Hom.comp_app_apply, ← Scheme.Modules.Hom.comp_app_apply,
      toQuotientIdealPow_descQuotientIdealPow] at hyy'
    rw [← sub_eq_zero, ← map_sub, quotientIdealPow_app_eq_zero_iff I f M n hU,
      ← (hρ hU).2, map_sub, hyy', sub_self]
  · obtain ⟨x, rfl⟩ := (hρ hU).1 z
    exact ⟨(M.toQuotientIdealPow f I n).app U x, by
      rw [← Scheme.Modules.Hom.comp_app_apply, toQuotientIdealPow_descQuotientIdealPow]⟩

end DescIso


section ThickeningPullback

variable {A : CommRingCat.{u}} (I : Ideal A) {X : Scheme.{u}} (f : X ⟶ Spec A) {Y : Scheme.{u}}
  (p : Y ⟶ X)

/-- The morphism `Y ×_X X_n ⟶ Y ×_X X_{n+1}`. -/
def thickeningPullbackMap (n : ℕ) :
    pullback p (thickening.ι f I n) ⟶ pullback p (thickening.ι f I (n + 1)) :=
  pullback.map p (thickening.ι f I n) p (thickening.ι f I (n + 1)) (𝟙 Y)
    (thickening.transition f I n) (𝟙 X) (by simp)
    (by rw [Category.comp_id, thickening.transition_ι])

@[reassoc (attr := simp)]
lemma thickeningPullbackMap_fst (n : ℕ) :
    thickeningPullbackMap I f p n ≫ pullback.fst p (thickening.ι f I (n + 1)) =
      pullback.fst p (thickening.ι f I n) := by
  simp only [thickeningPullbackMap, pullback.map, pullback.lift_fst, Category.comp_id]

lemma thickeningPullbackMap_comp (n : ℕ) :
    thickeningPullbackMap I f p n ≫ pullback.fst p (thickening.ι f I (n + 1)) ≫ p =
      pullback.fst p (thickening.ι f I n) ≫ p := by
  rw [thickeningPullbackMap_fst_assoc]

lemma pushforwardUnitMap_congr {Z Z' : Scheme.{u}} {g : Z ⟶ X} {g' : Z' ⟶ X} {h₁ h₂ : Z ⟶ Z'}
    (e : h₁ = h₂) (hg₁ : h₁ ≫ g' = g) (hg₂ : h₂ ≫ g' = g) :
    pushforwardUnitMap h₁ hg₁ = pushforwardUnitMap h₂ hg₂ := by
  subst e
  rfl

lemma comp_fst_comp_eq_of_comp_fst {n : ℕ}
    {τ : pullback p (thickening.ι f I n) ⟶ pullback p (thickening.ι f I (n + 1))}
    (hτ : τ ≫ pullback.fst _ _ = pullback.fst _ _) :
    τ ≫ pullback.fst p (thickening.ι f I (n + 1)) ≫ p =
      pullback.fst p (thickening.ι f I n) ≫ p := by
  rw [← Category.assoc, hτ]

/-- The reductions are compatible with any morphism `Y ×_X X_n ⟶ Y ×_X X_{n+1}` over `Y`. -/
lemma reductionMap_comp_pushforwardUnitMap' {n : ℕ}
    (τ : pullback p (thickening.ι f I n) ⟶ pullback p (thickening.ι f I (n + 1)))
    (hτ : τ ≫ pullback.fst _ _ = pullback.fst _ _) :
    reductionMap I f p (n + 1) ≫ pushforwardUnitMap τ (comp_fst_comp_eq_of_comp_fst I f p hτ) =
      reductionMap I f p n := by
  rw [reductionMap, reductionMap, ← pushforwardUnitMap_comp]
  exact pushforwardUnitMap_congr hτ _ _

lemma reductionMap_comp_pushforwardUnitMap (n : ℕ) :
    reductionMap I f p (n + 1) ≫
        pushforwardUnitMap (thickeningPullbackMap I f p n) (thickeningPullbackMap_comp I f p n) =
      reductionMap I f p n :=
  reductionMap_comp_pushforwardUnitMap' I f p _ (thickeningPullbackMap_fst I f p n)

end ThickeningPullback

section ReductionIso

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{u}}
  (f : X ⟶ Spec A) {Y : Scheme.{u}} (p : Y ⟶ X) [IsAffineHom p]

omit [IsNoetherianRing A] in
lemma reduction_smulA_eq_zero (n : ℕ) (a : A) (ha : a ∈ I ^ (n + 1)) :
    smulA (pushforwardUnit (pullback.fst p (thickening.ι f I n) ≫ p)) f a = 0 := by
  refine hom_ext_of_affine fun U hU s ↦ ?_
  obtain ⟨x, rfl⟩ := (reductionMap_app_surjective_and I f p n hU).1 s
  rw [smulA_app, ← Scheme.Modules.Hom.app_smul,
    ((reductionMap_app_surjective_and I f p n hU).2 _).mpr
      (Submodule.smul_mem_smul (AdicSystem.structMapV_mem_pow (f := f) ha) Submodule.mem_top)]
  rfl

/-- `p_* 𝒪_Y / I^{n+1} ≅ (Y ×_X X_n ⟶ X)_* 𝒪` for `p` affine (affine base change). -/
def reductionIso (n : ℕ) :
    (pushforwardUnit p).quotientIdealPow f I n ≅
      pushforwardUnit (pullback.fst p (thickening.ι f I n) ≫ p) :=
  have := isIso_descQuotientIdealPow I f n (reductionMap I f p n)
    (fun hU ↦ reductionMap_app_surjective_and I f p n hU) (reduction_smulA_eq_zero I f p n)
  asIso (descQuotientIdealPow I f n (reductionMap I f p n) (reduction_smulA_eq_zero I f p n))

@[reassoc (attr := simp)]
lemma toQuotientIdealPow_reductionIso_hom (n : ℕ) :
    (pushforwardUnit p).toQuotientIdealPow f I n ≫ (reductionIso I f p n).hom =
      reductionMap I f p n :=
  toQuotientIdealPow_descQuotientIdealPow I f n _ (reduction_smulA_eq_zero I f p n)

lemma quotientIdealPowMap_reductionIso (n : ℕ) :
    (pushforwardUnit p).quotientIdealPowMap f I n ≫ (reductionIso I f p n).hom =
      (reductionIso I f p (n + 1)).hom ≫
        pushforwardUnitMap (thickeningPullbackMap I f p n)
          (thickeningPullbackMap_comp I f p n) := by
  rw [← cancel_epi ((pushforwardUnit p).toQuotientIdealPow f I (n + 1)),
    Scheme.Modules.toQuotientIdealPow_comp_map_assoc, toQuotientIdealPow_reductionIso_hom,
    toQuotientIdealPow_reductionIso_hom_assoc, reductionMap_comp_pushforwardUnitMap]

/-- The isomorphisms `reductionIso` are compatible with any morphism `Y ×_X X_n ⟶ Y ×_X X_{n+1}`
over `Y`. -/
lemma quotientIdealPowMap_reductionIso' {n : ℕ}
    (τ : pullback p (thickening.ι f I n) ⟶ pullback p (thickening.ι f I (n + 1)))
    (hτ : τ ≫ pullback.fst _ _ = pullback.fst _ _) :
    (pushforwardUnit p).quotientIdealPowMap f I n ≫ (reductionIso I f p n).hom =
      (reductionIso I f p (n + 1)).hom ≫
        pushforwardUnitMap τ (comp_fst_comp_eq_of_comp_fst I f p hτ) := by
  rw [← cancel_epi ((pushforwardUnit p).toQuotientIdealPow f I (n + 1)),
    Scheme.Modules.toQuotientIdealPow_comp_map_assoc, toQuotientIdealPow_reductionIso_hom,
    toQuotientIdealPow_reductionIso_hom_assoc, reductionMap_comp_pushforwardUnitMap' I f p τ hτ]

end ReductionIso

section FiniteSections

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

lemma finite_pushforwardUnit_sections [IsFinite p] {U : X.Opens} (hU : IsAffineOpen U) :
    Module.Finite Γ(X, U) Γ(pushforwardUnit p, U) :=
  p.finite_app U hU

/-- The direct image of `𝒪_Y` along a finite morphism is coherent. -/
lemma isCoherent_pushforwardUnit [IsFinite p] : (pushforwardUnit p).IsCoherent where
  isQuasicoherent := inferInstance
  isFiniteType := isFiniteType_of_finite_sections _ (fun U : X.AffineZariskiSite ↦ U.toOpens)
    (by
      refine top_le_iff.mp fun x _ ↦ ?_
      obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.mp
        ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨U.1, U.2⟩, hU⟩) (fun U ↦ U.2)
    fun U ↦ finite_pushforwardUnit_sections p U.2

set_option backward.isDefEq.respectTransparency.types false in
/-- For `p` finite étale, the sections of `p_* 𝒪_Y` over affine opens are projective. -/
lemma projective_pushforwardUnit_sections [IsFinite p] [Etale p] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Projective Γ(X, U) Γ(pushforwardUnit p, U) := by
  have he : (p.app U).hom.Etale := by
    rw [Scheme.Hom.app_eq_appLE]
    exact HasRingHomProperty.appLE (P := @Etale) p ‹_› ⟨U, hU⟩ ⟨_, hU.preimage p⟩ le_rfl
  have hf : (p.app U).hom.Finite := p.finite_app U hU
  let _ := (p.app U).hom.toAlgebra
  have : Algebra.Etale Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := he
  have : Module.Finite Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := hf
  have : Module.FinitePresentation Γ(X, U) Γ(Y, p ⁻¹ᵁ U) :=
    .of_finite_of_finitePresentation _ _
  have : Module.Projective Γ(X, U) Γ(Y, p ⁻¹ᵁ U) := Module.Flat.projective_of_finitePresentation
  exact this

end FiniteSections

end AlgebraicGeometry.CohomologyAux
