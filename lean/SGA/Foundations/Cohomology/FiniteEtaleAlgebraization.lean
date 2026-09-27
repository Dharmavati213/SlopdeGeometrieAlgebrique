/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.Foundations.Cohomology.FiniteEtaleEquivalence
import SGA.Foundations.Cohomology.ProperProjectivity

/-!
# Algebraizable formal étale coverings of proper schemes

Let `A` be noetherian and `I`-adically complete and `f : X ⟶ Spec A` proper. An étale covering
`(Yₙ ⟶ Xₙ)` of the formal completion of `X` along `f⁻¹ V(I)` whose adic system `(Yₙ ⟶ X)_* 𝒪` is
algebraized by a coherent `𝒪_X`-module comes from a finite étale `Y ⟶ X`
(`exists_finiteEtale_of_algebraization`; EGA III 5.4.5, proof). This removes the projectivity
hypothesis of `exists_finiteEtale_of_formalFiniteEtale`, using
`projective_sections_of_liftingProperty_of_isProper`.

* `FormalAlgebraizable I f`: all these adic systems are algebraizable;
* `essSurj_pullback_thickening_of_formalAlgebraizable` and `formalAlgebraizable_of_essSurj`:
  given SGA 1 I.8.3 (base change of étale coverings along surjective closed immersions is an
  equivalence), algebraizability is equivalent to the essential surjectivity of
  `Y ↦ Y ×_X X₀` on étale coverings;
* `formalAlgebraizable_of_isClosedImmersion`: the projective case.
-/

universe u

open CategoryTheory Limits TopologicalSpace Opposite

noncomputable section

namespace AlgebraicGeometry.CohomologyAux

open Scheme.Modules
open Scheme (FiniteEtale FormalFiniteEtale)

section Algebraization

variable {A : CommRingCat.{u}} [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
  {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]

/-- **Algebraizations of formal étale coverings give étale coverings** (EGA III 5.4.5, proof;
proper case): let `A` be noetherian and `I`-adically complete, `f : X ⟶ Spec A` proper and
`(Yₙ ⟶ Xₙ)` an étale covering of the formal completion of `X` along `f⁻¹ V(I)`. If the adic system
`(Yₙ ⟶ X)_* 𝒪` is algebraized by a coherent `F`, then there is a finite étale `p : Y ⟶ X` with
`Y ×_X X₀ ≅ Y₀` over `X₀`. The algebraization is locally free
(`projective_sections_of_liftingProperty_of_isProper`), carries a unique algebra structure lifting
those of the `Yₙ` (`exists_moduleAlgebra_algebraization`), and `Y = Spec_X F`. -/
theorem exists_finiteEtale_of_algebraization
    (𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f)) (F : X.Modules) [F.IsCoherent]
    (e : ∀ n, F.quotientIdealPow f I n ≅ (formalAdicSystem I f 𝒴).obj n)
    (he : ∀ n, (e (n + 1)).hom ≫ (formalAdicSystem I f 𝒴).map n =
      F.quotientIdealPowMap f I n ≫ (e n).hom) :
    ∃ (Y : Scheme.{u}) (p : Y ⟶ X) (_ : IsFinite p) (_ : Etale p)
      (e : pullback p (thickening.ι f I 0) ≅ (𝒴.obj 0).left),
      e.hom ≫ formalQ I f 𝒴 0 = pullback.snd _ _ := by
  let G := formalAdicSystem I f 𝒴
  have hG := formalAdicSystem_isLocallyFree I f 𝒴
  have : F.IsQuasicoherent := Scheme.Modules.IsCoherent.isQuasicoherent
  have : F.IsFiniteType := Scheme.Modules.IsCoherent.isFiniteType
  have hproj : ∀ {V : X.Opens}, IsAffineOpen V → Module.Projective Γ(X, V) Γ(F, V) :=
    fun hV ↦ projective_sections_of_liftingProperty_of_isProper I f F
      (fun n _ hV' ↦ LiftingProperty.of_equiv (appLinearEquiv (e n) _).symm (hG n hV')) hV
  let alg : ∀ n, ModuleAlgebra (G.obj n) := fun n ↦
    pushforwardAlgebra (formalStructure I f 𝒴 n)
  have hmul : ∀ (n : ℕ) (U : X.Opens) (x y : Γ(G.obj (n + 1), U)),
      (G.map n).app U (mulApp (alg (n + 1)).mul U x y) =
        mulApp (alg n).mul U ((G.map n).app U x) ((G.map n).app U y) := fun n U x y ↦ by
    have h1 := mulApp_pushforwardAlgebra (formalStructure I f 𝒴 (n + 1)) U x y
    have h2 := mulApp_pushforwardAlgebra (formalStructure I f 𝒴 n) U
      ((G.map n).app U x) ((G.map n).app U y)
    have h3 := pushforwardUnitMap_pfMul (𝒴.transition n)
      (transition_formalStructure I f 𝒴 n) U x y
    exact (congrArg ((G.map n).app U) h1).trans (h3.trans h2.symm)
  have hone : ∀ n, (G.map n).app ⊤ (alg (n + 1)).one = (alg n).one := fun n ↦
    pushforwardUnitMap_one (𝒴.transition n) (transition_formalStructure I f 𝒴 n)
  obtain ⟨μ, hμ⟩ := exists_mul_algebraization I _ e he alg hmul hproj
  obtain ⟨one, hone'⟩ := exists_one_algebraization I _ e he alg hone
  obtain ⟨algB, hmulB, honeB⟩ := exists_moduleAlgebra_algebraization I _ e alg hμ hproj hone'
  have hmul0 : ∀ (U : X.Opens) (x y : Γ(F, U)),
      (algRed I _ e 0).app U (mulApp algB.mul U x y) =
        mulApp (alg 0).mul U ((algRed I _ e 0).app U x) ((algRed I _ e 0).app U y) := by
    rw [hmulB]
    exact algRed_mulApp I _ e alg hμ 0
  have hone0 : (algRed I _ e 0).app ⊤ algB.one = (alg 0).one := by
    rw [honeB]
    exact hone' 0
  have hsurj : ∀ {U : X.Opens}, IsAffineOpen U → Function.Surjective ((algRed I _ e 0).app U) :=
    fun hU ↦ algRed_app_surjective I _ e 0 hU
  have hker : ∀ {U : X.Opens}, IsAffineOpen U → ∀ x : Γ(F, U), (algRed I _ e 0).app U x = 0 ↔
      x ∈ (idealV f I U 1 • ⊤ : Submodule Γ(X, U) Γ(F, U)) := by
    intro U hU x
    constructor
    · intro h
      simpa only [zero_add, pow_one] using algRed_app_eq_zero I _ e 0 hU x h
    · intro h
      rw [algRed, Scheme.Modules.Hom.comp_app_apply,
        (toQuotientIdealPow_app_eq_zero_iff' I _ F hU 0 x).mpr (by rwa [zero_add, pow_one]),
        map_zero]
  have hunr := formallyUnramified_formal I f 𝒴
  have hetale : Etale algB.relativeSpecHom :=
    etale_relativeSpecHom_of_reduction I _ algB (alg 0) (algRed I _ e 0) hmul0 hone0 hsurj hker
      hunr hproj
  have hmul0' : ∀ (U : X.Opens) (x y : Γ(F, U)),
      (algRed I _ e 0).app U (mulApp algB.mul U x y) =
        pfMul _ ((algRed I _ e 0).app U x) ((algRed I _ e 0).app U y) := fun U x y ↦ by
    rw [hmul0]
    exact mulApp_pushforwardAlgebra _ U _ _
  have hiso := isIso_closedFibreLift I _ algB (formalQ I _ 𝒴 0) (algRed I _ e 0) hmul0' hone0
    hsurj hker
  refine ⟨_, algB.relativeSpecHom, inferInstance, hetale,
    (asIso (closedFibreLift I _ algB (formalQ I _ 𝒴 0) (algRed I _ e 0) hmul0' hone0)).symm, ?_⟩
  rw [Iso.symm_hom, asIso_inv, IsIso.inv_comp_eq]
  exact (closedFibreLift_snd I _ algB (formalQ I _ 𝒴 0) (algRed I _ e 0) hmul0' hone0).symm

/-- The isomorphism `h'_* 𝒪 ≅ h_* 𝒪` induced by an isomorphism of `X`-schemes. -/
def pushforwardUnitIso {Z Z' : Scheme.{u}} {g : Z ⟶ X} {g' : Z' ⟶ X} (φ : Z ≅ Z')
    (hφ : φ.hom ≫ g' = g) : pushforwardUnit g' ≅ pushforwardUnit g where
  hom := pushforwardUnitMap φ.hom hφ
  inv := pushforwardUnitMap φ.inv (by rw [← hφ, Iso.inv_hom_id_assoc])
  hom_inv_id := by
    rw [← pushforwardUnitMap_comp, ← pushforwardUnitMap_id]
    exact pushforwardUnitMap_congr φ.inv_hom_id _ _
  inv_hom_id := by
    rw [← pushforwardUnitMap_comp, ← pushforwardUnitMap_id]
    exact pushforwardUnitMap_congr φ.hom_inv_id _ _

/-- Étale coverings of the formal completion of `X` are **algebraizable** if the adic systems
`(Yₙ ⟶ X)_* 𝒪` are all algebraized by coherent `𝒪_X`-modules (EGA III 5.1.4 for these systems). -/
def FormalAlgebraizable : Prop :=
  ∀ 𝒴 : Scheme.FormalFiniteEtale (thickeningDiagram I f), ∃ (F : X.Modules) (_ : F.IsCoherent)
    (e : ∀ n, F.quotientIdealPow f I n ≅ (formalAdicSystem I f 𝒴).obj n),
    ∀ n, (e (n + 1)).hom ≫ (formalAdicSystem I f 𝒴).map n =
      F.quotientIdealPowMap f I n ≫ (e n).hom

omit [IsProper f] in
/-- **Formal étale coverings of a projective scheme are algebraizable** (EGA III 5.4.5, 5.1.4 for
locally free systems): the case `X ⊆ ℙ(τ; Spec A)` closed, by
`AdicSystem.exists_iso_quotientIdealPow_projective`. -/
theorem formalAlgebraizable_of_isClosedImmersion {τ : Type u} [Finite τ]
    (κ : X ⟶ ℙ(τ; Spec A)) [IsClosedImmersion κ] (hf : f = κ ≫ ℙ(τ; Spec A) ↘ Spec A) :
    FormalAlgebraizable I f := by
  subst hf
  intro 𝒴
  have hG := formalAdicSystem_isLocallyFree I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴
  have : ((formalAdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴).obj 0).IsCoherent :=
    isCoherent_pushforwardUnit (formalStructure I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴 0)
  obtain ⟨F, hF, e, he, -⟩ :=
    (formalAdicSystem I (κ ≫ ℙ(τ; Spec A) ↘ Spec A) 𝒴).exists_iso_quotientIdealPow_projective I κ hG
  exact ⟨F, hF, e, he⟩

variable (h83 : ∀ ⦃X Y : Scheme.{u}⦄ (i : X ⟶ Y), IsClosedImmersion i → Surjective i →
    (FiniteEtale.pullback i).IsEquivalence)

include h83 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Essential surjectivity from algebraizability** (SGA 1 IX.1.10): if the formal étale coverings
of `X` proper over `Spec A` are algebraizable, every étale covering of `X₀` extends to `X`. -/
theorem essSurj_pullback_thickening_of_formalAlgebraizable (hX : FormalAlgebraizable I f) :
    (FiniteEtale.pullback (thickening.ι f I 0)).EssSurj := by
  have := isEquivalence_formalToZero I f h83
  refine ⟨fun Y₀ ↦ ?_⟩
  let 𝒴 := (FormalFiniteEtale.toZero (thickeningDiagram I f)).objPreimage Y₀
  obtain ⟨F, hF, e, he⟩ := hX 𝒴
  obtain ⟨Y, p, hfin, het, e, he⟩ := exists_finiteEtale_of_algebraization I f 𝒴 F e he
  refine ⟨MorphismProperty.Over.mk ⊤ p ⟨hfin, het⟩, ⟨?_⟩⟩
  exact MorphismProperty.Over.isoMk e he ≪≫
    (FormalFiniteEtale.toZero (thickeningDiagram I f)).objObjPreimageIso Y₀

omit [IsAdicComplete I A] [IsProper f] in
include h83 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- **Algebraizability from essential surjectivity**: if every étale covering of `X₀` extends to
`X`, the formal étale coverings of `X` are algebraizable, by the direct images of the structure
sheaves of the extensions (`reductionIso`). -/
theorem formalAlgebraizable_of_essSurj
    (hX : (FiniteEtale.pullback (thickening.ι f I 0)).EssSurj) : FormalAlgebraizable I f := by
  have := isEquivalence_formalToZero I f h83
  intro 𝒴
  let Y := (FiniteEtale.pullback (thickening.ι f I 0)).objPreimage (𝒴.obj 0)
  let ψ : (formalCompletionFunctor I f).obj Y ≅ 𝒴 :=
    (FormalFiniteEtale.toZero (thickeningDiagram I f)).preimageIso
      ((FiniteEtale.pullback (thickening.ι f I 0)).objObjPreimageIso (𝒴.obj 0))
  have hw : ∀ n, (ψ.inv.app n).left ≫ pullback.snd Y.hom (thickening.ι f I n) =
      formalQ I f 𝒴 n := fun n ↦ MorphismProperty.Over.w (ψ.inv.app n)
  let φ : ∀ n, (𝒴.obj n).left ≅ pullback Y.hom (thickening.ι f I n) := fun n ↦
    { hom := (ψ.inv.app n).left
      inv := (ψ.hom.app n).left
      hom_inv_id := by
        rw [← MorphismProperty.Comma.comp_left, ← TowerLimit.comp_app, ψ.inv_hom_id]
        rfl
      inv_hom_id := by
        rw [← MorphismProperty.Comma.comp_left, ← TowerLimit.comp_app, ψ.hom_inv_id]
        rfl }
  have hφ : ∀ n, (φ n).hom ≫ pullback.fst Y.hom (thickening.ι f I n) ≫ Y.hom =
      formalStructure I f 𝒴 n := fun n ↦ by
    change (ψ.inv.app n).left ≫ _ = _
    rw [pullback.condition, ← Category.assoc, hw]
  refine ⟨pushforwardUnit Y.hom, isCoherent_pushforwardUnit Y.hom,
    fun n ↦ reductionIso I f Y.hom n ≪≫ pushforwardUnitIso (φ n) (hφ n), fun n ↦ ?_⟩
  simp only [Iso.trans_hom, Category.assoc]
  rw [← Category.assoc (quotientIdealPowMap f I _ n), quotientIdealPowMap_reductionIso,
    Category.assoc]
  congr 1
  change pushforwardUnitMap (φ (n + 1)).hom (hφ (n + 1)) ≫
      pushforwardUnitMap (𝒴.transition n) (transition_formalStructure I f 𝒴 n) =
    pushforwardUnitMap (thickeningPullbackMap I f Y.hom n)
        (thickeningPullbackMap_comp I f Y.hom n) ≫ pushforwardUnitMap (φ n).hom (hφ n)
  rw [← pushforwardUnitMap_comp, ← pushforwardUnitMap_comp]
  refine pushforwardUnitMap_congr ?_ _ _
  have h1 := FormalFiniteEtale.transition_comp_app_left ψ.inv n
  have h2 : ((formalCompletionFunctor I f).obj Y).transition n =
      thickeningPullbackMap I f Y.hom n := formalCompletion_iso_inv_left_fst I f Y n
  change 𝒴.transition n ≫ (ψ.inv.app (n + 1)).left =
    (ψ.inv.app n).left ≫ thickeningPullbackMap I f Y.hom n
  rw [h1, h2]

end Algebraization

end AlgebraicGeometry.CohomologyAux
