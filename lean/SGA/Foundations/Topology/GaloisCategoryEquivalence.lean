/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Galois.Topology
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Conj

/-!
# Galois categories and fibre functors along equivalences

Mathlib's `PreGaloisCategory` and `FiberFunctor` are given by axioms; we record that they are
invariant under equivalence of categories and isomorphism of functors, and that an equivalence
compatible with fibre functors identifies their automorphism groups as topological groups.

* `PreGaloisCategory.of_equivalence`: a category equivalent to a pre-Galois category is
  pre-Galois;
* `FiberFunctor.comp_isEquivalence`, `FiberFunctor.of_iso`: fibre functors are stable under
  precomposition with equivalences and under isomorphism;
* `autContinuousMulEquivOfIsEquivalence`: for an equivalence `H` and `H ⋙ F ≅ F'`,
  `Aut F ≃ₜ* Aut F'`.

## References

* [H. W. Lenstra, *Galois theory for schemes*][lenstra2008]
-/

universe u₁ u₂ v₁ v₂ w

open CategoryTheory Limits Functor

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] {D : Type v₁} [Category.{v₂} D]

/-- A category equivalent to a pre-Galois category is pre-Galois. -/
theorem of_equivalence (e : C ≌ D) [PreGaloisCategory D] : PreGaloisCategory C where
  hasTerminal := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasPullbacks := Adjunction.hasLimitsOfShape_of_equivalence e.functor
  hasFiniteCoproducts := ⟨fun _ ↦ Adjunction.hasColimitsOfShape_of_equivalence e.functor⟩
  hasQuotientsByFiniteGroups _ _ _ := Adjunction.hasColimitsOfShape_of_equivalence e.functor
  monoInducesIsoOnDirectSummand {X Y} i _ := by
    obtain ⟨Z', u', ⟨hc⟩⟩ := PreGaloisCategory.monoInducesIsoOnDirectSummand (e.functor.map i)
    refine ⟨e.inverse.obj Z', e.inverse.map u' ≫ e.unitInv.app Y, ⟨?_⟩⟩
    have h : e.functor.map (e.inverse.map u' ≫ e.unitInv.app Y) = e.counit.app Z' ≫ u' := by
      simp
    refine isColimitOfReflects e.functor
      ((isColimitMapCoconeBinaryCofanEquiv e.functor _ _).symm ?_)
    rw [h]
    exact BinaryCofan.isColimitCompRightIso (BinaryCofan.mk _ u') (e.counit.app Z') hc

/-- Precomposing a fibre functor with an equivalence of pre-Galois categories gives a fibre
functor. -/
theorem FiberFunctor.comp_isEquivalence [PreGaloisCategory C] [PreGaloisCategory D] (H : C ⥤ D)
    [H.IsEquivalence] (F : D ⥤ FintypeCat.{w}) [FiberFunctor F] : FiberFunctor (H ⋙ F) where
  preservesTerminalObjects := comp_preservesLimitsOfShape _ _
  preservesPullbacks := comp_preservesLimitsOfShape _ _
  preservesFiniteCoproducts := comp_preservesFiniteCoproducts _ _
  preservesEpis := inferInstance
  preservesQuotientsByFiniteGroups _ _ _ := comp_preservesColimitsOfShape _ _
  reflectsIsos := inferInstance

/-- A functor isomorphic to a fibre functor is a fibre functor. -/
theorem FiberFunctor.of_iso [PreGaloisCategory C] {F F' : C ⥤ FintypeCat.{w}} [FiberFunctor F]
    (i : F ≅ F') : FiberFunctor F' where
  preservesTerminalObjects := preservesLimitsOfShape_of_natIso i
  preservesPullbacks := preservesLimitsOfShape_of_natIso i
  preservesFiniteCoproducts := ⟨fun _ ↦ preservesColimitsOfShape_of_natIso i⟩
  preservesEpis := PreservesEpimorphisms.of_iso i
  preservesQuotientsByFiniteGroups _ _ _ := preservesColimitsOfShape_of_natIso i
  reflectsIsos := reflectsIsomorphisms_of_iso i

/-- An equivalence of categories `H`, compatible with functors `F` and `F'` to finite sets,
identifies the automorphism groups of `F` and `F'` as topological groups. -/
noncomputable def autContinuousMulEquivOfIsEquivalence (H : C ⥤ D) [H.IsEquivalence]
    {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}} (i : H ⋙ F ≅ F') :
    Aut F ≃ₜ* Aut F' := by
  let hH := (H.asEquivalence.congrLeft (E := FintypeCat.{w})).fullyFaithfulInverse
  let e : Aut F ≃* Aut F' := (hH.autMulEquivOfFullyFaithful F).trans i.conjAut
  have he (σ : Aut F) (X : C) : (e σ).app X = (i.app X).symm ≪≫ σ.app (H.obj X) ≪≫ i.app X :=
    rfl
  have hcont : Continuous e := by
    rw [(autEmbedding_isClosedEmbedding F').isInducing.continuous_iff, continuous_pi_iff]
    intro X
    change Continuous fun σ ↦ autEmbedding F' (e σ) X
    have : (fun σ ↦ autEmbedding F' (e σ) X) =
        (fun τ : Aut (F.obj (H.obj X)) ↦ (i.app X).symm ≪≫ τ ≪≫ i.app X) ∘
          (fun σ ↦ autEmbedding F σ (H.obj X)) := by
      funext σ
      rw [Function.comp_apply, autEmbedding_apply, autEmbedding_apply, he]
    rw [this]
    exact continuous_of_discreteTopology.comp
      ((continuous_apply _).comp (autEmbedding_isClosedEmbedding F).continuous)
  exact { e with
    continuous_toFun := hcont
    continuous_invFun := hcont.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv) }

@[simp]
lemma autContinuousMulEquivOfIsEquivalence_apply_hom_app (H : C ⥤ D) [H.IsEquivalence]
    {F : D ⥤ FintypeCat.{w}} {F' : C ⥤ FintypeCat.{w}} (i : H ⋙ F ≅ F') (σ : Aut F) (X : C) :
    (autContinuousMulEquivOfIsEquivalence H i σ).hom.app X =
      (i.inv.app X ≫ σ.hom.app (H.obj X)) ≫ i.hom.app X :=
  rfl

end CategoryTheory.PreGaloisCategory
