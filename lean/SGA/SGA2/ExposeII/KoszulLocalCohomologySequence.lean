/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulLocalCohomology
import SGA.SGA2.ExposeII.LocalCohomologyReindexing

/-!
# SGA 2, Exposé II, (7.3)–(7.6): the ideal-power comparison and boundaries

The canonical map from ordinary ideal-power local cohomology to stable
Koszul cohomology commutes with the actual coefficient boundaries. The
cofinal change from ideal powers to generator powers is included in this
compatibility, without a noetherian hypothesis.
-/

noncomputable section

universe u v

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

private theorem coefficientBoundary_comp {C : Type u} [Category.{v} C]
    {A₀ A₁ B₀ B₁ C₀ C₁ : C} {dA : A₀ ⟶ A₁} {dB : B₀ ⟶ B₁} {dC : C₀ ⟶ C₁}
    {e₀ : A₀ ⟶ B₀} {e₁ : A₁ ⟶ B₁} {f₀ : B₀ ⟶ C₀} {f₁ : B₁ ⟶ C₁}
    (he : dA ≫ e₁ = e₀ ≫ dB) (hf : dB ≫ f₁ = f₀ ≫ dC) :
    dA ≫ (e₁ ≫ f₁) = (e₀ ≫ f₀) ≫ dC := by
  rw [← Category.assoc, he, Category.assoc, hf, ← Category.assoc]

private theorem coefficientBoundary_iso_comp
    {C D : Type*} [Category C] [Category D] {X Y : C}
    {A₀ A₁ B₀ B₁ C₀ C₁ : C ⥤ D}
    {dA : A₀.obj X ⟶ A₁.obj Y} {dB : B₀.obj X ⟶ B₁.obj Y}
    {dC : C₀.obj X ⟶ C₁.obj Y}
    {e₀ : A₀ ≅ B₀} {e₁ : A₁ ≅ B₁} {f₀ : B₀ ≅ C₀} {f₁ : B₁ ≅ C₁}
    (he : dA ≫ e₁.hom.app Y = e₀.hom.app X ≫ dB)
    (hf : dB ≫ f₁.hom.app Y = f₀.hom.app X ≫ dC) :
    dA ≫ (e₁ ≪≫ f₁).hom.app Y = (e₀ ≪≫ f₀).hom.app X ≫ dC :=
  coefficientBoundary_comp he hf

/-- The ideal Ext boundary with the functor type used by `ofDiagram`. -/
def localCohomologyOfDiagramδ (D : ℕᵒᵖ ⥤ Ideal R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    (localCohomology.ofDiagram D i).obj S.X₃ ⟶
      (localCohomology.ofDiagram D (i + 1)).obj S.X₁ :=
  idealExtColimitδ D S hS i

/-- Replacing the named ideal diagram and support ideal by equal ones
preserves the generator-power boundary square. -/
theorem generatorPowersLocalCohomologyIsoOfEq_δ {ι : Type v} [Finite ι]
    (f : ι → R) (D : ℕᵒᵖ ⥤ Ideal R) (I : Ideal R)
    (hD : D = generatorPowersDiagram f) (hI : I = Ideal.span (Set.range f))
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    localCohomologyOfDiagramδ D S hS i ≫
        (generatorPowersLocalCohomologyIsoOfEq f D I hD hI (i + 1)).hom.app S.X₁ =
      (generatorPowersLocalCohomologyIsoOfEq f D I hD hI i).hom.app S.X₃ ≫
        localCohomologyδ I S hS i := by
  subst D I
  exact generatorPowersLocalCohomologyIso_δ f S hS i

/-- Passing between pointwise colimits and the colimit of functors respects
the actual coefficient boundaries. -/
theorem stableKoszulExtIsoOfDiagram_δ (fs : List R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    extColimitδ (koszulQuotientSystem fs) S hS i ≫
        (stableKoszulExtIsoOfDiagram fs (i + 1)).hom.app S.X₁ =
      (stableKoszulExtIsoOfDiagram fs i).hom.app S.X₃ ≫
        localCohomologyOfDiagramδ (koszulGeneratorIdeals fs) S hS i := by
  simp only [stableKoszulExtIsoOfDiagram, Iso.symm_hom,
    colimitIsoFlipCompColim_inv_app, localCohomologyOfDiagramδ, idealExtColimitδ,
    Iso.inv_hom_id_assoc]
  rfl

/-- The existing comparison from generator-power Ext to ordinary
ideal-power local cohomology commutes with coefficient boundaries. -/
@[reassoc]
theorem stableKoszulExtIsoLocalCohomology_δ (fs : List R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    extColimitδ (koszulQuotientSystem fs) S hS i ≫
        (stableKoszulExtIsoLocalCohomology fs (i + 1)).hom.app S.X₁ =
      (stableKoszulExtIsoLocalCohomology fs i).hom.app S.X₃ ≫
        localCohomologyδ (koszulIdeal fs) S hS i := by
  exact coefficientBoundary_iso_comp (stableKoszulExtIsoOfDiagram_δ fs S hS i)
    (generatorPowersLocalCohomologyIsoOfEq_δ (fun j : Fin fs.length => fs.get j)
      (koszulGeneratorIdeals fs) (koszulIdeal fs)
      (koszulIdealPowersDiagram_eq_generatorPowersDiagram fs) (koszulIdeal_eq_span_get fs) S hS i)

/-- II.(7.3)–(7.6): the canonical ideal-power Ext-to-Koszul comparison
commutes with the actual coefficient connecting maps. -/
theorem localCohomologyToStableKoszul_δ (fs : List R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    localCohomologyδ (koszulIdeal fs) S hS i ≫
        (localCohomologyToStableKoszul fs (i + 1)).app S.X₁ =
      (localCohomologyToStableKoszul fs i).app S.X₃ ≫
        (stableKoszulConnectingSequence fs).δ S hS i := by
  apply (cancel_epi ((stableKoszulExtIsoLocalCohomology fs i).hom.app S.X₃)).mp
  rw [← stableKoszulExtIsoLocalCohomology_δ_assoc]
  simp only [localCohomologyToStableKoszul, NatTrans.comp_app, Category.assoc,
    Iso.hom_inv_id_app_assoc]
  exact (stableKoszulExtComparisonConnectingHom fs).comm S hS i

end SGA.SGA2.ExposeII
