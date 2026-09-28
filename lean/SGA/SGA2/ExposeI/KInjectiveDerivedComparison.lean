/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# Actual cochain representatives of derived maps into K-injectives

These representatives compare a flasque resolution with an injective resolution
without asserting that the first resolution is termwise injective. Equality of
the derived maps gives a genuine homotopy of their cochain representatives.
-/

noncomputable section

open CategoryTheory Limits HomologicalComplex

namespace SGA.SGA2.ExposeI

set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
  {K L : CochainComplex C ℤ} [L.IsKInjective]

/-- A cochain representative of any derived morphism with K-injective target. -/
def kInjectiveLiftDerivedMap (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) : K ⟶ L :=
  (HomotopyCategory.quotient C (ComplexShape.up ℤ)).preimage
    (((CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L).surjective
        ((DerivedCategory.quotientCompQhIso C).hom.app K ≫ α ≫
          (DerivedCategory.quotientCompQhIso C).inv.app L)).choose)

/-- The actual representative has exactly the prescribed image in the derived category. -/
@[simp]
theorem Q_map_kInjectiveLiftDerivedMap
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :
    DerivedCategory.Q.map (kInjectiveLiftDerivedMap α) = α := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso C
  have h := ((CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) L).surjective
    (e.hom.app K ≫ α ≫ e.inv.app L)).choose_spec
  have hn := e.hom.naturality (kInjectiveLiftDerivedMap α)
  dsimp only [Functor.comp_map] at hn
  rw [kInjectiveLiftDerivedMap, q.map_preimage, h] at hn
  apply (cancel_epi (e.hom.app K)).mp
  simpa only [kInjectiveLiftDerivedMap, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id] using hn.symm

/-- Representatives of the same derived morphism into a K-injective complex
are genuinely chain homotopic. -/
def homotopyOfQMapEq (φ ψ : K ⟶ L) (h : DerivedCategory.Q.map φ = DerivedCategory.Q.map ψ) :
    Homotopy φ ψ := by
  apply HomotopyCategory.homotopyOfEq
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K) L).injective
  apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L)).mp
  simpa only [← Functor.comp_map, NatTrans.naturality] using
    congrArg (fun a ↦ (DerivedCategory.quotientCompQhIso C).hom.app K ≫ a) h

/-- The representative of an invertible derived morphism is a quasi-isomorphism. -/
instance kInjectiveLiftDerivedMap_quasiIso
    (α : DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) [IsIso α] :
    QuasiIso (kInjectiveLiftDerivedMap α) := by
  rw [← DerivedCategory.isIso_Q_map_iff_quasiIso, Q_map_kInjectiveLiftDerivedMap]
  infer_instance

end SGA.SGA2.ExposeI
