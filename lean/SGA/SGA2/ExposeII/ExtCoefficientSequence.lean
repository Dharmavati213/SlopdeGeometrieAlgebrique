/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulExtComparison

/-!
# SGA 2, Exposé II, (7.6): coefficient connecting maps for Ext

The actual module-valued Ext functors have coefficient connecting maps,
obtained by applying Hom to a projective resolution. The resolution
comparison transports the exact cohomology sequence to Ext. Naturality in
the resolved module lets these maps pass to the ideal-power direct limit.
-/

noncomputable section

universe u

open CategoryTheory Limits HomologicalComplex Opposite

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

/-- The projective-resolution computation of Ext is natural in coefficients. -/
def projectiveResolutionExtNatIso {X : ModuleCat.{u} R}
    (P : ProjectiveResolution X) (i : ℕ) :
    (Ext R (ModuleCat.{u} R) i).obj (op X) ≅
      (homCohomologyBifunctor i).obj (op P.complex) :=
  NatIso.ofComponents (P.isoExt i) (fun f ↦ projectiveResolution_isoExt_coeff_naturality P f i)

instance extCoefficient_additive (X : ModuleCat.{u} R) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).Additive :=
  Functor.additive_of_iso (projectiveResolutionExtNatIso (projectiveResolution X) i).symm

/-- The actual coefficient connecting homomorphism for module-valued Ext. -/
def extCoefficientδ (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).obj S.X₃ ⟶
      ((Ext R (ModuleCat.{u} R) (i + 1)).obj (op X)).obj S.X₁ :=
  ((projectiveResolution X).isoExt i S.X₃).hom ≫
    homCohomologyδ (projectiveResolution X).complex S hS i ≫
      ((projectiveResolution X).isoExt (i + 1) S.X₁).inv

@[reassoc (attr := simp)]
theorem extCoefficientδ_comp (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    extCoefficientδ X S hS i ≫ ((Ext R (ModuleCat.{u} R) (i + 1)).obj (op X)).map S.f = 0 := by
  let P := projectiveResolution X
  apply (cancel_mono (P.isoExt (i + 1) S.X₂).hom).mp
  dsimp only [P]
  simp only [extCoefficientδ, Category.assoc, zero_comp,
    projectiveResolution_isoExt_coeff_naturality,
    Iso.inv_hom_id_assoc, homCohomologyδ_comp, comp_zero]

@[reassoc (attr := simp)]
theorem comp_extCoefficientδ (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    ((Ext R (ModuleCat.{u} R) i).obj (op X)).map S.g ≫ extCoefficientδ X S hS i = 0 := by
  simp only [extCoefficientδ, ← Category.assoc,
    projectiveResolution_isoExt_coeff_naturality]
  simp only [Category.assoc, comp_homCohomologyδ_assoc, zero_comp, comp_zero]

/-- Exactness after the Ext connecting map. -/
theorem extCoefficient_exact₁ (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (extCoefficientδ_comp X S hS i)).Exact := by
  let P := projectiveResolution X
  let e : ShortComplex.mk _ _ (extCoefficientδ_comp X S hS i) ≅
      ShortComplex.mk _ _ (homCohomologyδ_comp P.complex S hS i) :=
    ShortComplex.isoMk (P.isoExt i S.X₃) (P.isoExt (i + 1) S.X₁)
      (P.isoExt (i + 1) S.X₂)
      (by simp [extCoefficientδ, P])
      (projectiveResolution_isoExt_coeff_naturality P S.f (i + 1)).symm
  exact ShortComplex.exact_of_iso e.symm (homCohomology_exact₁ P.complex S hS i)

/-- Exactness at the middle coefficient module in the Ext sequence. -/
theorem extCoefficient_exact₂ (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (S.map ((Ext R (ModuleCat.{u} R) i).obj (op X))).Exact := by
  let P := projectiveResolution X
  exact ShortComplex.exact_of_iso (S.mapNatIso (projectiveResolutionExtNatIso P i)).symm
    (homCohomology_exact₂ P.complex S hS i)

/-- Exactness before the Ext connecting map. -/
theorem extCoefficient_exact₃ (X : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (i : ℕ) :
    (ShortComplex.mk _ _ (comp_extCoefficientδ X S hS i)).Exact := by
  let P := projectiveResolution X
  let e : ShortComplex.mk _ _ (comp_extCoefficientδ X S hS i) ≅
      ShortComplex.mk _ _ (comp_homCohomologyδ P.complex S hS i) :=
    ShortComplex.isoMk (P.isoExt i S.X₂) (P.isoExt i S.X₃)
      (P.isoExt (i + 1) S.X₁)
      (projectiveResolution_isoExt_coeff_naturality P S.g i).symm
      (by simp [extCoefficientδ, P])
  exact ShortComplex.exact_of_iso e.symm (homCohomology_exact₃ P.complex S hS i)

/-- The coefficient connecting sequence of module-valued Ext. -/
def extConnectingSequence (X : ModuleCat.{u} R) :
    ConnectingSequence (ModuleCat.{u} R) (ModuleCat.{u} R) where
  obj i := (Ext R (ModuleCat.{u} R) i).obj (op X)
  δ := extCoefficientδ X
  map_δ := comp_extCoefficientδ X
  δ_map := extCoefficientδ_comp X
  exact_left := extCoefficient_exact₃ X
  exact_right := extCoefficient_exact₁ X

/-- Connecting homomorphisms are natural contravariantly in the resolved module. -/
theorem extCoefficientδ_naturality {X Y : ModuleCat.{u} R} (f : X ⟶ Y)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (i : ℕ) :
    extCoefficientδ Y S hS i ≫ ((Ext R (ModuleCat.{u} R) (i + 1)).map f.op).app S.X₁ =
      ((Ext R (ModuleCat.{u} R) i).map f.op).app S.X₃ ≫ extCoefficientδ X S hS i := by
  let P := projectiveResolution X
  let Q := projectiveResolution Y
  let g := ProjectiveResolution.lift f P Q
  have hc := ProjectiveResolution.lift_commutes f P Q
  apply (cancel_mono (P.isoExt (i + 1) S.X₁).hom).mp
  change (Q.isoExt i S.X₃).hom ≫ homCohomologyδ Q.complex S hS i ≫
      (Q.isoExt (i + 1) S.X₁).inv ≫
        ((Ext R (ModuleCat.{u} R) (i + 1)).map f.op).app S.X₁ ≫
          (P.isoExt (i + 1) S.X₁).hom =
    ((Ext R (ModuleCat.{u} R) i).map f.op).app S.X₃ ≫
      (P.isoExt i S.X₃).hom ≫ homCohomologyδ P.complex S hS i ≫
        (P.isoExt (i + 1) S.X₁).inv ≫ (P.isoExt (i + 1) S.X₁).hom
  rw [projectiveResolution_isoExt_hom_naturality f P Q g hc S.X₁ (i + 1)]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [projectiveResolution_isoExt_hom_naturality_assoc f P Q g hc S.X₃ i]
  exact congrArg (fun t ↦ (Q.isoExt i S.X₃).hom ≫ t)
    (homCohomologyδ_naturality_complex g S hS i)

end SGA.SGA2.ExposeII
