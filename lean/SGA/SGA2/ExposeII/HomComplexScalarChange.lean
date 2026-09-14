/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.KoszulBaseChange
import SGA.SGA2.ExposeII.KoszulCoefficientSequence

/-!
# The scalar-restricted Hom complex under tensor adjunction

Tensor extension and scalar restriction identify the actual Hom complexes,
linearly over the source ring. The comparison sends a homomorphism to its
evaluation on `1 ⊗ x` and retains the original differentials.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex
open scoped ChangeOfRings

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)

/-- The tensor/restriction adjunction, with its actual source-ring linearity. -/
def extendRestrictHomLinearEquiv (P : ModuleCat.{u} R) (M : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars σ).obj
      (ModuleCat.of S ((ModuleCat.extendScalars σ).obj P ⟶ M))) ≃ₗ[R]
        (P ⟶ (ModuleCat.restrictScalars σ).obj M) :=
  { (ModuleCat.extendRestrictScalarsAdj σ).homEquiv P M with
    map_add' := by intro f g; rfl
    map_smul' := by intro r f; rfl }

/-- Evaluation on the original tensor generators. -/
@[simp]
theorem extendRestrictHomLinearEquiv_apply (P : ModuleCat.{u} R) (M : ModuleCat.{u} S)
    (f : (ModuleCat.extendScalars σ).obj P ⟶ M) (x : P) :
    extendRestrictHomLinearEquiv σ P M f x = f ((1 : S) ⊗ₜ[R,σ] x) := rfl

/-- The actual Hom-complex adjunction, including its original differentials. -/
def homComplexScalarChangeIso (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars σ).mapHomologicalComplex _).obj
      (ChainComplex.linearYonedaObj
        (((ModuleCat.extendScalars σ).mapHomologicalComplex _).obj P) S M) ≅
      P.linearYonedaObj R ((ModuleCat.restrictScalars σ).obj M) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (extendRestrictHomLinearEquiv σ (P.X i) M).toModuleIso)
    (by intro i j _; ext f; rfl)

/-- The Hom-complex adjunction commutes with every original map of a
system of complexes, in particular with all Koszul power transitions. -/
def homComplexSystemScalarChangeIso
    (K : ℕᵒᵖ ⥤ ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} S) :
    (K ⋙ (ModuleCat.extendScalars σ).mapHomologicalComplex _).op ⋙
        homCochainBifunctor.flip.obj M ⋙ (ModuleCat.restrictScalars σ).mapHomologicalComplex _ ≅
      K.op ⋙ homCochainBifunctor.flip.obj ((ModuleCat.restrictScalars σ).obj M) :=
  NatIso.ofComponents (fun n ↦ homComplexScalarChangeIso σ (K.obj n.unop) M)
    (by intro n m f; ext i g; rfl)

/-- The full original direct system of Hom--Koszul complexes commutes
with scalar restriction, including every power-transition map. -/
def koszulHomComplexSystemScalarChangeIso (fs : List R) (M : ModuleCat.{u} S) :
    (koszulSystem (ModuleCat.of S S) (fs.map σ)).op ⋙
        homCochainBifunctor.flip.obj M ⋙ (ModuleCat.restrictScalars σ).mapHomologicalComplex _ ≅
      (koszulSystem (ModuleCat.of R R) fs).op ⋙
        homCochainBifunctor.flip.obj ((ModuleCat.restrictScalars σ).obj M) :=
  Functor.isoWhiskerRight (NatIso.op (koszulSystemBaseChangeIso σ fs))
    (homCochainBifunctor.flip.obj M ⋙ (ModuleCat.restrictScalars σ).mapHomologicalComplex _) ≪≫
      homComplexSystemScalarChangeIso σ (koszulSystem (ModuleCat.of R R) fs) M

end SGA.SGA2.ExposeII
