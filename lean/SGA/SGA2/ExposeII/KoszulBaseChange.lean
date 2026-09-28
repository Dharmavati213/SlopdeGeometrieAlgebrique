/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeII.KoszulScalarChange
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Actual extension of scalars for Koszul complexes

Tensor extension along any homomorphism of commutative rings carries the
original ring-coefficient Koszul complex to the Koszul complex of the mapped
list over the target ring. In particular this applies to quotient maps;
no flatness assumption is imposed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex TensorProduct
open scoped ChangeOfRings

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R S : Type u} [CommRing R] [CommRing S] (σ : R →+* S)

/-- Tensor extension is additive on the original linear maps. -/
instance extendScalars_additive : (ModuleCat.extendScalars σ).Additive where
  map_add {M N} f g := by
    let := σ.toAlgebra
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    change (1 : S) ⊗ₜ[R,σ] (f m + g m) =
      (1 : S) ⊗ₜ[R,σ] f m + (1 : S) ⊗ₜ[R,σ] g m
    exact TensorProduct.tmul_add _ _ _

/-- The actual tensor extension sends original scalar maps to the images
of the same scalars under the given ring homomorphism. -/
theorem extendScalars_map_smul {M N : ModuleCat.{u} R} (f : M ⟶ N) (r : R) :
    (ModuleCat.extendScalars σ).map (r • f) =
      σ r • (ModuleCat.extendScalars σ).map f := by
  let := σ.toAlgebra
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (1 : S) ⊗ₜ[R,σ] (r • f m) = σ r • ((1 : S) ⊗ₜ[R,σ] f m)
  rw [← TensorProduct.smul_tmul, TensorProduct.smul_tmul']
  rfl

/-- The original tensor right-unit isomorphism, for the given ring map. -/
def extendScalarsRingIso :
    (ModuleCat.extendScalars σ).obj (ModuleCat.of R R) ≅ ModuleCat.of S S := by
  let := σ.toAlgebra
  exact (AlgebraTensorModule.rid R S S).toModuleIso

/-- Genuine Koszul base change over an arbitrary ring homomorphism. -/
def koszulBaseChangeIso (fs : List R) :
    ((ModuleCat.extendScalars σ).mapHomologicalComplex _).obj
        (koszulComplex (ModuleCat.of R R) fs) ≅
      koszulComplex (ModuleCat.of S S) (fs.map σ) :=
  koszulScalarChangeIso σ (ModuleCat.extendScalars σ) (extendScalars_map_smul σ)
    (ModuleCat.of R R) (ModuleCat.of S S) (extendScalarsRingIso σ) fs

/-- Base change of the actual inverse system, preserving every power transition. -/
def koszulSystemBaseChangeIso (fs : List R) :
    koszulSystem (ModuleCat.of R R) fs ⋙
        (ModuleCat.extendScalars σ).mapHomologicalComplex _ ≅
      koszulSystem (ModuleCat.of S S) (fs.map σ) :=
  koszulSystemScalarChangeIso σ (ModuleCat.extendScalars σ) (extendScalars_map_smul σ)
    (ModuleCat.of R R) (ModuleCat.of S S) (extendScalarsRingIso σ) fs

end SGA.SGA2.ExposeII
