/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeV.ProjectiveHomologyExtRepresentatives
import SGA.SGA2.ExposeV.ProjectiveHomologyExtZero
import SGA.SGA2.ExposeV.ProjectiveExtConnectingCocycle
import SGA.SGA2.ExposeV.ModuleExtYonedaBoundary
import SGA.SGA2.ExposeII.ExtCoefficientSequence

/-!
# Comparing the original coefficient and Yoneda boundaries

The comparison is a theorem about the existing maps in every degree on the
unchanged module-valued Ext objects. The factor is the one forced by the
ordinary projective Hom differential and the derived-category convention.
-/

noncomputable section
universe u
open CategoryTheory Limits HomologicalComplex Opposite
open SGA.SGA2.ExposeII SGA.SGA2.ExposeIV

namespace SGA.SGA2.ExposeV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {N : ModuleCat.{u} R}

/-- The existing coefficient boundary acts on original Hom representatives
by the actual lift-and-differentiate rule. -/
theorem homCohomologyδ_mk (P : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (f₃ : P.complex.X n ⟶ S.X₃) (hf₃ : P.complex.d (n + 1) n ≫ f₃ = 0)
    (f₂ : P.complex.X n ⟶ S.X₂) (hf₂ : f₂ ≫ S.g = f₃)
    (f₁ : P.complex.X (n + 1) ⟶ S.X₁)
    (hf₁ : P.complex.d (n + 1) n ≫ f₂ = f₁ ≫ S.f) :
    homCohomologyδ P.complex S hS n
        (moduleCohomologyMk (P.complex.linearYonedaObj R S.X₃) n f₃ hf₃) =
      moduleCohomologyMk (P.complex.linearYonedaObj R S.X₁) (n + 1) f₁
        (projectiveLiftBoundary_cocycle P S hS f₂ f₁ hf₁) :=
  moduleCohomologyMk_δ (S.map (homCochainCoefficientFunctor P.complex))
    (homCochainCoefficientFunctor_shortExact P.complex S hS) n
    f₃ hf₃ f₂ hf₂ f₁ hf₁.symm (projectiveLiftBoundary_cocycle P S hS f₂ f₁ hf₁)

/-- Positive-degree projective Hom cohomology carries the original
coefficient boundary to the signed Yoneda boundary. -/
theorem projectiveModuleHomologyLinearIsoExtSucc_δ (P : ProjectiveResolution N)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (x : (P.complex.linearYonedaObj R S.X₃).homology (n + 1)) :
    ((projectiveModuleHomologyLinearIsoExtSucc P S.X₃ n).hom x).comp hS.extClass rfl =
      (n + 2 : ℤ).negOnePow •
        (projectiveModuleHomologyLinearIsoExtSucc P S.X₁ (n + 1)).hom
          (homCohomologyδ P.complex S hS (n + 1) x) := by
  obtain ⟨f₃, hf₃, rfl⟩ := moduleCohomologyMk_surjective
    (P.complex.linearYonedaObj R S.X₃) (n + 1) x
  obtain ⟨f₂, f₁, hf₂, hf₁⟩ := exists_projectiveBoundaryLift P S hS f₃ hf₃
  rw [homCohomologyδ_mk P S hS (n + 1) f₃ hf₃ f₂ hf₂ f₁ hf₁,
    projectiveModuleHomologyLinearIsoExtSucc_mk,
    projectiveModuleHomologyLinearIsoExtSucc_mk]
  exact projectiveExtMk_comp_extClass P S hS rfl f₃ hf₃ f₂ hf₂ f₁ hf₁

/-- On the original module-valued Ext objects, the positive-degree Yoneda
boundary is the degree-dependent sign times the original coefficient boundary. -/
theorem moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ_succ
    (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    moduleExtYonedaCovariantBoundary N S hS (n + 1) =
      (n + 2 : ℤ).negOnePow • extCoefficientδ N S hS (n + 1) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (moduleExtLinearEquivAbelianExt N S.X₁ (n + 1 + 1)).injective
  rw [moduleExtYonedaCovariantBoundary_compare]
  change ((projectiveModuleHomologyLinearIsoExtSucc (projectiveResolution N) S.X₃ n).hom
      (((projectiveResolution N).isoExt (n + 1) S.X₃).hom x)).comp hS.extClass rfl = _
  rw [projectiveModuleHomologyLinearIsoExtSucc_δ]
  change _ = (moduleExtLinearEquivAbelianExt N S.X₁ (n + 1 + 1))
    (((n + 2 : ℤ).negOnePow : ℤ) • (extCoefficientδ N S hS (n + 1) x))
  rw [map_zsmul]
  congr 1
  change _ = (projectiveModuleHomologyLinearIsoExtSucc (projectiveResolution N) S.X₁
    (n + 1)).hom (((projectiveResolution N).isoExt (n + 1 + 1) S.X₁).hom
      (((projectiveResolution N).isoExt (n + 1 + 1) S.X₁).inv _))
  congr 1
  exact (ConcreteCategory.congr_hom
    ((projectiveResolution N).isoExt (n + 1 + 1) S.X₁).inv_hom_id _).symm

/-- The existing module-valued coefficient boundary retains the actual
lifted representative under its specified resolution isomorphisms. -/
theorem extCoefficientδ_isoExt_inv_mk (N : ModuleCat.{u} R)
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact) (n : ℕ)
    (f₃ : (projectiveResolution N).complex.X n ⟶ S.X₃)
    (hf₃ : (projectiveResolution N).complex.d (n + 1) n ≫ f₃ = 0)
    (f₂ : (projectiveResolution N).complex.X n ⟶ S.X₂) (hf₂ : f₂ ≫ S.g = f₃)
    (f₁ : (projectiveResolution N).complex.X (n + 1) ⟶ S.X₁)
    (hf₁ : (projectiveResolution N).complex.d (n + 1) n ≫ f₂ = f₁ ≫ S.f) :
    extCoefficientδ N S hS n
        (((projectiveResolution N).isoExt n S.X₃).inv
          (moduleCohomologyMk ((projectiveResolution N).complex.linearYonedaObj R S.X₃)
            n f₃ hf₃)) =
      ((projectiveResolution N).isoExt (n + 1) S.X₁).inv
        (moduleCohomologyMk ((projectiveResolution N).complex.linearYonedaObj R S.X₁)
          (n + 1) f₁ (projectiveLiftBoundary_cocycle _ S hS f₂ f₁ hf₁)) := by
  let P := projectiveResolution N
  let x := moduleCohomologyMk (P.complex.linearYonedaObj R S.X₃) n f₃ hf₃
  change (P.isoExt (n + 1) S.X₁).inv
    (homCohomologyδ P.complex S hS n ((P.isoExt n S.X₃).hom ((P.isoExt n S.X₃).inv x))) = _
  have hx := ConcreteCategory.congr_hom (P.isoExt n S.X₃).inv_hom_id x
  change (P.isoExt n S.X₃).hom ((P.isoExt n S.X₃).inv x) = x at hx
  rw [hx, homCohomologyδ_mk P S hS n f₃ hf₃ f₂ hf₂ f₁ hf₁]

/-- In every degree, including zero, the Yoneda coefficient boundary on the
unchanged original Ext objects is exactly the signed original Hom boundary. -/
theorem moduleExtYonedaCovariantBoundary_eq_signed_extCoefficientδ
    (N : ModuleCat.{u} R) (S : ShortComplex (ModuleCat.{u} R))
    (hS : S.ShortExact) (n : ℕ) :
    moduleExtYonedaCovariantBoundary N S hS n =
      (n + 1 : ℤ).negOnePow • extCoefficientδ N S hS n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  let P := projectiveResolution N
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (P.isoExt n S.X₃).inv).mp inferInstance x
  obtain ⟨f₃, hf₃, rfl⟩ := moduleCohomologyMk_surjective
    (P.complex.linearYonedaObj R S.X₃) n y
  obtain ⟨f₂, f₁, hf₂, hf₁⟩ := exists_projectiveBoundaryLift P S hS f₃ hf₃
  apply (moduleExtLinearEquivAbelianExt N S.X₁ (n + 1)).injective
  change moduleExtLinearEquivAbelianExt N S.X₁ (n + 1)
      (moduleExtYonedaCovariantBoundary N S hS n _) =
    moduleExtLinearEquivAbelianExt N S.X₁ (n + 1)
      (((n + 1 : ℤ).negOnePow : ℤ) • (extCoefficientδ N S hS n _))
  rw [map_zsmul, moduleExtYonedaCovariantBoundary_compare,
    extCoefficientδ_isoExt_inv_mk N S hS n f₃ hf₃ f₂ hf₂ f₁ hf₁,
    moduleExtLinearEquivAbelianExt_isoExt_inv_mk,
    moduleExtLinearEquivAbelianExt_isoExt_inv_mk]
  exact projectiveExtMk_comp_extClass P S hS rfl f₃ hf₃ f₂ hf₂ f₁ hf₁

end SGA.SGA2.ExposeV
