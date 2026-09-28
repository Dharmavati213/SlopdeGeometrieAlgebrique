/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.MatlisFiniteLengthIntersection
import SGA.SGA2.ExposeIV.SupportedHomCogenerator

/-!
# Actual Hom duality detects finite length without completeness

The footnote in the proof of V.3.5 uses duality over a possibly noncomplete
local ring. Finite-length duality and the injectivity of the original bidual
evaluation suffice: if the dual has finite length, the source embeds in a
finite-length double dual. No finiteness or support assumption on the source,
and no completeness assumption on the ring, is needed.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {H : ModuleCat.{u} R} (hH : SupportedDualizingModule H)

include hH

/-- A supported dualizing module preserves finite length on the original
Hom module, over an arbitrary noetherian local base. -/
theorem SupportedDualizingModule.moduleHomDual_finiteLength
    (X : ModuleCat.{u} R) (hX : IsFiniteLength R X) :
    IsFiniteLength R ((moduleHomDual H).obj (op X)) := by
  have : Injective H :=
    ((supportedDualizingModule_iff_support_injective_residue H).mp hH).2.1
  apply Module.length_ne_top_iff.mp
  rw [moduleHomDual_length_finiteLength_of_residueTests ⊥ H (hH.allResidueTests H) X hX
    (by intro p _; change (⊥ : Ideal R) ≤ p.asIdeal; exact bot_le)]
  exact Module.length_ne_top_iff.mpr hX

/-- **V.3.5, duality step:** the original Hom dual detects finite length,
even for arbitrary source modules and without completeness of the base. -/
theorem SupportedDualizingModule.moduleHomDual_finiteLength_iff
    (X : ModuleCat.{u} R) :
    IsFiniteLength R ((moduleHomDual H).obj (op X)) ↔ IsFiniteLength R X := by
  constructor
  · intro hD
    exact (hH.moduleHomDual_finiteLength _ hD).of_injective
      (f := (moduleBidualEvaluation H X).hom) (hH.moduleBidualEvaluation_injective X)
  · exact hH.moduleHomDual_finiteLength X

/-- Extended length is unchanged, including when both lengths are infinite. -/
theorem SupportedDualizingModule.moduleHomDual_length (X : ModuleCat.{u} R) :
    Module.length R ((moduleHomDual H).obj (op X)) = Module.length R X := by
  have : Injective H :=
    ((supportedDualizingModule_iff_support_injective_residue H).mp hH).2.1
  by_cases hX : IsFiniteLength R X
  · exact moduleHomDual_length_finiteLength_of_residueTests ⊥ H (hH.allResidueTests H) X hX
      (by intro p _; change (⊥ : Ideal R) ≤ p.asIdeal; exact bot_le)
  · have hD := mt (hH.moduleHomDual_finiteLength_iff X).mp hX
    rw [← Module.length_ne_top_iff, not_not] at hX hD
    exact hD.trans hX.symm

/-- In the finite-dual case the original evaluation itself is invertible,
as in the footnote to V.3.5; no chosen bidual identification is substituted. -/
theorem SupportedDualizingModule.moduleBidualEvaluation_isIso_of_finiteLength_dual
    (X : ModuleCat.{u} R) (hD : IsFiniteLength R ((moduleHomDual H).obj (op X))) :
    IsIso (moduleBidualEvaluation H X) := by
  have : Injective H :=
    ((supportedDualizingModule_iff_support_injective_residue H).mp hH).2.1
  exact moduleBidualEvaluation_isIso_finiteLength_of_residueTests ⊥ H (hH.allResidueTests H)
    X ((hH.moduleHomDual_finiteLength_iff X).mp hD)
      (by intro p _; change (⊥ : Ideal R) ≤ p.asIdeal; exact bot_le)

end SGA.SGA2.ExposeIV
