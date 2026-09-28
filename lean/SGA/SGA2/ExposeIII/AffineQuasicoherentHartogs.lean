/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.SchemeModuleStalks
import SGA.SGA2.ExposeIII.AffineHartogs

/-!
# Hartogs for actual quasi-coherent modules on an affine scheme

The associated-module presentation is obtained from mathlib's genuine
quasi-coherent affine equivalence. The coefficient-finiteness hypothesis
is explicit; no affine presentation or stalk comparison is supplied as
an assumption.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- The genuine coefficient module of an actual affine scheme module. -/
def affineModuleCoefficients (M : (Spec R).Modules) : ModuleCat.{u} R :=
  (modulesSpecToSheaf.obj M).presheaf.obj (op ⊤)

/-- A quasi-coherent affine module has its canonical associated-module
presentation; this is a theorem, not an extra hypothesis. -/
def affineQuasicoherentPresentationIso (M : (Spec R).Modules) [M.IsQuasicoherent] :
    tilde (affineModuleCoefficients M) ≅ M := by
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  exact asIso M.fromTildeΓ

/-- Coefficient finiteness gives finiteness of the actual stalk module. -/
instance affineQuasicoherentStalkFinite (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R (affineModuleCoefficients M)] (p : PrimeSpectrum R) :
    Module.Finite ((Spec R).presheaf.stalk p) (schemeModuleStalk M p) := by
  have : Module.Finite ((Spec R).presheaf.stalk p)
      (schemeModuleStalk (tilde (affineModuleCoefficients M)) p) :=
    inferInstanceAs (Module.Finite ((Spec R).presheaf.stalk p)
      ((tilde (affineModuleCoefficients M)).presheaf.stalk p))
  exact Module.Finite.of_surjective
    (schemeModuleStalkLinearEquiv (affineQuasicoherentPresentationIso M) p).toLinearMap
    (schemeModuleStalkLinearEquiv (affineQuasicoherentPresentationIso M) p).surjective

/-- The localized coefficient depth equals the literal depth of the actual
quasi-coherent sheaf stalk over its actual structure-stalk ring. -/
theorem localDepth_affineModuleCoefficients [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R (affineModuleCoefficients M)] (p : PrimeSpectrum R) :
    localDepth (affineModuleCoefficients M) p = moduleStalkDepth M p := by
  have : Module.Finite ((Spec R).presheaf.stalk p)
      (schemeModuleStalk (tilde (affineModuleCoefficients M)) p) :=
    inferInstanceAs (Module.Finite ((Spec R).presheaf.stalk p)
      ((tilde (affineModuleCoefficients M)).presheaf.stalk p))
  rw [localDepth_eq_affineStalkDepth]
  change moduleStalkDepth (tilde (affineModuleCoefficients M)) p = moduleStalkDepth M p
  exact moduleStalkDepth_eq_of_iso (affineQuasicoherentPresentationIso M) p

section RestrictionTransport

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Actual section restriction transports through an actual module-sheaf
isomorphism. -/
theorem moduleRestriction_isIso_of_iso (e : M ≅ N) {U V : X.Opens} (i : U ⟶ V)
    [IsIso (M.presheaf.map i.op)] : IsIso (N.presheaf.map i.op) := by
  have hc : M.presheaf.map i.op ≫ e.hom.app U = e.hom.app V ≫ N.presheaf.map i.op :=
    e.hom.mapPresheaf.naturality i.op
  have : IsIso (e.hom.app V ≫ N.presheaf.map i.op) := by rw [← hc]; infer_instance
  exact IsIso.of_isIso_comp_left (e.hom.app V) (N.presheaf.map i.op)

theorem moduleRestriction_bijective_iff_of_iso (e : M ≅ N)
    {U V : X.Opens} (i : U ⟶ V) :
    Function.Bijective (M.presheaf.map i.op) ↔ Function.Bijective (N.presheaf.map i.op) := by
  rw [← ConcreteCategory.isIso_iff_bijective, ← ConcreteCategory.isIso_iff_bijective]
  exact ⟨fun _ => moduleRestriction_isIso_of_iso e i,
    fun _ => moduleRestriction_isIso_of_iso e.symm i⟩

end RestrictionTransport

/-- **III.3.5 on an affine scheme:** for a quasi-coherent module with finite
coefficient module, literal stalk depth at least two along `V(I)` is equivalent
to bijectivity of the actual global section restriction. -/
theorem affineQuasicoherent_hartogs_iff [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R (affineModuleCoefficients M)] (I : Ideal R) :
    (∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
      (2 : ℕ∞) ≤ moduleStalkDepth M p) ↔
      Function.Bijective (M.presheaf.map
        (homOfLE le_top : affineSupportComplement I ⟶ ⊤).op) := by
  simp only [← localDepth_affineModuleCoefficients]
  exact (le_depth_iff_forall_localDepth I (affineModuleCoefficients M) 2).symm.trans
    ((two_le_depth_iff_affineRestriction_bijective I (affineModuleCoefficients M)).trans
      (moduleRestriction_bijective_iff_of_iso (affineQuasicoherentPresentationIso M)
        (homOfLE le_top : affineSupportComplement I ⟶ ⊤)))

end SGA.SGA2.ExposeIII
