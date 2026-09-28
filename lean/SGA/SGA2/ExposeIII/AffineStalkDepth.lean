/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIII.DepthLocalization
import SGA.SGA2.ExposeII.AffineSupport
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Actual affine stalk modules and local depth

The genuine stalk of the associated module sheaf is compared with the
localized module, semilinearly over the canonical structure-stalk ring
isomorphism. Depth is then transported to the literal module over the
actual structure-sheaf stalk ring.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry RingTheory.Sequence
open SGA.SGA2.ExposeII

namespace SGA.SGA2.ExposeIII

set_option backward.isDefEq.respectTransparency false

section Transport

variable {A B : Type u} [CommRing A] [CommRing B]

local instance ringEquivInvPair (σ : A ≃+* B) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ

local instance ringEquivInvPair_symm (σ : A ≃+* B) :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.of_ringEquiv_symm σ

/-- Depth is invariant under a simultaneous ring and semilinear module
equivalence. The support ideal is transported by the actual ring map. -/
theorem depth_eq_of_semilinearEquiv [IsNoetherianRing A] [IsNoetherianRing B]
    (σ : A ≃+* B) (I : Ideal A) {M : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    [Module.Finite A M] [Module.Finite B N]
    (e : LinearEquiv σ.toRingHom (σ' := σ.symm.toRingHom) M N) :
    depth I M = depth (I.map σ.toRingHom) N := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  rw [le_depth_iff_exists_regular, le_depth_iff_exists_regular]
  constructor
  · rintro ⟨rs, hl, hm, hr⟩
    refine ⟨rs.map σ, by simpa using hl, ?_, (e.isWeaklyRegular_congr' rs).mp hr⟩
    intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact Ideal.mem_map_of_mem _ (hm a ha)
  · rintro ⟨rs, hl, hm, hr⟩
    refine ⟨rs.map σ.symm, by simpa using hl, ?_, (e.symm.isWeaklyRegular_congr' rs).mp hr⟩
    intro a ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
    obtain ⟨a₀, ha₀, hσ⟩ :=
      (Ideal.mem_map_iff_of_surjective σ.toRingHom σ.surjective).mp (hm b hb)
    rw [← hba, ← hσ]
    simpa using ha₀

end Transport

variable {R : CommRingCat.{u}}

/-- The existing canonical structure-stalk algebra, exposed at the scheme API. -/
instance affineStalkAlgebra (p : PrimeSpectrum R) :
    Algebra R ((Spec R).presheaf.stalk p) :=
  inferInstanceAs (Algebra R ((Spec.structureSheaf R).presheaf.stalk p))

/-- The natural stalk module structure from the associated sheaf of modules. -/
instance affineStalkModule (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    Module ((Spec R).presheaf.stalk p) ((tilde M).presheaf.stalk p) :=
  inferInstanceAs (Module ((structurePresheafInCommRingCat R).stalk p)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p))

/-- The natural scalar tower is unchanged by exposing the scheme stalk API. -/
instance affineStalkScalarTower (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    IsScalarTower R ((Spec R).presheaf.stalk p) ((tilde M).presheaf.stalk p) :=
  inferInstanceAs (IsScalarTower R ((structurePresheafInCommRingCat R).stalk p)
    ↑(TopCat.Presheaf.stalk (moduleStructurePresheaf R M).presheaf p))

/-- The canonical algebra isomorphism from `Rₚ` to the actual
structure-sheaf stalk of `Spec R`. -/
def affineStalkRingEquiv (p : PrimeSpectrum R) :
    Localization.AtPrime p.asIdeal ≃ₐ[R] (Spec R).presheaf.stalk p :=
  StructureSheaf.stalkIso R p

local instance affineStalkInvPair (p : PrimeSpectrum R) :
    RingHomInvPair (affineStalkRingEquiv p).toRingHom (affineStalkRingEquiv p).symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (affineStalkRingEquiv p).toRingEquiv

local instance affineStalkInvPair_symm (p : PrimeSpectrum R) :
    RingHomInvPair (affineStalkRingEquiv p).symm.toRingHom (affineStalkRingEquiv p).toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (affineStalkRingEquiv p).toRingEquiv

/-- The canonical localization equivalence for the actual associated
module-sheaf stalk, initially as an `R`-linear equivalence. -/
def affineModuleStalkLinearEquiv (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    LocalizedModule.AtPrime p.asIdeal M ≃ₗ[R] (tilde M).presheaf.stalk p :=
  IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M) (tilde.toStalk M p).hom

/-- The stalk comparison respects scalar multiplication through the
canonical structure-stalk ring isomorphism, not merely addition. -/
def affineModuleStalkSemilinearEquiv (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    LinearEquiv (affineStalkRingEquiv p).toRingHom
      (σ' := (affineStalkRingEquiv p).symm.toRingHom)
      (LocalizedModule.AtPrime p.asIdeal M) ((tilde M).presheaf.stalk p) := by
  letI : Module (Localization.AtPrime p.asIdeal) ((tilde M).presheaf.stalk p) :=
    Module.compHom _ (affineStalkRingEquiv p).toRingHom
  have : IsScalarTower R (Localization.AtPrime p.asIdeal) ((tilde M).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      change (affineStalkRingEquiv p) (algebraMap R (Localization.AtPrime p.asIdeal) r) • m = _
      rw [AlgEquiv.commutes]
      exact IsScalarTower.algebraMap_smul ((Spec R).presheaf.stalk p) r m
  let e := (affineModuleStalkLinearEquiv M p).extendScalarsOfIsLocalization
    p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  exact { e.toAddEquiv with map_smul' := e.map_smul }

/-- The comparison carries the localization image of a coefficient to
its actual associated-sheaf germ. -/
@[simp] theorem affineModuleStalkSemilinearEquiv_mk (M : ModuleCat.{u} R)
    (p : PrimeSpectrum R) (m : M) :
    affineModuleStalkSemilinearEquiv M p
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M m) = tilde.toStalk M p m :=
  IsLocalizedModule.linearEquiv_apply _ _ _ m

/-- Explicit compatibility with the actual structure-stalk scalar action. -/
theorem affineModuleStalkSemilinearEquiv_smul (M : ModuleCat.{u} R)
    (p : PrimeSpectrum R) (r : Localization.AtPrime p.asIdeal)
    (m : LocalizedModule.AtPrime p.asIdeal M) :
    affineModuleStalkSemilinearEquiv M p (r • m) =
      affineStalkRingEquiv p r • affineModuleStalkSemilinearEquiv M p m :=
  (affineModuleStalkSemilinearEquiv M p).map_smul' r m

/-- The abelian sheaf used in local cohomology has exactly the underlying
presheaf of the actual associated module sheaf. -/
def affineTildeAbStalkIso (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    (affineTildeAbSheaf M).presheaf.stalk p ≅ (tilde M).presheaf.stalk p :=
  Iso.refl _

/-- Actual abelian-sheaf stalks are the underlying groups of localized modules. -/
def affineTildeAbStalkEquiv (M : ModuleCat.{u} R) (p : PrimeSpectrum R) :
    (affineTildeAbSheaf M).presheaf.stalk p ≃+ LocalizedModule.AtPrime p.asIdeal M :=
  (affineTildeAbStalkIso M p).addCommGroupIsoToAddEquiv.trans
    (affineModuleStalkSemilinearEquiv M p).symm.toAddEquiv

/-- Depth of the literal associated-module stalk over the actual
structure-sheaf stalk ring at `p`. This does not redefine `localDepth`. -/
def affineStalkDepth (M : ModuleCat.{u} R) (p : PrimeSpectrum R) : ℕ∞ :=
  depth (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk p))
    (ModuleCat.of ((Spec R).presheaf.stalk p) ((tilde M).presheaf.stalk p))

/-- A finite coefficient module has a finite actual stalk module over its
actual local structure-stalk ring. -/
instance affineStalkModuleFinite (M : ModuleCat.{u} R) [Module.Finite R M]
    (p : PrimeSpectrum R) :
    Module.Finite ((Spec R).presheaf.stalk p) ((tilde M).presheaf.stalk p) :=
  Module.Finite.of_surjective (affineModuleStalkSemilinearEquiv M p).toLinearMap
    (affineModuleStalkSemilinearEquiv M p).surjective

/-- Noetherianity transfers through the actual structure-stalk ring isomorphism. -/
instance affineStalkNoetherian [IsNoetherianRing R] (p : PrimeSpectrum R) :
    IsNoetherianRing ((Spec R).presheaf.stalk p) :=
  isNoetherianRing_of_ringEquiv (Localization.AtPrime p.asIdeal)
    (affineStalkRingEquiv p).toRingEquiv

/-- The localized-module depth already used in Exposé III equals depth
of the literal associated-sheaf stalk over the actual structure-stalk ring. -/
theorem localDepth_eq_affineStalkDepth [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (p : PrimeSpectrum R) :
    localDepth M p = affineStalkDepth M p := by
  have h := depth_eq_of_semilinearEquiv (affineStalkRingEquiv p).toRingEquiv
    (IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal))
    (M := ModuleCat.of (Localization.AtPrime p.asIdeal) (LocalizedModule.AtPrime p.asIdeal M))
    (N := ModuleCat.of ((Spec R).presheaf.stalk p) ((tilde M).presheaf.stalk p))
    (affineModuleStalkSemilinearEquiv M p)
  rw [IsLocalRing.map_maximalIdeal_of_surjective
    (affineStalkRingEquiv p).toRingHom (affineStalkRingEquiv p).surjective] at h
  exact h

/-- The same equality with the actual stalk-ring/module expression
displayed in full. -/
theorem localDepth_eq_actual_stalk_depth [IsNoetherianRing R]
    (M : ModuleCat.{u} R) [Module.Finite R M] (p : PrimeSpectrum R) :
    localDepth M p =
      depth (IsLocalRing.maximalIdeal ((Spec R).presheaf.stalk p))
        (ModuleCat.of ((Spec R).presheaf.stalk p) ((tilde M).presheaf.stalk p)) :=
  localDepth_eq_affineStalkDepth M p

/-- Finite global ideal-depth bounds can be checked on the literal
associated-sheaf stalk modules along the closed support. -/
theorem le_depth_iff_forall_affineStalkDepth [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    (n : ℕ∞) ≤ depth I M ↔
      ∀ p : PrimeSpectrum R, p ∈ PrimeSpectrum.zeroLocus (I : Set R) →
        (n : ℕ∞) ≤ affineStalkDepth M p := by
  simpa only [localDepth_eq_affineStalkDepth] using le_depth_iff_forall_localDepth I M n

/-- The depth infimum formula III.2.9 expressed using actual affine stalks. -/
theorem depth_eq_iInf_affineStalkDepth [IsNoetherianRing R]
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] :
    depth I M = ⨅ (p : PrimeSpectrum R) (_ : p ∈ PrimeSpectrum.zeroLocus (I : Set R)),
      affineStalkDepth M p := by
  simpa only [localDepth_eq_affineStalkDepth] using III_2_9 I M

end SGA.SGA2.ExposeIII
