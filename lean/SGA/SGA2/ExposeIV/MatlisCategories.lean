/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.SGA2.ExposeIV.MatlisFiniteDual
import SGA.SGA2.ExposeIV.FiniteSocleAnnihilators
import SGA.SGA2.ExposeIV.CompleteFiniteModules

/-!
# The original categories in IV.5.1

`MatlisArtinianModuleCat` is the full category of locally Artinian modules
with finite actual socle. `MatlisCompleteModuleCat` is the full category
of modules complete for the original maximal-ideal filtration, with every
positive power quotient of finite length. Over a complete noetherian local
ring the second category is explicitly identified with finite modules.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The socle carries the canonical quotient action of the residue field. -/
instance localSocleResidueModule (X : ModuleCat.{u} R) :
    Module (R ⧸ IsLocalRing.maximalIdeal R) (localSocle (R := R) X) :=
  inferInstanceAs (Module (R ⧸ IsLocalRing.maximalIdeal R)
    (Submodule.torsionBySet R X (IsLocalRing.maximalIdeal R : Set R)))

instance localSocleResidueScalarTower (X : ModuleCat.{u} R) :
    IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R) (localSocle (R := R) X) :=
  inferInstanceAs (IsScalarTower R (R ⧸ IsLocalRing.maximalIdeal R)
    (Submodule.torsionBySet R X (IsLocalRing.maximalIdeal R : Set R)))

/-- Finite generation of the actual socle is equivalently finite dimension
over the residue field, with its original quotient scalar action. -/
theorem localSocle_finite_iff_finite_residue (X : ModuleCat.{u} R) :
    Module.Finite R (localSocle (R := R) X) ↔
      Module.Finite (R ⧸ IsLocalRing.maximalIdeal R) (localSocle (R := R) X) := by
  constructor
  · intro h
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ IsLocalRing.maximalIdeal R) _
  · intro h
    exact Module.Finite.trans (R ⧸ IsLocalRing.maximalIdeal R) _

/-- The literal locally Artinian and finite-socle conditions of `CA`. -/
def matlisArtinianModuleProperty : ObjectProperty (ModuleCat.{u} R) := fun X =>
  ModuleLocallyArtinian (R := R) X ∧ Module.Finite R (localSocle (R := R) X)

/-- The original full category `CA`. -/
abbrev MatlisArtinianModuleCat := (matlisArtinianModuleProperty R).FullSubcategory

/-- The literal finite power-quotient and actual adic-completeness conditions of `DA`. -/
def matlisCompleteModuleProperty : ObjectProperty (ModuleCat.{u} R) := fun M =>
  (∀ n : ℕ, IsFiniteLength R
    (M ⧸ (IsLocalRing.maximalIdeal R ^ (n + 1) • (⊤ : Submodule R M)))) ∧
    IsAdicComplete (IsLocalRing.maximalIdeal R) M

/-- The original full category `DA`, without replacing completeness by finiteness. -/
abbrev MatlisCompleteModuleCat := (matlisCompleteModuleProperty R).FullSubcategory

variable {R} [IsNoetherianRing R]

/-- The recorded local Artinian condition gives actual closed-point support. -/
theorem MatlisArtinianModuleCat.supported (X : MatlisArtinianModuleCat R) :
    supportedModuleProperty (IsLocalRing.maximalIdeal R) X.obj :=
  (moduleLocallyArtinian_iff_support_maximalIdeal X.obj).mp X.property.1

/-- Every original annihilator stage of a `CA` object has finite length. -/
theorem MatlisArtinianModuleCat.annihilator_isFiniteLength
    (X : MatlisArtinianModuleCat R) (n : ℕ) :
    IsFiniteLength R (Submodule.torsionBySet R X.obj
      ((IsLocalRing.maximalIdeal R ^ n : Ideal R) : Set R)) := by
  have := X.property.2
  exact maximalIdealAnnihilator_isFiniteLength_of_finite_socle X.obj
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing n

/-- Finite modules have actual finite-length maximal-ideal power quotients. -/
theorem finiteModule_powerQuotient_isFiniteLength
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    IsFiniteLength R
      (M ⧸ (IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R M))) := by
  let Q := ModuleCat.of R
    (M ⧸ (IsLocalRing.maximalIdeal R ^ n • (⊤ : Submodule R M)))
  have hQ := finiteSource_powerQuotient_supported (IsLocalRing.maximalIdeal R) M n
  exact finite_supported_isFiniteLength_of_fg
    (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing Q hQ

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- Over a complete ring, the original `DA` condition is exactly finite generation. -/
theorem matlisCompleteModuleProperty_iff_finite (M : ModuleCat.{u} R) :
    matlisCompleteModuleProperty R M ↔ Module.Finite R M := by
  constructor
  · rintro ⟨hquot, hcomplete⟩
    have : IsAdicComplete (IsLocalRing.maximalIdeal R) M := hcomplete
    have hlen := hquot 0
    change IsFiniteLength R
      (M ⧸ (IsLocalRing.maximalIdeal R ^ 1 • (⊤ : Submodule R M))) at hlen
    rw [pow_one] at hlen
    have := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
    have : Module.Finite R
        (M ⧸ (IsLocalRing.maximalIdeal R • (⊤ : Submodule R M))) := inferInstance
    exact finite_of_isHausdorff_of_finite_reduction (IsLocalRing.maximalIdeal R) M
  · intro hM
    exact ⟨fun n => finiteModule_powerQuotient_isFiniteLength M (n + 1),
      isAdicComplete_of_finite (IsLocalRing.maximalIdeal R) M⟩

/-- The source's identification of `DA` with finite modules over a complete
ring is literally the identity on underlying modules and all their maps. -/
def matlisCompleteFiniteEquivalence : MatlisCompleteModuleCat R ≌ FGModuleCat R where
  functor := (ModuleCat.isFG R).lift (matlisCompleteModuleProperty R).ι
    (fun M => (matlisCompleteModuleProperty_iff_finite M.obj).mp M.property)
  inverse := (matlisCompleteModuleProperty R).lift (ModuleCat.isFG R).ι
    (fun M => (matlisCompleteModuleProperty_iff_finite M.obj).mpr inferInstance)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end SGA.SGA2.ExposeIV
