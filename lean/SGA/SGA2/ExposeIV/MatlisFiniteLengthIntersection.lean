/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MatlisCompleteDuality
import SGA.SGA2.ExposeIV.FiniteLengthHomDuality

/-!
# IV.5.1: the finite-length intersection and its actual Hom duality

Finite modules belonging to the literal category `CA` are exactly the
original finite-length modules. The category identification leaves every
module and every linear map unchanged. Both actual Matlis Hom functors
restrict to the previously constructed finite-length Hom duality; their
canonical bidual evaluations agree with its original evaluation maps.
-/

noncomputable section
universe u
open CategoryTheory Opposite

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- The literal intersection of finite modules with the original category `CA`. -/
def matlisFiniteArtinianModuleProperty : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.Finite R M ∧ matlisArtinianModuleProperty R M

/-- All original linear maps between modules in the actual intersection. -/
abbrev MatlisFiniteArtinianModuleCat := (matlisFiniteArtinianModuleProperty R).FullSubcategory

variable {R} [IsNoetherianRing R]

/-- **IV.5.1, intersection assertion.** Finiteness together with the literal
`CA` property is equivalent to finite length of the original module. -/
theorem matlisFiniteArtinianModuleProperty_iff_finiteLength (M : ModuleCat.{u} R) :
    matlisFiniteArtinianModuleProperty R M ↔ IsFiniteLength R M := by
  constructor
  · rintro ⟨hfinite, hCA⟩
    have := hfinite
    have htop := (moduleLocallyArtinian_iff_finiteLength M).mp hCA.1
      (⊤ : Submodule R M) Module.Finite.fg_top
    exact htop.of_surjective (f := (⊤ : Submodule R M).subtype)
      (fun x ↦ ⟨⟨x, Submodule.mem_top⟩, rfl⟩)
  · intro hlen
    have : IsNoetherian R M := (isFiniteLength_iff_isNoetherian_isArtinian.mp hlen).1
    refine ⟨inferInstance, ?_, inferInstance⟩
    intro N _
    exact (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (hlen.of_injective (f := N.subtype) N.subtype_injective)).2

/-- The category equivalence is the identity on original modules and maps. -/
def matlisFiniteLengthIntersectionEquivalence :
    MatlisFiniteArtinianModuleCat R ≌ FiniteLengthModuleCat R where
  functor := (finiteLengthModuleProperty R).lift (matlisFiniteArtinianModuleProperty R).ι
    (fun M ↦ (matlisFiniteArtinianModuleProperty_iff_finiteLength M.obj).mp M.property)
  inverse := (matlisFiniteArtinianModuleProperty R).lift (finiteLengthInclusion R)
    (fun M ↦ (matlisFiniteArtinianModuleProperty_iff_finiteLength M.obj).mpr M.property)
  unitIso := Iso.refl _
  counitIso := Iso.refl _

/-- No original module or map changes under the intersection identification. -/
theorem matlisFiniteLengthIntersectionEquivalence_functor_forget :
    (matlisFiniteLengthIntersectionEquivalence (R := R)).functor ⋙ finiteLengthInclusion R =
      (matlisFiniteArtinianModuleProperty R).ι := rfl

theorem matlisFiniteLengthIntersectionEquivalence_inverse_forget :
    (matlisFiniteLengthIntersectionEquivalence (R := R)).inverse ⋙
        (matlisFiniteArtinianModuleProperty R).ι = finiteLengthInclusion R := rfl

/-- The original inclusion of finite-length modules into finite modules. -/
def finiteLengthToMatlisFinite : FiniteLengthModuleCat R ⥤ FGModuleCat R :=
  (ModuleCat.isFG R).lift (finiteLengthInclusion R)
    (fun M ↦ show Module.Finite R M.obj from inferInstance)

/-- The original inclusion of finite-length modules into `CA`. -/
def finiteLengthToMatlisArtinian : FiniteLengthModuleCat R ⥤ MatlisArtinianModuleCat R :=
  (matlisArtinianModuleProperty R).lift (finiteLengthInclusion R)
    (fun M ↦ ((matlisFiniteArtinianModuleProperty_iff_finiteLength M.obj).mpr M.property).2)

omit [IsLocalRing R] [IsNoetherianRing R] in
theorem finiteLengthToMatlisFinite_forget :
    finiteLengthToMatlisFinite (R := R) ⋙ (ModuleCat.isFG R).ι = finiteLengthInclusion R := rfl

theorem finiteLengthToMatlisArtinian_forget :
    finiteLengthToMatlisArtinian (R := R) ⋙ (matlisArtinianModuleProperty R).ι =
      finiteLengthInclusion R := rfl

variable (H : ModuleCat.{u} R) (hH : SupportedDualizingModule H)

include hH in
/-- Over a local ring the supported residue test is the test at every
maximal ideal, as required by the original finite-length Hom duality. -/
theorem SupportedDualizingModule.allResidueTests : moduleHomDualResidueTests (⊥ : Ideal R) H := by
  obtain ⟨_, _, hres⟩ := (supportedDualizingModule_iff_support_injective_residue H).mp hH
  intro m hm _
  have heq : m = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hm
  subst m
  exact hres _ inferInstance le_rfl

include hH in
private theorem matlisIntersectionCoefficientInjective : Injective H :=
  ((supportedDualizingModule_iff_support_injective_residue H).mp hH).2.1

/-- The finite-source Matlis functor restricts literally to the old
finite-length Hom functor, on both objects and original precomposition maps. -/
theorem finiteLength_matlisFiniteHom :
    letI := matlisIntersectionCoefficientInjective H hH
    (finiteLengthToMatlisFinite (R := R)).op ⋙ matlisFiniteHom H hH =
      finiteLengthHomDual H (hH.allResidueTests H) ⋙ finiteLengthToMatlisArtinian (R := R) := rfl

/-- The auto-duality on the intersection is the existing actual Hom
anti-equivalence, with the same coefficient module, not a new involution. -/
def matlisFiniteLengthAntiEquivalence :
    (FiniteLengthModuleCat R)ᵒᵖ ≌ FiniteLengthModuleCat R := by
  letI := matlisIntersectionCoefficientInjective H hH
  exact finiteLengthHomAntiEquivalence H (hH.allResidueTests H)

@[simp]
theorem matlisFiniteLengthAntiEquivalence_functor :
    letI := matlisIntersectionCoefficientInjective H hH
    (matlisFiniteLengthAntiEquivalence H hH).functor =
      finiteLengthHomDual H (hH.allResidueTests H) := rfl

variable [IsAdicComplete (IsLocalRing.maximalIdeal R) R]

/-- The opposite direction of complete-base Matlis duality has exactly
the same restriction to original finite-length modules. -/
theorem finiteLength_matlisArtinianHom :
    letI := matlisIntersectionCoefficientInjective H hH
    (finiteLengthToMatlisArtinian (R := R)).op ⋙ matlisArtinianHom H hH =
      finiteLengthHomDual H (hH.allResidueTests H) ⋙ finiteLengthToMatlisFinite (R := R) := rfl

/-- The original finite-length inclusion into the literal complete category. -/
def finiteLengthToMatlisComplete : FiniteLengthModuleCat R ⥤ MatlisCompleteModuleCat R :=
  finiteLengthToMatlisFinite (R := R) ⋙ (matlisCompleteFiniteEquivalence (R := R)).inverse

/-- The literal `DA`-valued Hom functor also has the same finite-length restriction. -/
theorem finiteLength_matlisHomToComplete :
    letI := matlisIntersectionCoefficientInjective H hH
    (finiteLengthToMatlisArtinian (R := R)).op ⋙ matlisHomToComplete H hH =
      finiteLengthHomDual H (hH.allResidueTests H) ⋙ finiteLengthToMatlisComplete (R := R) := rfl

/-- The canonical evaluation from the finite-module Matlis construction
is exactly the original finite-length evaluation after inclusion. -/
theorem finiteLength_matlisFiniteEvaluation (M : FiniteLengthModuleCat R) :
    letI := matlisIntersectionCoefficientInjective H hH
    ((matlisFiniteEvaluationIso H hH).hom.app
      ((finiteLengthToMatlisFinite (R := R)).obj M)).hom =
        ((finiteLengthHomEvaluationIso H (hH.allResidueTests H)).hom.app M).hom := rfl

/-- The canonical evaluation from the `CA` Matlis construction agrees
with that same evaluation on the actual intersection. -/
theorem finiteLength_matlisArtinianEvaluation (M : FiniteLengthModuleCat R) :
    letI := matlisIntersectionCoefficientInjective H hH
    ((matlisArtinianEvaluationIso H hH).hom.app
      ((finiteLengthToMatlisArtinian (R := R)).obj M)).hom =
        ((finiteLengthHomEvaluationIso H (hH.allResidueTests H)).hom.app M).hom := rfl

end SGA.SGA2.ExposeIV
