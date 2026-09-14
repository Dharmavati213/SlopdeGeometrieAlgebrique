/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.ModuleBidualSimpleTests

/-!
# The genuine category of finite-length modules

Objects are original modules of finite length, and every original linear
map is a morphism. The inclusion is fully faithful, linear, and exact.
No chosen finite presentation or support witness is part of an object.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable (R : Type u) [CommRing R]

/-- Finite length as an actual property of modules. -/
def finiteLengthModuleProperty : ObjectProperty (ModuleCat.{u} R) :=
  fun M => IsFiniteLength R M

/-- The full category in IV.4.2. -/
abbrev FiniteLengthModuleCat := (finiteLengthModuleProperty R).FullSubcategory

/-- The actual inclusion, unchanged on original modules and linear maps. -/
def finiteLengthInclusion : FiniteLengthModuleCat R ⥤ ModuleCat.{u} R :=
  (finiteLengthModuleProperty R).ι

instance : (finiteLengthInclusion R).Full := (finiteLengthModuleProperty R).fullyFaithfulι.full
instance : (finiteLengthInclusion R).Faithful :=
  (finiteLengthModuleProperty R).fullyFaithfulι.faithful
instance : (finiteLengthInclusion R).Additive := by unfold finiteLengthInclusion; infer_instance
instance : (finiteLengthInclusion R).Linear R := by unfold finiteLengthInclusion; infer_instance

/-- Finite length is closed under actual submodules, quotients, and extensions. -/
instance : (finiteLengthModuleProperty R).IsSerreClass where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    IsFiniteLength.of_subsingleton⟩
  prop_of_mono f _ h := h.of_injective ((ModuleCat.mono_iff_injective f).mp inferInstance)
  prop_of_epi f _ h := h.of_surjective ((ModuleCat.epi_iff_surjective f).mp inferInstance)
  prop_X₂_of_shortExact hS h₁ h₃ := by
    apply Module.length_ne_top_iff.mp
    rw [Module.length_eq_add_of_exact _ _
      ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)]
    simpa only [ne_eq, ENat.add_eq_top, not_or] using
      And.intro (Module.length_ne_top_iff.mpr h₁) (Module.length_ne_top_iff.mpr h₃)

instance : (finiteLengthModuleProperty R).IsClosedUnderFiniteProducts := by
  have : (finiteLengthModuleProperty R).IsClosedUnderBinaryProducts := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro _ ⟨F, hF⟩
    exact (finiteLengthModuleProperty R).prop_of_iso
      ((biprod.isoProd _ _) ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
      ((finiteLengthModuleProperty R).prop_biprod
        (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

instance : Abelian (FiniteLengthModuleCat R) := inferInstance

instance : PreservesFiniteLimits (finiteLengthInclusion R) := by
  have : ∀ {M N : FiniteLengthModuleCat R} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (finiteLengthInclusion R) :=
    fun f => (finiteLengthModuleProperty R).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

instance : PreservesFiniteColimits (finiteLengthInclusion R) := by
  have : ∀ {M N : FiniteLengthModuleCat R} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (finiteLengthInclusion R) :=
    fun f => (finiteLengthModuleProperty R).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

instance : (finiteLengthInclusion R).PreservesHomology := inferInstance

instance (M : FiniteLengthModuleCat R) : IsNoetherian R M.obj :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp M.property).1

instance (M : FiniteLengthModuleCat R) : IsArtinian R M.obj :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp M.property).2

/-- Exactness inside the full finite-length category is the original module exactness. -/
theorem finiteLengthInclusion_shortExact_iff (S : ShortComplex (FiniteLengthModuleCat R)) :
    (S.map (finiteLengthInclusion R)).ShortExact ↔ S.ShortExact :=
  ⟨fun h => CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (finiteLengthInclusion R) h, fun h => h.map_of_exact (finiteLengthInclusion R)⟩

end SGA.SGA2.ExposeIV
