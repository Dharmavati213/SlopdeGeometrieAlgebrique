/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.AdditiveFunctorModules
import SGA.SGA2.ExposeIV.InjectivityCriterion
import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
import Mathlib.CategoryTheory.Abelian.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# The actual category of finite modules supported on a closed set

This is the full subcategory used in SGA 2, IV.1.3: its objects are actual
finitely generated modules with support contained in `V(J)`. Over a noetherian
ring it is abelian and its inclusion in finite modules is fully faithful and
exact. No category of replacement presentations is used.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R]

/-- The support condition as an actual property of arbitrary modules. -/
def supportedModuleProperty (J : Ideal R) : ObjectProperty (ModuleCat.{u} R) :=
  fun M ↦ Module.support R M ⊆ PrimeSpectrum.zeroLocus (J : Set R)

instance (J : Ideal R) : (supportedModuleProperty J).IsSerreClass where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _, by
    change Module.support R PUnit ⊆ _
    rw [Module.support_eq_empty]
    exact Set.empty_subset _⟩
  prop_of_mono f _ h :=
    (Module.support_subset_of_injective f.hom ((ModuleCat.mono_iff_injective f).mp
      inferInstance)).trans h
  prop_of_epi f _ h :=
    (Module.support_subset_of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp
      inferInstance)).trans h
  prop_X₂_of_shortExact hS h₁ h₃ := by
    change Module.support R _ ⊆ _
    rw [Module.support_of_exact
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp hS.exact)
      ((ModuleCat.mono_iff_injective _).mp hS.mono_f)
      ((ModuleCat.epi_iff_surjective _).mp hS.epi_g)]
    exact Set.union_subset h₁ h₃

/-- Support on `V(J)` inside the genuine category of finite modules. -/
def supportedFiniteModuleProperty (J : Ideal R) : ObjectProperty (FGModuleCat.{u} R) :=
  (supportedModuleProperty J).inverseImage (forget₂ (FGModuleCat R) (ModuleCat R))

/-- The finite supported module category of IV.1.3. -/
abbrev SupportedFGModuleCat (J : Ideal R) := (supportedFiniteModuleProperty J).FullSubcategory

/-- Forget only the support condition, retaining the original finite module. -/
def supportedFiniteInclusion (J : Ideal R) : SupportedFGModuleCat J ⥤ FGModuleCat.{u} R :=
  (supportedFiniteModuleProperty J).ι

/-- The support condition imposes no restriction on morphisms. -/
def fullyFaithfulSupportedFiniteInclusion (J : Ideal R) :
    (supportedFiniteInclusion J).FullyFaithful :=
  (supportedFiniteModuleProperty J).fullyFaithfulι

instance (J : Ideal R) : (supportedFiniteInclusion J).Full :=
  (fullyFaithfulSupportedFiniteInclusion J).full

instance (J : Ideal R) : (supportedFiniteInclusion J).Faithful :=
  (fullyFaithfulSupportedFiniteInclusion J).faithful

/-- The underlying-module inclusion is likewise the actual forgetful functor. -/
def supportedFiniteToModule (J : Ideal R) : SupportedFGModuleCat J ⥤ ModuleCat.{u} R :=
  supportedFiniteInclusion J ⋙ forget₂ (FGModuleCat R) (ModuleCat R)

instance (J : Ideal R) : (supportedFiniteInclusion J).Additive := by
  unfold supportedFiniteInclusion
  infer_instance

instance (J : Ideal R) : (supportedFiniteInclusion J).Linear R := by
  unfold supportedFiniteInclusion
  infer_instance

section Noetherian

variable [IsNoetherianRing R]

instance (J : Ideal R) : (supportedFiniteModuleProperty J).IsSerreClass := by
  unfold supportedFiniteModuleProperty
  infer_instance

private theorem serre_closedUnderBinaryProducts {C : Type*} [Category C] [Abelian C]
    (P : ObjectProperty C) [P.IsSerreClass] : P.IsClosedUnderBinaryProducts := by
  apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
  rintro _ ⟨F, hF⟩
  exact P.prop_of_iso ((biprod.isoProd _ _) ≪≫ (HasLimit.isoOfNatIso (diagramIsoPair F)).symm)
    (P.prop_biprod (hF ⟨WalkingPair.left⟩) (hF ⟨WalkingPair.right⟩))

instance (J : Ideal R) : (supportedFiniteModuleProperty J).IsClosedUnderFiniteProducts := by
  let := serre_closedUnderBinaryProducts (supportedFiniteModuleProperty J)
  exact ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The finite supported category is genuinely abelian. -/
instance (J : Ideal R) : Abelian (SupportedFGModuleCat J) := inferInstance

/-- The actual inclusion preserves finite limits. -/
instance (J : Ideal R) : PreservesFiniteLimits (supportedFiniteInclusion J) := by
  have : ∀ {M N : SupportedFGModuleCat J} (f : M ⟶ N),
      PreservesLimit (parallelPair f 0) (supportedFiniteInclusion J) :=
    fun f ↦ (supportedFiniteModuleProperty J).preservesKernels_ι f
  exact Functor.preservesFiniteLimits_of_preservesKernels _

/-- The actual inclusion preserves finite colimits. -/
instance (J : Ideal R) : PreservesFiniteColimits (supportedFiniteInclusion J) := by
  have : ∀ {M N : SupportedFGModuleCat J} (f : M ⟶ N),
      PreservesColimit (parallelPair f 0) (supportedFiniteInclusion J) :=
    fun f ↦ (supportedFiniteModuleProperty J).preservesCokernels_ι f
  exact Functor.preservesFiniteColimits_of_preservesCokernels _

instance (J : Ideal R) : (supportedFiniteInclusion J).PreservesHomology := inferInstance

/-- Supported short exact sequences are actual short exact module sequences. -/
theorem supportedFiniteInclusion_shortExact (J : Ideal R)
    {S : ShortComplex (SupportedFGModuleCat J)} (hS : S.ShortExact) :
    (S.map (supportedFiniteInclusion J)).ShortExact :=
  hS.map_of_exact (supportedFiniteInclusion J)

/-- Every object has a uniform ideal-power annihilator, without adding an
annihilation witness to the definition of the category. -/
theorem supportedFinite_exists_pow_annihilator (J : Ideal R) (M : SupportedFGModuleCat J) :
    ∃ n : ℕ, J ^ n ≤ Module.annihilator R M.obj :=
  (support_subset_zeroLocus_iff_exists_pow_le_annihilator J M.obj).mp M.property

end Noetherian

end SGA.SGA2.ExposeIV
