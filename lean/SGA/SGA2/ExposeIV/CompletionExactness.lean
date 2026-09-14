/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import SGA.SGA2.ExposeIV.SupportedScalarChange

/-!
# Actual completion maps on exact sequences of complete modules

For modules already adically complete, the original completion maps are
bijective. Naturality therefore transfers exactness to the unchanged maps
on completions, with their genuine completed-ring scalar actions.
-/

noncomputable section
universe u
open CategoryTheory

namespace SGA.SGA2.ExposeIV

variable {R : Type u} [CommRing R] (J : Ideal R)

/-- The actual completion of an injective map between complete modules
is injective, with no finite-generation hypothesis on either module. -/
theorem completion_map_injective_of_complete
    {A B : Type u} [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    [IsAdicComplete J A] [IsAdicComplete J B]
    (f : A →ₗ[R] B) (hf : Function.Injective f) :
    Function.Injective (AdicCompletion.map J f) := by
  intro a b hab
  obtain ⟨a, rfl⟩ := (AdicCompletion.of_bijective J A).2 a
  obtain ⟨b, rfl⟩ := (AdicCompletion.of_bijective J A).2 b
  exact congrArg (AdicCompletion.of J A) (hf ((AdicCompletion.of_bijective J B).1 hab))

/-- Exactness is preserved by the actual completion maps when the original
modules are already complete. No finiteness or flatness is needed. -/
theorem completion_map_exact_of_complete
    {A B C : Type u} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    [IsAdicComplete J A] [IsAdicComplete J B] [IsAdicComplete J C]
    (f : A →ₗ[R] B) (g : B →ₗ[R] C) (h : Function.Exact f g) :
    Function.Exact (AdicCompletion.map J f) (AdicCompletion.map J g) := by
  intro b
  obtain ⟨b, rfl⟩ := (AdicCompletion.of_bijective J B).2 b
  constructor
  · intro hb
    have hb' : g b = 0 := (AdicCompletion.of_bijective J C).1
      (by simpa only [AdicCompletion.map_of, map_zero] using hb)
    obtain ⟨a, ha⟩ := (h b).mp hb'
    exact ⟨AdicCompletion.of J A a, by rw [AdicCompletion.map_of, ha]⟩
  · rintro ⟨a, ha⟩
    obtain ⟨a, rfl⟩ := (AdicCompletion.of_bijective J A).2 a
    have ha' : f a = b := (AdicCompletion.of_bijective J B).1 ha
    rw [AdicCompletion.map_of, (h b).mpr ⟨a, ha'⟩, map_zero]

/-- The short complex of the original completed modules and maps. -/
def completionShortComplex (S : ShortComplex (ModuleCat.{u} R)) :
    ShortComplex (ModuleCat.{u} (AdicCompletion J R)) :=
  ModuleCat.shortComplexOfCompEqZero (AdicCompletion.map J S.f.hom)
    (AdicCompletion.map J S.g.hom) (by
      rw [AdicCompletion.map_comp, ← ModuleCat.hom_comp, S.zero]
      exact AdicCompletion.map_zero J)

theorem completionShortComplex_exact_of_complete
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.Exact)
    [IsAdicComplete J S.X₁] [IsAdicComplete J S.X₂] [IsAdicComplete J S.X₃] :
    (completionShortComplex J S).Exact := by
  apply ModuleCat.shortComplex_exact
  exact completion_map_exact_of_complete J S.f.hom S.g.hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS)

/-- Completing an original scalar endomorphism gives multiplication by
its actual image in the completed ring. -/
theorem completion_map_smul_id (M : ModuleCat.{u} R) [IsAdicComplete J M] (x : R) :
    ModuleCat.ofHom (AdicCompletion.map J (x • 𝟙 M).hom) =
      algebraMap R (AdicCompletion J R) x • 𝟙 (ModuleCat.of (AdicCompletion J R)
        (AdicCompletion J M)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  obtain ⟨y, rfl⟩ := (AdicCompletion.of_bijective J M).2 y
  change AdicCompletion.map J (x • 𝟙 M).hom (AdicCompletion.of J M y) =
    algebraMap R (AdicCompletion J R) x • AdicCompletion.of J M y
  rw [AdicCompletion.map_of, algebraMap_smul]
  exact (AdicCompletion.of J M).map_smul x y

/-- Completing an already complete supported module preserves its actual
support condition over the completed ring. -/
theorem completion_supported_of_complete (hJ : J.FG)
    (M : ModuleCat.{u} R) [IsAdicComplete J M]
    (hM : supportedModuleProperty J M) :
    supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R)))
      (ModuleCat.of (AdicCompletion J R) (AdicCompletion J M)) := by
  apply (supported_restrictScalars_iff _ J hJ _).mp
  exact (Module.support_subset_of_surjective (AdicCompletion.of J M)
    (AdicCompletion.of_bijective J M).2).trans hM

end SGA.SGA2.ExposeIV
