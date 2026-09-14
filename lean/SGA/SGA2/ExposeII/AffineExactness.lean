/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeII.AffineSupport
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Exactness of the associated abelian sheaf

Localization preserves injections, so the associated-module-sheaf functor
preserves monomorphisms. Together with its adjunction this gives left
exactness. Surjectivity of a module map lifts the numerator of every local
fraction, proving local surjectivity of the associated abelian sheaf map.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace AlgebraicGeometry

namespace SGA.SGA2.ExposeII

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}}

/-- The associated abelian sheaf, functorially in its coefficient module. -/
def affineTildeAbFunctor : ModuleCat.{u} R ⥤ TopCat.Sheaf AddCommGrpCat.{u} (Spec R) :=
  tilde.functor R ⋙ SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf

@[simp]
theorem affineTildeAbFunctor_obj (M : ModuleCat.{u} R) :
    affineTildeAbFunctor.obj M = affineTildeAbSheaf M := rfl

/-- An injective coefficient map induces an injective map on every
open-section group of the associated sheaf. -/
theorem affineTildeAb_map_app_injective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Injective f) (U : (Spec R).Opens) :
    Function.Injective ((affineTildeAbFunctor.map f).hom.app (op U)) := by
  intro s t h
  apply Subtype.ext
  apply funext
  intro x
  exact IsLocalizedModule.map_injective x.val.asIdeal.primeCompl
    (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl M)
    (LocalizedModule.mkLinearMap x.val.asIdeal.primeCompl N) f.hom hf
      (congrArg (fun a ↦ a.val x) h)

instance affineTildeAbFunctor_preservesMonomorphisms :
    (affineTildeAbFunctor (R := R)).PreservesMonomorphisms where
  preserves f _ := by
    have : ∀ U, Mono ((affineTildeAbFunctor.map f).hom.app U) := fun U ↦
      (AddCommGrpCat.mono_iff_injective _).mpr
        (affineTildeAb_map_app_injective f
          ((ModuleCat.mono_iff_injective f).mp inferInstance) U.unop)
    have : Mono (affineTildeAbFunctor.map f).hom := NatTrans.mono_of_mono_app _
    exact CategoryTheory.Sheaf.Hom.mono_of_presheaf_mono
      (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u} (affineTildeAbFunctor.map f)

instance tildeFunctor_preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f _ := by
    apply (SheafOfModules.toSheaf (Spec R).ringCatSheaf).mono_of_mono_map
    exact inferInstanceAs (Mono (affineTildeAbFunctor.map f))

instance tildeFunctor_preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

instance tildeFunctor_preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

instance affineTildeAbFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (affineTildeAbFunctor (R := R)) := by
  let : PreservesFiniteLimits (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf) := inferInstance
  exact comp_preservesFiniteLimits (tilde.functor R) _

instance affineTildeAbFunctor_additive : (affineTildeAbFunctor (R := R)).Additive := by
  let : (SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).Additive := inferInstance
  change (tilde.functor R ⋙ SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf).Additive
  infer_instance

/-- Surjective coefficient maps lift sections locally by lifting the
numerators of their fractional representatives. -/
theorem affineTildeAb_map_locallySurjective {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hf : Function.Surjective f) :
    TopCat.Presheaf.IsLocallySurjective (affineTildeAbFunctor.map f).hom := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U s x hx
  obtain ⟨g, hxg, hle, a, ha⟩ := StructureSheaf.exists_const U s x hx
  obtain ⟨b, hb⟩ := hf a
  refine ⟨PrimeSpectrum.basicOpen g, hle, ⟨?_, hxg⟩⟩
  refine ⟨StructureSheaf.const b g _ le_rfl, ?_⟩
  change StructureSheaf.comapₗ f.hom _ _ .rfl (StructureSheaf.const b g _ le_rfl) = _
  rw [StructureSheaf.comapₗ_const, hb]
  exact ha

instance affineTildeAbFunctor_preservesEpimorphisms :
    (affineTildeAbFunctor (R := R)).PreservesEpimorphisms where
  preserves f _ := by
    apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
    exact affineTildeAb_map_locallySurjective f
      ((ModuleCat.epi_iff_surjective f).mp inferInstance)

instance affineTildeAbFunctor_preservesHomology :
    (affineTildeAbFunctor (R := R)).PreservesHomology :=
  (affineTildeAbFunctor (R := R)).preservesHomology_of_preservesEpis_and_kernels

/-- The actual associated abelian sheaf construction preserves short
exact sequences over an arbitrary commutative ring. -/
theorem affineTildeAb_shortExact {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact) :
    (S.map affineTildeAbFunctor).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map _

end SGA.SGA2.ExposeII
