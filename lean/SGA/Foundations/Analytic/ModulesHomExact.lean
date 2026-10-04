/-
Copyright (c) 2026 SlopdeGeometrieAlgebrique contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: SlopdeGeometrieAlgebrique contributors
-/
import SGA.Foundations.Analytic.ModulesHomStalk

/-!
# Left exactness of internal Hom

Internal Hom sends a right exact presentation of its source to a left exact sequence
of module sheaves. This is the presentation argument used in the finite-presentation
stalk comparison for the Hom sheaf.

Adopted from the unmerged branch `codex/foundations-missing-inputs` (commit `c65c9a0`, file
`ModuleHomExact.lean`).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.LocallyRingedSpace.Modules

variable {X : LocallyRingedSpace.{u}}

instance isLeftAdjoint_overFunctor (U : Opens X) :
    (SheafOfModules.overFunctor X.ringCatSheaf U).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint

lemma homOnOverEquiv_zero {M N : X.Modules} (U : Opens X) :
    homOnOverEquiv (M := M) (N := N) U 0 = 0 := rfl

/-- Precomposition by an epimorphism is injective on local morphisms. -/
theorem homOn_precomp_injective {M M' N : X.Modules} (f : M' ⟶ M) [Epi f] (U : Opens X) :
    Function.Injective (fun φ : HomOn M N U ↦ φ.precomp f) := by
  intro φ ψ h
  apply (homOnOverEquiv U).injective
  have : Epi (f.over U) :=
    inferInstanceAs (Epi ((SheafOfModules.overFunctor X.ringCatSheaf U).map f))
  apply (cancel_epi (f.over U)).mp
  simpa only [homOnOverEquiv_precomp] using congrArg (homOnOverEquiv U) h

instance mono_sheafHomPrecomp {M M' : X.Modules} (f : M' ⟶ M) [Epi f] (N : X.Modules) :
    Mono (sheafHomPrecomp f N) := by
  have : Mono (sheafHomPrecomp f N).val :=
    PresheafOfModules.mono_of_injective fun {U} ↦ homOn_precomp_injective f U.unop
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map this

/-- The complex obtained by applying internal Hom into `N` to a complex in the source. -/
def sheafHomComplex (C : ShortComplex X.Modules) (N : X.Modules) : ShortComplex X.Modules :=
  ShortComplex.mk (sheafHomPrecomp C.g N) (sheafHomPrecomp C.f N) (by
    ext U φ
    apply HomOn.ext
    funext V hV
    apply LinearMap.ext
    intro m
    change φ.app V hV (C.g.val.app (op V) (C.f.val.app (op V) m)) = 0
    have hz : C.g.val.app (op V) (C.f.val.app (op V) m) = 0 := by
      change (C.f ≫ C.g).val.app (op V) m = 0
      rw [C.zero]
      rfl
    rw [hz, map_zero])

/-- Restriction of `𝒪_X`-modules to an open `U`, with source `X.Modules` (so that the instances
of `X.Modules` apply). -/
abbrev overFunctorModules (U : Opens X) :
    X.Modules ⥤ SheafOfModules.{u} (X.ringCatSheaf.over U) :=
  SheafOfModules.overFunctor X.ringCatSheaf U

instance (U : Opens X) : (overFunctorModules U).PreservesZeroMorphisms :=
  inferInstanceAs (SheafOfModules.overFunctor X.ringCatSheaf U).PreservesZeroMorphisms

instance (U : Opens X) : Limits.PreservesFiniteColimits (overFunctorModules U) :=
  inferInstanceAs (Limits.PreservesFiniteColimits (SheafOfModules.overFunctor X.ringCatSheaf U))

/-- A right exact sequence of source sheaves induces a left exact sequence of Hom sheaves. -/
theorem exact_sheafHomComplex (C : ShortComplex X.Modules) (hC : C.Exact) [Epi C.g]
    (N : X.Modules) : (sheafHomComplex C N).Exact := by
  apply exact_of_sections
  intro U φ
  constructor
  · intro hφ
    have hCU : (C.map (overFunctorModules U)).Exact :=
      hC.map_of_epi_of_preservesCokernel _ inferInstance inferInstance
    have : Epi (C.map (overFunctorModules U)).g :=
      inferInstanceAs (Epi ((SheafOfModules.overFunctor X.ringCatSheaf U).map C.g))
    have hzero : C.f.over U ≫ homOnOverEquiv U φ = 0 := by
      rw [← homOnOverEquiv_precomp, ← homOnOverEquiv_zero U]
      exact congrArg (homOnOverEquiv U) hφ
    obtain ⟨ψ, hψ⟩ := hCU.desc' (homOnOverEquiv U φ) hzero
    refine ⟨(homOnOverEquiv U).symm ψ, ?_⟩
    apply (homOnOverEquiv U).injective
    change homOnOverEquiv U (((homOnOverEquiv U).symm ψ).precomp C.g) = homOnOverEquiv U φ
    rw [homOnOverEquiv_precomp, Equiv.apply_symm_apply]
    exact hψ
  · rintro ⟨ψ, rfl⟩
    change ((sheafHomComplex C N).f ≫ (sheafHomComplex C N).g).val.app (op U) ψ = 0
    rw [(sheafHomComplex C N).zero]
    rfl

end AlgebraicGeometry.LocallyRingedSpace.Modules
