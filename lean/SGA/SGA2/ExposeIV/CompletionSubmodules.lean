/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.SupportedCompletionEquivalence

/-!
# Actual submodules of supported modules over a completed ring

Every submodule over the original ring is automatically stable under the
completed-ring action. In particular finite generation is unchanged by
restriction of scalars on supported modules. These are assertions about the
original subsets and scalar actions, not just abstract equivalence classes.
-/

noncomputable section
universe u
open CategoryTheory ModuleCat TensorProduct

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsNoetherianRing R] (J : Ideal R)
variable (M : ModuleCat.{u} (AdicCompletion J R))
variable (hM : supportedModuleProperty (J.map (algebraMap R (AdicCompletion J R))) M)

local instance : Module R M := Module.compHom M (algebraMap R (AdicCompletion J R))

include hM in
/-- Every actual `R`-submodule of a supported completed-ring module is stable
under its existing completed-ring scalar action. -/
theorem completion_submodule_smul_mem
    (N : Submodule R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M))
    (a : AdicCompletion J R) {x : M} (hx : x ∈ N) : a • x ∈ N := by
  let f := algebraMap R (AdicCompletion J R)
  let j : ModuleCat.of R N ⟶ (restrictScalars f).obj M :=
    ofHom (Y := (restrictScalars f).obj M) N.subtype
  let g : (extendScalars f).obj (ModuleCat.of R N) ⟶ M :=
    ((extendRestrictScalarsAdj f).homEquiv _ _).symm j
  have hg (y : N) : g ((1 : AdicCompletion J R) ⊗ₜ[R] y) = y.val := by
    have he := ConcreteCategory.congr_hom
      (((extendRestrictScalarsAdj f).homEquiv _ _).apply_symm_apply j) y
    exact he
  have hN : supportedModuleProperty J (ModuleCat.of R N) :=
    (Module.support_subset_of_injective N.subtype N.subtype_injective).trans
      ((supported_restrictScalars_iff f J J.fg_of_isNoetherianRing M).mpr hM)
  obtain ⟨y, hy⟩ := adicTensorUnit_surjective_of_support J N hN
    (a ⊗ₜ[R] (⟨x, hx⟩ : N))
  have he : y.val = a • x := by
    calc
      y.val = g ((1 : AdicCompletion J R) ⊗ₜ[R] y) := (hg y).symm
      _ = g (a ⊗ₜ[R] (⟨x, hx⟩ : N)) := congrArg g hy
      _ = g (a • ((1 : AdicCompletion J R) ⊗ₜ[R] (⟨x, hx⟩ : N))) := by
        congr 1
        change (a ⊗ₜ[R] (⟨x, hx⟩ : N) : AdicCompletion J R ⊗[R] N) =
          (a * 1) ⊗ₜ[R] (⟨x, hx⟩ : N)
        rw [mul_one]
      _ = a • x := by rw [map_smul, hg]
  exact he ▸ y.property

/-- The completed-ring submodule with exactly the original underlying subset. -/
def completionSubmodule
    (N : Submodule R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M)) :
    Submodule (AdicCompletion J R) M where
  carrier := {x | x ∈ N}
  zero_mem' := N.zero_mem
  add_mem' := N.add_mem
  smul_mem' := fun a _ hx => completion_submodule_smul_mem J M hM N a hx

include hM in
/-- Finite generation of an actual supported module is unchanged by
restriction from the completed ring. -/
theorem completion_restrictScalars_finite [Module.Finite (AdicCompletion J R) M] :
    Module.Finite R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M) := by
  classical
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule (AdicCompletion J R) M).FG)
  let P : Submodule R ((restrictScalars (algebraMap R (AdicCompletion J R))).obj M) :=
    Submodule.span R (s : Set M)
  have hP : P = ⊤ := by
    apply top_unique
    intro x _
    have hle : Submodule.span (AdicCompletion J R) (s : Set M) ≤
        completionSubmodule J M hM P :=
      Submodule.span_le.mpr (fun y hy => Submodule.subset_span hy)
    apply hle
    rw [hs]
    trivial
  refine ⟨?_⟩
  rw [← hP]
  exact Submodule.fg_span s.finite_toSet

end SGA.SGA2.ExposeIV
