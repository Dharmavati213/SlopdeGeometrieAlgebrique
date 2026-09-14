/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import SGA.SGA2.ExposeIV.MacaulayContinuousDual

/-!
# Evaluation on the original adic continuous dual

Evaluation at one is coefficient-field linear for the restriction of the
original source-induced ring action. Multiplication recovers evaluation at
every source-ring element. These are the scalar comparisons used by the
glued residue form.
-/

noncomputable section
universe u
open CategoryTheory

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]

/-- Evaluation at one, linear for the original scalar-restricted action. -/
def adicContinuousDualEvaluation (I : Ideal A) :
    (ModuleCat.restrictScalars (algebraMap K A)).obj
      (ModuleCat.of A (adicContinuousDual (K := K) I)) ⟶ ModuleCat.of K K := by
  letI : TopologicalSpace A := I.adicTopology
  letI : TopologicalSpace K := ⊥
  let V := (ModuleCat.restrictScalars (algebraMap K A)).obj
    (ModuleCat.of A (adicContinuousDual (K := K) I))
  letI := V.isModule
  refine ModuleCat.ofHom (X := V) (Y := ModuleCat.of K K)
    { toFun := fun (φ : V) => (show adicContinuousDual (K := K) I from φ) 1
      map_add' := fun φ ψ => rfl
      map_smul' := ?_ }
  intro c φ
  let ψ : adicContinuousDual (K := K) I := φ
  change ψ (1 * algebraMap K A c) = c • ψ 1
  rw [one_mul]
  have he : algebraMap K A c = c • (1 : A) := by simp [Algebra.smul_def]
  rw [he, map_smul]

@[simp]
theorem adicContinuousDualEvaluation_apply (I : Ideal A)
    (φ : adicContinuousDual (K := K) I) : adicContinuousDualEvaluation I φ = φ 1 := rfl

theorem adicContinuousDualEvaluation_smul (I : Ideal A) (a : A)
    (φ : adicContinuousDual (K := K) I) : adicContinuousDualEvaluation I (a • φ) = φ a := by
  change φ (1 * a) = φ a
  rw [one_mul]

end SGA.SGA2.ExposeIV
