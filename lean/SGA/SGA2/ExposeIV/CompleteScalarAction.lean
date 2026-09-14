/-
Copyright (c) 2026 SGAenglishpluslean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SGAenglishpluslean contributors
-/
import Mathlib.RingTheory.AdicCompletion.Completeness

/-!
# Genuine completed scalar linearity for separated targets

An original-ring linear map between completed-ring modules is linear for
the existing completed actions when its target is separated. This is
proved by approximating each completed scalar modulo every ideal power.
In particular the original module completion map respects an already
given completed action, without transporting or replacing that action.
-/

noncomputable section
universe u

namespace SGA.SGA2.ExposeIV

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] (J : Ideal R) (hJ : J.FG)

include hJ

/-- Every completed scalar has an original scalar representative modulo
each actual ideal power. -/
theorem completion_exists_approximation (a : AdicCompletion J R) (n : ℕ) :
    ∃ r : R, a - algebraMap R (AdicCompletion J R) r ∈
      J ^ n • (⊤ : Submodule R (AdicCompletion J R)) := by
  obtain ⟨r, hr⟩ := (J ^ n • (⊤ : Submodule R R)).mkQ_surjective
    (AdicCompletion.eval J R n a)
  refine ⟨r, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker, map_sub]
  change AdicCompletion.eval J R n a - AdicCompletion.eval J R n (AdicCompletion.of J R r) = 0
  rw [AdicCompletion.eval_of, hr, sub_self]

variable {M N : Type u} [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N]
variable [Module (AdicCompletion J R) M] [Module (AdicCompletion J R) N]
variable [IsScalarTower R (AdicCompletion J R) M] [IsScalarTower R (AdicCompletion J R) N]

omit hJ in
/-- Multiplying by an approximating scalar error lands in the same original
ideal-power submodule, for an arbitrary existing completed action. -/
theorem completion_scalar_smul_mem_pow (n : ℕ) (a : AdicCompletion J R)
    (ha : a ∈ J ^ n • (⊤ : Submodule R (AdicCompletion J R))) (x : M) :
    a • x ∈ J ^ n • (⊤ : Submodule R M) := by
  have ha' : a ∈ (J ^ n).map (algebraMap R (AdicCompletion J R)) := by
    change a ∈ ((J ^ n).map (algebraMap R (AdicCompletion J R))).restrictScalars R
    rw [← Ideal.smul_top_eq_map]
    exact ha
  have hx : a • x ∈ (J ^ n).map (algebraMap R (AdicCompletion J R)) •
      (⊤ : Submodule (AdicCompletion J R) M) :=
    Submodule.smul_mem_smul ha' Submodule.mem_top
  change a • x ∈ ((J ^ n).map (algebraMap R (AdicCompletion J R)) •
    (⊤ : Submodule (AdicCompletion J R) M)).restrictScalars R at hx
  rwa [Submodule.restrictScalars_map_smul_eq, Submodule.restrictScalars_top] at hx

/-- Every original-ring linear map into a separated target respects the
original completed scalar actions. No support or finiteness is assumed. -/
theorem map_completed_smul_of_isHausdorff [IsHausdorff J N]
    (g : M →ₗ[R] N) (a : AdicCompletion J R) (x : M) :
    g (a • x) = a • g x := by
  apply (IsHausdorff.eq_iff_smodEq (I := J)).mpr
  intro n
  obtain ⟨r, hr⟩ := completion_exists_approximation J hJ a n
  let d := a - algebraMap R (AdicCompletion J R) r
  have h₁ : g (d • x) ∈ J ^ n • (⊤ : Submodule R N) :=
    Submodule.smul_top_le_comap_smul_top (J ^ n) g
      (completion_scalar_smul_mem_pow J n d hr x)
  have h₂ : d • g x ∈ J ^ n • (⊤ : Submodule R N) :=
    completion_scalar_smul_mem_pow J n d hr (g x)
  rw [SModEq.sub_mem]
  have he : g (a • x) - a • g x = g (d • x) - d • g x := by
    dsimp only [d]
    rw [sub_smul, map_sub, sub_smul, algebraMap_smul, algebraMap_smul, g.map_smul]
    abel
  rw [he]
  exact Submodule.sub_mem _ h₁ h₂

/-- The same original map, bundled with the proved completed linearity. -/
def completionLinearMap [IsHausdorff J N] (g : M →ₗ[R] N) :
    M →ₗ[AdicCompletion J R] N where
  toFun := g
  map_add' := g.map_add
  map_smul' := map_completed_smul_of_isHausdorff J hJ g

@[simp]
theorem completionLinearMap_apply [IsHausdorff J N] (g : M →ₗ[R] N) (x : M) :
    completionLinearMap J hJ g x = g x := rfl

variable (M) in
/-- The original completion map is linear for an existing completed action. -/
def completionOfLinearMap : M →ₗ[AdicCompletion J R] AdicCompletion J M := by
  have : IsAdicComplete J (AdicCompletion J M) := AdicCompletion.isAdicComplete (M := M) hJ
  exact completionLinearMap J hJ (AdicCompletion.of J M)

@[simp]
theorem completionOfLinearMap_apply (x : M) :
    completionOfLinearMap J hJ M x = AdicCompletion.of J M x := rfl

variable (M) in
/-- For an already complete module this is an equivalence for the existing
completed action, not merely for the original ring action. -/
def completionOfLinearEquiv [IsAdicComplete J M] :
    M ≃ₗ[AdicCompletion J R] AdicCompletion J M :=
  LinearEquiv.ofBijective (completionOfLinearMap J hJ M) (AdicCompletion.of_bijective J M)

@[simp]
theorem completionOfLinearEquiv_apply [IsAdicComplete J M] (x : M) :
    completionOfLinearEquiv J hJ M x = AdicCompletion.of J M x := rfl

end SGA.SGA2.ExposeIV
